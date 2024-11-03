from __future__ import print_function
from unicorn import *
from unicorn.arm64_const import *
from struct import unpack, pack, unpack_from, calcsize
from ida_funcs import get_func
from idc import get_qword, get_bytes, read_selection_start, read_selection_end, here, get_item_size, get_segm_attr, SEGATTR_START, SEGATTR_END
from idc import get_func_attr, FUNCATTR_START, FUNCATTR_END
from idautils import XrefsTo, Segments

PAGE_ALIGN = 0x4000  # 16k

COMPILE_GCC = 1
COMPILE_MSVC = 2

TRACE_OFF = 0
TRACE_DATA_READ = 1
TRACE_DATA_WRITE = 2
TRACE_CODE = 4


class Emu(object):
    def __init__(self, stack=0xf000000, ssize=3):
        self.arch = UC_ARCH_ARM64
        self.mode = UC_MODE_ARM
        self.stack = self._alignAddr(stack)
        self.ssize = ssize
        self.data = []
        self.regs = []
        self.curUC = None
        self.traceOption = TRACE_OFF
        self.logBuffer = []
        self.altFunc = {}
        self.minBorder = None
        self.maxBorder = None
        self._init()
        self._calcBinaryBorders()

    def _calcBinaryBorders(self):
        for seg in Segments():
            s = get_segm_attr(seg, SEGATTR_START)
            e = get_segm_attr(seg, SEGATTR_END)
            if self.minBorder == None or self.minBorder > s:
                self.minBorder = s
            if self.maxBorder == None or self.maxBorder < e:
                self.maxBorder = e
        print(f"{self.minBorder:016x} - {self.maxBorder:016x}")

    def _addTrace(self, logInfo):
        self.logBuffer.append(logInfo)

    # callback for tracing invalid memory access (READ or WRITE, FETCH)
    def _hook_mem_invalid(self, uc, access, address, size, value, user_data):
        if access in [UC_MEM_READ_UNMAPPED, UC_MEM_WRITE_UNMAPPED]:
            if address > self.minBorder and address < self.maxBorder:
                return self._hook_mem_unmapped(uc, access, address, size, value, user_data)

        if self.traceOption & TRACE_DATA_WRITE:
            self._addTrace(f"### Memory unmapped WRITE at 0x{address:x}, data size = 0x{size:x}, data value = 0x{value:x}")
        elif self.traceOption & TRACE_DATA_READ:
            self._addTrace(f"### Memory unmapped READ at 0x{address:x}, data size = 0x{size:x}")

        return False

    def _hook_mem_unmapped(self, uc, access, address, size, value, user_data):
        addr = self._alignAddr(address)
        uc.mem_map(addr, PAGE_ALIGN)
        data = self._getOriginData(addr, PAGE_ALIGN)
        uc.mem_write(addr, data)
        return True

    def _hook_mem_access(self, uc, access, address, size, value, user_data):
        if access == UC_MEM_WRITE and self.traceOption & TRACE_DATA_WRITE:
            self._addTrace(f"### Memory WRITE at 0x{address:x}, data size = 0x{size:x}, data value = 0x{value:x}")
        elif access == UC_MEM_READ and self.traceOption & TRACE_DATA_READ:
            self._addTrace(f"### Memory READ at 0x{address:x}, data size = 0x{size:x}")

    def _hook_code(self, uc, address, size, user_data):
        if self.traceOption & TRACE_CODE:
            self._addTrace(f"### Trace Instruction at 0x{address:x}, size = 0x{size:x}")
        if address in self.altFunc.keys():
            func, argc, balance = self.altFunc[address]
            try:
                sp = uc.reg_read(self.REG_SP)
                if self.REG_RA == 0:
                    RA = unpack(self.pack_fmt, str(uc.mem_read(sp, self.step)))[0]
                    sp += self.step
                else:
                    RA = uc.reg_read(self.REG_RA)

                args = []
                i = 0
                while i < argc and i < len(self.REG_ARGS):
                    args.append(uc.reg_read(self.REG_ARGS[i]))
                    i += 1
                sp2 = sp
                while i < argc:
                    args.append(unpack(self.pack_fmt, str(uc.mem_read(sp2, self.step)))[0])
                    sp2 += self.step
                    i += 1

                res = func(uc, self.logBuffer, args)
                if type(res) != int: res = 0
                uc.reg_write(self.REG_RES, res)
                uc.reg_write(self.REG_PC, RA)
                if balance:
                    uc.reg_write(self.REG_SP, sp2)
                else:
                    uc.reg_write(self.REG_SP, sp)
            except Exception as e:
                self._addTrace(f"alt exception: {e}")

    def _alignAddr(self, addr):
        return addr // PAGE_ALIGN * PAGE_ALIGN

    def _getOriginData(self, address, size):
        res = []
        for offset in range(0, size, 64):
            tmp = get_bytes(address + offset, 64)
            if tmp == None:
                res.extend([pack("<Q", get_qword(address + offset + i)) for i in range(0, 64, 8)])
            else:
                res.append(tmp)
        res = b"".join(res)
        return res[:size]

    def _init(self):
        self.step = 8
        self.pack_fmt = '<Q'
        self.REG_PC = UC_ARM64_REG_PC
        self.REG_SP = UC_ARM64_REG_SP
        self.REG_RA = UC_ARM64_REG_LR
        self.REG_RES = UC_ARM64_REG_X0
        self.REG_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X3,
                            UC_ARM64_REG_X4, UC_ARM64_REG_X5, UC_ARM64_REG_X6, UC_ARM64_REG_X7]

    def _initStackAndArgs(self, uc, RA, args):
        uc.mem_map(self.stack, (self.ssize + 1) * PAGE_ALIGN)
        sp = self.stack + self.ssize * PAGE_ALIGN
        uc.reg_write(self.REG_SP, sp)

        if self.REG_RA == 0:
            uc.mem_write(sp, pack(self.pack_fmt, RA))
        else:
            uc.reg_write(self.REG_RA, RA)

        ## init the arguments
        i = 0
        while i < len(self.REG_ARGS) and i < len(args):
            uc.reg_write(self.REG_ARGS[i], args[i])
            i += 1

        while i < len(args):
            sp += self.step
            uc.mem_write(sp, pack(self.pack_fmt, args[i]))
            i += 1

    def _getBit(self, value, offset):
        mask = 1 << offset
        return 1 if (value & mask) > 0 else 0

    def _showRegs(self, uc):
        print(">>> regs:")
        try:
            X0 = uc.reg_read(UC_ARM64_REG_X0)
            X1 = uc.reg_read(UC_ARM64_REG_X1)
            X2 = uc.reg_read(UC_ARM64_REG_X2)
            X3 = uc.reg_read(UC_ARM64_REG_X3)
            X4 = uc.reg_read(UC_ARM64_REG_X4)
            X5 = uc.reg_read(UC_ARM64_REG_X5)
            X6 = uc.reg_read(UC_ARM64_REG_X6)
            X7 = uc.reg_read(UC_ARM64_REG_X7)
            X8 = uc.reg_read(UC_ARM64_REG_X8)
            X9 = uc.reg_read(UC_ARM64_REG_X9)
            X10 = uc.reg_read(UC_ARM64_REG_X10)
            X11 = uc.reg_read(UC_ARM64_REG_X11)
            X12 = uc.reg_read(UC_ARM64_REG_X12)
            X13 = uc.reg_read(UC_ARM64_REG_X13)
            X14 = uc.reg_read(UC_ARM64_REG_X14)
            X15 = uc.reg_read(UC_ARM64_REG_X15)
            X16 = uc.reg_read(UC_ARM64_REG_X16)
            X17 = uc.reg_read(UC_ARM64_REG_X17)
            X18 = uc.reg_read(UC_ARM64_REG_X18)
            X19 = uc.reg_read(UC_ARM64_REG_X19)
            X20 = uc.reg_read(UC_ARM64_REG_X20)
            X21 = uc.reg_read(UC_ARM64_REG_X21)
            X22 = uc.reg_read(UC_ARM64_REG_X22)
            X23 = uc.reg_read(UC_ARM64_REG_X23)
            X24 = uc.reg_read(UC_ARM64_REG_X24)
            X25 = uc.reg_read(UC_ARM64_REG_X25)
            X26 = uc.reg_read(UC_ARM64_REG_X26)
            X27 = uc.reg_read(UC_ARM64_REG_X27)
            X28 = uc.reg_read(UC_ARM64_REG_X28)
            X29 = uc.reg_read(UC_ARM64_REG_X29)
            FP = uc.reg_read(UC_ARM64_REG_FP)
            SP = uc.reg_read(UC_ARM64_REG_SP)
            PC = uc.reg_read(UC_ARM64_REG_PC)
            LR = uc.reg_read(UC_ARM64_REG_LR)
            print(f"    x0:  0x{X0:016x} x1:  0x{X1:016x} x2:  0x{X2:016x} x3:  0x{X3:016x}")
            print(f"    x4:  0x{X4:016x} x5:  0x{X5:016x} x6:  0x{X6:016x} x7:  0x{X7:016x}")
            print(f"    x8:  0x{X8:016x} x9:  0x{X9:016x} x10: 0x{X10:016x} x11: 0x{X11:016x}")
            print(f"    x12: 0x{X12:016x} x13: 0x{X13:016x} x14: 0x{X14:016x} x15: 0x{X15:016x}")
            print(f"    x16: 0x{X16:016x} x16: 0x{X16:016x} x17: 0x{X17:016x} x18: 0x{X18:016x}")
            print(f"    x20: 0x{X20:016x} x21: 0x{X21:016x} x22: 0x{X22:016x} x23: 0x{X23:016x}")
            print(f"    x24: 0x{X24:016x} x25: 0x{X25:016x} x27: 0x{X27:016x} x28: 0x{X28:016x}")
            print(f"    x29: 0x{X29:016x} fp:  0x{FP:016x} sp:  0x{SP:016x} lr:  0x{LR:016x}")
            print(f"    pc:  0x{PC:016x}")
        except UcError as e:
            print(f"#ERROR: {e}")

    def _initData(self, uc):
        for address, data, init in self.data:
            addr = self._alignAddr(address)
            size = PAGE_ALIGN
            while size < len(data): size += PAGE_ALIGN
            uc.mem_map(addr, size)
            if init: uc.mem_write(addr, self._getOriginData(addr, size))
            uc.mem_write(address, data)

    def _initRegs(self, uc):
        for reg, value in self.regs:
            uc.reg_write(reg, value)

    def _createUc(self):
        self.curUC = Uc(self.arch, self.mode)
        self.curUC.ctl_set_cpu_model(UC_CPU_ARM64_MAX)

    def _emulate(self, startAddr, stopAddr, args=[], TimeOut=0, Count=0):
        try:
            self.logBuffer = []
            if self.curUC == None:
                self._createUc()

            uc = self.curUC

            self._initStackAndArgs(uc, stopAddr, args)
            self._initData(uc)
            self._initRegs(uc)

            # add the invalid memory access hook
            uc.hook_add(UC_HOOK_MEM_READ_UNMAPPED | UC_HOOK_MEM_WRITE_UNMAPPED,
                        self._hook_mem_invalid)

            uc.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, self._hook_mem_unmapped)

            # add the trace hook
            if self.traceOption & (TRACE_DATA_READ | TRACE_DATA_WRITE):
                uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, self._hook_mem_access)
            uc.hook_add(UC_HOOK_CODE, self._hook_code)

            # start emulate
            uc.emu_start(startAddr, stopAddr, timeout=TimeOut, count=Count)
        except UcError as e:
            print("#ERROR: %s" % e)

    # set the data before emulation
    def setData(self, address, data, init=False):
        self.data.append((address, data, init))

    def setReg(self, reg, value):
        self.regs.append((reg, value))

    def showRegs(self, *regs):
        if self.curUC == None:
            print("current uc is none.")
            return
        for reg in regs:
            print("0x%x" % self.curUC.reg_read(reg))

    def readStack(self, fmt, count):
        if self.curUC == None:
            print("current uc is none.")
            return
        stackData = []
        stackPointer = self.curUC.reg_read(self.REG_SP)
        for i in range(count):
            dataSize = calcsize(fmt)
            data = self.curUC.mem_read(stackPointer + i * dataSize, dataSize)
            st = unpack_from(fmt, data)
            stackData.append((stackPointer + i * dataSize, st[0]))
        return stackData

    def showData(self, fmt, addr, count=1):
        if self.curUC == None:
            print("current uc is none.")
            return
        if count > 1: print('[')
        for i in range(count):
            dataSize = calcsize(fmt)
            data = self.curUC.mem_read(addr + i * dataSize, dataSize)
            if count > 1: print('    ', end='')
            st = unpack_from(fmt, data)
            if count > 1: print(',')
        print(']') if count > 1 else print('')

    def setTrace(self, opt):
        if opt != TRACE_OFF:
            self.traceOption |= opt
        else:
            self.traceOption = TRACE_OFF

    def showTrace(self):
        logs = "\n".join(self.logBuffer)
        print(logs)
        self._showRegs(self.curUC)

    def alt(self, address, func, argc, balance=False):
        """
        If call the address, will call the func instead.
        the arguments of func : func(uc, consoleouput, args)
        """
        assert (callable(func))
        self.altFunc[address] = (func, argc, balance)

    def eFunc(self, address=None, retAddr=None, args=[]):
        if address == None: address = here()
        func_s = get_func_attr(address, FUNCATTR_START)
        func_e = get_func_attr(address, FUNCATTR_END)
        if retAddr == None:
            refs = [ref.frm for ref in XrefsTo(func_s, 0)]
            if len(refs) != 0:
                retAddr = refs[0] + get_item_size(refs[0])
            else:
                print("Please offer the return address.")
                return
        self._emulate(func_s, retAddr, args)
        res = self.curUC.reg_read(self.REG_RES)
        return res

    def eBlock(self, codeStart=None, codeEnd=None):
        if codeStart == None: codeStart = read_selection_start()
        if codeEnd == None: codeEnd = read_selection_end()
        self._emulate(codeStart, codeEnd)
        self._showRegs(self.curUC)

    def eUntilAddress(self, startAddr, stopAddr, args=[], TimeOut=0, Count=0):
        self._emulate(startAddr=startAddr, stopAddr=stopAddr, args=args, TimeOut=TimeOut, Count=Count)
        self._showRegs(self.curUC)
