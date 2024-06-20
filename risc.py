#!/usr/bin/python3

'''
file forked from @geohot/twitchcore. Commentary added, and addition made to skip program header/ begin at the 
    elf entry point (0x80000000) rather than 0x00
'''

import struct, glob, binascii, itertools
from elftools.elf.elffile import ELFFile
from cpu import Funct3, regnames, Ops

class RegFile:
    # 32 regs, + pc
    def __init__(self):
        self.regs=[0]*33
    def __getitem__(self,key):
        print('get', key)
        return self.regs[key]
    def __setitem__(self, key, value):
        if key==0:
            print("invalid map", key, value)
            return
        self.regs[key]= value & 0xffffffff # 32 bit padding
        

def reset():
    global regfile,mem 
    regfile=RegFile()
    mem=b'\x00' * 0x4000 

def signext(x, len_): #return sign rep. if sign bit
    if x>>(len_-1) == 1:
        return -((1<<len_)-x)
    return x

def arith(funct3, x, y, alt):
    if funct3==Funct3.SLLI:
        return x << (y&0x1f)
    elif funct3==Funct3.SRLI:
        ret=0
        if alt: #srai
            sb = (x >> 31)
            return ( ((0xFFFFFFFF*sb) << (32- y&0x1f)) | x >> (y&0x1f) )
    elif funct3==Funct3.ADDI:
        if alt:
            return x-y
        else:
            return x+y
    elif funct3==Funct3.ORI:
        return x|y
    elif funct3==Funct3.XORI:
        return x^y
    elif funct3==Funct3.ANDI:
        return x&y
    elif funct3==Funct3.SLT:
        return signext(x,32) < signext(y,32) 
    elif funct3==Funct3.SLTU:
        return (0xffffffff & x) < (0xffffffff & y) 

def cond(funct3, vs1, vs2):
    ret = False
    if funct3 == Funct3.BEQ:
      ret = vs1 == vs2
    elif funct3 == Funct3.BNE:
      ret = vs1 != vs2
    elif funct3 == Funct3.BLT:
      ret = sign_extend(vs1, 32) < sign_extend(vs2, 32)
    elif funct3 == Funct3.BGE:
      ret = sign_extend(vs1, 32) >= sign_extend(vs2, 32)
    elif funct3 == Funct3.BLTU:
      ret = vs1 < vs2
    elif funct3 == Funct3.BGEU:
      ret = vs1 >= vs2
    else:
      dump()
      raise Exception("write %r funct3 %r" % (opcode, funct3))
    return ret
  
def w_mem(addr, dat):
    #write to mem
    global mem
    print("writing %s bytes from addr %s to mem" % (len(dat), hex(addr)) )
    #4byte addrs
    addr-=ELF_EP
    assert addr >=0
    assert addr < len(mem) 
    mem=mem[:addr]+dat+mem[addr+len(dat):]

def r32(addr):
  addr -= ELF_EP#displace
  if addr < 0 or addr >= len(mem):
    raise Exception("read out of bounds: %s" % hex(addr))
  #print(mem[addr:addr+4])
  return struct.unpack("<I", mem[addr:addr+4])[0]

def b_arith(imm, cond):
    print("branch taken to -> ", hex(regfile[PC] + imm ))
    return regfile[PC] + imm if cond else 0

        

def step(): #parse inst, update regfiles
    global regfile
    pc=regfile[PC]
    print('starting with pc, ', hex(pc))
    ins=r32(regfile[PC])
    def get_bits(start, end):
        #print(ins)
        return (ins >> start) & ( (1 << (end-start+1)) -1) #e-s = bits to read

    op=Ops(get_bits(0,6))
    funct3=Funct3(get_bits(12,14))
    #print(funct3)

    # parse by types R/I/S/U

    imm_i=signext(get_bits(20,31), 32)
    imm_s=signext(get_bits(25,31) << 5 |  get_bits(7,11), 32)
    imm_u=get_bits(12,31)
    imm_b=signext(get_bits(8,11)<<1  | (get_bits(25,30) << 5) | get_bits(7,8) << 11 | get_bits(31,32) << 12, 13)
    imm_j=signext(get_bits(21,30) << 1 | get_bits(20,21) << 11 | get_bits(12,19) << 12 | get_bits(30,31) << 20, 21)
    
    print('branch immediate', imm_b)
    
    #index return register

    rd=get_bits(7,11)
    print("rd:",rd)
    funct7 = get_bits(25, 31)
    rs2=get_bits(20,24)
    rs1=get_bits(15,19)
    print("src registers: ", rs1, rs2)
    print(op, funct3, rs1, rs2)


    #these operations 'write back' values to the RD register
    regwriteback= op in [Ops.JAL, Ops.JALR, Ops.AUIPC, Ops.LUI, Ops.LOAD,  Ops.OP, Ops.IMM, Ops.LOAD]

    # alt value of funct7, (ops.op) add-> sub, and logical shift -> arithmetic shift
    isalt = funct7 == 0x0100000 and op == Ops.OP or (op == Ops.IMM and funct3 == Funct3.SRAI)

    branch_taken= op == Ops.BRANCH and cond(funct3, rs1, rs2)
    
    #map all types to ops ? Ops.OP: vs2 beacuse imm[11:5] is kept for func7, which determines alt instruct
    imm = {Ops.LUI: imm_u, Ops.STORE: imm_s, Ops.AUIPC: imm_u, Ops.OP: rs2, Ops.LOAD: imm_i, Ops.IMM:imm_i,
            Ops.BRANCH:imm_b, Ops.JAL:imm_j, Ops.JALR:imm_i, Ops.MISC:imm_i, Ops.SYSTEM:imm_i}[op]

    # determine reg src, depending on op type: pc if pc is written to (auipc) 
    # conditional. lui does not need pc -> upper immediate is loaded unto a separate register,
    # otherwise the src reg is encoded in rs1 [15:19]
    a_src = pc if op in [Ops.AUIPC, Ops.JAL, Ops.BRANCH] else (0 if op == Ops.LUI else rs1)

    #applying only to arithmetic ops| load-> width, though not in func3 struct
    a_funct3 = funct3 if op in [Ops.OP, Ops.IMM] else Funct3.ADD
    # non -arth: load_func = func3 if op == Ops.LOAD
    #           branch_func = func3 if op == Ops.BRANCH

    # pc is changed if jmp or branch condition is met 
    pcwrite= op in [Ops.JALR, Ops.JAL] or branch_taken
    if op==Ops.BRANCH:
        pend=b_arith(imm, branch_taken)        
    else:
        pend=arith(a_funct3, a_src, imm, isalt) # output of computation 
                                            # returns a no-take for branches

    # for a LB instruction: a_funct3: LB, a_src: rs1, imm: (I-type; [11:5] << 5 + [4:0]), isalt=False
    # print(op, funct3, a_src, imm, pend)



    if op == Ops.SYSTEM:
      # I-type instruction
      if funct3 == Funct3.ECALL:
        print("  ecall, terminates", regfile[3])
        if regfile[3] > 1:
          raise Exception("FAILURE IN TEST, PLZ CHECK")
        elif regfile[3] == 1:
          return False

    # mem is given as rs1, must be read (1 byte) and stored
    if op == Ops.LOAD:
        print('Ops.LOAD | pend: %s rs1 in %s , immediate added: %s' % pend, rs1, imm)
        #print(op, funct3, a_src, imm, pend)
        if func3 == Funct3.LB:
            pend=signext(r32(pend) & 0xFF, 8) 
        if func3 == Funct3.LW:
            pend=signext(r32(pend) & 0xFFFFFFFF, 32)
        if funct3 == Funct3.LH:
            pend=signext(r32(pend) & 0xFFFF, 16)
        if funct3 == Funct3.LHU:
            pend= r32(pend) & 0xFFFF
        if funct3 == Funct3.LBU:
            pend=r32(pend) & 0xFF

    elif op == Ops.STORE:
        print('Ops.LOAD | pend: %s rs1 in %s , immediate added: %s | new value (pend) is to be written to mem' % pend, rs1, imm)
        # why unsigned?
        if funct3==Funct3.SB:
            w_mem(pend, struct.pack("B", rs2&0xFF))
        if funct3==Funct3.SW:
            w_mem(pend, struct.pack("I", rs2&0xFFFFFFFF))
        if funct3==Funct3.SH:
            w_mem(pend, struct.pack("H", rs2&0xFFFF))
    
    # for branch/jmp: 
    #   - jal : Op.JAL, imm_i, fucnt3 = (default) Funct3.ADD (000), rs1 (src) = pc (incremented by imm)

    if pcwrite:
        print('pcwrote,', rd, op, branch_taken)
        if regwriteback: # JAL/JALR
            print('write to reg')
            regfile[rd]=PC+4 # return next instruction to RD, sometimes discarded/unneeded by program (rd specified as x0)
            #print('next address stored in register %s (rd)', (rd))
        regfile[PC]=pend             
    else: #for all other instructions, point pc to next instruction
        if regwriteback:
            print('wrote', op)
            regfile[rd]=pend
        regfile[PC]=regfile[PC]+4
        print('pc updated, ',hex(regfile[PC]))


    # display info about op
    print("Op: %s, funct3: %s, rs1: %s rs2: %s is_alt(funct7 !=0): %s immediate: %s\n\
    requires writeback: %s addressed rdest: %s r_dest_value: %s | PC @ %s Performed Computation: %s PC is now %s" %\
    (op, a_funct3, hex(a_src), rs2, isalt, imm, regwriteback, rd, regfile[rd], PC, hex(pend),  hex(regfile[PC])))
        
    
    return True

if __name__=="__main__":
    PC=32
    regfile = mem = None
    ELF_EP=0x80000000

    w_bytes=0
    for file_ in glob.glob("../twitchcore/riscv-tests/isa/rv32ui-p-*"):
        if file_.endswith('.dump'):
            continue 
        with open(file_, "rb") as f:
            reset()
            ef = ELFFile(f)
            segs  = itertools.islice(ef.iter_segments(), 1,None)
            for sec in segs:
                w_mem(sec.header.p_paddr, sec.data())
                w_bytes+=len(sec.data())
            
            regfile[PC]=ELF_EP
            f.close()

            ic=0
            while step():
               ic+=1 
            print(ic, " instructions completed")
            exit(0)

