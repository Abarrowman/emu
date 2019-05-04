#include <array>
#include <limits>
#include <type_traits>
#include <cstdio>

using word = uint16_t;
using dword = uint32_t;
using byte = uint8_t;

constexpr word word_max = std::numeric_limits<word>::max();
constexpr dword dword_max = std::numeric_limits<dword>::max();
constexpr size_t memory_size = size_t{ 1 } + word_max;
constexpr size_t register_count = 8;
constexpr word memory_start = 0x0800;

constexpr word stack_bottom = 0x0000;
constexpr word null_loc = 0x0000;


// Helper functions to shorten enum casts
template<typename E>
constexpr dword dv(E e) {
  return static_cast<dword>(e);
}

template<typename E>
constexpr word wv(E e) {
  return static_cast<word>(e);
}

template<typename E>
constexpr byte bv(E e) {
  return static_cast<byte>(e);
}


enum class reg_code : byte {
  ra = 0,  // the first general purpose register
  rb,      // the second general purpose register
  rc,      // the thrid general purpose register
  rd,      // the forth general purpose register
  pc,      // the program counter
  sp,      // the stack pointer
  fl,      // the flags register
  de,      // the debug register
};

enum class flag_bit_idx : word {
  ze = 0,  // zero bit
  ca,      // carry bit 
  si,      // z_sign bit
  ov,      // overflow
  er       // error bit    
};

enum class flag_bit : word {
  ze = 1 << wv(flag_bit_idx::ze),  // zero bit
  ca = 1 << wv(flag_bit_idx::ca),  // carry bit 
  si = 1 << wv(flag_bit_idx::si),  // z_sign bit
  ov = 1 << wv(flag_bit_idx::ov),  // error bit
  er = 1 << wv(flag_bit_idx::er)   // error bit
};

enum class error_code : word {
  np = 0,  // null pointer 
  dz,      // division by zero
  bop      // bad op code
};

enum class op_code : byte {
  // special op codes
  nop = 0,  // no operation
  hlt,      // halt
  
  // io op codes
  mov,      // move
  cmove,    // conditionally move if ze=1 (cmp dst = src)
  cmovg,    // conditionally move if si=ov & ze=0 (cmp signed dst > src)
  cmova,    // conditionally move if cf=0 & ze=0 (cmp unsigned dst > src)

  // stack op codes
  call,     // pushes pc then mov 
  push,     // pushes a value onto the stack
  pop,      // pops a value from the stack

  // core arithmatic  op codes
  cmp,      // compare
  add,      // addition +=
  sub,      // subtraction -=

  // other arithmatic op codes
  mul,      // multiplication *=
  div,      // division /=
  rem,      // remainder %=

  // bitwise op codes
  ande,      // bitwise and &= (not called and because it is a c++ keyword)
  ore,       // bitwise or |= (not called or because it is a c++ keyword)
  xore,      // bitwise or ^= (not called xor because it is a c++ keyword)
  lsh,      // left shift <<=
  rshl,     // logical right shift >>>=
  rsha      // arithmatic right shift  >>=
};

enum class ind_bits : byte {
  di = 0x1,  // destination indirect
  si = 0x2,  // source indirect
  cs = 0x4   // constant source
};

enum class ind_mode : byte {
  ddr = 0x0,  //  dst =  src 000
  idr = 0x1,  // *dst =  src 001
  dir = 0x2,  //  dst = *src 010
  iir = 0x3,  // *dst = *src 011
  ddc = 0x4,  //  dst =  val 100
  idc = 0x5,  // *dst =  val 101
  dic = 0x6,  //  dst = *val 110
  iic = 0x7   // *dst = *val 111
};

struct state {
  bool running;
  std::array<word, register_count> registers;
  std::array<byte, memory_size> memory;
};

struct instruction {
  op_code op;     // bits  0 -  5
  ind_mode mode;  // bits  6 -  8
  reg_code dst;   // bits  9 - 11
  reg_code src;   // bits 12 - 14
  // bit 15 is currently unused 
  word val;      // bits 16 - 31

  instruction() {}

  instruction(dword inst) :
    op(static_cast<op_code>(inst & 0x3f)),           // bits  0 -  5
    mode(static_cast<ind_mode>((inst >> 6) & 0x7)),  // bits  6 -  8
    dst(static_cast<reg_code>((inst >> 9) & 0x7)),   // bits  9 - 11
    src(static_cast<reg_code>((inst >> 12) & 0x7)),  // bits 12 - 14
    val(inst >> 16) {}                               // bits 16 - 31

  instruction(
    op_code o,
    ind_mode m = ind_mode::ddr,
    reg_code d = reg_code::ra,
    reg_code s = reg_code::ra,
    word v = 0) :
    op(o),
    mode(m),
    dst(d),
    src(s),
    val(v) {}

  dword to_dword() const {
    dword result = dv(op) | (dv(mode) << 6) | (dv(dst) << 9) | (dv(src) << 12) | (dv(val) << 16);
    instruction again{ result };
    return result;
  }
};

void null_error(state& s) {
  s.running = false;
  s.registers[bv(reg_code::fl)] |= wv(flag_bit::er);
  s.registers[bv(reg_code::de)] |= wv(error_code::np);
}

void div_by_zero_error(state& s) {
  s.running = false;
  s.registers[bv(reg_code::fl)] |= wv(flag_bit::er);
  s.registers[bv(reg_code::de)] |= wv(error_code::dz);
}

void null_check(state& s, word loc) {
  if (loc == null_loc) {
    null_error(s);
  }
}

dword read_dword(state& s, word loc) {
  null_check(s, loc);

  dword first = s.memory[loc];
  dword second = s.memory[loc + 1];
  dword third = s.memory[loc + 2];
  dword forth = s.memory[loc + 3];

  dword result = first | (second << 8) | (third << 16) | (forth << 24);
  return result;
}

word read_word(state& s, word loc) {
  null_check(s, loc);

  word first = s.memory[loc];
  word second = s.memory[loc + 1];

  word result = first | (second << 8);
  return result;
}

void write_word(state& s, word loc, word val) {
  null_check(s, loc);

  s.memory[loc] = val & 0xff;
  s.memory[loc + 1] = val >> 8;
}

void write_dword(state& s, word loc, dword val) {
  null_check(s, loc);

  s.memory[loc] = val & 0xff;
  s.memory[loc + 1] = (val >> 8) & 0xff;
  s.memory[loc + 2] = (val >> 16) & 0xff;
  s.memory[loc + 3] = (val >> 24) & 0xff;
}

void push_word(state& s, word w) {
  s.registers[bv(reg_code::sp)] += sizeof(word);
  write_word(s, s.registers[bv(reg_code::sp)], w);
}

word pop_word(state& s) {
  word popped = read_word(s, s.registers[bv(reg_code::sp)]);
  s.registers[bv(reg_code::sp)] -= sizeof(word);
  return popped;
}

word get_rvalue(state& s, instruction inst) {
  word right_val;
  if (bv(inst.mode) & bv(ind_bits::cs)) {
    right_val = inst.val;
  } else {
    right_val = s.registers[bv(inst.src)];
  }

  if (bv(inst.mode) & bv(ind_bits::si)) {
    right_val = read_word(s, right_val);
  }

  return right_val;
}

void set_lvalue(state& s, instruction inst, word val) {
  if (bv(inst.mode) & bv(ind_bits::di)) {
    write_word(s, s.registers[bv(inst.dst)], val);
  } else {
    s.registers[bv(inst.dst)] = val;
  }
}

word get_lvalue(state& s, instruction inst) {
  word left_val;
  if (bv(inst.mode) & bv(ind_bits::di)) {
    left_val = read_word(s, s.registers[bv(inst.dst)]);
  } else {
    left_val = s.registers[bv(inst.dst)];
  }
  return left_val;
}

template<bool addition>
word set_arithmatic_flags(state& s, word x, word y, dword result) {
  word z = static_cast<word>(result);

  word carry = static_cast<word>((result >> 16) & 0x1);
  word z_sign = (z >> 15) & 0x1;
  word zero = (z == 0);

  word x_sign = (x >> 15) & 0x1;
  word y_sign = (y >> 15) & 0x1;

  // if x and y have the same sign and x and z have different signs
  word add_overflow = (1 ^ x_sign ^ y_sign) & (x_sign ^ z_sign);

  // if x and y have different signs and x and z have different signs
  word sub_overflow = (x_sign ^ y_sign)  & (x_sign ^ z_sign);

  word overflow = addition ? add_overflow : sub_overflow;

  word disable_mask = ~(
    wv(flag_bit::ze) |
    wv(flag_bit::ca) |
    wv(flag_bit::si) |
    wv(flag_bit::ov));

  word enable_mask =
    (zero << wv(flag_bit_idx::ze)) |
    (carry << wv(flag_bit_idx::ca)) |
    (z_sign << wv(flag_bit_idx::si)) |
    (overflow << wv(flag_bit_idx::ov));

  word cleared = s.registers[bv(reg_code::fl)] & disable_mask;
  s.registers[bv(reg_code::fl)] = cleared | enable_mask;

  return z;
}

template<typename F>
void binary_op(F f, state& s, instruction inst) {
  word right_val = get_rvalue(s, inst);
  word left_val = get_lvalue(s, inst);
  
  word result = f(s, left_val, right_val);
  set_lvalue(s, inst, result);
}

void add_op(state& s, instruction inst) {
  word right_val = get_rvalue(s, inst);
  word left_val = get_lvalue(s, inst);

  dword result = static_cast<dword>(left_val) + right_val;
  word final_val = set_arithmatic_flags<true>(s, left_val, right_val, result);
  set_lvalue(s, inst, final_val);
}

void sub_op(state& s, instruction inst) {
  word right_val = get_rvalue(s, inst);
  word left_val = get_lvalue(s, inst);

  dword result = static_cast<dword>(left_val) - right_val;
  word final_val = set_arithmatic_flags<false>(s, left_val, right_val, result);
  set_lvalue(s, inst, final_val);
}

template<typename F>
void condition_move_op(F f, state& s, instruction inst) {
  word right_val = get_rvalue(s, inst);
  word flags = s.registers[bv(reg_code::fl)];
  if (f(flags)) {
    set_lvalue(s, inst, right_val);
  }
}

void cmp_op(state& s, instruction inst) {
  word right_val = get_rvalue(s, inst);
  word left_val = get_lvalue(s, inst);

  dword result = static_cast<dword>(left_val) - right_val;
  set_arithmatic_flags<false>(s, left_val, right_val, result);
}

void mov_op(state& s, instruction inst) {
  condition_move_op([](word flags) { return true; }, s, inst);
}

void push_op(state& s, instruction inst) {
  word right_val = get_rvalue(s, inst);
  push_word(s, right_val);
}

void pop_op(state& s, instruction inst) {
  word popped = pop_word(s);
  set_lvalue(s, inst, popped);
}

void call_op(state& s, instruction inst) {
  push_word(s, s.registers[bv(reg_code::pc)]);
  mov_op(s, inst);
}

void hlt_op(state& s, instruction inst) {
  s.running = false;
  s.registers[bv(reg_code::pc)] -= sizeof(dword);

}

void loop(state& s) {
  while (s.running) {
    word op_address = s.registers[bv(reg_code::pc)];
    dword inst_word = read_dword(s, op_address);
    instruction inst = { inst_word };
    s.registers[bv(reg_code::pc)] += sizeof(dword);

    switch (inst.op) {
    case op_code::nop:
      break;

    case op_code::hlt:
      hlt_op(s, inst);
      break;

    case op_code::mov:
      mov_op(s, inst);
      break;

    case op_code::cmove:
      condition_move_op([](word flags) {
        word zero = ((flags >> wv(flag_bit_idx::ze)) & 0x1);
        return zero;
      }, s, inst);
      break;

    case op_code::cmovg:
      condition_move_op([](word flags) {
        word zero = ((flags >> wv(flag_bit_idx::ze)) & 0x1);
        word sign = ((flags >> wv(flag_bit_idx::si)) & 0x1);
        word overflow = ((flags >> wv(flag_bit_idx::ov)) & 0x1);

        // si=ov and ze=0
        return (1 ^ sign ^ overflow) & (1 ^ zero);
      }, s, inst);
      break;

    case op_code::cmova:
      condition_move_op([](word flags) {
        word zero = ((flags >> wv(flag_bit_idx::ze)) & 0x1);
        word carry = ((flags >> wv(flag_bit_idx::ca)) & 0x1);
        // ca=0 and ze=0
        return (1 ^ carry) & (1 ^ zero);
      }, s, inst);
      break;

    case op_code::call:
      call_op(s, inst);
      break;
    
    case op_code::push:
      push_op(s, inst);
      break;

    case op_code::pop:
      pop_op(s, inst);
      break;

    case op_code::cmp:
      cmp_op(s, inst);
      break;

    case op_code::add:
      add_op(s, inst);
      break;

    case op_code::sub:
      sub_op(s, inst);
      break;

    case op_code::mul:
      binary_op([](state& s, word x, word y) {
        return x * y;
      }, s, inst);
      break;

    case op_code::div:
      binary_op([](state& s, word x, word y) {
        if (y == 0) {
          div_by_zero_error(s);
          return 0;
        } else {
          return x / y;
        }
      }, s, inst);
      break;

    case op_code::rem:
      binary_op([](state& s, word x, word y) {
        if (y == 0) {
          div_by_zero_error(s);
          return 0;
        } else {
          return x % y;
        }
      }, s, inst);
      break;

    case op_code::ande:
      binary_op([](state& s, word x, word y) {
        return x & y;
      }, s, inst);
      break;

    case op_code::ore:
      binary_op([](state& s, word x, word y) {
        return x | y;
      }, s, inst);
      break;

    case op_code::xore:
      binary_op([](state& s, word x, word y) {
        return x ^ y;
      }, s, inst);
      break;

    case op_code::lsh:
      binary_op([](state& s, word x, word y) {
        return x << y;
      }, s, inst);
      break;

    case op_code::rshl:
      binary_op([](state& s, word x, word y) {
        return x >> y;
      }, s, inst);
      break;

    case op_code::rsha:
      binary_op([](state& s, word x, word y) {
        word result = x >> y;
        word xsign = (x >> 15) & 0x1;
        word ysign = (y >> 15) & 0x1;
        if (xsign & (~ysign)) {
          result |= ~(word_max >> y);
        }
        return result;
      }, s, inst);
      break;

    default:
      s.registers[bv(reg_code::de)] = wv(error_code::bop);
      s.registers[bv(reg_code::fl)] |= wv(flag_bit::er);
      s.running = false;
      break;
    }

  }
}

void init(state& s) {
  s.registers[bv(reg_code::ra)] = 0;
  s.registers[bv(reg_code::rb)] = 0;
  s.registers[bv(reg_code::rc)] = 0;
  s.registers[bv(reg_code::rd)] = 0;
  s.registers[bv(reg_code::pc)] = memory_start;
  s.registers[bv(reg_code::sp)] = stack_bottom;
  s.registers[bv(reg_code::fl)] = 0;
  s.registers[bv(reg_code::de)] = 0;

  // initialize program
  s.memory.fill(0);
  write_dword(s, 0x0800, instruction{ op_code::nop }.to_dword());
  write_dword(s, 0x0804, instruction{ op_code::mov, ind_mode::ddc, reg_code::ra, reg_code::ra, 0x1337 }.to_dword());
  write_dword(s, 0x0808, instruction{ op_code::mov, ind_mode::ddr, reg_code::rb, reg_code::ra }.to_dword());
  write_dword(s, 0x080c, instruction{ op_code::mov, ind_mode::ddc, reg_code::rc, reg_code::ra, 0x0707 }.to_dword());
  write_dword(s, 0x0810, instruction{ op_code::mov, ind_mode::ddc, reg_code::rd, reg_code::ra, 0x0a0a }.to_dword());

  write_dword(s, 0x0814, instruction{ op_code::add, ind_mode::ddr, reg_code::rd, reg_code::rc }.to_dword());            // rd = 0x1111
  write_dword(s, 0x0818, instruction{ op_code::mul, ind_mode::ddc, reg_code::rd, reg_code::ra, 2 }.to_dword());         // rd = 0x2222
  write_dword(s, 0x081c, instruction{ op_code::sub, ind_mode::ddc, reg_code::rd, reg_code::ra, 0x0220 }.to_dword());    // rd = 0x2002
  write_dword(s, 0x0820, instruction{ op_code::mov, ind_mode::ddr, reg_code::rc, reg_code::rd }.to_dword());            // rc = 0x2002
  write_dword(s, 0x0824, instruction{ op_code::lsh, ind_mode::ddc, reg_code::rd, reg_code::ra, 2 }.to_dword());         // rd = 0x8008
  write_dword(s, 0x0828, instruction{ op_code::rsha, ind_mode::ddc, reg_code::rd, reg_code::ra, 1 }.to_dword());        // rd = 0xc004
  write_dword(s, 0x082c, instruction{ op_code::rshl, ind_mode::ddc, reg_code::rd, reg_code::ra, 1 }.to_dword());        // rd = 0x6002
  write_dword(s, 0x0830, instruction{ op_code::xore, ind_mode::ddr, reg_code::rd, reg_code::rc }.to_dword());             // rd = 0x4000
  write_dword(s, 0x0834, instruction{ op_code::add, ind_mode::ddc, reg_code::rd, reg_code::ra, 0xf000 }.to_dword());    // rd = 0x3000
  write_dword(s, 0x0838, instruction{ op_code::mov, ind_mode::ddr, reg_code::pc, reg_code::rd }.to_dword());            // pc = 0x3000

  write_dword(s, 0x083c, instruction{ op_code::hlt }.to_dword()); // do not halt here

  write_dword(s, 0x3000, instruction{ op_code::rem, ind_mode::ddr, reg_code::rc, reg_code::rb }.to_dword());            // rc = 0x0ccb
  write_dword(s, 0x3004, instruction{ op_code::cmp, ind_mode::ddc, reg_code::rc, reg_code::ra, 0x0ccb }.to_dword());    // ze = 1
  write_dword(s, 0x3008, instruction{ op_code::cmove, ind_mode::ddc, reg_code::pc, reg_code::ra, 0x4000 }.to_dword());  // ze = 1
  write_dword(s, 0x300c, instruction{ op_code::hlt }.to_dword()); // do not halt here

  write_dword(s, 0x4000, instruction{ op_code::push, ind_mode::ddr, reg_code::ra, reg_code::ra }.to_dword());           // *sp = 0x1337 sp = 0x0002
  write_dword(s, 0x4004, instruction{ op_code::sub, ind_mode::ddc, reg_code::ra, reg_code::ra, 1 }.to_dword());         // ra = 0x1336

  write_dword(s, 0x4008, instruction{ op_code::cmp, ind_mode::idr, reg_code::sp, reg_code::ra }.to_dword());            // ze=0 ca=0
  write_dword(s, 0x400c, instruction{ op_code::cmova, ind_mode::ddc, reg_code::pc, reg_code::ra, 0x5000 }.to_dword());  //
  write_dword(s, 0x4010, instruction{ op_code::hlt }.to_dword()); // do not halt here

  write_dword(s, 0x5000, instruction{ op_code::pop, ind_mode::ddr, reg_code::rc }.to_dword());                          // rc=1337 sp=0x0000
  write_dword(s, 0x5004, instruction{ op_code::hlt }.to_dword()); // halt here

  s.running = true;
}

void print_registers(state& s) {
  printf("ra = %04x\n", s.registers[bv(reg_code::ra)]);
  printf("rb = %04x\n", s.registers[bv(reg_code::rb)]);
  printf("rc = %04x\n", s.registers[bv(reg_code::rc)]);
  printf("rd = %04x\n", s.registers[bv(reg_code::rd)]);
  printf("pc = %04x\n", s.registers[bv(reg_code::pc)]);
  printf("sp = %04x\n", s.registers[bv(reg_code::sp)]);

  word flags = s.registers[bv(reg_code::fl)];

  printf("fl = [ze=%x, ca=%x, si=%x, er=%x]\n",
    (flags >> wv(flag_bit_idx::ze)) & 1,
    (flags >> wv(flag_bit_idx::ca)) & 1,
    (flags >> wv(flag_bit_idx::si)) & 1,
    (flags >> wv(flag_bit_idx::er)) & 1);
  printf("de = %04x\n", s.registers[bv(reg_code::de)]);
}

int main() {
  state s;
  init(s);
  loop(s);
  print_registers(s);

  word flags = s.registers[wv(reg_code::fl)];
  if (flags & wv(flag_bit::er)) {
    return s.registers[wv(reg_code::de)];
  } else {
    return 0;
  }
}
