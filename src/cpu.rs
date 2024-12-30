use crate::opcodes;
use bitflags::{bitflags, Flags};
use std::collections::HashMap;

bitflags! {
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIV           = 0b10000000;
    }
}

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlags,
    pub program_counter: u16,
    memory: [u8; 0xFFFF],
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlags::from_bits_truncate(0b100100),
            program_counter: 0,
            memory: [0; 0xFFFF],
        }
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = CpuFlags::from_bits_truncate(0b100100);

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run()
    }

    pub fn run(&mut self) {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODE_MAP;

        loop {
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes
                .get(&code)
                .expect(&format!("OpCode {:x} is not recognized", code));

            match opcode.code {
                /* ADC */
                0x69 | 0x65 | 0x75 | 0x6d | 0x7d | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }
                /* AND */
                0x29 | 0x25 | 0x35 | 0x2d | 0x3d | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }
                /* ASL */
                0x0a => {
                    self.asl_accumulator();
                }
                0x06 | 0x16 | 0x0e | 0x1e => {
                    self.asl(&opcode.mode);
                }
                /* BCC */
                0x90 => {
                    self.branch(!self.status.contains(CpuFlags::CARRY));
                }
                /* BCS */
                0xb0 => {
                    self.branch(self.status.contains(CpuFlags::CARRY));
                }
                /* BEQ */
                0xf0 => {
                    self.branch(self.status.contains(CpuFlags::ZERO));
                }
                /* BIT */
                0x24 | 0x2c => {
                    self.bit(&opcode.mode);
                }
                /* BMI */
                0x30 => {
                    self.branch(self.status.contains(CpuFlags::NEGATIV));
                }
                /* BNE */
                0xd0 => {
                    self.branch(!self.status.contains(CpuFlags::ZERO));
                }
                /* BPL */
                0x10 => {
                    self.branch(!self.status.contains(CpuFlags::NEGATIV));
                }
                /* BVC */
                0x50 => {
                    self.branch(!self.status.contains(CpuFlags::OVERFLOW));
                }
                /* BVS */
                0x70 => {
                    self.branch(self.status.contains(CpuFlags::OVERFLOW));
                }
                /* CLC */
                0x18 => {
                    self.clear_carry_flag();
                }
                /* CLD */
                0xd8 => {
                    self.status.remove(CpuFlags::DECIMAL_MODE);
                }
                /* CLI */
                0x58 => {
                    self.status.remove(CpuFlags::INTERRUPT_DISABLE);
                }
                /* CLV */
                0xb8 => {
                    self.status.remove(CpuFlags::OVERFLOW);
                }
                /* CMP */
                0xc9 | 0xc5 | 0xd5 | 0xcd | 0xdd | 0xd9 | 0xc1 | 0xd1 => {
                    self.compare(&opcode.mode, self.register_a);
                }
                /* CPX */
                0xe0 | 0xe4 | 0xec => {
                    self.compare(&opcode.mode, self.register_x);
                }
                /* CPY */
                0xc0 | 0xc4 | 0xcc => {
                    self.compare(&opcode.mode, self.register_y);
                }
                /* DEC */
                0xc6 | 0xd6 | 0xce | 0xde => {
                    self.dec(&opcode.mode);
                }
                /* DEX */
                0xca => {
                    self.dex();
                }
                /* DEY */
                0x88 => {
                    self.dey();
                }
                /* LDA */
                0xa9 | 0xa5 | 0xb5 | 0xad | 0xbd | 0xb9 | 0xa1 | 0xb1 => {
                    self.lda(&opcode.mode);
                }
                /* LDX */
                0xa2 | 0xa6 | 0xb6 | 0xae | 0xbe => {
                    self.ldx(&opcode.mode);
                }
                /* LDY */
                0xa0 | 0xa4 | 0xb4 | 0xac | 0xbc => {
                    self.ldy(&opcode.mode);
                }
                /* STA */
                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }

                0xAA => self.tax(),
                0xE8 => self.inx(),
                0x00 => return,
                _ => todo!(),
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }

    fn add_to_register_a(&mut self, data: u8) {
        let sum = self.register_a as u16
            + data as u16
            + (if self.status.contains(CpuFlags::CARRY) {
                1
            } else {
                0
            }) as u16;

        let carry = sum > 0xff;
        if carry {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        let result = sum as u8;
        if (data ^ result) & (result ^ self.register_a) & 0x80 != 0 {
            self.status.insert(CpuFlags::OVERFLOW);
        } else {
            self.status.remove(CpuFlags::OVERFLOW);
        }

        self.set_register_a(result);
    }

    fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn set_register_x(&mut self, value: u8) {
        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn set_register_y(&mut self, value: u8) {
        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.add_to_register_a(value);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(value & self.register_a);
    }

    fn asl_accumulator(&mut self) {
        let mut data = self.register_a;
        if data >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data << 1;
        self.set_register_a(data);
    }

    fn asl(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        if data >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data << 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn branch(&mut self, condition: bool) {
        if condition {
            let jump = self.mem_read(self.program_counter) as i8;
            let jump_addr = self
                .program_counter
                .wrapping_add(jump as u16)
                .wrapping_add(1); // jump先のアドレスはラベルの1つ前に置き換えられる

            self.program_counter = jump_addr;
        }
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(value);
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_x(value)
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_y(value)
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        let and = self.register_a & data;
        if and == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        self.status.set(CpuFlags::NEGATIV, data & 0b1000_0000 > 0);
        self.status.set(CpuFlags::OVERFLOW, data & 0b0100_0000 > 0);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn compare(&mut self, mode: &AddressingMode, compare_with: u8) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        if compare_with >= value {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        self.update_zero_and_negative_flags(compare_with.wrapping_sub(value));
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let value = value.wrapping_sub(1);
        self.mem_write(addr, value);

        self.update_zero_and_negative_flags(value);
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        if result & 0b1000_0000 != 0 {
            self.status.insert(CpuFlags::NEGATIV);
        } else {
            self.status.remove(CpuFlags::NEGATIV);
        }
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }
            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }
            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn clear_carry_flag(&mut self) {
        self.status.remove(CpuFlags::CARRY);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_0xa9_lda_immediate_load_date() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), false);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), false);
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
    }

    #[test]
    fn test_0xa9_lda_negative_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xF0, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), true);
    }

    #[test]
    fn test_lda_indirect_y() {
        let mut cpu = CPU::new();
        // LDA #$42
        // STA $2020
        // LDA #$10
        // STA $00
        // LDA #$20
        // STA $01
        // LDY #$10
        // LDA ($00),Y
        cpu.load_and_run(vec![
            0xa9, 0x42, 0x8d, 0x20, 0x20, 0xa9, 0x10, 0x85, 0x00, 0xa9, 0x20, 0x85, 0x01, 0xa0,
            0x10, 0xb1, 0x00, 0x00,
        ]);
        assert_eq!(cpu.register_a, 0x42);
    }

    #[test]
    fn test_ldx() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa2, 0x05, 0x00]);
        assert_eq!(cpu.register_x, 0x05);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), false);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), false);
    }

    #[test]
    fn test_ldy() {
        let mut cpu = CPU::new();
        // LDA #$c5
        // STA $15
        // LDX #$05
        // LDY $10,X
        cpu.load_and_run(vec![0xa9, 0xc5, 0x85, 0x15, 0xa2, 0x05, 0xb4, 0x10, 0x00]);
        assert_eq!(cpu.register_y, 0xc5);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), false);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), true);
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x0A, 0xaa, 0x00]);
        assert_eq!(cpu.register_x, 10);
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1);
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        cpu.register_x = 0xff;
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1);
    }

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);
        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_sta_zero_page() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x0A, 0x85, 0x10, 0x00]);
        let value = cpu.mem_read(0x10);
        assert_eq!(value, 0x0A);
    }

    #[test]
    fn test_sta_absolute() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc5, 0x8d, 0x01, 0xc0, 0x00]);
        let value = cpu.mem_read_u16(0xc001);
        assert_eq!(value, 0xc5);
    }

    #[test]
    fn test_adc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0x69, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), false);
        assert_eq!(cpu.status.contains(CpuFlags::OVERFLOW), false);
    }

    #[test]
    fn test_adc_with_carry() {
        let mut cpu = CPU::new();
        // LDA 0xff, ADC 0x01 (occur overflow), ADC 0x05, BRK
        cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0x01, 0x69, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x06);
    }

    #[test]
    fn test_adc_carry() {
        let mut cpu = CPU::new();
        // LDA 0xff, ADC 0x01 (occur overflow), BRK
        cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0x01, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), true);
    }

    #[test]
    fn test_adc_overflow() {
        let mut cpu = CPU::new();
        // LDA 0x80(-128), ADC 0xff(-1) (overflow will occur), BRK
        cpu.load_and_run(vec![0xa9, 0x80, 0x69, 0xff, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::OVERFLOW), true);
    }

    #[test]
    fn test_and() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x55, 0x29, 0x0f, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
    }

    #[test]
    fn test_asl_accumulator() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x03, 0x0a, 0x00]);
        assert_eq!(cpu.register_a, 0x06);
    }

    #[test]
    fn test_asl() {
        let mut cpu = CPU::new();
        // 0000 0101
        cpu.load_and_run(vec![0xa9, 0x05, 0x85, 0x10, 0x06, 0x10, 0x00]);
        let value = cpu.mem_read(0x10);
        // 0000 1010
        assert_eq!(value, 0x0A);
    }

    #[test]
    fn test_bcc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xfe, 0x69, 0x01, 0x90, 0xfc, 0x00]);
        assert_eq!(cpu.register_a, 0x00);
    }

    #[test]
    fn test_bcs() {
        let mut cpu = CPU::new();
        // LDA #$ff
        // ADC #$01
        // BCS load20
        // LDA #$10
        // load20:
        // LDA #$20
        cpu.load_and_run(vec![
            0xa9, 0xff, 0x69, 0x01, 0xb0, 0x02, 0xa9, 0x10, 0xa9, 0x20, 0x00,
        ]);
        assert_eq!(cpu.register_a, 0x20);
    }

    #[test]
    fn test_beq() {
        let mut cpu = CPU::new();
        // LDA #$00
        // BEQ load20
        // LDA #$10
        // load20:
        // LDA #$20
        cpu.load_and_run(vec![0xa9, 0x00, 0xf0, 0x02, 0xa9, 0x10, 0xa9, 0x20, 0x00]);
        assert_eq!(cpu.register_a, 0x20);
    }

    #[test]
    fn test_bit_nv_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0x85, 0x00, 0xa9, 0xf0, 0x24, 0x00, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), false);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), true);
        assert_eq!(cpu.status.contains(CpuFlags::OVERFLOW), true);
    }

    #[test]
    fn test_bit_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x0c, 0x85, 0x00, 0xa9, 0xf0, 0x24, 0x00, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), false);
        assert_eq!(cpu.status.contains(CpuFlags::OVERFLOW), false);
    }

    #[test]
    fn test_bmi() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc1, 0x30, 0x02, 0x69, 0x05, 0x69, 0x02, 0x00]);
        assert_eq!(cpu.register_a, 0xc3);
    }

    #[test]
    fn test_bne() {
        let mut cpu = CPU::new();
        // @todo use SBC
        cpu.load_and_run(vec![0xa9, 0xc1, 0xd0, 0x02, 0x69, 0x05, 0x69, 0x02, 0x00]);
        assert_eq!(cpu.register_a, 0xc3);
    }

    #[test]
    fn test_bpl() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x71, 0x10, 0x02, 0x69, 0x05, 0x69, 0x02, 0x00]);
        assert_eq!(cpu.register_a, 0x73);
    }

    #[test]
    fn test_bvc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![
            0xa9, 0xfe, 0x69, 0x01, 0x50, 0x02, 0x69, 0x02, 0x69, 0x02, 0x00,
        ]);
        assert_eq!(cpu.register_a, 0x01);
    }

    #[test]
    fn test_bvs() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![
            0xa9, 0x7f, 0x69, 0x7f, 0x70, 0x02, 0x69, 0x02, 0x69, 0x02, 0x00,
        ]);
        // 0x7f + 0x7f -> 0xfe + 0x02 -> 0x00
        assert_eq!(cpu.register_a, 0x00);
    }

    #[test]
    fn test_clc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0x01, 0x18, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), false);
    }

    #[test]
    fn test_clv() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x81, 0x69, 0x81, 0xb8, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::OVERFLOW), false);
    }

    #[test]
    fn test_cmp_negative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![
            0xa9, 0x01, 0x8d, 0x10, 0xc0, 0xa9, 0x81, 0xcd, 0x10, 0xc0, 0x00,
        ]);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), true);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), true);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), false);
    }

    #[test]
    fn test_cmp_zero() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x01, 0xc9, 0x01, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), false);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), true);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
    }

    #[test]
    fn test_cmp_carry_false() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0xc0, 0xa9, 0x01, 0xc5, 0xc0, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), false);
    }

    #[test]
    fn test_cpx() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa2, 0x01, 0xe0, 0x01, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), false);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), true);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
    }

    #[test]
    fn test_cpy() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa0, 0x01, 0xc0, 0x01, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), false);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), true);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
    }

    #[test]
    fn test_dec() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x01, 0x85, 0xf0, 0xc6, 0xf0, 0x00]);
        assert_eq!(cpu.mem_read(0xf0), 0x00);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
    }

    #[test]
    fn test_dex() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa2, 0x01, 0xca, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
    }

    #[test]
    fn test_dey() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa0, 0x01, 0x88, 0x00]);
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
    }
}
