use crate::cartridge::Rom;
use crate::cpu::Mem;

pub struct Bus {
    cpu_vram: [u8; 0x800], //2048
    //cpu_vram: [u8; 0xFFFF],
    rom: Rom,
}

impl Bus {
    pub fn new(rom: Rom) -> Self {
        Bus {
            cpu_vram: [0; 0x800],
            //cpu_vram: [0; 0xFFFF],
            rom,
        }
    }

    fn read_prg_rom(&self, mut addr: u16) -> u8 {
        addr -= 0x8000;
        if self.rom.prg_rom.len() == 0x4000 && addr >= 0x4000 {
            addr = addr % 0x4000;
        }
        self.rom.prg_rom[addr as usize]
    }
}

const RAM: u16 = 0x0000;
const RAM_MIRRORS_END: u16 = 0x1FFF;
const PPU_REGISTER: u16 = 0x2000;
const PPU_MIRRORS_REGISTER: u16 = 0x3FFF;

impl Mem for Bus {
    fn mem_read(&self, addr: u16) -> u8 {
        match addr {
            RAM..=RAM_MIRRORS_END => {
                let mirror_down_addr = addr & 0b00000111_11111111;
                self.cpu_vram[mirror_down_addr as usize]
            }
            PPU_REGISTER..=PPU_MIRRORS_REGISTER => {
                let mirror_down_addr = addr & 0b00100000_00000111;
                todo!("PPU is not support yet");
            }
            0x8000..=0xFFFF => self.read_prg_rom(addr),
            _ => {
                println!("Ignoring mem access at {}", addr);
                0
            }
        }
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        match addr {
            RAM..=RAM_MIRRORS_END => {
                let mirror_down_addr = addr & 0b00000111_11111111;
                self.cpu_vram[mirror_down_addr as usize] = data;
            }
            PPU_REGISTER..=PPU_MIRRORS_REGISTER => {
                let mirror_down_addr = addr & 0b00100000_00000111;
                todo!("PPU is not support yet");
            }
            0x8000..=0xFFFF => {
                panic!("Attempt to write to Cartridge ROM space");
            }
            _ => {
                println!("Ignoring mem write-access at {}", addr);
            }
        }
    }
}
