inductive State
| s0
| s120
| s240

inductive Rotation
| r0
| r120
| r240


def act : Rotation → State → State := _

def add_rotation : Rotation → Rotation → Rotation
| r0, r => r
| r, r0 => r
| r120, r120 => r240
| r120, r240 => r0
| r240, r120 => r0
| r240, r240 => r120

def sub_state : State → State → Rotation
--a2, a1 ... a2 - a1
| s0, s0 => r0
| s0, s120 => r240 --becase we're rotating counterclockwise
| s0, s240 => r120
| s120, s0 => r120
| s120, s120 => r0
| s120, s240 => r120
| s240, s0 => r240
| s240, s120 => s240
| s240, s240 => r0


instance : Add Rotation := ⟨add_rotation⟩  --you need angle brackets here
#reduce r120 + r120


instance : AddSemiGroup Rotation (f, id, g) := ⟨




  ⟩
