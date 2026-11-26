import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20006_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 8]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [21, 14]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [24, 20]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [21, 25]⟩, ⟨.and, [29, 19]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [32, 23]⟩, ⟨.or, [32, 17]⟩, ⟨.and, [25, 31]⟩, ⟨.or, [26, 30]⟩, ⟨.and, [34, 16]⟩, ⟨.or, [29, 24]⟩, ⟨.and, [15, 1]⟩, ⟨.or, [36, 27]⟩, ⟨.and, [40, 33]⟩, ⟨.or, [35, 39]⟩, ⟨.and, [38, 22]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [45, 44]⟩], 46⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14714778660030304590 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20006_aux

theorem PEqualNP.Outside.L_meta_20006 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14714778660030304590 : ℕ).testBit (8 * u.val + v.val)) 31) :=
  PEqualNP.Outside.L_meta_20006_aux.main
