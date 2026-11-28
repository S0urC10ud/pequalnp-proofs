import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54914 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50350 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨{ gates := [⟨.or, [5, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [5, 0]⟩, ⟨.or, [2, 1]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [15, 14]⟩], output := 16 }, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
