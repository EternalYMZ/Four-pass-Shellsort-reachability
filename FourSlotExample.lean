import Shellsort.SlotCollisionPenalty

noncomputable section
open Shellsort
namespace SlotPotentialCheck

/-- Input array (2,0,3,1), represented as rank-to-position permutation. -/
def input : RankPlacement 4 where
  toFun := ![1,3,0,2]
  invFun := ![2,0,3,1]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private def U (x : Fin 4) (i : ℕ) : ℝ :=
  (![![-20,0,-20,-1], ![-20,-1,-20,0], ![0,-20,-1,-20], ![-1,-20,0,-20]]
    : Fin 4 → Fin 4 → ℝ) x ⟨i%4, by omega⟩

private def V (x : Fin 4) (i : ℕ) : ℝ :=
  (![![0,1,2,3], ![1,0,1,2], ![2,1,0,1], ![3,2,1,0]]
    : Fin 4 → Fin 4 → ℝ) x ⟨i%4, by omega⟩

private def slot : Fin 4 → ℝ := ![0,1,1,0]

private theorem preLip : gapPotentialBound U 2 1 := by
  intro x i hi
  have : i ≤ 1 := by omega
  interval_cases i <;> fin_cases x <;> norm_num [U, Matrix.cons_val]

private theorem postLip : gapPotentialBound V 1 1 := by
  intro x i hi
  have : i ≤ 2 := by omega
  interval_cases i <;> fin_cases x <;> norm_num [V, Matrix.cons_val]

private theorem prices (x i : Fin 4) : U x i.val - V x i.val ≤ -2 + slot i := by
  fin_cases x <;> fin_cases i <;> norm_num [U, V, slot, Matrix.cons_val]

theorem four_slot_certificate :
    3 ≤ gapInsertionCost input 2 (by decide) + gapInsertionCost (gapSort input 2) 1 (by decide) := by
  let a : {k : ℕ // 0 < k} := ⟨2, by decide⟩
  let b : {k : ℕ // 0 < k} := ⟨1, by decide⟩
  have h := slotPotential_twoBlock input [a] [b] U V (fun _ => 1) (fun _ => 1)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (by intro k hk
        have he : k = a := by simpa using hk
        subst k
        exact preLip)
    (by intro k hk
        have he : k = b := by simpa using hk
        subst k
        exact postLip)
    (fun _ => -2) slot prices
  have he : slotPotential U input = 0 := by
    norm_num [slotPotential, Fin.sum_univ_four, U, input, Matrix.cons_val]
  have hf : slotPotential V (Equiv.refl (Fin 4)) = 0 := by
    norm_num [slotPotential, Fin.sum_univ_four, V, Matrix.cons_val]
  have hh : (∑ x : Fin 4, (-2 : ℝ)) + ∑ i : Fin 4, slot i = -6 := by
    norm_num [Fin.sum_univ_four, slot, Matrix.cons_val]
  simp only [List.map_cons, List.map_nil, sortWord, a, b, gapSort_one, he, hf, hh,
    weightedWordShifts, one_mul, add_zero] at h
  exact_mod_cast (show (3:ℝ) ≤ (gapInsertionCost input 2 (by decide):ℝ) +
      (gapInsertionCost (gapSort input 2) 1 (by decide):ℝ) by linarith)

#print axioms Shellsort.slotPotential_gap
#print axioms Shellsort.slotPotential_word
#print axioms Shellsort.slotPotential_checkpoint
#print axioms Shellsort.slotPotential_twoBlock
#print axioms Shellsort.weightedWordShifts_unit
#print axioms Shellsort.twoBlock_slot_deficit
#print axioms four_slot_certificate
end SlotPotentialCheck
