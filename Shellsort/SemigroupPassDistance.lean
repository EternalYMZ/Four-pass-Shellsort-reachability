import Shellsort.RetainedGapOrder
import Mathlib.Algebra.Order.Ring.Int

/-! Ordered slot distances after a prescribed Shellsort prefix. -/

namespace Shellsort

/-- Suppose a nonnegative sum of earlier gaps reaches the residue of `ell`
modulo `gcd u v`. If the remaining distance is at least `u * v`, earlier
passes with gaps `u` and `v` supply the rest of an ordered path. -/
theorem sortWord_ordered_of_residue_path {n u v ell : ℕ} (p : RankPlacement n)
    (ks path : List ℕ) (hu : 0 < u) (hv : 0 < v) (hU : u ∈ ks) (hV : v ∈ ks)
    (used : ∀ c ∈ path, 0 < c ∧ c ∈ ks)
    (div : u.gcd v ∣ ell - path.sum) (size : u * v + path.sum ≤ ell)
    (i j : Fin n) (dist : j.val = i.val + ell) :
    (sortWord p ks).symm i ≤ (sortWord p ks).symm j := by
  have hp : u.pred * v.pred ≤ u * v := Nat.mul_le_mul (Nat.pred_le _) (Nat.pred_le _)
  obtain ⟨x, y, hxy⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le u v
    (ell - path.sum) div (by omega)
  let steps := path ++ List.replicate x u ++ List.replicate y v
  apply sortWord_ordered_path p ks steps
  · intro c hc
    simp only [steps, List.mem_append, List.mem_replicate] at hc
    rcases hc with ((hc | hc) | hc)
    · exact used c hc
    · exact hc.2 ▸ ⟨hu, hU⟩
    · exact hc.2 ▸ ⟨hv, hV⟩
  · simp [steps, List.sum_append, Nat.mul_comm] at *
    omega

end Shellsort
