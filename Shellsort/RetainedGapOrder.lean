import Shellsort.BinaryGapLocalOrder
import Shellsort.TagPosition
import Shellsort.TagThreshold

/-! Retention of previous gap orders by an actual later pass. -/

noncomputable section
namespace Shellsort

/-- Each occupied slot in the second chain beyond its initial overhang has
an occupied predecessor in the first chain, one retained step to the left. -/
theorem chainLowerCount_shift_bound {n k a : ℕ} (_hk : 0 < k)
    (B : Finset (Fin n))
    (closed : ∀ u v : Fin n, v.val = u.val + a → v ∈ B → u ∈ B)
    (i j : Fin n) (step : j.val = i.val + a) :
    chainLowerCount B k (j.val % k) ≤
      (j.val / k - i.val / k) + chainLowerCount B k (i.val % k) := by
  classical
  let s := j.val / k - i.val / k
  let R := B.filter (fun y => y.val % k = j.val % k)
  let L := B.filter (fun y => y.val % k = i.val % k)
  have hq : i.val / k ≤ j.val / k := Nat.div_le_div_right (by omega)
  have split : j.val / k = i.val / k + s := by dsimp [s]; omega
  have idj := Nat.mod_add_div j.val k
  have idi := Nat.mod_add_div i.val k
  rw [split, Nat.mul_add] at idj
  have base : j.val % k + k*s = i.val % k + a := by omega
  have early : (R.filter (fun y => y.val < a)).card ≤ s := by
    rw [← Finset.card_range s]
    apply Finset.card_le_card_of_injOn (fun y : Fin n => y.val / k)
    · intro y hy
      obtain ⟨hyR, hya⟩ := Finset.mem_filter.mp hy
      have hr := (Finset.mem_filter.mp hyR).2
      apply Finset.mem_range.mpr
      by_contra! hn
      have hm := Nat.mul_le_mul_left k hn
      have hid := Nat.mod_add_div y.val k
      omega
    · intro y hy z hz heq
      have hy' := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
      have hz' := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
      apply Fin.ext
      change y.val / k = z.val / k at heq
      have idy := Nat.mod_add_div y.val k
      rw [heq, hy', ← hz', Nat.mod_add_div] at idy
      exact idy.symm
  let back (y : Fin n) : Fin n := ⟨y.val-a, lt_of_le_of_lt (Nat.sub_le ..) y.isLt⟩
  have late : (R.filter (fun y => ¬ y.val < a)).card ≤ L.card := by
    apply Finset.card_le_card_of_injOn back
    · intro y hy
      obtain ⟨hyR,hya⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyB,hyr⟩ := Finset.mem_filter.mp hyR
      have eqn : (back y).val + a = y.val := Nat.sub_add_cancel (by omega)
      apply Finset.mem_filter.mpr
      refine ⟨closed _ _ eqn.symm hyB, Nat.ModEq.add_right_cancel' a ?_⟩
      rw [eqn, ← step]
      exact hyr
    · intro y hy z hz heq
      have hy' := (Finset.mem_filter.mp hy).2
      have hz' := (Finset.mem_filter.mp hz).2
      have eqn : y.val - a = z.val - a := congrArg Fin.val heq
      exact Fin.ext (by omega)
  have total := Finset.card_filter_add_card_filter_not (s := R) (fun y => y.val < a)
  change R.card ≤ s + L.card
  omega

theorem lowerStep_retains_order {n k a : ℕ} (hk : 0 < k) (B : Finset (Fin n))
    (closed : ∀ u v : Fin n, v.val = u.val + a → v ∈ B → u ∈ B)
    (i j : Fin n) (step : j.val = i.val + a) (hj : j ∈ lowerStep B k) :
    i ∈ lowerStep B k := by
  simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and, chainOrdinal_eq_div k hk] at hj ⊢
  have count := chainLowerCount_shift_bound hk B closed i j step
  have hq : i.val / k ≤ j.val / k := Nat.div_le_div_right (by omega)
  omega

/-- Sorting the new chains preserves every earlier step order. -/
theorem gapSort_retains_step {n a : ℕ} (p : RankPlacement n) (k : ℕ)
    (ordered : SlotStepOrdered p a) : SlotStepOrdered (gapSort p k) a := by
  by_cases hk : k = 0
  · simpa [hk, gapSort_zero] using ordered
  intro i j step
  let q := gapSort p k
  let t := (q.symm j).val + 1
  have closed (u v : Fin n) (h : v.val = u.val + a) (hv : v ∈ thresholdSet p t) :
      u ∈ thresholdSet p t :=
    (threshold_mem p t u).mpr (lt_trans (ordered u v h) ((threshold_mem p t v).mp hv))
  have hj : j ∈ thresholdSet q t := (threshold_mem q t j).mpr (Nat.lt_succ_self _)
  have hi : i ∈ thresholdSet q t := by
    dsimp only [q] at hj ⊢
    rw [gapSort_threshold_commutes] at hj ⊢
    exact lowerStep_retains_order (Nat.pos_of_ne_zero hk) _ closed i j step hj
  have le : (q.symm i).val ≤ (q.symm j).val := Nat.le_of_lt_succ ((threshold_mem q t i).mp hi)
  change q.symm i < q.symm j
  apply lt_of_le_of_ne le
  intro he
  have hij := q.symm.injective (Fin.ext he)
  subst j
  exact (ordered i i step).false

theorem sortWord_retains_step {n a : ℕ} (p : RankPlacement n) (ks : List ℕ)
    (ordered : SlotStepOrdered p a) : SlotStepOrdered (sortWord p ks) a := by
  induction ks generalizing p with
  | nil => exact ordered
  | cons k ks ih => exact ih _ (gapSort_retains_step p k ordered)

theorem sortWord_step_of_mem {n a : ℕ} (p : RankPlacement n) (ks : List ℕ)
    (ha : 0 < a) (mem : a ∈ ks) : SlotStepOrdered (sortWord p ks) a := by
  induction ks generalizing p with
  | nil => simp at mem
  | cons k ks ih =>
    rcases List.mem_cons.mp mem with rfl | hm
    · exact sortWord_retains_step (gapSort p a) ks (slotStepOrdered_after_gapSort p ha)
    · exact ih _ hm

private theorem ordered_mul {n h : ℕ} (q : RankPlacement n) (ord : SlotStepOrdered q h)
    (u : ℕ) (i j : Fin n) (dist : j.val = i.val + u*h) : q.symm i ≤ q.symm j := by
  induction u generalizing i j with
  | zero =>
    have eqn : j = i := Fin.ext (by simpa using dist)
    simp [eqn]
  | succ u ih =>
    rw [Nat.succ_mul] at dist
    let v : Fin n := ⟨i.val + u*h, by have := j.isLt; omega⟩
    apply le_trans (ih i v rfl)
    exact le_of_lt (ord v j (by dsimp [v]; omega))

theorem gapSort_fixed_of_step {n h : ℕ} (q : RankPlacement n) (ord : SlotStepOrdered q h) :
    gapSort q h = q := by
  apply gapSort_unique
  · intro x; rfl
  · intro x y hm
    have increasing (i j : Fin n) (he : i.val % h = j.val % h) (lt : i < j) :
        q.symm i < q.symm j := by
      have hij : i.val ≤ j.val := le_of_lt lt
      obtain ⟨u,hu⟩ := (Nat.modEq_iff_dvd' hij).mp he
      have dist : j.val = i.val + u*h := by rw [Nat.mul_comm u h]; omega
      exact lt_of_le_of_ne (ordered_mul q ord u i j dist)
        (fun eqn => (ne_of_lt lt) (q.symm.injective eqn))
    constructor
    · intro hlt
      simpa using increasing (q x) (q y) hm hlt
    · intro hlt
      by_contra! hn
      rcases eq_or_lt_of_le hn with eqn | inv
      · exact (ne_of_lt hlt) (q.injective eqn.symm)
      · have hyx : y < x := by simpa using increasing (q y) (q x) hm.symm inv
        exact hlt.asymm hyx

theorem sortWord_fixed_of_checkpoint_orders {n : ℕ} (q : RankPlacement n) (ks : List ℕ)
    (ord : ∀ k ∈ ks, 0 < k → SlotStepOrdered q k) : sortWord q ks = q := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have fixed : gapSort q k = q := by
      by_cases hk : k = 0
      · simpa [hk] using gapSort_zero q
      · exact gapSort_fixed_of_step q (ord k (by simp) (Nat.pos_of_ne_zero hk))
    change sortWord (gapSort q k) ks = q
    rw [fixed]
    exact ih (fun h hm => ord h (List.mem_cons_of_mem _ hm))

/-- The whole support of a checkpoint under a full-support input law.
Every jointly ordered placement is reached, via that placement as input. -/
theorem checkpoint_reachable_iff_orders {n : ℕ} (q : RankPlacement n) (ks : List ℕ) :
    (∃ p : RankPlacement n, sortWord p ks = q) ↔
      ∀ k ∈ ks, 0 < k → SlotStepOrdered q k := by
  constructor
  · rintro ⟨p,rfl⟩ k hm hk
    exact sortWord_step_of_mem p ks hk hm
  · intro h
    exact ⟨q, sortWord_fixed_of_checkpoint_orders q ks h⟩

/-- A sum of earlier positive gaps is an ordered distance at the current
checkpoint; the empty sum gives the degenerate equality case. -/
theorem sortWord_ordered_path {n : ℕ} (p : RankPlacement n) (ks path : List ℕ)
    (used : ∀ b ∈ path, 0 < b ∧ b ∈ ks) (i j : Fin n)
    (dist : j.val = i.val + path.sum) :
    (sortWord p ks).symm i ≤ (sortWord p ks).symm j := by
  induction path generalizing i j with
  | nil =>
    have eqn : i = j := Fin.ext (by simpa using dist.symm)
    simp [eqn]
  | cons b bs ih =>
    rw [List.sum_cons] at dist
    let u : Fin n := ⟨i.val+b, by have := j.isLt; omega⟩
    have hb := used b (by simp)
    apply le_trans (le_of_lt (sortWord_step_of_mem p ks hb.1 hb.2 i u rfl))
    apply ih (fun c hc => used c (List.mem_cons_of_mem _ hc)) u j
    dsimp [u]
    omega

/-- A computable menu of already ordered distances can be removed from the
possible inversion pairs of the next pass. -/
theorem gapInsertionCost_le_uncovered_distances {n h : ℕ} (p : RankPlacement n)
    (ks : List ℕ) (hh : 0 < h) (covered : Finset ℕ)
    (witness : ∀ b ∈ covered, ∃ path : List ℕ,
      (∀ c ∈ path, 0 < c ∧ c ∈ ks) ∧ path.sum = b) :
    gapInsertionCost (sortWord p ks) h hh ≤
      ((gapPositionPairs n h).filter (fun ij => ij.2.val - ij.1.val ∉ covered)).card := by
  rw [gapInsertionCost_eq_gapInversions]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hz, hInv⟩ := Finset.mem_filter.mp hz
  apply Finset.mem_filter.mpr
  refine ⟨hz, ?_⟩
  intro coveredDist
  obtain ⟨path, used, hsum⟩ := witness _ coveredDist
  have ltSlots : z.1.val < z.2.val := (Finset.mem_filter.mp hz).2.1
  exact (not_lt_of_ge (sortWord_ordered_path p ks path used z.1 z.2 (by omega))) hInv

/-- The earlier conditional cost lemma now applies at the real checkpoint,
even if arbitrarily many unrelated passes occurred since the two witnesses. -/
theorem gapInsertionCost_le_of_prior_two_three {n h : ℕ} (p : RankPlacement n)
    (ks : List ℕ) (hh : 0 < h) (h₂ : 2*h ∈ ks) (h₃ : 3*h ∈ ks) :
    gapInsertionCost (sortWord p ks) h hh ≤ n-h :=
  binaryGap_insertionCost_le _ hh (sortWord_step_of_mem p ks (by omega) h₂)
    (sortWord_step_of_mem p ks (by omega) h₃)

/-- Odd zero-based levels in the h-chains, one available slot per matched pair. -/
def oddChainLevels (n h : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i.val / h) % 2 = 1)

/-- Once 2h and 3h have occurred, the remaining h-inversions are pairwise
disjoint adjacent edges on the h-chains. Each shift uses two different slots
and exactly one odd-level slot. -/
theorem gapInsertionCost_matching_of_prior_two_three {n h : ℕ} (p : RankPlacement n)
    (ks : List ℕ) (hh : 0 < h) (h₂ : 2*h ∈ ks) (h₃ : 3*h ∈ ks) :
    2 * gapInsertionCost (sortWord p ks) h hh ≤ n ∧
      gapInsertionCost (sortWord p ks) h hh ≤ (oddChainLevels n h).card := by
  classical
  let q := sortWord p ks
  have ordered₂ : SlotStepOrdered q (2*h) := sortWord_step_of_mem p ks (by omega) h₂
  have ordered₃ : SlotStepOrdered q (3*h) := sortWord_step_of_mem p ks (by omega) h₃
  let E := (gapPositionPairs n h).filter (fun ij => q.symm ij.2 < q.symm ij.1)
  have adj (z : Fin n × Fin n) (hz : z ∈ E) : z.2.val = z.1.val + h := by
    obtain ⟨hz, hv⟩ := Finset.mem_filter.mp hz
    exact binaryGap_inverted_pair_adjacent q ordered₂ ordered₃
      (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hz).2.2 hv
  have leftInj : Set.InjOn Prod.fst (E : Set (Fin n × Fin n)) := by
    intro x hx y hy eqn
    apply Prod.ext eqn (Fin.ext ?_)
    change x.1 = y.1 at eqn
    rw [adj x hx, adj y hy, eqn]
  have rightInj : Set.InjOn Prod.snd (E : Set (Fin n × Fin n)) := by
    intro x hx y hy eqn
    apply Prod.ext (Fin.ext ?_) eqn
    have hu := congrArg Fin.val eqn
    change x.2.val = y.2.val at hu
    have ax := adj x hx
    have ay := adj y hy
    omega
  have sep : Disjoint (E.image Prod.fst) (E.image Prod.snd) := by
    apply Finset.disjoint_left.mpr
    intro v left right
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp left
    obtain ⟨y,hy,hf⟩ := Finset.mem_image.mp right
    have eqn : x.1 = y.2 := he.trans hf.symm
    have hu := congrArg Fin.val eqn
    have ax := adj x hx
    have ay := adj y hy
    have ord := ordered₂ y.1 x.2 (by omega)
    have invx : q.symm x.2 < q.symm x.1 := (Finset.mem_filter.mp hx).2
    have invy : q.symm y.2 < q.symm y.1 := (Finset.mem_filter.mp hy).2
    rw [eqn] at invx
    exact (lt_trans invx invy).asymm ord
  have bound := Finset.card_le_univ (E.image Prod.fst ∪ E.image Prod.snd)
  rw [Finset.card_union_of_disjoint sep, Finset.card_image_of_injOn leftInj,
    Finset.card_image_of_injOn rightInj, Fintype.card_fin] at bound
  rw [gapInsertionCost_eq_gapInversions]
  change 2 * E.card ≤ n ∧ E.card ≤ _
  refine ⟨by omega, ?_⟩
  let mark (x : Fin n × Fin n) := if (x.1.val / h) % 2 = 1 then x.1 else x.2
  apply Finset.card_le_card_of_injOn mark
  · intro z hz
    change mark z ∈ oddChainLevels n h
    simp only [oddChainLevels, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [mark]
    split_ifs with odd
    · exact odd
    · rw [adj z hz, Nat.add_div_right _ hh]
      omega
  · intro x hx y hy eqn
    dsimp only [mark] at eqn
    split_ifs at eqn with hxOdd hyOdd hyOdd
    · exact leftInj hx hy eqn
    · exact (Finset.disjoint_left.mp sep (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
        (Finset.mem_image.mpr ⟨y,hy,eqn.symm⟩)).elim
    · exact (Finset.disjoint_left.mp sep (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
        (Finset.mem_image.mpr ⟨x,hx,eqn⟩)).elim
    · exact rightInj hx hy eqn

end Shellsort
end
