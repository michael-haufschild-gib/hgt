import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Separation

/-! # Isometry detected by a fair choice between two separated prime bands at fixed count -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization

open Filter Topology Set _root_.RHTower VacuumCalibration
attribute [local instance] Classical.propDecidable

/-- Relative upper-band weight of the count pairs (0,k) and (k,0). For positive k these events are disjoint. -/
def upperChoice (c d b e : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) (k : ℕ) :=
  let upper := VacuumCalibration.vacuum c d h s * atom (added b e h) s k
  let lower := atom (added c d h) s k * VacuumCalibration.vacuum b e h s
  upper / (lower + upper)

/-- Joint Born weight of an event in each independent factor. -/
def pairWeight (L H : Finset Nat.Primes) (s : ℝ) (P : SquarefreeBitConfig L → Prop)
    (Q : SquarefreeBitConfig H → Prop) :=
  ∑ z : SquarefreeBitConfig L × SquarefreeBitConfig H,
    if P z.1 ∧ Q z.2 then finiteSquarefreeBornWeight L s z.1 * finiteSquarefreeBornWeight H s z.2 else 0

private def eventWeight (S : Finset Nat.Primes) (s : ℝ) (P : SquarefreeBitConfig S → Prop) :=
  ∑ x, if P x then finiteSquarefreeBornWeight S s x else 0

private theorem pairWeight_factor (L H : Finset Nat.Primes) (s : ℝ) (P : SquarefreeBitConfig L → Prop)
    (Q : SquarefreeBitConfig H → Prop) :
    pairWeight L H s P Q = eventWeight L s P * eventWeight H s Q := by
  have he (x : SquarefreeBitConfig L) (y : SquarefreeBitConfig H) :
      (if P x ∧ Q y then finiteSquarefreeBornWeight L s x*finiteSquarefreeBornWeight H s y else 0) =
        (if P x then finiteSquarefreeBornWeight L s x else 0)*(if Q y then finiteSquarefreeBornWeight H s y else 0) := by
    by_cases hx : P x <;> by_cases hy : Q y <;> simp [hx,hy]
  rw [pairWeight,Fintype.sum_prod_type]
  unfold eventWeight
  simp only [he,← Finset.mul_sum,← Finset.sum_mul]

private theorem pairWeight_from_split {L B : Finset Nat.Primes} (i : L ⊆ B) (s : ℝ)
    (P : SquarefreeBitConfig L → Prop) (Q : SquarefreeBitConfig (B\L) → Prop) :
    pairWeight L (B\L) s P Q = ∑ x : SquarefreeBitConfig B,
      if P ((splitBits i x).1) ∧ Q ((splitBits i x).2) then finiteSquarefreeBornWeight B s x else 0 := by
  let f (z : SquarefreeBitConfig L × SquarefreeBitConfig (B\L)) :=
    if P z.1 ∧ Q z.2 then finiteSquarefreeBornWeight L s z.1*finiteSquarefreeBornWeight (B\L) s z.2 else 0
  calc _ = ∑ x : SquarefreeBitConfig B, f (splitBits i x) := ((splitBits i).sum_comp f).symm
       _ = _ := Finset.sum_congr rfl fun x _ => by simp only [f,weight_split i s x]

/-- Every product event on disjoint prime bands is a Born event on their single union packet. -/
theorem pairWeight_on_union {L H : Finset Nat.Primes} (hd : Disjoint L H) (s : ℝ) :
    ∃ e : SquarefreeBitConfig (L ∪ H) ≃ SquarefreeBitConfig L × SquarefreeBitConfig H,
      ∀ (P : SquarefreeBitConfig L → Prop) (Q : SquarefreeBitConfig H → Prop),
        pairWeight L H s P Q = ∑ x, if P (e x).1 ∧ Q (e x).2 then finiteSquarefreeBornWeight (L ∪ H) s x else 0 := by
  have hi : L ⊆ L ∪ H := Finset.subset_union_left
  have hrem : (L ∪ H)\L = H := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_union]
    exact ⟨fun h => h.1.resolve_left h.2,fun h => ⟨Or.inr h,fun hl => Finset.disjoint_left.mp hd hl h⟩⟩
  have he : ∃ e : SquarefreeBitConfig (L ∪ H) ≃ SquarefreeBitConfig L × SquarefreeBitConfig ((L ∪ H)\L),
      ∀ P Q, pairWeight L ((L ∪ H)\L) s P Q =
        ∑ x, if P (e x).1 ∧ Q (e x).2 then finiteSquarefreeBornWeight (L ∪ H) s x else 0 :=
    ⟨splitBits hi,fun P Q => pairWeight_from_split hi s P Q⟩
  rwa [hrem] at he

theorem separated_disjoint {c d b e : ℝ} (hdb : d ≤ b) (h : Ioi (0:ℝ)) :
    Disjoint (added c d h) (added b e h) := by
  apply Finset.disjoint_left.mpr
  intro p hl hu
  exact (not_lt_of_ge (((mem_added c d h p).mp hl).2.trans hdb)) ((mem_added b e h p).mp hu).1

theorem positive_count_alternatives_disjoint (L H : Finset Nat.Primes) {k : ℕ} (hk : 0 < k) :
    Disjoint {z : SquarefreeBitConfig L × SquarefreeBitConfig H | z.1 = 0 ∧ (squarefreeOccupationFinset z.2).card = k}
      {z | (squarefreeOccupationFinset z.1).card = k ∧ z.2 = 0} := by
  have h0 : squarefreeOccupationFinset (0 : SquarefreeBitConfig L) = ∅ := by
    ext p
    simp [mem_squarefreeOccupationFinset]
  apply Set.disjoint_left.mpr
  intro z hu hl
  have hcount : (squarefreeOccupationFinset z.1).card = k := hl.1
  have hzero : z.1 = 0 := hu.1
  rw [hzero,h0,Finset.card_empty] at hcount
  exact hk.ne hcount

/-- Both alternatives are read on the same product of the two finite configuration spaces. -/
theorem upperChoice_eq_joint (c d b e : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) (k : ℕ) :
    let L := added c d h
    let H := added b e h
    let upper := pairWeight L H s (· = 0) (fun y => (squarefreeOccupationFinset y).card = k)
    let lower := pairWeight L H s (fun x => (squarefreeOccupationFinset x).card = k) (· = 0)
    upperChoice c d b e h s k = upper / (lower + upper) := by
  dsimp only
  have empty (S : Finset Nat.Primes) : eventWeight S s (· = 0) = finiteSquarefreeBornWeight S s 0 := by
    let w (x : SquarefreeBitConfig S) :=
      @ite ℝ (x = 0) (Classical.propDecidable _) (finiteSquarefreeBornWeight S s x) 0
    change (∑ x, w x) = _
    calc (∑ x, w x) = w 0 := Finset.sum_eq_single_of_mem (f := w) (0 : SquarefreeBitConfig S)
           (Finset.mem_univ _) (fun x _ hx => if_neg hx)
         _ = _ := if_pos rfl
  have count (S : Finset Nat.Primes) :
      eventWeight S s (fun x => (squarefreeOccupationFinset x).card = k) = atom S s k := by
    unfold eventWeight atom
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : (squarefreeOccupationFinset x).card = k <;> simp [hx]
  simp only [pairWeight_factor,empty,count,upperChoice,VacuumCalibration.vacuum]

theorem upperChoice_eq (c d b e : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) (k : ℕ) :
    upperChoice c d b e h s k = coefficient (added b e h) s k /
      (coefficient (added c d h) s k + coefficient (added b e h) s k) := by
  let L := finiteSquarefreePartition (added c d h) s
  let H := finiteSquarefreePartition (added b e h) s
  have hL : 0 < L := finiteSquarefreePartition_pos _ _
  have hH : 0 < H := finiteSquarefreePartition_pos _ _
  let u := atom (added b e h) s k
  let l := atom (added c d h) s k
  simp only [upperChoice,VacuumCalibration.vacuum_eq,coefficient]
  change (L⁻¹*u)/(l*H⁻¹+L⁻¹*u) = (H*u)/(L*l+H*u)
  rw [← mul_div_mul_left (L⁻¹*u) (l*H⁻¹+L⁻¹*u) (mul_pos hL hH).ne',mul_add]
  have hu : L*H*(L⁻¹*u) = H*u := by field_simp
  have hl : L*H*(l*H⁻¹) = L*l := by field_simp
  rw [hu,hl]

private theorem upper_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x/y)/(1+x/y) = x/(y+x) := by
  have h : 0 < 1+x/y := add_pos zero_lt_one (div_pos hx hy)
  field_simp

private theorem lower_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1/(1+y/x) = x/(y+x) := by
  have h : 0 < 1+y/x := add_pos zero_lt_one (div_pos hy hx)
  field_simp
  ring

theorem upperChoice_above {c d b e s : ℝ} (hc : 0 < c) (hcd : c < d) (hdb : d < b) (hbe : b < e)
    (hs : 1 < s) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => upperChoice c d b e h s k) criticalApproach (𝓝 0) := by
  have hz := high_odds_above hc hcd hdb hbe hs hk
  have H := hz.div ((tendsto_const_nhds (x := (1:ℝ))).add hz) (by norm_num)
  rw [zero_div] at H
  apply H.congr'
  filter_upwards [coefficient_eventually_pos hc hcd s k,coefficient_eventually_pos (hc.trans (hcd.trans hdb)) hbe s k]
    with h hl hu
  rw [upperChoice_eq]
  exact upper_ratio hu hl

theorem upperChoice_below {c d b e s : ℝ} (hc : 0 < c) (hcd : c < d) (hdb : d < b) (hbe : b < e)
    (hs : s < 1) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => upperChoice c d b e h s k) criticalApproach (𝓝 1) := by
  have hz := low_odds_below hc hcd hdb hbe hs hk
  have H := (tendsto_const_nhds (x := (1:ℝ))).div ((tendsto_const_nhds (x := (1:ℝ))).add hz) (by norm_num)
  rw [add_zero,div_one] at H
  apply H.congr'
  filter_upwards [coefficient_eventually_pos hc hcd s k,coefficient_eventually_pos (hc.trans (hcd.trans hdb)) hbe s k]
    with h hl hu
  rw [upperChoice_eq]
  exact lower_ratio hu hl

/-- Equal logarithmic widths give equal limiting weights for every count at inverse temperature one. -/
theorem upperChoice_one {c d r : ℝ} (hc : 0 < c) (hcd : c < d) (hr : 0 < r) (k : ℕ) :
    Tendsto (fun h => upperChoice c d (r*c) (r*d) h 1 k) criticalApproach (𝓝 (1/2)) := by
  have hl := coefficient_limit hc hcd k
  have hu := coefficient_limit (mul_pos hr hc) (mul_lt_mul_of_pos_left hcd hr) k
  rw [mul_div_mul_left _ _ hr.ne'] at hu
  let m := Real.log (d/c)^k/k.factorial
  have hm : 0 < m := div_pos (pow_pos (Real.log_pos ((one_lt_div hc).mpr hcd)) k) (Nat.cast_pos.mpr (Nat.factorial_pos k))
  have H := hu.div (hl.add hu) (add_pos hm hm).ne'
  have he : m/(m+m) = 1/2 := by rw [← two_mul]; field_simp
  change Tendsto _ _ (𝓝 (m/(m+m))) at H
  rw [he] at H
  exact H.congr fun h => (upperChoice_eq c d (r*c) (r*d) h 1 k).symm

/-- With the total count fixed, a fair choice between two separated equal-width bands is equivalent to isometric splitting. -/
theorem split_isometric_iff_fair_choice {c d r : ℝ} (hc : 0 < c) (hcd : c < d) (hr : 0 < r) (hsep : d < r*c)
    (s : ℂ) {k : ℕ} (hk : 0 < k) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      Tendsto (fun h => upperChoice c d (r*c) (r*d) h (2*s.re) k) criticalApproach (𝓝 (1/2)) := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  rw [split_isometric_iff]
  have hbe := mul_lt_mul_of_pos_left hcd hr
  constructor
  · intro H
    rw [show 2*s.re = 1 by rw [H]; ring]
    exact upperChoice_one hc hcd hr k
  · intro H
    rcases lt_trichotomy (2*s.re) 1 with ht | ht | ht
    · have he := tendsto_nhds_unique H (upperChoice_below hc hcd hsep hbe ht hk)
      norm_num at he
    · linarith only [ht]
    · have he := tendsto_nhds_unique H (upperChoice_above hc hcd hsep hbe ht hk)
      norm_num at he

#print axioms pairWeight_on_union
#print axioms separated_disjoint
#print axioms positive_count_alternatives_disjoint
#print axioms upperChoice_eq_joint
#print axioms upperChoice_eq
#print axioms upperChoice_above
#print axioms upperChoice_below
#print axioms upperChoice_one
#print axioms split_isometric_iff_fair_choice

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization
