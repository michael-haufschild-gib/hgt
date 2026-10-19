import GaloisForLFunctions.BiScaleUncertainty.SieveLocalVisibilityClassification
import GaloisForLFunctions.BiScaleUncertainty.SieveArithmeticSourceAnchors

/-!
# Prime-Anchor Phase Separation, Squarefree Visibility Closure, and Cubic Instability

`SieveLocalVisibilityClassification` proves its local Hölder classification under the
hypothesis `selbergMultiplesCoord N b (TopAnchor.topOrder N) ≠ 0`. However, as shown in
`SieveArithmeticSourceAnchors`, every squarefree-supported coefficient row (including
Möbius and Barban–Vehov tapers) has vanishing highest-dyadic coordinate for `N ≥ 4`.

This module develops two general mechanisms that resolve local visibility and stability
beyond the highest-dyadic stratum:

1. **Squarefree closure of arithmetic visibility (`squarefree_of_visible`):**
   In any commutative group, the additive order of a sum divides the least common multiple
   of the summands' orders. Because `Nat.lcm` preserves squarefreeness, any mode `q` that is
   first-order visible from a squarefree active support must itself be squarefree.
   Consequently, for any squarefree-supported source `b`, every non-squarefree mode `q` is
   simultaneously inactive (`q ∉ activeModes N b`) and invisible (`¬Visible N (activeModes N b) q`).

2. **General anchor phase relation (`anchor_phase_relation_of_factorization_le`):**
   Any active anchor `a ∈ Icc 1 N` controls the translation phase of every mode `q ∈ Icc 1 N`
   whose 2-adic valuation satisfies `q.factorization 2 ≤ a.factorization 2`. In particular,
   even an odd prime anchor (`a.factorization 2 = 0`) locks the translation phase of every odd
   mode `q` (`q.factorization 2 = 0`) via an odd-exponent relation `z_a^p = z_q^u` with `Odd u`.

Combining (1) and (2) at the smallest odd composite square `q = 9` (`¬Squarefree 9` and
`9.factorization 2 = 0 ≤ a.factorization 2`) proves unconditionally that **every**
squarefree-supported source with `N ≥ 9` and **any** nonzero coordinate anchor `a ∈ Icc 1 N`
(in particular, any Möbius or Barban–Vehov taper with a surviving prime anchor) fails
`LocalPairwiseHolder N b α` for every `α > 1/3`. On the positive side, any retained even
anchor (`1 ≤ u.factorization 2`) recovers every odd mode with cube-root stability `2 * δ`.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset
open GaloisForLFunctions.BezoutValuationIncidence RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility

open ValuationPhase ParityNeighborhood

set_option autoImplicit false

/-! ## 1. Squarefree Closure of First-Order Arithmetic Visibility -/

/-- The least common multiple of two squarefree natural numbers is squarefree. -/
theorem squarefree_lcm_of_squarefree {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    Squarefree (Nat.lcm d e) := by
  refine Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero hd.ne_zero he.ne_zero) fun p => ?_
  rw [Nat.factorization_lcm hd.ne_zero he.ne_zero, Finsupp.sup_apply]
  exact max_le (hd.natFactorization_le_one p) (he.natFactorization_le_one p)

/-- In any commutative group, the additive order of a sum of two elements with squarefree
orders is again squarefree. -/
theorem squarefree_addOrderOf_add {G : Type*} [AddCommGroup G] {x y : G}
    (hx : Squarefree (addOrderOf x)) (hy : Squarefree (addOrderOf y)) :
    Squarefree (addOrderOf (x + y)) :=
  (squarefree_lcm_of_squarefree hx hy).squarefree_of_dvd
    (AddCommute.all x y).addOrderOf_add_dvd_lcm

/-- In any commutative group, the additive order of a finite sum of elements with squarefree
orders is squarefree. -/
theorem squarefree_addOrderOf_sum {G : Type*} [AddCommGroup G] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → G) (hr : ∀ i ∈ s, Squarefree (addOrderOf (r i))) :
    Squarefree (addOrderOf (∑ i ∈ s, r i)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact squarefree_addOrderOf_add (hr a (mem_insert_self a s))
      (ih (fun i hi => hr i (mem_insert_of_mem hi)))

/-- **Squarefree Closure of Visibility:** If every active mode in `S` is squarefree, then
every mode `q` that is first-order visible from `S` must also be squarefree. -/
theorem squarefree_of_visible {N : ℕ} {S : Finset ℕ} (hS : ∀ u ∈ S, Squarefree u)
    {q : ℕ} (hv : Visible N S q) :
    Squarefree q := by
  classical
  obtain ⟨m, _, r, hz, i, hi, hr⟩ := hv
  have hsum : r i + ∑ j ∈ (univ : Finset (Fin m)).erase i, r j = 0 := by
    rw [add_sum_erase univ r (mem_univ i), hz]
  have hneg : ∑ j ∈ (univ : Finset (Fin m)).erase i, r j = -r i :=
    eq_neg_of_add_eq_zero_right hsum
  have hord : addOrderOf (∑ j ∈ (univ : Finset (Fin m)).erase i, r j) = q := by
    rw [hneg, addOrderOf_neg, hi]
  rw [← hord]
  exact squarefree_addOrderOf_sum ((univ : Finset (Fin m)).erase i) r
    (fun j hj => hS _ (hr j (mem_erase.mp hj).1))

/-- Every active mode of a squarefree-supported coefficient row is squarefree. -/
theorem activeModes_squarefree_of_squarefree_support {N : ℕ} {b : ℕ → ℝ}
    (hb : ∀ d, ¬Squarefree d → b d = 0) {u : ℕ} (hu : u ∈ activeModes N b) :
    Squarefree u := by
  by_contra hns
  exact (mem_filter.mp hu).2
    (selbergMultiplesCoord_eq_zero_of_not_squarefree N u b hb hns)

/-- For any squarefree-supported source `b`, every non-squarefree mode `q` is both inactive
and invisible from `activeModes N b`. -/
theorem not_visible_of_not_squarefree_of_squarefree_support {N : ℕ} {b : ℕ → ℝ}
    (hb : ∀ d, ¬Squarefree d → b d = 0) {q : ℕ} (hq : ¬Squarefree q) :
    q ∉ activeModes N b ∧ ¬Visible N (activeModes N b) q :=
  ⟨fun h => hq (activeModes_squarefree_of_squarefree_support hb h),
   fun hv => hq (squarefree_of_visible
     (fun _ hu => activeModes_squarefree_of_squarefree_support hb hu) hv)⟩

/-! ## 2. General Anchor Phase Separation & Local Instability -/

/-- **General Anchor Phase Relation:** Any anchor `a ∈ Icc 1 N` controls the translation phase
of every mode `q ∈ Icc 1 N` with `q.factorization 2 ≤ a.factorization 2` via an odd-power
relation `(translationPhase N a h)^p = (translationPhase N q h)^u` with `Odd u`.
When `a` is an odd prime (`a.factorization 2 = 0`), this applies to every odd mode `q`. -/
theorem anchor_phase_relation_of_factorization_le (N : ℕ) {a q : ℕ}
    (ha : a ∈ Icc 1 N) (hq : q ∈ Icc 1 N)
    (hva : q.factorization 2 ≤ a.factorization 2) :
    ∃ p u : ℕ, Odd u ∧ ∀ h : ℕ,
      (translationPhase N a h) ^ p = (translationPhase N q h) ^ u := by
  obtain ⟨i, haeq⟩ := order_odd_decomposition (mem_Icc.mp ha).1
  obtain ⟨j, hqeq⟩ := order_odd_decomposition (mem_Icc.mp hq).1
  let p : ℕ := 2 ^ (a.factorization 2 - q.factorization 2) * (2 * i + 1)
  let u : ℕ := 2 * j + 1
  have ha' : a = 2 ^ (q.factorization 2) * p := by
    dsimp [p]
    rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hva]
    exact haeq
  have hq' : q = 2 ^ (q.factorization 2) * u := hqeq
  have hda : a ∣ N.factorial := Nat.dvd_factorial (mem_Icc.mp ha).1 (mem_Icc.mp ha).2
  have hdq : q ∣ N.factorial := Nat.dvd_factorial (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
  have he : p * (N.factorial / a) = u * (N.factorial / q) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) (q.factorization 2))
    calc
      2 ^ (q.factorization 2) * (p * (N.factorial / a)) =
          a * (N.factorial / a) := by rw [ha']; ring
      _ = N.factorial := Nat.mul_div_cancel' hda
      _ = q * (N.factorial / q) := (Nat.mul_div_cancel' hdq).symm
      _ = (2 ^ (q.factorization 2) * u) * (N.factorial / q) :=
        congrArg (fun x => x * (N.factorial / q)) hq'
      _ = 2 ^ (q.factorization 2) * (u * (N.factorial / q)) := Nat.mul_assoc _ _ _
  refine ⟨p, u, ⟨j, rfl⟩, ?_⟩
  intro h
  exact translationPhase_relation N a q h p u he

/-- Any retained anchor `a ∈ Icc 1 N` prevents translations from hiding a signed missing-mode
spike `q ≠ a` whenever `a` and `q` satisfy an odd-power phase relation. -/
theorem spike_separation_of_anchor_relation (N : ℕ) (b : ℕ → ℝ) {a q : ℕ}
    (ha : a ∈ Icc 1 N) (hq : q ∈ Icc 1 N) (hne : q ≠ a)
    (hA : 1 ≤ |selbergMultiplesCoord N b a|)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (h p u : ℕ) (hu : Odd u)
    (hphase : (translationPhase N a h) ^ p = (translationPhase N q h) ^ u)
    (D : ℝ)
    (herr : ∀ n, |sieveSeq N (spikeWeights N b q (-t)) n -
      sieveSeq N (spikeWeights N b q t) (n + h)| ≤ D) :
    2 * t ≤ ((p : ℝ) + u) * D := by
  let A : ℝ := selbergMultiplesCoord N b a
  let z : ℂ := translationPhase N a h
  let w : ℂ := translationPhase N q h
  have hstrong := translated_coordinate_error N (spikeWeights N b q t)
    (spikeWeights N b q (-t)) h D herr
    ((N.factorial / a : ℕ) : ZMod N.factorial)
  rw [frequency_order ha,
    coordinate_spikeWeights N b q (-t) hq, coordinate_spikeWeights N b q t hq] at hstrong
  simp only [spikeProfile, if_neg hne.symm] at hstrong
  change ‖(A : ℂ) - z * (A : ℂ)‖ ≤ D at hstrong
  rw [show (A : ℂ) - z * (A : ℂ) = (A : ℂ) * (1 - z) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs] at hstrong
  have hz : ‖1 - z‖ ≤ D :=
    (le_mul_of_one_le_left (norm_nonneg _) hA).trans hstrong
  have hweak := translated_coordinate_error N (spikeWeights N b q t)
    (spikeWeights N b q (-t)) h D herr ((N.factorial / q : ℕ) : ZMod N.factorial)
  rw [frequency_order hq, coordinate_spikeWeights N b q (-t) hq,
    coordinate_spikeWeights N b q t hq] at hweak
  simp only [spikeProfile, if_true, Complex.ofReal_neg] at hweak
  change ‖-(t : ℂ) - w * (t : ℂ)‖ ≤ D at hweak
  rw [show -(t : ℂ) - w * (t : ℂ) = -(t : ℂ) * (1 + w) by ring,
    norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] at hweak
  have hzsmall : t * ‖1 - z‖ ≤ D := by
    have hh := mul_le_mul_of_nonneg_right ht1 (norm_nonneg (1 - z))
    exact (show t * ‖1 - z‖ ≤ ‖1 - z‖ by simpa only [one_mul] using hh).trans hz
  have hp := phase_incompatibility z w p u
    (translationPhase_norm N a h).le (translationPhase_norm N q h).le hu hphase
  calc
    2 * t ≤ (p : ℝ) * (t * ‖1 - z‖) + (u : ℝ) * (t * ‖1 + w‖) := by
      nlinarith only [mul_le_mul_of_nonneg_left hp ht]
    _ ≤ (p : ℝ) * D + (u : ℝ) * D :=
      add_le_add (mul_le_mul_of_nonneg_left hzsmall (Nat.cast_nonneg p))
        (mul_le_mul_of_nonneg_left hweak (Nat.cast_nonneg u))
    _ = ((p : ℝ) + u) * D := by ring

/-- Any nonzero coordinate `a ∈ Icc 1 N` rules out local Hölder exponents above `1`. -/
theorem not_above_one_of_anchor (N : ℕ) (b : ℕ → ℝ) {a : ℕ} (ha : a ∈ Icc 1 N)
    (hb : selbergMultiplesCoord N b a ≠ 0) (α : ℝ) (hα : 1 < α) :
    ¬LocalPairwiseHolder N b α := by
  obtain ⟨scl, hscl, hnorm⟩ := normalize_coordinate N b a hb
  intro h
  have h' : LocalPairwiseHolder N (fun d => scl * b d) α :=
    (local_holder_scale_iff N b α scl hscl.ne').mpr h
  let b' : ℕ → ℝ := fun d => scl * b d
  have hb' : 2 ≤ |selbergMultiplesCoord N b' a| := hnorm.ge
  let M : ℝ := coordinateBudget N b'
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (coordinateBudget_one_le N b')
  let L : ℝ := (N.factorial : ℝ) ^ 6 * 6 * (2 * M) ^ 6 * M
  let W : ℝ := (∑ q ∈ Icc 1 N, (q.totient : ℝ)) * M
  have hnot : ¬LocalPairwiseHolder N b' α := by
    apply not_holder_of_witnesses N 1 (by decide) b' (fun _ => b')
      (fun t d => (1 + t) * b' d) L W 1 α (by dsimp [L]; positivity)
      (by dsimp [W]; positivity) (by simpa using hα)
    · intro t ht _ n
      constructor
      · simp only [sub_self, abs_zero]
        dsimp [W]
        positivity
      · exact radial_near_base N b' t ht n
    · intro t ht ht1
      constructor
      · intro v
        simpa only [pow_one] using radial_raw_error N b' t ht ht1 5 (by decide) v
      · intro v
        simpa only [pow_one] using radial_raw_error N b' t ht ht1 6 (by decide) v
    · intro t ht _ h D herr
      simpa only [one_mul] using radial_separation N b' a ha hb' t ht h D herr
  exact hnot h'

/-- **General Anchor Cubic Instability:** If `b` has any nonzero anchor `a ∈ Icc 1 N` and an
invisible missing mode `q ∈ Icc 1 N` with `q.factorization 2 ≤ a.factorization 2`, then
`LocalPairwiseHolder N b α` fails for every `α > 1/3`. -/
theorem not_holder_invisible_of_anchor (N : ℕ) (b : ℕ → ℝ) {a q : ℕ}
    (ha : a ∈ Icc 1 N) (hb : selbergMultiplesCoord N b a ≠ 0)
    (hq : q ∈ Icc 1 N) (hva : q.factorization 2 ≤ a.factorization 2)
    (hmissing : q ∉ activeModes N b) (hv : ¬Visible N (activeModes N b) q)
    (α : ℝ) (hα : 1 / 3 < α) :
    ¬LocalPairwiseHolder N b α := by
  obtain ⟨scl, hscl, hnorm⟩ := normalize_coordinate N b a hb
  have hs := activeModes_scale N b scl hscl.ne'
  intro h
  have h' : LocalPairwiseHolder N (fun d => scl * b d) α :=
    (local_holder_scale_iff N b α scl hscl.ne').mpr h
  let b' : ℕ → ℝ := fun d => scl * b d
  have hA : 1 ≤ |selbergMultiplesCoord N b' a| := by change 1 ≤ |selbergMultiplesCoord N (fun d => scl * b d) a|; linarith [hnorm]
  have hmissing' : q ∉ activeModes N b' := by simpa only [b', hs] using hmissing
  have hv' : ¬Visible N (activeModes N b') q := by simpa only [b', hs] using hv
  have hq0 := coordinate_zero_of_not_active N b' q hmissing'
  have hne : q ≠ a := by
    intro heq
    rw [← heq, hq0, abs_zero] at hA
    linarith
  obtain ⟨p, u, hu, hphase⟩ := anchor_phase_relation_of_factorization_le N ha hq hva
  let L : ℝ := 2 * (N.factorial : ℝ) ^ 6 * (coordinateBudget N b') ^ 6
  have hM : 0 ≤ coordinateBudget N b' :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (coordinateBudget_one_le N b')
  have hnot : ¬LocalPairwiseHolder N b' α := by
    apply not_holder_of_witnesses N 3 (by decide) b'
      (spikeWeights N b' q) (fun t => spikeWeights N b' q (-t))
      L (q.totient : ℝ) ((p : ℝ) + u) α (by dsimp [L]; positivity) (by positivity) hα
    · intro t ht _ n
      constructor
      · simpa only [abs_of_nonneg ht] using spike_near_base N b' q hq hq0 t n
      · simpa only [abs_neg, abs_of_nonneg ht] using spike_near_base N b' q hq hq0 (-t) n
    · intro t ht ht1
      exact ⟨invisible_raw_error N b' q hq hv' t ht ht1 5 (Or.inl rfl),
        invisible_raw_error N b' q hq hv' t ht ht1 6 (Or.inr rfl)⟩
    · intro t ht ht1 h D herr
      exact spike_separation_of_anchor_relation N b' ha hq hne hA t ht ht1 h p u hu
        (hphase h) D herr
  exact hnot h'

/-! ## 3. Unconditional Cubic Ceiling for Squarefree-Supported & Prime-Anchored Rows -/

/-- The odd square `9` is not squarefree and has 2-adic valuation `0`. -/
theorem not_squarefree_nine_and_factorization_two :
    ¬Squarefree (9 : ℕ) ∧ (9 : ℕ).factorization 2 = 0 := by
  constructor
  · intro h9
    have hu := h9 3 (by decide : 3 * 3 ∣ 9)
    norm_num at hu
  · exact Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 9)

/-- **Universal Cubic Ceiling for Squarefree-Supported Rows:**
For `N ≥ 9`, every squarefree-supported source `b` with at least one nonzero coordinate
`a ∈ Icc 1 N` fails `LocalPairwiseHolder N b α` for all `α > 1/3`.
This holds regardless of whether `a` is even or an odd prime anchor, because the odd
non-squarefree mode `q = 9` has `9.factorization 2 = 0 ≤ a.factorization 2` and is
invisible from the squarefree active support. -/
theorem not_holder_above_cubic_of_squarefree_support (N : ℕ) (hN : 9 ≤ N)
    (b : ℕ → ℝ) (hb_sq : ∀ d, ¬Squarefree d → b d = 0)
    {a : ℕ} (ha : a ∈ Icc 1 N) (hba : selbergMultiplesCoord N b a ≠ 0)
    (α : ℝ) (hα : 1 / 3 < α) :
    ¬LocalPairwiseHolder N b α := by
  have h9mem : 9 ∈ Icc 1 N := mem_Icc.mpr ⟨by decide, hN⟩
  obtain ⟨h9sq, h9fac⟩ := not_squarefree_nine_and_factorization_two
  obtain ⟨h9miss, h9vis⟩ := not_visible_of_not_squarefree_of_squarefree_support hb_sq h9sq
  have hva : (9 : ℕ).factorization 2 ≤ a.factorization 2 := by
    rw [h9fac]
    exact Nat.zero_le _
  exact not_holder_invisible_of_anchor N b ha hba h9mem hva h9miss h9vis α hα

/-- **Prime-Anchored Möbius Taper Cubic Ceiling:**
For `N ≥ 9`, every Möbius taper `d mapsto μ(d) * w(d)` with a surviving prime-tail anchor
`p ∈ sievePrimeTail N` (`w p ≠ 0`) fails `LocalPairwiseHolder` for all `α > 1/3`. -/
theorem moebius_taper_primeTail_not_holder_above_cubic {N p : ℕ} (hN : 9 ≤ N)
    (hp : p ∈ sievePrimeTail N) (w : ℕ → ℝ) (hwp : w p ≠ 0)
    (α : ℝ) (hα : 1 / 3 < α) :
    ¬LocalPairwiseHolder N (fun d => (μ d : ℝ) * w d) α := by
  have hp_mem : p ∈ Icc 1 N := Icc_subset_Icc_left (by decide) (mem_filter.mp hp).1
  have hcoord : selbergMultiplesCoord N (fun d => (μ d : ℝ) * w d) p ≠ 0 :=
    (selbergMultiplesCoord_moebius_mul_primeTail_ne_zero_iff hp w).mpr hwp
  apply not_holder_above_cubic_of_squarefree_support N hN (fun d => (μ d : ℝ) * w d)
    (fun d hd => by simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd])
    hp_mem hcoord α hα

/-- **Prime-Anchored Barban–Vehov Cubic Ceiling:**
For `N ≥ 9`, the Barban–Vehov weight with any prime-tail anchor `p ∈ sievePrimeTail N`
below the cutoff `p < X` fails `LocalPairwiseHolder` for all `α > 1/3`. -/
theorem barbanVehov_primeTail_not_holder_above_cubic {N p X : ℕ} (hN : 9 ≤ N)
    (hp : p ∈ sievePrimeTail N) (hpX : p < X)
    (α : ℝ) (hα : 1 / 3 < α) :
    ¬LocalPairwiseHolder N (barbanVehovWeight X) α := by
  have hp_mem : p ∈ Icc 1 N := Icc_subset_Icc_left (by decide) (mem_filter.mp hp).1
  have hcoord : selbergMultiplesCoord N (barbanVehovWeight X) p ≠ 0 :=
    (selbergMultiplesCoord_barbanVehov_primeTail_ne_zero_iff hp X).mpr hpX
  apply not_holder_above_cubic_of_squarefree_support N hN (barbanVehovWeight X)
    (fun d hd => by simp [barbanVehovWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd])
    hp_mem hcoord α hα

/-! ## 4. Positive Cube-Root Recovery of Odd Modes from Any Retained Even Anchor -/

/-- **Even-Anchor Cube-Root Recovery of Odd Coordinates:**
While the top dyadic coordinate vanishes on squarefree-supported rows for `N ≥ 4`, any
retained even anchor `u ∈ Icc 1 N` (`1 ≤ u.factorization 2`, such as `u = 2` or `u = 2p`
for an odd prime `p ≤ N/2`) has strictly larger 2-adic valuation than every odd mode
`d ∈ Icc 1 N` (`d.factorization 2 = 0`). Consequently, fifth and sixth raw moment agreement
within `δ^3` forces every odd Selberg coordinate to agree within `2 * δ` without needing
the top dyadic stratum. -/
theorem odd_coordinate_cubic_error_of_even_anchor (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {u d : ℕ} (hu : u ∈ Icc 1 N) (hd : d ∈ Icc 1 N)
    (hu_even : 1 ≤ u.factorization 2) (hd_odd : d.factorization 2 = 0)
    (hc : 1 ≤ |selbergMultiplesCoord N c u|)
    (he : 1 ≤ |selbergMultiplesCoord N e u|)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ δ ^ 3)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ δ ^ 3) :
    |selbergMultiplesCoord N e d - selbergMultiplesCoord N c d| ≤ 2 * δ := by
  have hdu : d.factorization 2 < u.factorization 2 := by omega
  have ha := coordinate_sixth_error N c e (δ ^ 3) h6 u hu
  have hh := TopAnchor.lower_error
    (selbergMultiplesCoord N c d) (selbergMultiplesCoord N e d)
    (selbergMultiplesCoord N c u) (selbergMultiplesCoord N e u)
    δ hc he hδ hδ1 ha (coordinate_sixth_error N c e (δ ^ 3) h6 d hd)
    (TopAnchor.lower_product_error N c e (δ ^ 3) h5 hd hu hdu)
  simpa only [abs_sub_comm] using hh

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
end
