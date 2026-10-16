import GaloisForLFunctions.RHTower.WeilLogShiftAdjacentUniqueness
import GaloisForLFunctions.RHTower.WeilLogShiftCouplingOperations
import GaloisForLFunctions.RHTower.WeilLogShiftMomentRatios

/-!
# Adjacent coupling of the nodal probability profiles of an arbitrary ordered node family

For a strictly increasing node family `h : Fin (r + 2) → ℝ`, the normalized nodal-weight vector
`c = finiteWeilNormalizedMomentDual h` has the exact binomial sign `(-1) ^ (r + 1 - i)` at every
node, and every proper prefix sum has its strict alternating sign.  Its positive and negative parts,
normalized to probabilities `P` and `Q`, therefore have disjoint supports and strictly positive
cut masses `m_i = |Σ_{j ≤ i} (P_j - Q_j)|`.

Main results:
* `finiteWeilNodalEdgeMass_pos`, `finiteWeilNodalEdgeMass_sum`: the adjacent edge masses are
  strictly positive and sum to one;
* `finiteWeilNodalCoupling`: the explicit coupling of `P` to `Q` carried by the adjacent edges;
* `finiteWeilNodalTransport_eq_of_banded`: it is the only coupling supported on adjacent indices;
* `finiteWeilNodalCoupling_index_cost`, `finiteWeilNodalTransport_index_unique_minimizer`: for
  the index cost `|i - j|` its cost is exactly one, and it is the unique optimal coupling.

No ordering hypothesis on prefix sums is assumed: the signs come from the nodal deletion
recurrence (`finiteWeilNormalizedMomentDual_prefix_pos`).
-/

open scoped BigOperators NNReal

noncomputable section
namespace RHTower

/-! ### Exact binomial sign of the nodal weights -/

/-- Every normalized nodal weight of a strictly increasing node family carries the binomial sign
`(-1) ^ (r + 1 - i)`. -/
theorem finiteWeilNormalizedMomentDual_parity_pos {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (i : Fin (r + 2)) :
    0 < finiteWeilBinomialParity r i * finiteWeilNormalizedMomentDual h i := by
  suffices H : ∀ m : ℕ, ∀ i : Fin (r + 2), (i : ℕ) + m = r + 1 →
      0 < finiteWeilBinomialParity r i * finiteWeilNormalizedMomentDual h i from
    H (r + 1 - i) i (by omega)
  intro m
  induction m with
  | zero =>
    intro i hi
    have hl : i = Fin.last (r + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hl
    have hpos := finiteWeilNormalizedMomentDual_last_pos h hh
    simpa [finiteWeilBinomialParity] using hpos
  | succ m ih =>
    intro i hi
    let j : Fin (r + 1) := ⟨i, by omega⟩
    have hjc : j.castSucc = i := Fin.ext rfl
    have hjs := ih j.succ (by simp only [Fin.val_succ, j]; omega)
    have hadj := finiteWeilNormalizedMomentDual_adjacent_mul_neg h hh j
    have hpar := finiteWeilBinomialParity_adjacent r j
    rw [hjc] at hadj hpar
    rw [hpar] at hjs
    rcases finiteWeilBinomialParity_eq_one_or_neg_one r i with e | e
    · rw [e] at hjs ⊢
      nlinarith
    · rw [e] at hjs ⊢
      nlinarith

theorem finiteWeilNormalizedMomentDual_parity {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (i : Fin (r + 2)) :
    finiteWeilNormalizedMomentDual h i =
      finiteWeilBinomialParity r i * |finiteWeilNormalizedMomentDual h i| := by
  have hp := finiteWeilNormalizedMomentDual_parity_pos h hh i
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r i with e | e
  · rw [e, one_mul] at hp ⊢
    rw [abs_of_pos hp]
  · rw [e] at hp ⊢
    rw [abs_of_neg (by linarith only [hp])]
    ring

theorem finiteWeilNormalizedMomentDual_sum_zero {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : Function.Injective h) : ∑ i, finiteWeilNormalizedMomentDual h i = 0 := by
  simpa only [pow_zero, mul_one] using
    finiteWeilNormalizedMomentDual_moment h hh 0 (by omega)

/-! ### The two probability profiles -/

/-- Normalized positive part of the nodal-weight vector. -/
def finiteWeilNodalPositiveProfile {r : ℕ} (h : Fin (r + 2) → ℝ) : Fin (r + 2) → ℝ :=
  finiteWeilPositiveProfile (finiteWeilNormalizedMomentDual h)

/-- Normalized negative part of the nodal-weight vector. -/
def finiteWeilNodalNegativeProfile {r : ℕ} (h : Fin (r + 2) → ℝ) : Fin (r + 2) → ℝ :=
  finiteWeilNegativeProfile (finiteWeilNormalizedMomentDual h)

theorem finiteWeilNodal_scale_pos {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h) :
    0 < 2 / finiteWeilAbsMass (finiteWeilNormalizedMomentDual h) :=
  (finiteWeil_profile_scale_bounds _ (finiteWeilNormalizedMomentDual_norm h hh.injective)
    (finiteWeilNormalizedMomentDual_sum_zero h hh.injective)).1

/-- The two profiles are disjointly supported probabilities covering every node, with absolute
difference two, and they share every moment `Σ P_i h_i ^ p = Σ Q_i h_i ^ p` with `p ≤ r`. -/
theorem finiteWeilNodalProfiles_spec {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h) :
    (∀ i, 0 ≤ finiteWeilNodalPositiveProfile h i ∧ 0 ≤ finiteWeilNodalNegativeProfile h i ∧
      finiteWeilNodalPositiveProfile h i * finiteWeilNodalNegativeProfile h i = 0 ∧
      0 < finiteWeilNodalPositiveProfile h i + finiteWeilNodalNegativeProfile h i) ∧
    (∑ i, finiteWeilNodalPositiveProfile h i) = 1 ∧
    (∑ i, finiteWeilNodalNegativeProfile h i) = 1 ∧
    (∑ i, |finiteWeilNodalPositiveProfile h i - finiteWeilNodalNegativeProfile h i|) = 2 ∧
    (∀ p ≤ r, (∑ i, finiteWeilNodalPositiveProfile h i * h i ^ p) =
      ∑ i, finiteWeilNodalNegativeProfile h i * h i ^ p) := by
  obtain ⟨hp, hpsum, hqsum, htv⟩ := finiteWeil_profiles_spec (finiteWeilNormalizedMomentDual h)
    (finiteWeilNormalizedMomentDual_norm h hh.injective)
    (finiteWeilNormalizedMomentDual_sum_zero h hh.injective)
    (finiteWeilNormalizedMomentDual_ne_zero h hh.injective)
  refine ⟨hp, hpsum, hqsum, htv, fun p hpr => ?_⟩
  apply sub_eq_zero.mp
  unfold finiteWeilNodalPositiveProfile finiteWeilNodalNegativeProfile
  rw [finiteWeil_profile_pairing, finiteWeilNormalizedMomentDual_moment h hh.injective p
    (by omega), mul_zero]

theorem finiteWeilNodalProfiles_parity {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (j : Fin (r + 2)) :
    finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j =
      finiteWeilBinomialParity r j *
        |finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j| := by
  have hscale := finiteWeilNodal_scale_pos h hh
  unfold finiteWeilNodalPositiveProfile finiteWeilNodalNegativeProfile
  simp only [finiteWeil_profile_difference]
  rw [abs_mul, abs_of_pos hscale]
  calc
    _ = (2 / finiteWeilAbsMass (finiteWeilNormalizedMomentDual h)) *
        (finiteWeilBinomialParity r j * |finiteWeilNormalizedMomentDual h j|) :=
      congrArg (fun x => (2 / finiteWeilAbsMass (finiteWeilNormalizedMomentDual h)) * x)
        (finiteWeilNormalizedMomentDual_parity h hh j)
    _ = _ := by ring

theorem finiteWeilNodalPositiveProfile_zero_of_parity {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (u : Fin (r + 2)) (hu : finiteWeilBinomialParity r u = -1) :
    finiteWeilNodalPositiveProfile h u = 0 := by
  have hc := finiteWeilNormalizedMomentDual_parity h hh u
  rw [hu, neg_one_mul] at hc
  have hz : |finiteWeilNormalizedMomentDual h u| + finiteWeilNormalizedMomentDual h u = 0 := by
    linarith only [hc]
  change (|finiteWeilNormalizedMomentDual h u| + finiteWeilNormalizedMomentDual h u) /
    finiteWeilAbsMass (finiteWeilNormalizedMomentDual h) = 0
  rw [hz, zero_div]

theorem finiteWeilNodalNegativeProfile_zero_of_parity {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (u : Fin (r + 2)) (hu : finiteWeilBinomialParity r u = 1) :
    finiteWeilNodalNegativeProfile h u = 0 := by
  have hc := finiteWeilNormalizedMomentDual_parity h hh u
  rw [hu, one_mul] at hc
  change (|finiteWeilNormalizedMomentDual h u| - finiteWeilNormalizedMomentDual h u) /
    finiteWeilAbsMass (finiteWeilNormalizedMomentDual h) = 0
  rw [← hc, sub_self, zero_div]

theorem finiteWeilNodalProfiles_difference_sum {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) :
    (∑ j, (finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j)) = 0 := by
  rw [Finset.sum_sub_distrib, (finiteWeilNodalProfiles_spec h hh).2.1,
    (finiteWeilNodalProfiles_spec h hh).2.2.1, sub_self]

/-! ### Strict prefix signs and the adjacent edge masses -/

/-- Prefix sum of `P - Q` through node `i`. -/
def finiteWeilNodalPrefixDifference {r : ℕ} (h : Fin (r + 2) → ℝ) (i : Fin (r + 1)) : ℝ :=
  ∑ j ∈ Finset.Iic i.castSucc, (finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j)

/-- The mass carried by the adjacent edge between nodes `i` and `i + 1`. -/
def finiteWeilNodalEdgeMass {r : ℕ} (h : Fin (r + 2) → ℝ) (i : Fin (r + 1)) : ℝ :=
  |finiteWeilNodalPrefixDifference h i|

theorem finiteWeilNodalPrefixDifference_eq {r : ℕ} (h : Fin (r + 2) → ℝ) (i : Fin (r + 1)) :
    finiteWeilNodalPrefixDifference h i =
      (2 / finiteWeilAbsMass (finiteWeilNormalizedMomentDual h)) *
        ∑ j ∈ Finset.Iic i.castSucc, finiteWeilNormalizedMomentDual h j := by
  unfold finiteWeilNodalPrefixDifference finiteWeilNodalPositiveProfile
    finiteWeilNodalNegativeProfile
  simp only [finiteWeil_profile_difference, Finset.mul_sum]

/-- Every proper prefix of `P - Q` has the strict sign of its last node. -/
theorem finiteWeilNodalPrefixDifference_pos {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (i : Fin (r + 1)) :
    0 < finiteWeilBinomialParity r i.castSucc * finiteWeilNodalPrefixDifference h i := by
  rw [finiteWeilNodalPrefixDifference_eq]
  have hprefix : 0 < finiteWeilBinomialParity r i.castSucc *
      ∑ j ∈ Finset.Iic i.castSucc, finiteWeilNormalizedMomentDual h j :=
    finiteWeilNormalizedMomentDual_prefix_pos h hh i
  have hp := mul_pos (finiteWeilNodal_scale_pos h hh) hprefix
  simpa only [mul_left_comm] using hp

theorem finiteWeilNodalEdgeMass_pos {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (i : Fin (r + 1)) : 0 < finiteWeilNodalEdgeMass h i := by
  apply abs_pos.mpr
  intro he
  have hp := finiteWeilNodalPrefixDifference_pos h hh i
  rw [he, mul_zero] at hp
  exact (lt_irrefl 0) hp

theorem finiteWeilNodalPrefixDifference_signed_mass {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (i : Fin (r + 1)) :
    finiteWeilNodalPrefixDifference h i =
      finiteWeilBinomialParity r i.castSucc * finiteWeilNodalEdgeMass h i := by
  have hp := finiteWeilNodalPrefixDifference_pos h hh i
  have habs : finiteWeilNodalEdgeMass h i =
      finiteWeilBinomialParity r i.castSucc * finiteWeilNodalPrefixDifference h i := by
    simpa only [abs_mul, finiteWeilBinomialParity_abs, one_mul, finiteWeilNodalEdgeMass] using
      abs_of_pos hp
  rw [habs, ← mul_assoc, ← pow_two, finiteWeilBinomialParity_sq, one_mul]

theorem finiteWeilNodalProfiles_parity_pairing {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) :
    (∑ j, (finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j) *
      finiteWeilBinomialParity r j) = 2 := by
  have hpoint (j : Fin (r + 2)) :
      (finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j) *
        finiteWeilBinomialParity r j =
        |finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j| := by
    calc
      _ = (finiteWeilBinomialParity r j *
          |finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j|) *
          finiteWeilBinomialParity r j :=
        congrArg (fun x => x * finiteWeilBinomialParity r j) (finiteWeilNodalProfiles_parity h hh j)
      _ = finiteWeilBinomialParity r j ^ 2 *
          |finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j| := by ring
      _ = _ := by rw [finiteWeilBinomialParity_sq, one_mul]
  simp_rw [hpoint]
  exact (finiteWeilNodalProfiles_spec h hh).2.2.2.1

/-- The adjacent edge masses form a probability vector: total transported mass is one. -/
theorem finiteWeilNodalEdgeMass_sum {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h) :
    (∑ i, finiteWeilNodalEdgeMass h i) = 1 := by
  have hp := finiteWeil_prefix_pairing_zero
    (fun j => finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j)
    (finiteWeilBinomialParity r) (finiteWeilNodalProfiles_difference_sum h hh)
  rw [finiteWeilNodalProfiles_parity_pairing h hh] at hp
  have hedge (i : Fin (r + 1)) :
      (∑ j ∈ Finset.Iic i.castSucc,
        (finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j)) *
        (finiteWeilBinomialParity r i.castSucc - finiteWeilBinomialParity r i.succ) =
          2 * finiteWeilNodalEdgeMass h i := by
    change finiteWeilNodalPrefixDifference h i *
      (finiteWeilBinomialParity r i.castSucc - finiteWeilBinomialParity r i.succ) = _
    rw [finiteWeilNodalPrefixDifference_signed_mass h hh, finiteWeilBinomialParity_adjacent]
    calc
      _ = 2 * finiteWeilBinomialParity r i.castSucc ^ 2 * finiteWeilNodalEdgeMass h i := by ring
      _ = _ := by rw [finiteWeilBinomialParity_sq, mul_one]
  simp_rw [hedge] at hp
  rw [← Finset.mul_sum] at hp
  linarith

/-- Each oriented adjacent edge transports `P - Q` exactly: summation by parts along the edges. -/
theorem finiteWeilNodalEdge_pairing {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (f : Fin (r + 2) → ℝ) :
    (∑ i, finiteWeilNodalEdgeMass h i *
      (f (finiteWeilCanonicalEdgeSource r i) - f (finiteWeilCanonicalEdgeTarget r i))) =
      ∑ j, (finiteWeilNodalPositiveProfile h j - finiteWeilNodalNegativeProfile h j) * f j := by
  rw [finiteWeil_prefix_pairing_zero _ f (finiteWeilNodalProfiles_difference_sum h hh)]
  apply Finset.sum_congr rfl
  intro i _
  change _ = finiteWeilNodalPrefixDifference h i * (f i.castSucc - f i.succ)
  rw [finiteWeilCanonicalEdge_difference, finiteWeilNodalPrefixDifference_signed_mass h hh]
  ring

/-! ### The explicit adjacent coupling -/

/-- The plan that moves mass `m_i` along the `i`-th adjacent edge, from its positive-parity end to
its negative-parity end. -/
def finiteWeilNodalEdgePlan {r : ℕ} (h : Fin (r + 2) → ℝ) (u v : Fin (r + 2)) : ℝ :=
  ∑ i, if finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v
    then finiteWeilNodalEdgeMass h i else 0

theorem finiteWeilNodalEdgePlan_nonneg {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (u v : Fin (r + 2)) : 0 ≤ finiteWeilNodalEdgePlan h u v := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (finiteWeilNodalEdgeMass_pos h hh i).le
  · exact le_rfl

theorem finiteWeilNodalEdgePlan_row_sum {r : ℕ} (h : Fin (r + 2) → ℝ) (u : Fin (r + 2)) :
    (∑ v, finiteWeilNodalEdgePlan h u v) =
      ∑ i, if finiteWeilCanonicalEdgeSource r i = u then finiteWeilNodalEdgeMass h i else 0 := by
  unfold finiteWeilNodalEdgePlan
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : finiteWeilCanonicalEdgeSource r i = u <;> simp [hs]

theorem finiteWeilNodalEdgePlan_col_sum {r : ℕ} (h : Fin (r + 2) → ℝ) (v : Fin (r + 2)) :
    (∑ u, finiteWeilNodalEdgePlan h u v) =
      ∑ i, if finiteWeilCanonicalEdgeTarget r i = v then finiteWeilNodalEdgeMass h i else 0 := by
  unfold finiteWeilNodalEdgePlan
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : finiteWeilCanonicalEdgeTarget r i = v <;> simp [ht]

theorem finiteWeilNodalEdgePlan_divergence {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (u : Fin (r + 2)) :
    (∑ v, finiteWeilNodalEdgePlan h u v) - (∑ v, finiteWeilNodalEdgePlan h v u) =
      finiteWeilNodalPositiveProfile h u - finiteWeilNodalNegativeProfile h u := by
  rw [finiteWeilNodalEdgePlan_row_sum, finiteWeilNodalEdgePlan_col_sum, ← Finset.sum_sub_distrib]
  have hp := finiteWeilNodalEdge_pairing h hh (fun j => if j = u then 1 else 0)
  simpa [mul_sub, mul_ite] using hp

theorem finiteWeilNodalEdgePlan_marginals {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (u : Fin (r + 2)) :
    (∑ v, finiteWeilNodalEdgePlan h u v) = finiteWeilNodalPositiveProfile h u ∧
      (∑ v, finiteWeilNodalEdgePlan h v u) = finiteWeilNodalNegativeProfile h u := by
  have hd := finiteWeilNodalEdgePlan_divergence h hh u
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r u with hu | hu
  · have hcol : (∑ v, finiteWeilNodalEdgePlan h v u) = 0 := by
      rw [finiteWeilNodalEdgePlan_col_sum]
      apply Finset.sum_eq_zero
      intro i _
      have hne : finiteWeilCanonicalEdgeTarget r i ≠ u := by
        intro e
        have ht := finiteWeilCanonicalEdgeTarget_parity r i
        rw [e, hu] at ht
        norm_num at ht
      simp [hne]
    have hQ := finiteWeilNodalNegativeProfile_zero_of_parity h hh u hu
    refine ⟨?_, by rw [hcol, hQ]⟩
    simpa only [hcol, hQ, sub_zero] using hd
  · have hrow : (∑ v, finiteWeilNodalEdgePlan h u v) = 0 := by
      rw [finiteWeilNodalEdgePlan_row_sum]
      apply Finset.sum_eq_zero
      intro i _
      have hne : finiteWeilCanonicalEdgeSource r i ≠ u := by
        intro e
        have hs := finiteWeilCanonicalEdgeSource_parity r i
        rw [e, hu] at hs
        norm_num at hs
      simp [hne]
    have hP := finiteWeilNodalPositiveProfile_zero_of_parity h hh u hu
    refine ⟨by rw [hrow, hP], ?_⟩
    rw [hrow, hP] at hd
    linarith only [hd]

theorem finiteWeilNodalEdgePlan_zero_of_nonadjacent {r : ℕ} (h : Fin (r + 2) → ℝ)
    (u v : Fin (r + 2)) (huv : (u : ℕ) + 1 ≠ (v : ℕ)) (hvu : (v : ℕ) + 1 ≠ (u : ℕ)) :
    finiteWeilNodalEdgePlan h u v = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hne : ¬(finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v) := by
    intro he
    have ha := finiteWeilCanonicalEdge_adjacent r i
    rw [he.1, he.2] at ha
    exact ha.elim huv hvu
  simp [hne]

/-- `P` as a nonnegative real profile. -/
def finiteWeilNodalPositiveNNProfile {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (u : Fin (r + 2)) : ℝ≥0 :=
  NNReal.mk (finiteWeilNodalPositiveProfile h u) ((finiteWeilNodalProfiles_spec h hh).1 u).1

/-- `Q` as a nonnegative real profile. -/
def finiteWeilNodalNegativeNNProfile {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (u : Fin (r + 2)) : ℝ≥0 :=
  NNReal.mk (finiteWeilNodalNegativeProfile h u) ((finiteWeilNodalProfiles_spec h hh).1 u).2.1

/-- The adjacent coupling of `P` to `Q`. -/
def finiteWeilNodalCoupling {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h) :
    HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh) where
  plan u v := NNReal.mk (finiteWeilNodalEdgePlan h u v) (finiteWeilNodalEdgePlan_nonneg h hh u v)
  row u := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, finiteWeilNodalPositiveNNProfile] using
      (finiteWeilNodalEdgePlan_marginals h hh u).1
  col v := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, finiteWeilNodalNegativeNNProfile] using
      (finiteWeilNodalEdgePlan_marginals h hh v).2

theorem finiteWeilNodalCoupling_apply {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (u v : Fin (r + 2)) :
    ((finiteWeilNodalCoupling h hh).plan u v : ℝ) = finiteWeilNodalEdgePlan h u v := rfl

theorem finiteWeilNodalCoupling_zero_of_nonadjacent {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (u v : Fin (r + 2)) (huv : (u : ℕ) + 1 ≠ (v : ℕ))
    (hvu : (v : ℕ) + 1 ≠ (u : ℕ)) : (finiteWeilNodalCoupling h hh).plan u v = 0 := by
  apply NNReal.coe_injective
  exact finiteWeilNodalEdgePlan_zero_of_nonadjacent h u v huv hvu

/-- The coupling cost of any cost matrix is the edge-mass average of its edge values. -/
theorem finiteWeilNodalCoupling_cost_eq {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (c : Fin (r + 2) → Fin (r + 2) → ℝ) :
    finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) c =
      ∑ i, finiteWeilNodalEdgeMass h i *
        c (finiteWeilCanonicalEdgeSource r i) (finiteWeilCanonicalEdgeTarget r i) := by
  change (∑ u, ∑ v, finiteWeilNodalEdgePlan h u v * c u v) = _
  unfold finiteWeilNodalEdgePlan
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ u, ∑ i, ∑ v,
        (if finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v
          then finiteWeilNodalEdgeMass h i else 0) * c u v := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ u, ∑ v,
        (if finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v
          then finiteWeilNodalEdgeMass h i else 0) * c u v := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hrow (u : Fin (r + 2)) :
          (∑ v, (if finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v
            then finiteWeilNodalEdgeMass h i else 0) * c u v) =
          if finiteWeilCanonicalEdgeSource r i = u then
            finiteWeilNodalEdgeMass h i * c u (finiteWeilCanonicalEdgeTarget r i) else 0 := by
        by_cases hu : finiteWeilCanonicalEdgeSource r i = u
        · simp [hu, ite_mul]
        · simp [hu]
      simp_rw [hrow]
      simp

/-! ### Index cost: the coupling is the unique optimum, at cost exactly one -/

theorem finiteWeilNodalCoupling_index_cost {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h) :
    finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) finiteWeilIndexCost = 1 := by
  rw [finiteWeilNodalCoupling_cost_eq]
  simp only [finiteWeilCanonicalEdge_index_cost, mul_one]
  exact finiteWeilNodalEdgeMass_sum h hh

theorem finiteWeilNodalProfiles_index_dual_pairing {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) :
    (∑ u, (finiteWeilNodalPositiveNNProfile h hh u : ℝ) * (finiteWeilBinomialParity r u / 2)) -
      (∑ u, (finiteWeilNodalNegativeNNProfile h hh u : ℝ) *
        (finiteWeilBinomialParity r u / 2)) = 1 := by
  change (∑ u, finiteWeilNodalPositiveProfile h u * (finiteWeilBinomialParity r u / 2)) -
    (∑ u, finiteWeilNodalNegativeProfile h u * (finiteWeilBinomialParity r u / 2)) = 1
  calc
    _ = (∑ u, (finiteWeilNodalPositiveProfile h u - finiteWeilNodalNegativeProfile h u) *
        finiteWeilBinomialParity r u) / 2 := by
      simp only [Finset.sum_div, sub_mul, Finset.sum_sub_distrib, mul_div_assoc, sub_div]
    _ = 1 := by rw [finiteWeilNodalProfiles_parity_pairing h hh]; norm_num

theorem finiteWeilNodalTransport_index_lower_bound {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) :
    1 ≤ finiteWeilCouplingCost gamma finiteWeilIndexCost := by
  rw [← finiteWeilNodalProfiles_index_dual_pairing h hh]
  exact finiteWeilCoupling_dual_bound gamma finiteWeilIndexCost
    (fun u => finiteWeilBinomialParity r u / 2) (finiteWeilBinomialParity_index_dual r)

theorem finiteWeilNodalTransport_source_zero {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) (u v : Fin (r + 2))
    (hu : finiteWeilBinomialParity r u = -1) : gamma.plan u v = 0 := by
  have hr := congrArg NNReal.toReal (gamma.row u)
  simp only [NNReal.coe_sum, finiteWeilNodalPositiveNNProfile, NNReal.coe_mk] at hr
  rw [finiteWeilNodalPositiveProfile_zero_of_parity h hh u hu] at hr
  apply NNReal.coe_injective
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => (gamma.plan u j).coe_nonneg)).mp hr v (Finset.mem_univ v)

theorem finiteWeilNodalTransport_target_zero {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) (u v : Fin (r + 2))
    (hv : finiteWeilBinomialParity r v = 1) : gamma.plan u v = 0 := by
  have hc := congrArg NNReal.toReal (gamma.col v)
  simp only [NNReal.coe_sum, finiteWeilNodalNegativeNNProfile, NNReal.coe_mk] at hc
  rw [finiteWeilNodalNegativeProfile_zero_of_parity h hh v hv] at hc
  apply NNReal.coe_injective
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => (gamma.plan j v).coe_nonneg)).mp hc u (Finset.mem_univ u)

/-- Disjoint marginal supports exclude every diagonal entry. -/
theorem finiteWeilNodalTransport_diagonal {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) (u : Fin (r + 2)) : gamma.plan u u = 0 := by
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r u with hu | hu
  · exact finiteWeilNodalTransport_target_zero h hh gamma u u hu
  · exact finiteWeilNodalTransport_source_zero h hh gamma u u hu

theorem finiteWeilNodalTransport_reverse_edge_zero {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) (i : Fin (r + 1)) :
    gamma.plan (finiteWeilCanonicalEdgeTarget r i) (finiteWeilCanonicalEdgeSource r i) = 0 :=
  finiteWeilNodalTransport_source_zero h hh gamma _ _ (finiteWeilCanonicalEdgeTarget_parity r i)

/-- An index-optimal coupling has no mass on pairs at distance at least two. -/
theorem finiteWeilNodalTransport_index_banded {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh))
    (hopt : finiteWeilCouplingCost gamma finiteWeilIndexCost = 1) (u v : Fin (r + 2))
    (hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ)) : gamma.plan u v = 0 := by
  have ha : finiteWeilCouplingCost gamma finiteWeilIndexCost =
      (∑ a, (finiteWeilNodalPositiveNNProfile h hh a : ℝ) * (finiteWeilBinomialParity r a / 2)) -
        (∑ b, (finiteWeilNodalNegativeNNProfile h hh b : ℝ) *
          (finiteWeilBinomialParity r b / 2)) := by
    rw [hopt, finiteWeilNodalProfiles_index_dual_pairing h hh]
  exact finiteWeilCoupling_zero_of_strict_dual gamma finiteWeilIndexCost
    (fun a => finiteWeilBinomialParity r a / 2) (finiteWeilBinomialParity_index_dual r) ha u v
    (finiteWeilBinomialParity_index_dual_strict r u v hfar)

/-! ### Uniqueness among adjacent couplings -/

theorem finiteWeilNodalProfiles_cut_pairing {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (i : Fin (r + 1)) :
    (∑ u, (finiteWeilNodalPositiveNNProfile h hh u : ℝ) * finiteWeilCutIndicator i u) -
      (∑ u, (finiteWeilNodalNegativeNNProfile h hh u : ℝ) * finiteWeilCutIndicator i u) =
        finiteWeilNodalPrefixDifference h i := by
  change (∑ u, finiteWeilNodalPositiveProfile h u * finiteWeilCutIndicator i u) -
    (∑ u, finiteWeilNodalNegativeProfile h u * finiteWeilCutIndicator i u) = _
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  simp only [finiteWeilCutIndicator, mul_ite, mul_one, mul_zero]
  change (∑ u, if u ≤ i.castSucc then
    finiteWeilNodalPositiveProfile h u - finiteWeilNodalNegativeProfile h u else 0) = _
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext u
    simp
  · intro u _
    rfl

/-- In a coupling supported on adjacent pairs, the net flux across cut `i` is the prefix mass. -/
theorem finiteWeilNodalCoupling_cut_flux {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh))
    (hband : ∀ u v : Fin (r + 2), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) →
      gamma.plan u v = 0)
    (i : Fin (r + 1)) :
    (gamma.plan i.castSucc i.succ : ℝ) - (gamma.plan i.succ i.castSucc : ℝ) =
      finiteWeilNodalPrefixDifference h i := by
  have hp := finiteWeilCoupling_pairing gamma (finiteWeilCutIndicator i)
  rw [finiteWeilNodalProfiles_cut_pairing h hh] at hp
  unfold finiteWeilCouplingCost at hp
  rw [finiteWeil_banded_cut_pairing (fun u v => (gamma.plan u v : ℝ))
    (fun u v huv => by rw [hband u v huv]; rfl)] at hp
  exact hp.symm

theorem finiteWeilNodalTransport_edge_mass {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh))
    (hband : ∀ u v : Fin (r + 2), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) →
      gamma.plan u v = 0)
    (i : Fin (r + 1)) :
    (gamma.plan (finiteWeilCanonicalEdgeSource r i) (finiteWeilCanonicalEdgeTarget r i) : ℝ) =
      finiteWeilNodalEdgeMass h i := by
  have hp := finiteWeilNodalCoupling_cut_flux h hh gamma hband i
  have hz := finiteWeilNodalTransport_reverse_edge_zero h hh gamma i
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r i.castSucc with hs | hs
  · simp only [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, hs,
      ↓reduceIte] at hz ⊢
    have hz' : (gamma.plan i.succ i.castSucc : ℝ) = 0 := congrArg NNReal.toReal hz
    rw [hz', sub_zero, finiteWeilNodalPrefixDifference_signed_mass h hh, hs, one_mul] at hp
    exact hp
  · norm_num [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, hs] at hz ⊢
    have hz' : (gamma.plan i.castSucc i.succ : ℝ) = 0 := congrArg NNReal.toReal hz
    rw [hz', finiteWeilNodalPrefixDifference_signed_mass h hh, hs, neg_one_mul] at hp
    linarith only [hp]

/-- The adjacent coupling is the only coupling of `P` to `Q` supported on adjacent indices. -/
theorem finiteWeilNodalTransport_eq_of_banded {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh))
    (hband : ∀ u v : Fin (r + 2), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) →
      gamma.plan u v = 0) :
    gamma = finiteWeilNodalCoupling h hh := by
  have hc (u v : Fin (r + 2)) (hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ)) :
      (finiteWeilNodalCoupling h hh).plan u v = 0 :=
    finiteWeilNodalCoupling_zero_of_nonadjacent h hh u v (by omega) (by omega)
  apply finiteWeilCoupling_ext
  intro u v
  by_cases he : u = v
  · subst v
    rw [finiteWeilNodalTransport_diagonal h hh gamma,
      finiteWeilNodalTransport_diagonal h hh (finiteWeilNodalCoupling h hh)]
  · by_cases ha : (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)
    · obtain ⟨i, hi⟩ := finiteWeilCanonicalEdge_covers_adjacent r u v ha
      rcases hi with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rw [← hu, ← hv]
        apply NNReal.coe_injective
        rw [finiteWeilNodalTransport_edge_mass h hh gamma hband,
          finiteWeilNodalTransport_edge_mass h hh (finiteWeilNodalCoupling h hh) hc]
      · rw [← hu, ← hv, finiteWeilNodalTransport_reverse_edge_zero h hh gamma,
          finiteWeilNodalTransport_reverse_edge_zero h hh (finiteWeilNodalCoupling h hh)]
    · have hval : (u : ℕ) ≠ (v : ℕ) := fun e => he (Fin.ext e)
      have hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) := by omega
      rw [hband u v hfar, hc u v hfar]

theorem finiteWeilNodalTransport_index_minimum_iff {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) :
    finiteWeilCouplingCost gamma finiteWeilIndexCost = 1 ↔ gamma = finiteWeilNodalCoupling h hh := by
  constructor
  · intro hopt
    exact finiteWeilNodalTransport_eq_of_banded h hh gamma
      (finiteWeilNodalTransport_index_banded h hh gamma hopt)
  · intro he
    rw [he, finiteWeilNodalCoupling_index_cost]

/-- For the index cost `|i - j|`, the adjacent coupling is the unique optimal coupling of `P`
to `Q`, at every order `r` and for every strictly increasing node family. -/
theorem finiteWeilNodalTransport_index_unique_minimizer {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
        (finiteWeilNodalNegativeNNProfile h hh),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
          (finiteWeilNodalNegativeNNProfile h hh),
        finiteWeilCouplingCost gamma finiteWeilIndexCost ≤
          finiteWeilCouplingCost eta finiteWeilIndexCost := by
  refine ⟨finiteWeilNodalCoupling h hh, fun eta => ?_, fun gamma hg => ?_⟩
  · rw [finiteWeilNodalCoupling_index_cost]
    exact finiteWeilNodalTransport_index_lower_bound h hh eta
  · have hle := hg (finiteWeilNodalCoupling h hh)
    rw [finiteWeilNodalCoupling_index_cost] at hle
    exact (finiteWeilNodalTransport_index_minimum_iff h hh gamma).mp
      (le_antisymm hle (finiteWeilNodalTransport_index_lower_bound h hh gamma))

end RHTower
