import GaloisForLFunctions.RHTower.Sieve.MaynardEndpointReserve
import GaloisForLFunctions.RHTower.Sieve.MaynardTrimmedAmplitudeCells

/-!
# Logarithmic mass above Maynard's endpoint cutoff

A degree-`k` Heath--Brown box has at most `2k` factors.  Factors shorter than the endpoint cutoff
`x₁^(1/(40k))` can therefore carry at most `1/20` of the total logarithmic length.  At least
`19/20` of the logarithmic mass lies on factors to which a near-one pointwise deficit may be
applied.  This is the exact combinatorial step in Maynard's ultra-near-one case.
-/

noncomputable section
namespace RHTower.Sieve

open Finset

/-- Indices whose logarithmic length is at least the Maynard endpoint fraction of total length. -/
def maynardEndpointLongFactorSet
    (L X k : ℕ) (T0 : ℝ) (box : HeathBrownBoxChoice L X k) :
    Finset (HeathBrownBoxFactorIndex k box.m) := by
  classical
  exact Finset.univ.filter fun i =>
    heathBrownBoxTotalExponent L X k T0 box / (40 * k : ℕ) ≤
      dyadicLogExponent T0
        (heathBrownBoxFactorExponent box.a box.b box.q i)

theorem dyadicLogExponent_nonneg
    {T0 : ℝ} (hT0 : 1 < T0) (q : ℕ) :
    0 ≤ dyadicLogExponent T0 q := by
  rw [dyadicLogExponent, Real.logb]
  have hpow : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero q (by norm_num : 2 ≠ 0)))
  exact div_nonneg (Real.log_nonneg hpow) (Real.log_nonneg hT0.le)

/-- Generic endpoint mass lemma.  Among at most `2k` nonnegative weights, those below
`total/(40k)` carry at most `total/20`. -/
theorem sum_endpoint_short_weights_le_one_twentieth
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 0 < k) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hcard : Fintype.card ι ≤ 2 * k) :
    ∑ i ∈ (Finset.univ.filter fun i =>
        w i < (∑ j, w j) / (40 * k : ℕ)), w i ≤
      (1 / 20 : ℝ) * ∑ i, w i := by
  classical
  let total : ℝ := ∑ i, w i
  let short : Finset ι := Finset.univ.filter fun i =>
    w i < total / (40 * k : ℕ)
  have htotal : 0 ≤ total := Finset.sum_nonneg fun i _ => hw i
  have hkcast : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (40 * k : ℕ) := by positivity
  have hratio : 0 ≤ total / (40 * k : ℕ) := div_nonneg htotal hden.le
  have hsum : ∑ i ∈ short, w i ≤
      (short.card : ℝ) * (total / (40 * k : ℕ)) := by
    calc
      ∑ i ∈ short, w i ≤ ∑ _i ∈ short, total / (40 * k : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2.le
      _ = (short.card : ℝ) * (total / (40 * k : ℕ)) := by simp
  have hshortCardNat : short.card ≤ 2 * k :=
    (Finset.card_le_univ short).trans hcard
  have hshortCard : (short.card : ℝ) ≤ 2 * k := by
    exact_mod_cast hshortCardNat
  have hcardMul :
      (short.card : ℝ) * (total / (40 * k : ℕ)) ≤
        (2 * k : ℝ) * (total / (40 * k : ℕ)) :=
    mul_le_mul_of_nonneg_right hshortCard hratio
  have hcollapse :
      (2 * k : ℝ) * (total / (40 * k : ℕ)) =
        (1 / 20 : ℝ) * total := by
    push_cast
    field_simp
    ring
  simpa [short, total, hcollapse] using hsum.trans (hcardMul.trans_eq hcollapse)

/-- Complementary generic form: endpoint-long indices carry at least `19/20` of total mass. -/
theorem nineteen_twentieths_total_le_sum_endpoint_long_weights
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 0 < k) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hcard : Fintype.card ι ≤ 2 * k) :
    (19 / 20 : ℝ) * ∑ i, w i ≤
      ∑ i ∈ (Finset.univ.filter fun i =>
        (∑ j, w j) / (40 * k : ℕ) ≤ w i), w i := by
  classical
  let long : Finset ι := Finset.univ.filter fun i =>
    (∑ j, w j) / (40 * k : ℕ) ≤ w i
  let short : Finset ι := Finset.univ.filter fun i =>
    w i < (∑ j, w j) / (40 * k : ℕ)
  have hshort := sum_endpoint_short_weights_le_one_twentieth k hk w hw hcard
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset ι)
    (fun i => (∑ j, w j) / (40 * k : ℕ) ≤ w i) w
  have hnot : ∑ i ∈ (Finset.univ.filter fun i =>
      ¬ (∑ j, w j) / (40 * k : ℕ) ≤ w i), w i =
      ∑ i ∈ short, w i := by
    apply Finset.sum_congr
    · ext i
      simp [short, not_le]
    · intro i hi
      rfl
  rw [hnot] at hsplit
  have hsplit' : ∑ i, w i = ∑ i ∈ long, w i + ∑ i ∈ short, w i := by
    simpa [long] using hsplit.symm
  have hshort' : ∑ i ∈ short, w i ≤ (1 / 20 : ℝ) * ∑ i, w i := by
    simpa [short] using hshort
  rw [hsplit'] at hshort'
  have : (19 / 20 : ℝ) *
        (∑ i ∈ long, w i + ∑ i ∈ short, w i) ≤
      ∑ i ∈ long, w i := by
    linarith
  calc
    (19 / 20 : ℝ) * ∑ i, w i =
        (19 / 20 : ℝ) *
          (∑ i ∈ long, w i + ∑ i ∈ short, w i) := by rw [hsplit']
    _ ≤ ∑ i ∈ long, w i := this
    _ = ∑ i ∈ (Finset.univ.filter fun i =>
        (∑ j, w j) / (40 * k : ℕ) ≤ w i), w i := by rfl

/-- **Literal degree-`k` Heath--Brown endpoint mass law.**  At least `19/20` of a box's exact
height-logarithmic exponent belongs to factors of relative length at least `1/(40k)`. -/
theorem nineteen_twentieths_heathBrownBoxTotalExponent_le_endpointLong
    {L X k : ℕ} (hk : 0 < k) {T0 : ℝ} (hT0 : 1 < T0)
    (box : HeathBrownBoxChoice L X k) :
    (19 / 20 : ℝ) * heathBrownBoxTotalExponent L X k T0 box ≤
      ∑ i ∈ maynardEndpointLongFactorSet L X k T0 box,
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent box.a box.b box.q i) := by
  let I := HeathBrownBoxFactorIndex k box.m
  let w : I → ℝ := fun i => dyadicLogExponent T0
    (heathBrownBoxFactorExponent box.a box.b box.q i)
  have hw : ∀ i, 0 ≤ w i := fun i => dyadicLogExponent_nonneg hT0 _
  have hm : box.m < k := box.1.isLt
  have hcardEq : Fintype.card I = 2 * (k - box.m) :=
    card_heathBrownBoxFactorIndex hm
  have hcard : Fintype.card I ≤ 2 * k := by
    rw [hcardEq]
    omega
  have hmass := nineteen_twentieths_total_le_sum_endpoint_long_weights
    k hk w hw hcard
  simpa [I, w, maynardEndpointLongFactorSet, heathBrownBoxTotalExponent] using hmass

/-- Finite-family rigidity from a deficit on an entire subset.  Only the subset's total
logarithmic length matters; individual factor lengths disappear. -/
theorem maynard_finite_subset_deficit_with_log_slack
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {x alpha ell Delta E : ℝ} (N a slack : ι → ℝ) (u : Finset ι)
    (hx : 1 < x) (hN : ∀ i, 1 ≤ N i)
    (hlogTotal : Real.log x = ∑ i, Real.log (N i))
    (hweighted : alpha * Real.log x = ∑ i, a i * Real.log (N i))
    (hDelta : 0 ≤ Delta) (hslack : ∀ i, 0 ≤ slack i)
    (hall : ∀ i, a i ≤ 1 + slack i)
    (hu : ∀ i ∈ u, a i ≤ 1 - Delta)
    (hlengthMass : ell * Real.log x ≤ ∑ i ∈ u, Real.log (N i))
    (hslackMass : ∑ i, slack i * Real.log (N i) ≤ E * Real.log x) :
    alpha ≤ 1 - (ell * Delta - E) := by
  classical
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogN : ∀ i, 0 ≤ Real.log (N i) := fun i => Real.log_nonneg (hN i)
  have hterm : ∀ i, a i * Real.log (N i) ≤
      Real.log (N i) + slack i * Real.log (N i) -
        (if i ∈ u then Delta * Real.log (N i) else 0) := by
    intro i
    by_cases hi : i ∈ u
    · have hmul := mul_le_mul_of_nonneg_right (hu i hi) (hlogN i)
      have hslackTerm : 0 ≤ slack i * Real.log (N i) :=
        mul_nonneg (hslack i) (hlogN i)
      simp only [if_pos hi]
      nlinarith
    · simp only [if_neg hi, sub_zero]
      have hmul := mul_le_mul_of_nonneg_right (hall i) (hlogN i)
      nlinarith
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hdeltaLength : Delta * (ell * Real.log x) ≤
      Delta * ∑ i ∈ u, Real.log (N i) :=
    mul_le_mul_of_nonneg_left hlengthMass hDelta
  have hpenalty :
      ∑ i, (if i ∈ u then Delta * Real.log (N i) else 0) =
        Delta * ∑ i ∈ u, Real.log (N i) := by
    calc
      ∑ i, (if i ∈ u then Delta * Real.log (N i) else 0) =
          ∑ i ∈ u, Delta * Real.log (N i) := by simp
      _ = Delta * ∑ i ∈ u, Real.log (N i) := by rw [Finset.mul_sum]
  have hgoal : alpha * Real.log x ≤
      (1 - (ell * Delta - E)) * Real.log x := by
    calc
      alpha * Real.log x = ∑ i, a i * Real.log (N i) := hweighted
      _ ≤ (∑ i, Real.log (N i)) +
          (∑ i, slack i * Real.log (N i)) -
            Delta * ∑ i ∈ u, Real.log (N i) := by
        rw [← hpenalty]
        simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib] using hsum
      _ ≤ Real.log x + E * Real.log x -
          Delta * ∑ i ∈ u, Real.log (N i) := by
        rw [← hlogTotal]
        linarith
      _ ≤ Real.log x + E * Real.log x - Delta * (ell * Real.log x) :=
        sub_le_sub_left hdeltaLength _
      _ = (1 - (ell * Delta - E)) * Real.log x := by ring
  exact le_of_mul_le_mul_right hgoal hlogx

/-- Actual-product threshold form of subset deficit rigidity. -/
theorem maynard_product_threshold_subset_deficit_with_log_slack
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {c alpha ell Delta E : ℝ} (N W slack : ι → ℝ) (u : Finset ι)
    (hN : ∀ i, 1 < N i) (hW : ∀ i, 0 < W i)
    (hDelta : 0 ≤ Delta) (hslack : ∀ i, 0 ≤ slack i)
    (hall : ∀ i, maynardAmplitude c (N i) (W i) ≤ 1 + slack i)
    (hu : ∀ i ∈ u, maynardAmplitude c (N i) (W i) ≤ 1 - Delta)
    (hlengthMass : ell * Real.log (∏ i, N i) ≤
      ∑ i ∈ u, Real.log (N i))
    (hslackMass : ∑ i, slack i * Real.log (N i) ≤
      E * Real.log (∏ i, N i))
    (hlarge : (∏ i, N i) ^ (alpha - c) ≤ ∏ i, W i) :
    alpha ≤ 1 - (ell * Delta - E) := by
  classical
  have hx : 1 < ∏ i, N i := by
    calc
      1 = ∏ _i : ι, (1 : ℝ) := by simp
      _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
        (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
  have hlogTotal : Real.log (∏ i, N i) = ∑ i, Real.log (N i) :=
    Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i)))
  have hweighted := maynardGlobalAmplitude_weighted_mean (c := c) N W hN hW rfl rfl
  have hglobal : alpha ≤ maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) :=
    le_maynardAmplitude_of_rpow_le hx hlarge
  exact hglobal.trans
    (maynard_finite_subset_deficit_with_log_slack N
      (fun i => maynardAmplitude c (N i) (W i)) slack u hx
        (fun i => (hN i).le) hlogTotal hweighted hDelta hslack hall hu
        hlengthMass hslackMass)

end RHTower.Sieve
