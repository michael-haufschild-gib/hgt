import GaloisForLFunctions.HTGeometry.PrivatePrimeApproximation
import GaloisForLFunctions.HTGeometry.BoundedRelationLogMagnitudeHypertranscendence
import GaloisForLFunctions.HTGeometry.PolynomialPowerFiniteDifference

/-!
# Arbitrary private-prime profile realization

This leaf completes the constructive surface of the bounded-relation log-magnitude theorem.
Every prescribed positive superlinear real profile has an arbitrarily close positive rational
realization with private denominator primes.  The resulting exponential series is entire,
full-support, and hypertranscendental for every algebraic unit-modulus phase sequence.

The polynomial specialization uses `B * ((n : ℝ) + 1) ^ β`, rather than the paper card's literal
`B * (n : ℝ) ^ β`: the latter vanishes at `n = 0` and therefore does not satisfy the positivity
hypothesis of the arbitrary-profile theorem.
-/

open Filter Finset PowerSeries Asymptotics

namespace GaloisForLFunctions

noncomputable section

/-- A positive rational realization of `g` within `ε`, equipped with strictly increasing private
denominator primes, superlinear growth, and the resulting bounded-relation confinement. -/
def IsPrivatePrimeSuperlinearApproximation
    (g ε : ℕ → ℝ) (b : ℕ → ℚ) (p : ℕ → ℕ) : Prop :=
  (∀ n, (p n).Prime) ∧
    StrictMono p ∧
    (∀ n, 0 < (b n : ℝ)) ∧
    (∀ n, |(b n : ℝ) - g n| < ε n) ∧
    Tendsto (fun n => (b n : ℝ) / (n : ℝ)) atTop atTop ∧
    (∀ n, 1 < padicNorm (p n) (b n)) ∧
    (∀ n m, m ≠ n → padicNorm (p n) (b m) ≤ 1) ∧
    BoundedRelationConfinement (fun n => (b n : ℝ))

/-- Every prescribed positive superlinear real profile has an arbitrarily close positive rational
realization with strictly increasing private denominator primes. -/
theorem exists_privatePrime_superlinear_profile_realization
    (g ε : ℕ → ℝ) (hgpos : ∀ n, 0 < g n) (hε : ∀ n, 0 < ε n)
    (hgrowth : Tendsto (fun n => g n / (n : ℝ)) atTop atTop) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation g ε b p := by
  obtain ⟨b, p, hp, hpmono, hbpos, hclose, hself, hother⟩ :=
    exists_privatePrime_rational_approximation g ε hgpos hε
  have hpTop : Tendsto p atTop atTop := hpmono.tendsto_atTop
  have hcloseε : ∀ n, |(b n : ℝ) - g n| < ε n := by
    intro n
    exact (hclose n).trans_le (min_le_left _ _)
  have hcloseOne : ∀ n, |(b n : ℝ) - g n| < 1 := by
    intro n
    exact (hclose n).trans_le (min_le_right _ _)
  have hbgrowth : Tendsto (fun n => (b n : ℝ) / (n : ℝ)) atTop atTop :=
    tendsto_div_natCast_atTop_of_abs_sub_lt_one hgrowth hcloseOne
  have hconf : BoundedRelationConfinement (fun n => (b n : ℝ)) :=
    boundedRelationConfinement_of_privatePrime hp hpTop hself hother
  exact ⟨b, p, hp, hpmono, hbpos, hcloseε, hbgrowth, hself, hother, hconf⟩

/-- Every algebraic unit-phase series built from a private-prime superlinear approximation is
entire, has full Taylor support, and is hypertranscendental. -/
theorem IsPrivatePrimeSuperlinearApproximation.entire_fullSupport_hypertranscendental
    {g ε : ℕ → ℝ} {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation g ε b p)
    {u : ℕ → ℂ} (huAlg : ∀ n, IsAlgebraic ℚ (u n)) (huNorm : ∀ n, ‖u n‖ = 1) :
    ContDiff ℂ (⊤ : ℕ∞)
        (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) ∧
      (∀ n, PowerSeries.coeff n
        (taylorPS (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u)) ≠ 0) ∧
      Hypertranscendental
        (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) := by
  rcases h with ⟨_hp, _hpmono, hbpos, _hclose, hgrowth,
    _hself, _hother, hconf⟩
  have hbAlg : ∀ n, IsAlgebraic ℚ ((b n : ℚ) : ℝ) := by
    intro n
    exact isAlgebraic_rat ℚ (b n)
  exact ⟨contDiff_boundedRelationExponentialFunction hgrowth huNorm,
    taylorPS_boundedRelationExponentialFunction_coeff_ne_zero hgrowth huNorm,
    hypertranscendental_boundedRelationExponentialFunction
      hbpos hgrowth hbAlg hconf huAlg huNorm⟩

/-- Capstone form of arbitrary-profile realization: one private-prime rational approximation works
for every algebraic unit-modulus phase sequence. -/
theorem exists_privatePrime_superlinear_profile_entire_fullSupport_hypertranscendental
    (g ε : ℕ → ℝ) (hgpos : ∀ n, 0 < g n) (hε : ∀ n, 0 < ε n)
    (hgrowth : Tendsto (fun n => g n / (n : ℝ)) atTop atTop) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation g ε b p ∧
      ∀ u : ℕ → ℂ,
        (∀ n, IsAlgebraic ℚ (u n)) →
        (∀ n, ‖u n‖ = 1) →
        ContDiff ℂ (⊤ : ℕ∞)
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) ∧
          (∀ n, PowerSeries.coeff n
            (taylorPS (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u)) ≠ 0) ∧
          Hypertranscendental
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) := by
  obtain ⟨b, p, hprofile⟩ :=
    exists_privatePrime_superlinear_profile_realization g ε hgpos hε hgrowth
  refine ⟨b, p, hprofile, ?_⟩
  intro u huAlg huNorm
  exact hprofile.entire_fullSupport_hypertranscendental huAlg huNorm

/-- The everywhere-positive shifted polynomial profile.  The shift is essential at index zero:
`B * (0 : ℝ) ^ β = 0`, whereas the realization theorem requires a positive prescribed profile. -/
def boundedRelationShiftedPolynomialProfile (B β : ℝ) (n : ℕ) : ℝ :=
  B * ((n : ℝ) + 1) ^ β

/-- A shifted polynomial profile with positive scale and exponent above one is superlinear. -/
theorem tendsto_boundedRelationShiftedPolynomialProfile_div_natCast_atTop
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β) :
    Tendsto (fun n => boundedRelationShiftedPolynomialProfile B β n / (n : ℝ))
      atTop atTop := by
  have hlead : Tendsto (fun n : ℕ => B * (n : ℝ) ^ (β - 1)) atTop atTop :=
    ((tendsto_rpow_atTop (sub_pos.mpr hβ)).comp tendsto_natCast_atTop_atTop).const_mul_atTop hB
  refine tendsto_atTop_mono' atTop ?_ hlead
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hbase : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hpow : (n : ℝ) ^ β ≤ ((n : ℝ) + 1) ^ β :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hbase (by linarith)
  rw [boundedRelationShiftedPolynomialProfile, Real.rpow_sub_one hnpos.ne' β]
  calc
    B * ((n : ℝ) ^ β / (n : ℝ)) =
        (B * (n : ℝ) ^ β) / (n : ℝ) := by ring
    _ ≤ (B * ((n : ℝ) + 1) ^ β) / (n : ℝ) :=
      (div_le_div_iff_of_pos_right hnpos).2
        (mul_le_mul_of_nonneg_left hpow hB.le)

/-- First forward difference of a real sequence. -/
def boundedRelationFirstDifference (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  x (n + 1) - x n

/-- Second forward difference of a real sequence. -/
def boundedRelationSecondDifference (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  x (n + 2) - 2 * x (n + 1) + x n

private def boundedRelationFirstDifferenceStencil : ℕ →₀ ℝ :=
  Finsupp.single 1 1 - Finsupp.single 0 1

private def boundedRelationSecondDifferenceStencil : ℕ →₀ ℝ :=
  Finsupp.single 2 1 - Finsupp.single 1 2 + Finsupp.single 0 1

private theorem boundedRelationFirstDifferenceStencil_sum (g : ℕ → ℝ) :
    boundedRelationFirstDifferenceStencil.sum (fun r a => a * g r) = g 1 - g 0 := by
  rw [boundedRelationFirstDifferenceStencil, Finsupp.sum_sub_index]
  · simp
  · intro a b₁ b₂
    ring

private theorem boundedRelationSecondDifferenceStencil_sum (g : ℕ → ℝ) :
    boundedRelationSecondDifferenceStencil.sum (fun r a => a * g r) =
      g 2 - 2 * g 1 + g 0 := by
  rw [boundedRelationSecondDifferenceStencil,
    Finsupp.sum_add_index (by intros; simp) (by intros; ring),
    Finsupp.sum_sub_index (by intros; ring)]
  simp

private theorem polynomialPowerFiniteDifference_boundedRelationFirstDifferenceStencil
    (β x : ℝ) :
    polynomialPowerFiniteDifference β boundedRelationFirstDifferenceStencil x =
      (x + 1) ^ β - x ^ β := by
  simpa [polynomialPowerFiniteDifference] using
    boundedRelationFirstDifferenceStencil_sum (fun r => (x + (r : ℝ)) ^ β)

private theorem polynomialPowerFiniteDifference_boundedRelationSecondDifferenceStencil
    (β x : ℝ) :
    polynomialPowerFiniteDifference β boundedRelationSecondDifferenceStencil x =
      (x + 2) ^ β - 2 * (x + 1) ^ β + x ^ β := by
  simpa [polynomialPowerFiniteDifference] using
    boundedRelationSecondDifferenceStencil_sum (fun r => (x + (r : ℝ)) ^ β)

private theorem boundedRelationFirstDifferenceStencil_moments :
    stretchedMoment boundedRelationFirstDifferenceStencil 0 = 0 ∧
    stretchedMoment boundedRelationFirstDifferenceStencil 1 = 1 := by
  constructor <;>
    rw [stretchedMoment, boundedRelationFirstDifferenceStencil_sum] <;> norm_num

private theorem boundedRelationSecondDifferenceStencil_moments :
    stretchedMoment boundedRelationSecondDifferenceStencil 0 = 0 ∧
    stretchedMoment boundedRelationSecondDifferenceStencil 1 = 0 ∧
    stretchedMoment boundedRelationSecondDifferenceStencil 2 = 2 := by
  constructor
  · rw [stretchedMoment, boundedRelationSecondDifferenceStencil_sum]
    norm_num
  constructor <;>
    rw [stretchedMoment, boundedRelationSecondDifferenceStencil_sum] <;> norm_num

private theorem polynomialPower_firstDifference_isEquivalent_of_one_lt
    {β : ℝ} (hβ : 1 < β) :
    (fun x : ℝ => (x + 1) ^ β - x ^ β) ~[atTop]
      fun x => β * x ^ (β - 1) := by
  have h := polynomialPowerFiniteDifference_isEquivalent
    (β := β) boundedRelationFirstDifferenceStencil 1
    (by
      intro k hk
      interval_cases k
      exact boundedRelationFirstDifferenceStencil_moments.1)
    (by rw [boundedRelationFirstDifferenceStencil_moments.2]; norm_num)
    (descPochhammer_eval_ne_zero_of_natCast_lt (by exact_mod_cast hβ))
  have hc : polynomialPowerDifferenceCoefficient β
      boundedRelationFirstDifferenceStencil 1 = β := by
    rw [polynomialPowerDifferenceCoefficient]
    rw [boundedRelationFirstDifferenceStencil_moments.2]
    norm_num [descPochhammer]
  rw [hc] at h
  simpa only [Nat.cast_one] using h.congr_left
    (Eventually.of_forall fun x =>
      polynomialPowerFiniteDifference_boundedRelationFirstDifferenceStencil β x)

private theorem polynomialPower_secondDifference_isEquivalent_of_one_lt
    {β : ℝ} (hβ : 1 < β) :
    (fun x : ℝ => (x + 2) ^ β - 2 * (x + 1) ^ β + x ^ β) ~[atTop]
      fun x => (β * (β - 1)) * x ^ (β - 2) := by
  have hpoch : (descPochhammer ℝ 2).eval β ≠ 0 := by
    have hβ0 : β ≠ 0 := by linarith
    have hβ1 : β - 1 ≠ 0 := by linarith
    simpa [descPochhammer] using mul_ne_zero hβ0 hβ1
  have h := polynomialPowerFiniteDifference_isEquivalent
    (β := β) boundedRelationSecondDifferenceStencil 2
    (by
      intro k hk
      interval_cases k
      · exact boundedRelationSecondDifferenceStencil_moments.1
      · exact boundedRelationSecondDifferenceStencil_moments.2.1)
    (by rw [boundedRelationSecondDifferenceStencil_moments.2.2]; norm_num)
    hpoch
  have hc : polynomialPowerDifferenceCoefficient β
      boundedRelationSecondDifferenceStencil 2 = β * (β - 1) := by
    rw [polynomialPowerDifferenceCoefficient]
    rw [boundedRelationSecondDifferenceStencil_moments.2.2]
    norm_num [descPochhammer]
  rw [hc] at h
  simpa only [Nat.cast_ofNat] using h.congr_left
    (Eventually.of_forall fun x =>
      polynomialPowerFiniteDifference_boundedRelationSecondDifferenceStencil β x)

/-- First differences of the positive shifted polynomial profile have their expected leading
asymptotic for every `β > 1`. -/
theorem boundedRelationShiftedPolynomialProfile_firstDifference_isEquivalent
    {B β : ℝ} (hβ : 1 < β) :
    (fun n : ℕ => boundedRelationFirstDifference
      (boundedRelationShiftedPolynomialProfile B β) n) ~[atTop]
      fun n : ℕ => B * (β * (((n : ℝ) + 1) ^ (β - 1))) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hbase := (polynomialPower_firstDifference_isEquivalent_of_one_lt hβ).comp_tendsto hshift
  have hmul := IsEquivalent.mul (IsEquivalent.refl (u := fun _ : ℕ => B)) hbase
  convert hmul using 1
  ext n
  simp [boundedRelationFirstDifference, boundedRelationShiftedPolynomialProfile,
    Function.comp_apply, Nat.cast_add, Pi.mul_apply]
  ring_nf

/-- Second differences of the positive shifted polynomial profile have their expected leading
asymptotic throughout the full range `β > 1`, including `1 < β < 2`. -/
theorem boundedRelationShiftedPolynomialProfile_secondDifference_isEquivalent
    {B β : ℝ} (hβ : 1 < β) :
    (fun n : ℕ => boundedRelationSecondDifference
      (boundedRelationShiftedPolynomialProfile B β) n) ~[atTop]
      fun n : ℕ => B * ((β * (β - 1)) * (((n : ℝ) + 1) ^ (β - 2))) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hbase := (polynomialPower_secondDifference_isEquivalent_of_one_lt hβ).comp_tendsto hshift
  have hmul := IsEquivalent.mul (IsEquivalent.refl (u := fun _ : ℕ => B)) hbase
  convert hmul using 1
  ext n
  simp [boundedRelationSecondDifference, boundedRelationShiftedPolynomialProfile,
    Function.comp_apply, Nat.cast_add, Pi.mul_apply]
  ring_nf

/-- Pointwise approximation errors give the exact induced first-difference error bound. -/
theorem IsPrivatePrimeSuperlinearApproximation.firstDifference_error_lt
    {g ε : ℕ → ℝ} {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation g ε b p) (n : ℕ) :
    |boundedRelationFirstDifference (fun k => (b k : ℝ)) n -
        boundedRelationFirstDifference g n| < ε (n + 1) + ε n := by
  have hclose := h.2.2.2.1
  let e : ℕ → ℝ := fun k => (b k : ℝ) - g k
  calc
    |boundedRelationFirstDifference (fun k => (b k : ℝ)) n -
        boundedRelationFirstDifference g n| = |e (n + 1) - e n| := by
          congr 1
          simp [boundedRelationFirstDifference, e]
          ring
    _ ≤ |e (n + 1)| + |e n| := by
      simpa using abs_sub_le (e (n + 1)) 0 (e n)
    _ < ε (n + 1) + ε n := add_lt_add (hclose (n + 1)) (hclose n)

/-- Pointwise approximation errors give the exact induced second-difference error bound. -/
theorem IsPrivatePrimeSuperlinearApproximation.secondDifference_error_lt
    {g ε : ℕ → ℝ} {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation g ε b p) (n : ℕ) :
    |boundedRelationSecondDifference (fun k => (b k : ℝ)) n -
        boundedRelationSecondDifference g n| <
      ε (n + 2) + 2 * ε (n + 1) + ε n := by
  have hclose := h.2.2.2.1
  let e : ℕ → ℝ := fun k => (b k : ℝ) - g k
  have hbound : |e (n + 2) - 2 * e (n + 1) + e n| ≤
      |e (n + 2)| + 2 * |e (n + 1)| + |e n| := by
    calc
      |e (n + 2) - 2 * e (n + 1) + e n| ≤
          |e (n + 2) - 2 * e (n + 1)| + |e n| := abs_add_le _ _
      _ ≤ (|e (n + 2)| + |2 * e (n + 1)|) + |e n| := by
        gcongr
        simpa using abs_sub_le (e (n + 2)) 0 (2 * e (n + 1))
      _ = |e (n + 2)| + 2 * |e (n + 1)| + |e n| := by
        rw [abs_mul]
        norm_num
  calc
    |boundedRelationSecondDifference (fun k => (b k : ℝ)) n -
        boundedRelationSecondDifference g n| =
        |e (n + 2) - 2 * e (n + 1) + e n| := by
          congr 1
          simp [boundedRelationSecondDifference, e]
          ring
    _ ≤ |e (n + 2)| + 2 * |e (n + 1)| + |e n| := hbound
    _ < ε (n + 2) + 2 * ε (n + 1) + ε n := by
      nlinarith [hclose (n + 2), hclose (n + 1), hclose n]

private theorem expNeg_isLittleO_shiftedRpow
    {c γ : ℝ} (hc : c ≠ 0) :
    (fun n : ℕ => Real.exp (-(n : ℝ))) =o[atTop]
      fun n : ℕ => c * (((n : ℝ) + 1) ^ γ) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hbase :=
    (isLittleO_exp_neg_mul_rpow_atTop one_pos γ).comp_tendsto hshift
  have hexp : (fun n : ℕ => Real.exp (-(n : ℝ))) =o[atTop]
      fun n : ℕ => (((n : ℝ) + 1) ^ γ) := by
    have hscaled := hbase.const_mul_left (Real.exp 1)
    convert hscaled using 1
    ext n
    simp only [Function.comp_apply]
    rw [← Real.exp_add]
    congr 1
    ring
  exact hexp.const_mul_right hc

private theorem expError_isLittleO_shiftedRpow
    {e : ℕ → ℝ} (he : ∀ n, |e n| < Real.exp (-(n : ℝ)))
    {c γ : ℝ} (hc : c ≠ 0) :
    e =o[atTop] fun n : ℕ => c * (((n : ℝ) + 1) ^ γ) := by
  have heO : e =O[atTop] fun n : ℕ => Real.exp (-(n : ℝ)) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact (he n).le
  exact heO.trans_isLittleO (expNeg_isLittleO_shiftedRpow hc)

private theorem firstDifferenceError_isLittleO
    {g : ℕ → ℝ} {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation g
      (fun n => Real.exp (-(n : ℝ))) b p)
    {c γ : ℝ} (hc : c ≠ 0) :
    (fun n => boundedRelationFirstDifference (fun k => (b k : ℝ)) n -
      boundedRelationFirstDifference g n) =o[atTop]
        fun n : ℕ => c * (((n : ℝ) + 1) ^ γ) := by
  let err : ℕ → ℝ := fun n =>
    boundedRelationFirstDifference (fun k => (b k : ℝ)) n -
      boundedRelationFirstDifference g n
  have herrO : err =O[atTop] fun n : ℕ => Real.exp (-(n : ℝ)) := by
    refine IsBigO.of_bound 2 (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hshiftExp : Real.exp (-((n + 1 : ℕ) : ℝ)) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    have herr := h.firstDifference_error_lt n
    dsimp [err]
    nlinarith
  exact herrO.trans_isLittleO
    (expNeg_isLittleO_shiftedRpow (c := c) (γ := γ) hc)

private theorem secondDifferenceError_isLittleO
    {g : ℕ → ℝ} {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation g
      (fun n => Real.exp (-(n : ℝ))) b p)
    {c γ : ℝ} (hc : c ≠ 0) :
    (fun n => boundedRelationSecondDifference (fun k => (b k : ℝ)) n -
      boundedRelationSecondDifference g n) =o[atTop]
        fun n : ℕ => c * (((n : ℝ) + 1) ^ γ) := by
  let err : ℕ → ℝ := fun n =>
    boundedRelationSecondDifference (fun k => (b k : ℝ)) n -
      boundedRelationSecondDifference g n
  have herrO : err =O[atTop] fun n : ℕ => Real.exp (-(n : ℝ)) := by
    refine IsBigO.of_bound 4 (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hshiftExp1 : Real.exp (-((n + 1 : ℕ) : ℝ)) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    have hshiftExp2 : Real.exp (-((n + 2 : ℕ) : ℝ)) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    have herr := h.secondDifference_error_lt n
    dsimp [err]
    nlinarith
  exact herrO.trans_isLittleO
    (expNeg_isLittleO_shiftedRpow (c := c) (γ := γ) hc)

/-- Exponentially accurate realization preserves the shifted polynomial value asymptotic. -/
theorem IsPrivatePrimeSuperlinearApproximation.isEquivalent_shiftedPolynomialProfile
    {B β : ℝ} (hB : 0 < B) {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation
      (boundedRelationShiftedPolynomialProfile B β)
      (fun n => Real.exp (-(n : ℝ))) b p) :
    (fun n => (b n : ℝ)) ~[atTop]
      boundedRelationShiftedPolynomialProfile B β := by
  have herr : (fun n => (b n : ℝ) - boundedRelationShiftedPolynomialProfile B β n)
      =o[atTop] boundedRelationShiftedPolynomialProfile B β := by
    simpa [boundedRelationShiftedPolynomialProfile] using
      (expError_isLittleO_shiftedRpow h.2.2.2.1
        (c := B) (γ := β) hB.ne')
  refine ((IsEquivalent.refl (u := boundedRelationShiftedPolynomialProfile B β)).add_isLittleO
    herr).congr_left ?_
  filter_upwards with n
  simp only [Pi.add_apply]
  ring

/-- Exponentially accurate realization preserves the shifted polynomial first-difference
asymptotic. -/
theorem IsPrivatePrimeSuperlinearApproximation.firstDifference_isEquivalent
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β)
    {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation
      (boundedRelationShiftedPolynomialProfile B β)
      (fun n => Real.exp (-(n : ℝ))) b p) :
    (fun n => boundedRelationFirstDifference (fun k => (b k : ℝ)) n) ~[atTop]
      fun n : ℕ => B * (β * (((n : ℝ) + 1) ^ (β - 1))) := by
  have hpure := boundedRelationShiftedPolynomialProfile_firstDifference_isEquivalent
    (B := B) hβ
  have hc : B * β ≠ 0 := mul_ne_zero hB.ne' (by linarith)
  have herr : (fun n => boundedRelationFirstDifference (fun k => (b k : ℝ)) n -
      boundedRelationFirstDifference (boundedRelationShiftedPolynomialProfile B β) n) =o[atTop]
        fun n : ℕ => B * (β * (((n : ℝ) + 1) ^ (β - 1))) := by
    simpa only [mul_assoc] using
      (firstDifferenceError_isLittleO h (c := B * β) (γ := β - 1) hc)
  refine (hpure.add_isLittleO herr).congr_left ?_
  filter_upwards with n
  simp only [Pi.add_apply]
  ring

/-- Exponentially accurate realization preserves the shifted polynomial second-difference
asymptotic for every `β > 1`; no convex-separation lower bound `β ≥ 2` is used. -/
theorem IsPrivatePrimeSuperlinearApproximation.secondDifference_isEquivalent
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β)
    {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation
      (boundedRelationShiftedPolynomialProfile B β)
      (fun n => Real.exp (-(n : ℝ))) b p) :
    (fun n => boundedRelationSecondDifference (fun k => (b k : ℝ)) n) ~[atTop]
      fun n : ℕ => B * ((β * (β - 1)) * (((n : ℝ) + 1) ^ (β - 2))) := by
  have hpure := boundedRelationShiftedPolynomialProfile_secondDifference_isEquivalent
    (B := B) hβ
  have hc : B * (β * (β - 1)) ≠ 0 := by
    exact mul_ne_zero hB.ne' (mul_ne_zero (by linarith) (by linarith))
  have herr : (fun n => boundedRelationSecondDifference (fun k => (b k : ℝ)) n -
      boundedRelationSecondDifference (boundedRelationShiftedPolynomialProfile B β) n) =o[atTop]
        fun n : ℕ => B * ((β * (β - 1)) * (((n : ℝ) + 1) ^ (β - 2))) := by
    simpa only [mul_assoc] using
      (secondDifferenceError_isLittleO h
        (c := B * (β * (β - 1))) (γ := β - 2) hc)
  refine (hpure.add_isLittleO herr).congr_left ?_
  filter_upwards with n
  simp only [Pi.add_apply]
  ring

/-- Positive shifted polynomial profiles have exponentially close private-prime rational
realizations whose algebraic unit-phase series are entire, full-support, and hypertranscendental. -/
theorem exists_privatePrime_shiftedPolynomial_profile_entire_fullSupport_hypertranscendental
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation
        (boundedRelationShiftedPolynomialProfile B β)
        (fun n => Real.exp (-(n : ℝ))) b p ∧
      (fun n => (b n : ℝ)) ~[atTop]
        boundedRelationShiftedPolynomialProfile B β ∧
      (fun n => boundedRelationFirstDifference (fun k => (b k : ℝ)) n) ~[atTop]
        (fun n : ℕ => B * (β * (((n : ℝ) + 1) ^ (β - 1)))) ∧
      (fun n => boundedRelationSecondDifference (fun k => (b k : ℝ)) n) ~[atTop]
        (fun n : ℕ => B * ((β * (β - 1)) * (((n : ℝ) + 1) ^ (β - 2)))) ∧
      ∀ u : ℕ → ℂ,
        (∀ n, IsAlgebraic ℚ (u n)) →
        (∀ n, ‖u n‖ = 1) →
        ContDiff ℂ (⊤ : ℕ∞)
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) ∧
          (∀ n, PowerSeries.coeff n
            (taylorPS (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u)) ≠ 0) ∧
          Hypertranscendental
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) := by
  obtain ⟨b, p, hprofile, hall⟩ :=
    exists_privatePrime_superlinear_profile_entire_fullSupport_hypertranscendental
      (boundedRelationShiftedPolynomialProfile B β)
      (fun n => Real.exp (-(n : ℝ)))
      (fun n => mul_pos hB (Real.rpow_pos_of_pos (by positivity) β))
      (fun n => Real.exp_pos _)
      (tendsto_boundedRelationShiftedPolynomialProfile_div_natCast_atTop hB hβ)
  exact ⟨b, p, hprofile,
    hprofile.isEquivalent_shiftedPolynomialProfile hB,
    hprofile.firstDifference_isEquivalent hB hβ,
    hprofile.secondDifference_isEquivalent hB hβ, hall⟩

/-- The shifted polynomial specialization has a deterministic all-positive coefficient fiber:
take every algebraic phase equal to one. -/
theorem exists_privatePrime_shiftedPolynomial_positive_entire_fullSupport_hypertranscendental
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation
        (boundedRelationShiftedPolynomialProfile B β)
        (fun n => Real.exp (-(n : ℝ))) b p ∧
      (fun n => (b n : ℝ)) ~[atTop]
        boundedRelationShiftedPolynomialProfile B β ∧
      (fun n => boundedRelationFirstDifference (fun k => (b k : ℝ)) n) ~[atTop]
        (fun n : ℕ => B * (β * (((n : ℝ) + 1) ^ (β - 1)))) ∧
      (fun n => boundedRelationSecondDifference (fun k => (b k : ℝ)) n) ~[atTop]
        (fun n : ℕ => B * ((β * (β - 1)) * (((n : ℝ) + 1) ^ (β - 2)))) ∧
      ContDiff ℂ (⊤ : ℕ∞)
          (boundedRelationExponentialFunction (fun n => (b n : ℝ)) (fun _ => 1)) ∧
        (∀ n, PowerSeries.coeff n
          (taylorPS (boundedRelationExponentialFunction
            (fun n => (b n : ℝ)) (fun _ => 1))) ≠ 0) ∧
        Hypertranscendental
          (boundedRelationExponentialFunction (fun n => (b n : ℝ)) (fun _ => 1)) := by
  obtain ⟨b, p, hprofile, hvalue, hfirst, hsecond, hall⟩ :=
    exists_privatePrime_shiftedPolynomial_profile_entire_fullSupport_hypertranscendental hB hβ
  refine ⟨b, p, hprofile, hvalue, hfirst, hsecond, ?_⟩
  exact hall (fun _ => 1) (by intro n; exact isAlgebraic_one) (by intro n; simp)

end

end GaloisForLFunctions
