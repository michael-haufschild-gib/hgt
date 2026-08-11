import GaloisForLFunctions.RHTower.GaussHodgeWeilArithmeticDeviationGap
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# The total deviation mass and the all-heights arithmetic ceiling

Two closures of the deviation-moment programme.

**The total deviation mass.**  Normalizing the squared deviation of each divisor copy by its
squared spectral norm produces a series that converges *unconditionally* — the genus-one
Hadamard convergence `Σ 1/‖alpha_q‖² < ∞` dominates it through the strip bound.  The resulting
single real number

`xiTotalDeviationMass = Σ' (Im alpha_q)² / ‖alpha_q‖²`

is nonnegative, at most a quarter of the Hadamard sum, and **RH is exactly the statement that
it equals zero** (`riemannHypothesis_iff_totalDeviationMass_eq_zero`).

**The all-heights arithmetic ceiling.**  The zero-free gaps assemble into one weight profile
`xiArithmeticDeviationCeiling`, strictly below `1/4` at every divisor copy — uniformly at
height ≤ 3, by the de la Vallée-Poussin margin above — and the deviation-moment lower bound
holds against this profile for every test with convergent divided-difference energy
(`exists_arithmetic_weighted_moment_bound`), with no support restriction.  The distance between
this ceiling and `0` is the exact remaining content of RH.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The total deviation mass -/

/-- The normalized squared deviation of one divisor copy. -/
def xiDeviationMassDensity (q : XiZeroCopy) : ℝ :=
  (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q‖ ^ 2

/-- The total normalized deviation mass of the multiplicity-exact Xi divisor. -/
def xiTotalDeviationMass : ℝ :=
  ∑' q : XiZeroCopy, xiDeviationMassDensity q

theorem xiDeviationMassDensity_nonneg (q : XiZeroCopy) :
    0 ≤ xiDeviationMassDensity q := by
  rw [xiDeviationMassDensity]
  positivity

/-- The strip dominates each density by a quarter of the Hadamard density. -/
theorem xiDeviationMassDensity_le (q : XiZeroCopy) :
    xiDeviationMassDensity q ≤ (1 / 4) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  have him : (xiSpectralPoint q).im ^ 2 ≤ 1 / 4 := by
    have h := abs_xiSpectralPoint_im_lt_half q
    nlinarith [abs_nonneg ((xiSpectralPoint q).im), sq_abs ((xiSpectralPoint q).im)]
  have hrw : (1 / 4 : ℝ) * (1 / ‖xiSpectralPoint q‖ ^ 2) =
      (1 / 4) / ‖xiSpectralPoint q‖ ^ 2 := by ring
  rw [xiDeviationMassDensity, hrw, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right him (inv_nonneg.mpr (sq_nonneg _))

/-- **Unconditional convergence of the total deviation mass**, by genus-one Hadamard
convergence and the strip. -/
theorem xiDeviationMassDensity_summable :
    Summable xiDeviationMassDensity :=
  Summable.of_nonneg_of_le xiDeviationMassDensity_nonneg xiDeviationMassDensity_le
    (xiSpectralPoint_inv_sq_summable.mul_left (1 / 4))

/-- The total deviation mass is at most a quarter of the Hadamard sum. -/
theorem xiTotalDeviationMass_le_quarter :
    xiTotalDeviationMass ≤
      (1 / 4) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  rw [xiTotalDeviationMass, ← tsum_mul_left]
  exact xiDeviationMassDensity_summable.tsum_le_tsum xiDeviationMassDensity_le
    (xiSpectralPoint_inv_sq_summable.mul_left (1 / 4))

theorem xiTotalDeviationMass_nonneg : 0 ≤ xiTotalDeviationMass :=
  tsum_nonneg xiDeviationMassDensity_nonneg

/-- **RH ⟺ the total deviation mass vanishes.**  The Riemann hypothesis is the vanishing of
one unconditionally convergent nonnegative series over the divisor. -/
theorem riemannHypothesis_iff_totalDeviationMass_eq_zero :
    RiemannHypothesis ↔ xiTotalDeviationMass = 0 := by
  constructor
  · intro hRH
    rw [xiTotalDeviationMass]
    have hzero : ∀ q : XiZeroCopy, xiDeviationMassDensity q = 0 := by
      intro q
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      rw [xiDeviationMassDensity, ht]
      simp
    rw [tsum_congr hzero, tsum_zero]
  · intro hmass
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hle : xiDeviationMassDensity q ≤ xiTotalDeviationMass :=
      xiDeviationMassDensity_summable.le_tsum q
        fun r _ => xiDeviationMassDensity_nonneg r
    have hdens : xiDeviationMassDensity q = 0 :=
      le_antisymm (hmass ▸ hle) (xiDeviationMassDensity_nonneg q)
    have him : (xiSpectralPoint q).im = 0 := by
      rw [xiDeviationMassDensity] at hdens
      by_cases hnorm : ‖xiSpectralPoint q‖ ^ 2 = 0
      · have : xiSpectralPoint q = 0 :=
          norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hnorm)
        rw [this]
        simp
      · have hsq : (xiSpectralPoint q).im ^ 2 = 0 :=
          (div_eq_zero_iff.mp hdens).resolve_right hnorm
        exact pow_eq_zero_iff two_ne_zero |>.mp hsq
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, him]

/-! ## The all-heights arithmetic ceiling -/

/-- The arithmetic ceiling on squared deviations: a uniform gap below height `3`, the de la
Vallée-Poussin margin above. -/
def xiArithmeticDeviationCeiling (δ A : ℝ) (q : XiZeroCopy) : ℝ :=
  if |(xiSpectralPoint q).re| ≤ 3 then 1 / 4 - δ
  else 1 / 4 - A / Real.log |(xiSpectralPoint q).re| ^ 9 / 2

/-- **The all-heights arithmetic weight profile.**  There are arithmetic constants `δ, A` for
which the ceiling bounds every squared deviation, sits strictly below `1/4` at every divisor
copy, and the deviation-moment lower bound holds against it for every square-summable test with
convergent divided-difference energy — no support restriction. -/
theorem exists_arithmetic_weighted_moment_bound :
    ∃ δ A : ℝ, 0 < δ ∧ A ∈ Set.Ioc 0 (1 / 2) ∧
      (∀ q : XiZeroCopy,
        (xiSpectralPoint q).im ^ 2 ≤ xiArithmeticDeviationCeiling δ A q) ∧
      (∀ q : XiZeroCopy, xiArithmeticDeviationCeiling δ A q < 1 / 4) ∧
      ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        Summable (fun q : XiZeroCopy =>
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) →
        (∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2) -
            ∑' q : XiZeroCopy, xiArithmeticDeviationCeiling δ A q *
              ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 ≤
          (xiWeilPolarization F F).re := by
  obtain ⟨δ₀, hδ₀, hlow⟩ := exists_xiSpectralPoint_deviation_gap_low
  obtain ⟨A, hA, hhigh⟩ := exists_xiSpectralPoint_deviation_gap_high
  set δ : ℝ := min δ₀ (1 / 8) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδle : δ ≤ 1 / 8 := min_le_right _ _
  have hlog : ∀ q : XiZeroCopy, 3 < |(xiSpectralPoint q).re| →
      1 < Real.log |(xiSpectralPoint q).re| := by
    intro q hq
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hpoint : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ xiArithmeticDeviationCeiling δ A q := by
    intro q
    rw [xiArithmeticDeviationCeiling]
    by_cases hq : |(xiSpectralPoint q).re| ≤ 3
    · rw [if_pos hq]
      have := hlow q hq
      have hδ₀ge : δ ≤ δ₀ := min_le_left _ _
      linarith
    · rw [if_neg hq]
      exact hhigh q (not_le.mp hq)
  have hlt : ∀ q : XiZeroCopy, xiArithmeticDeviationCeiling δ A q < 1 / 4 := by
    intro q
    rw [xiArithmeticDeviationCeiling]
    by_cases hq : |(xiSpectralPoint q).re| ≤ 3
    · rw [if_pos hq]
      linarith
    · rw [if_neg hq]
      have hl := hlog q (not_le.mp hq)
      have : 0 < A / Real.log |(xiSpectralPoint q).re| ^ 9 / 2 := by
        apply div_pos (div_pos hA.1 (pow_pos (by linarith) 9))
        norm_num
      linarith
  have hnonneg : ∀ q : XiZeroCopy, 0 ≤ xiArithmeticDeviationCeiling δ A q := by
    intro q
    rw [xiArithmeticDeviationCeiling]
    by_cases hq : |(xiSpectralPoint q).re| ≤ 3
    · rw [if_pos hq]
      linarith
    · rw [if_neg hq]
      have hl := hlog q (not_le.mp hq)
      have hpow : 1 ≤ Real.log |(xiSpectralPoint q).re| ^ 9 := one_le_pow₀ hl.le
      have hεle : A / Real.log |(xiSpectralPoint q).re| ^ 9 ≤ 1 / 2 :=
        le_trans (div_le_self hA.1.le hpow) hA.2
      linarith
  refine ⟨δ, A, hδpos, hA, hpoint, hlt, ?_⟩
  intro F hF hD
  rw [xiWeilPolarization_re_eq_deviation_moment hF]
  have hwsum : Summable (fun q : XiZeroCopy => xiArithmeticDeviationCeiling δ A q *
      ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le
      (fun q => mul_nonneg (hnonneg q) (sq_nonneg _)) (fun q => ?_) (hD.mul_left (1 / 4))
    exact mul_le_mul_of_nonneg_right (le_of_lt (hlt q)) (sq_nonneg _)
  have hmoment : (∑' q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) ≤
      ∑' q : XiZeroCopy, xiArithmeticDeviationCeiling δ A q *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 :=
    (deviation_dslope_energy_summable hF).tsum_le_tsum
      (fun q => mul_le_mul_of_nonneg_right (hpoint q) (sq_nonneg _)) hwsum
  linarith

/-- The arithmetic ceiling also caps the total deviation mass below its strip bound: the mass
is dominated by the ceiling-weighted Hadamard sum. -/
theorem xiTotalDeviationMass_le_arithmetic_ceiling :
    ∃ δ A : ℝ, 0 < δ ∧ A ∈ Set.Ioc 0 (1 / 2) ∧
      (∀ q : XiZeroCopy, xiArithmeticDeviationCeiling δ A q < 1 / 4) ∧
      xiTotalDeviationMass ≤
        ∑' q : XiZeroCopy,
          xiArithmeticDeviationCeiling δ A q * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  obtain ⟨δ, A, hδ, hA, hpoint, hlt, -⟩ := exists_arithmetic_weighted_moment_bound
  have hnonneg : ∀ q : XiZeroCopy, 0 ≤ xiArithmeticDeviationCeiling δ A q :=
    fun q => le_trans (sq_nonneg _) (hpoint q)
  have hwsum : Summable (fun q : XiZeroCopy =>
      xiArithmeticDeviationCeiling δ A q * (1 / ‖xiSpectralPoint q‖ ^ 2)) := by
    refine Summable.of_nonneg_of_le
      (fun q => mul_nonneg (hnonneg q) (by positivity)) (fun q => ?_)
      (xiSpectralPoint_inv_sq_summable.mul_left (1 / 4))
    exact mul_le_mul_of_nonneg_right (le_of_lt (hlt q)) (by positivity)
  refine ⟨δ, A, hδ, hA, hlt, ?_⟩
  rw [xiTotalDeviationMass]
  refine xiDeviationMassDensity_summable.tsum_le_tsum (fun q => ?_) hwsum
  rw [xiDeviationMassDensity, div_eq_mul_inv, one_div]
  exact mul_le_mul_of_nonneg_right (hpoint q) (inv_nonneg.mpr (sq_nonneg _))

end

end RHTower
