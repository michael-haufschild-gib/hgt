import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorShortRange
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSelfConvCrossHarmonicBound
import GaloisForLFunctions.RHTower.XiMassPrefixQuadratureDefect
import GaloisForLFunctions.RHTower.XiMassJetWindowDamped

/-!
# Two-aperture reciprocal Levinson landing

A single reciprocal-tuned Levinson detector cannot land coefficient-faithfully on the prime
source: every prime inside its aperture is erased. The detector *family* contains the source.
For a prime beyond two distinct apertures, their coefficient difference is

`(1 / log M₁ - 1 / log M₂) * Lambda(p) / sqrt(p)`.

Thus a reciprocal-log secant recovers every cofinite true-prime coefficient exactly *after the
true-prime projection is supplied*. This module sums that projected identity on the moving Xi-mass
cone, bounds the complementary fixed prime packet, and proves that the resulting projected
detector-secant line bound is equivalent to RH. `XiMassLevinsonRoughTailHorizon` proves that no
fixed finite linear aperture family can itself create the omitted true-prime projection.
-/

open Complex Finset
open scoped ArithmeticFunction

namespace RHTower

noncomputable section

namespace Sieve

theorem barbanVehovCoeff_prime_of_aperture_lt
    {M p : ℕ} (hM : 1 ≤ M) (hp : p.Prime) (hMp : M < p) :
    barbanVehovCoeff M p = Real.log M := by
  rw [barbanVehovCoeff, hp.divisors]
  simp [barbanVehovWeight, hp.ne_one.symm, hM, not_le.mpr hMp]

theorem barbanVehovLogMomentCoeff_prime_of_aperture_lt
    {M p : ℕ} (hM : 1 ≤ M) (hp : p.Prime) (hMp : M < p) :
    barbanVehovLogMomentCoeff M p = 0 := by
  rw [barbanVehovLogMomentCoeff, hp.divisors]
  simp [barbanVehovWeight, hp.ne_one.symm, hM, not_le.mpr hMp]

/-- **Single-aperture no-go.** Reciprocal tuning erases every prime in the aperture. -/
theorem levinsonReciprocalMollifiedCriticalDetectorCoeff_prime_eq_zero
    {M p : ℕ} (hM : 1 < M) (hp : p.Prime) (hpM : p ≤ M) :
    levinsonLinearMollifiedCriticalDetectorCoeff (1 / Real.log M) M p = 0 := by
  rw [levinsonLinearMollifiedCriticalDetectorCoeff_eq_vonMangoldt
    hp.one_lt hpM, vonMangoldtSelfConv_eq_zero_of_prime hp]
  have hlog : Real.log (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hM))
  norm_cast
  field_simp [hlog]
  ring

/-- Outside one aperture, reciprocal-tuned coefficient is affine in `1 / log M`. -/
theorem levinsonReciprocalMollifiedCriticalDetectorCoeff_prime_of_aperture_lt
    {M p : ℕ} (hM : 1 < M) (hp : p.Prime) (hMp : M < p) :
    levinsonLinearMollifiedCriticalDetectorCoeff (1 / Real.log M) M p =
      ((((1 - Real.log p / Real.log M) / Real.sqrt p : ℝ)) : ℂ) := by
  rw [levinsonLinearMollifiedCriticalDetectorCoeff_eq hp.pos,
    barbanVehovCoeff_prime_of_aperture_lt hM.le hp hMp,
    barbanVehovLogMomentCoeff_prime_of_aperture_lt hM.le hp hMp]
  have hlog : Real.log (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hM))
  norm_cast
  field_simp [hlog]
  ring

/-- Reciprocal-log slope between two mollifier apertures. -/
def levinsonReciprocalApertureSlope (M₁ M₂ : ℕ) : ℝ :=
  1 / Real.log M₁ - 1 / Real.log M₂

theorem levinsonReciprocalApertureSlope_pos
    {M₁ M₂ : ℕ} (hM₁ : 1 < M₁) (hM₁M₂ : M₁ < M₂) :
    0 < levinsonReciprocalApertureSlope M₁ M₂ := by
  have hlog₁ : 0 < Real.log (M₁ : ℝ) :=
    Real.log_pos (by exact_mod_cast hM₁)
  have hM₁0 : (0 : ℝ) < (M₁ : ℝ) := by
    exact_mod_cast (show 0 < M₁ by omega)
  have hM₂0 : (0 : ℝ) < (M₂ : ℝ) := by
    exact_mod_cast (show 0 < M₂ by omega)
  have hMlt : (M₁ : ℝ) < (M₂ : ℝ) := by exact_mod_cast hM₁M₂
  have hloglt : Real.log (M₁ : ℝ) < Real.log (M₂ : ℝ) := by
    exact Real.strictMonoOn_log hM₁0 hM₂0 hMlt
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hlog₁ hloglt)

theorem levinsonReciprocalApertureSlope_ne_zero
    {M₁ M₂ : ℕ} (hM₁ : 1 < M₁) (hM₁M₂ : M₁ < M₂) :
    levinsonReciprocalApertureSlope M₁ M₂ ≠ 0 :=
  ne_of_gt (levinsonReciprocalApertureSlope_pos hM₁ hM₁M₂)

/-- **Prime-source secant.** Two exterior reciprocal-tuned detector coefficients recover the
literal von-Mangoldt half-density coefficient. -/
theorem levinsonReciprocalMollifiedCriticalDetectorCoeff_prime_secant
    {M₁ M₂ p : ℕ} (hM₁ : 1 < M₁) (hM₁M₂ : M₁ < M₂)
    (hp : p.Prime) (hM₂p : M₂ < p) :
    levinsonLinearMollifiedCriticalDetectorCoeff (1 / Real.log M₂) M₂ p -
        levinsonLinearMollifiedCriticalDetectorCoeff (1 / Real.log M₁) M₁ p =
      (((levinsonReciprocalApertureSlope M₁ M₂ *
          (ArithmeticFunction.vonMangoldt p / Real.sqrt p) : ℝ) : ℂ)) := by
  rw [levinsonReciprocalMollifiedCriticalDetectorCoeff_prime_of_aperture_lt
      (lt_trans hM₁ hM₁M₂) hp hM₂p,
    levinsonReciprocalMollifiedCriticalDetectorCoeff_prime_of_aperture_lt
      hM₁ hp (lt_trans hM₁M₂ hM₂p),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [levinsonReciprocalApertureSlope]
  norm_cast
  ring

end Sieve

theorem exp_neg_log_nat_div_two_eq_inv_sqrt {n : ℕ} (hn : 0 < n) :
    Real.exp (-Real.log (n : ℝ) / 2) = 1 / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR]
  rw [one_div, ← Real.exp_neg]
  congr 1
  ring

/-- Prime indices in the moving critical cone. -/
def xiMassLevinsonPrimeConeIndices (d u : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1)).filter
    (fun k => Nat.Prime (k + 2))

theorem xiMassCriticalTruePrimeCone_eq_levinsonIndexSum
    (a sigma d u : ℝ) :
    xiMassCriticalTruePrimeCone a sigma d u =
      ∑ k ∈ xiMassLevinsonPrimeConeIndices d u,
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
  exact xiMassCriticalTruePrimeCone_eq_finsetSum a sigma d u

/-- One Xi-mass Fourier atom whose arithmetic amplitude is the literal difference of two
reciprocal-tuned Levinson detector coefficients. -/
def xiMassLevinsonReciprocalPrimeSecantAtom
    (a : ℝ) (tau : ℂ) (M₁ M₂ p : ℕ) : ℂ :=
  (Sieve.levinsonLinearMollifiedCriticalDetectorCoeff
      (1 / Real.log M₂) M₂ p -
    Sieve.levinsonLinearMollifiedCriticalDetectorCoeff
      (1 / Real.log M₁) M₁ p) *
    stripFourier (xiMassAnalyticTest a tau) (Real.log p : ℂ)

theorem xiMassLevinsonReciprocalPrimeSecantAtom_eq_slope_mul
    {a : ℝ} {tau : ℂ} {M₁ M₂ p : ℕ}
    (hM₁ : 1 < M₁) (hM₁M₂ : M₁ < M₂) (hp : p.Prime) (hM₂p : M₂ < p) :
    xiMassLevinsonReciprocalPrimeSecantAtom a tau M₁ M₂ p =
      (Sieve.levinsonReciprocalApertureSlope M₁ M₂ : ℂ) *
        xiMassCenteredPrimeAtom a tau p := by
  rw [xiMassLevinsonReciprocalPrimeSecantAtom,
    Sieve.levinsonReciprocalMollifiedCriticalDetectorCoeff_prime_secant
      hM₁ hM₁M₂ hp hM₂p,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    xiMassCenteredPrimeAtom, lseriesTerm_vonMangoldt_prime_eq hp,
    exp_neg_log_nat_div_two_eq_inv_sqrt hp.pos]
  push_cast
  ring

/-- Moving cofinite prime cone carried by the two-aperture detector secant. -/
def xiMassLevinsonReciprocalPrimeSecantCone
    (a sigma d u : ℝ) (M₁ M₂ : ℕ) : ℂ :=
  ∑ k ∈ (xiMassLevinsonPrimeConeIndices d u).filter
      (fun k => M₂ < k + 2),
    xiMassLevinsonReciprocalPrimeSecantAtom
      a ((sigma : ℂ) + u * I) M₁ M₂ (k + 2)

/-- The complementary finite prime packet below the larger aperture. -/
def xiMassLevinsonPrimePrefixCone
    (a sigma d u : ℝ) (M₂ : ℕ) : ℂ :=
  ∑ k ∈ (xiMassLevinsonPrimeConeIndices d u).filter
      (fun k => k + 2 ≤ M₂),
    xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)

/-- **Exact coefficient-faithful landing.** Detector secant equals its nonzero slope times the
true-prime cone after deleting one finite prime prefix. -/
theorem xiMassLevinsonReciprocalPrimeSecantCone_eq_slope_mul_sub_prefix
    {a sigma d u : ℝ} {M₁ M₂ : ℕ}
    (hM₁ : 1 < M₁) (hM₁M₂ : M₁ < M₂) :
    xiMassLevinsonReciprocalPrimeSecantCone a sigma d u M₁ M₂ =
      (Sieve.levinsonReciprocalApertureSlope M₁ M₂ : ℂ) *
        (xiMassCriticalTruePrimeCone a sigma d u -
          xiMassLevinsonPrimePrefixCone a sigma d u M₂) := by
  classical
  rw [xiMassLevinsonReciprocalPrimeSecantCone]
  have hpoint : ∀ k ∈ (xiMassLevinsonPrimeConeIndices d u).filter
      (fun k => M₂ < k + 2),
      xiMassLevinsonReciprocalPrimeSecantAtom
          a ((sigma : ℂ) + u * I) M₁ M₂ (k + 2) =
        (Sieve.levinsonReciprocalApertureSlope M₁ M₂ : ℂ) *
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
    intro k hk
    have hp : Nat.Prime (k + 2) :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    have hM₂p : M₂ < k + 2 := (Finset.mem_filter.mp hk).2
    exact xiMassLevinsonReciprocalPrimeSecantAtom_eq_slope_mul
      hM₁ hM₁M₂ hp hM₂p
  rw [Finset.sum_congr rfl hpoint, ← Finset.mul_sum]
  rw [xiMassCriticalTruePrimeCone_eq_levinsonIndexSum,
    xiMassLevinsonPrimePrefixCone]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (xiMassLevinsonPrimeConeIndices d u) (fun k => M₂ < k + 2)
    (fun k => xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2))
  simp only [not_lt] at hsplit
  rw [← hsplit]
  ring

/-- Every moving prefix below one fixed detector aperture is uniformly bounded in vertical time. -/
theorem norm_xiMassLevinsonPrimePrefixCone_le
    {a sigma d u : ℝ} {M₂ : ℕ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hM₂ : 1 < M₂) :
    ‖xiMassLevinsonPrimePrefixCone a sigma d u M₂‖ ≤
      (M₂ : ℝ) * Real.log M₂ * xiMassVerticalBound sigma := by
  classical
  rw [xiMassLevinsonPrimePrefixCone]
  let s := (xiMassLevinsonPrimeConeIndices d u).filter
      (fun k => k + 2 ≤ M₂)
  have hsub : s ⊆ Finset.range M₂ := by
    intro k hk
    rw [Finset.mem_range]
    have hkM : k + 2 ≤ M₂ := (Finset.mem_filter.mp hk).2
    omega
  have hcard : s.card ≤ M₂ := by
    simpa using Finset.card_le_card hsub
  have hV : 0 ≤ xiMassVerticalBound sigma :=
    xiMassVerticalBound_nonneg sigma
  calc
    ‖∑ k ∈ s,
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)‖
        ≤ ∑ k ∈ s,
            ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ s, Real.log M₂ * xiMassVerticalBound sigma := by
      apply Finset.sum_le_sum
      intro k hk
      have hkbase : k ∈ xiMassLevinsonPrimeConeIndices d u :=
        (Finset.mem_filter.mp hk).1
      have hp : Nat.Prime (k + 2) :=
        (Finset.mem_filter.mp hkbase).2
      have hpM : k + 2 ≤ M₂ := (Finset.mem_filter.mp hk).2
      have hlog : Real.log ((k + 2 : ℕ) : ℝ) ≤ Real.log (M₂ : ℝ) := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hpM)
      exact (norm_xiMassCenteredPrimeAtom_le_verticalBound ha hsigma hp).trans
        (mul_le_mul_of_nonneg_right hlog hV)
    _ = (s.card : ℝ) * (Real.log M₂ * xiMassVerticalBound sigma) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M₂ : ℝ) * (Real.log M₂ * xiMassVerticalBound sigma) := by
      refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ?_
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hM₂.le)) hV
    _ = (M₂ : ℝ) * Real.log M₂ * xiMassVerticalBound sigma := by
      rw [mul_assoc]

/-- Uniform vertical bound on the actual two-aperture detector-secant cone. -/
def XiMassLevinsonReciprocalPrimeSecantConeLineBound
    (a sigma d : ℝ) (M₁ M₂ : ℕ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassLevinsonReciprocalPrimeSecantCone a sigma d u M₁ M₂‖ ≤ C

/-- Removing the fixed prime prefix and multiplying by the nonzero aperture slope preserves
exactly the RH-bearing line-bound problem. -/
theorem xiMassLevinsonReciprocalPrimeSecantConeLineBound_iff_truePrime
    {a sigma d : ℝ} {M₁ M₂ : ℕ}
    (ha : 0 < a) (hsigma : 0 < sigma)
    (hM₁ : 1 < M₁) (hM₁M₂ : M₁ < M₂) :
    XiMassLevinsonReciprocalPrimeSecantConeLineBound a sigma d M₁ M₂ ↔
      XiMassCriticalTruePrimeConeLineBound a sigma d := by
  let B : ℝ := (M₂ : ℝ) * Real.log M₂ * xiMassVerticalBound sigma
  let z : ℂ := (Sieve.levinsonReciprocalApertureSlope M₁ M₂ : ℂ)
  have hz : z ≠ 0 := by
    dsimp only [z]
    exact_mod_cast Sieve.levinsonReciprocalApertureSlope_ne_zero hM₁ hM₁M₂
  have hM₂ : 1 < M₂ := lt_trans hM₁ hM₁M₂
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖z⁻¹‖ * C + B, fun u hu => ?_⟩
    have hprefix :
        ‖xiMassLevinsonPrimePrefixCone a sigma d u M₂‖ ≤ B := by
      simpa only [B] using
        norm_xiMassLevinsonPrimePrefixCone_le ha hsigma hM₂
    have hlanding :=
      xiMassLevinsonReciprocalPrimeSecantCone_eq_slope_mul_sub_prefix
        (a := a) (sigma := sigma) (d := d) (u := u)
        hM₁ hM₁M₂
    have hrecover :
        xiMassCriticalTruePrimeCone a sigma d u =
          z⁻¹ * xiMassLevinsonReciprocalPrimeSecantCone a sigma d u M₁ M₂ +
            xiMassLevinsonPrimePrefixCone a sigma d u M₂ := by
      rw [hlanding]
      change xiMassCriticalTruePrimeCone a sigma d u =
        z⁻¹ * (z *
          (xiMassCriticalTruePrimeCone a sigma d u -
            xiMassLevinsonPrimePrefixCone a sigma d u M₂)) +
          xiMassLevinsonPrimePrefixCone a sigma d u M₂
      rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
      ring
    rw [hrecover]
    calc
      ‖z⁻¹ * xiMassLevinsonReciprocalPrimeSecantCone a sigma d u M₁ M₂ +
          xiMassLevinsonPrimePrefixCone a sigma d u M₂‖
          ≤ ‖z⁻¹ * xiMassLevinsonReciprocalPrimeSecantCone a sigma d u M₁ M₂‖ +
              ‖xiMassLevinsonPrimePrefixCone a sigma d u M₂‖ :=
        norm_add_le _ _
      _ = ‖z⁻¹‖ *
            ‖xiMassLevinsonReciprocalPrimeSecantCone a sigma d u M₁ M₂‖ +
              ‖xiMassLevinsonPrimePrefixCone a sigma d u M₂‖ := by
        rw [norm_mul]
      _ ≤ ‖z⁻¹‖ * C + B :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg _))
          hprefix
  · rintro ⟨C, hC⟩
    refine ⟨‖z‖ * (C + B), fun u hu => ?_⟩
    have hprefix :
        ‖xiMassLevinsonPrimePrefixCone a sigma d u M₂‖ ≤ B := by
      simpa only [B] using
        norm_xiMassLevinsonPrimePrefixCone_le ha hsigma hM₂
    rw [xiMassLevinsonReciprocalPrimeSecantCone_eq_slope_mul_sub_prefix
      (a := a) (sigma := sigma) (d := d) (u := u) hM₁ hM₁M₂]
    change ‖z *
      (xiMassCriticalTruePrimeCone a sigma d u -
        xiMassLevinsonPrimePrefixCone a sigma d u M₂)‖ ≤ _
    rw [norm_mul]
    calc
      ‖z‖ * ‖xiMassCriticalTruePrimeCone a sigma d u -
          xiMassLevinsonPrimePrefixCone a sigma d u M₂‖
          ≤ ‖z‖ * (‖xiMassCriticalTruePrimeCone a sigma d u‖ +
            ‖xiMassLevinsonPrimePrefixCone a sigma d u M₂‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖z‖ * (C + B) :=
        mul_le_mul_of_nonneg_left (add_le_add (hC u hu) hprefix)
          (norm_nonneg _)

/-- **T1 prime-projected landing capstone.** For every pair of distinct legal fixed apertures, RH
is equivalent to uniform boundedness of the reciprocal-detector secant after restricting it to the
moving true-prime Xi-mass cone. -/
theorem riemannHypothesis_iff_xiMassLevinsonReciprocalPrimeSecantConeLineBound
    {a c sigma d : ℝ} {M₁ M₂ : ℕ}
    (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a)
    (hM₁ : 1 < M₁) (hM₁M₂ : M₁ < M₂) :
    RiemannHypothesis ↔
      XiMassLevinsonReciprocalPrimeSecantConeLineBound a sigma d M₁ M₂ := by
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hdhalf hda)
  exact (riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassLevinsonReciprocalPrimeSecantConeLineBound_iff_truePrime
        ha hsigma hM₁ hM₁M₂).symm

end

end RHTower
