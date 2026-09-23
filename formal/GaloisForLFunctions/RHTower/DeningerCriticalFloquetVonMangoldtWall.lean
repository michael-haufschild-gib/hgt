import GaloisForLFunctions.RHTower.DeningerMertensAdiabaticCorner
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogTarget
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogMellin
import GaloisForLFunctions.RHTower.DeningerMeyerXiSpectralInclusion
import GaloisForLFunctions.RHTower.DeningerMeyerDilationFlow
import GaloisForLFunctions.RHTower.DeningerArithmeticTimeDistribution
import GaloisForLFunctions.RHTower.SoninSemilocalAllEvenJacobiResidue
import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Critical Floquet renormalization and the von Mangoldt wall

This file formalizes the source-side classification proved on the Route-L paper card
`deninger-critical-floquet-von-mangoldt-renormalization-wall`.

The source is the literal all-weight Meyer logarithmic target.  Prime-circle periodization is
unfolded to the full autocorrelation lattice, the centered logarithmic prime sum is reindexed as
the von Mangoldt prime-power current, and one compact two-bump source produces both signs for
every nonnegative diagonal weighting which sees the prime two.  The negative source is the
matching half-density Euler coboundary.

No Riemann-hypothesis premise, Xi-divisor hypothesis, positivity assumption, numerical
computation, or new axiom occurs.
-/

open Bornology Complex Filter Function MeasureTheory Set Topology
open scoped Classical ContDiff Interval

namespace RHTower

noncomputable section

/-! ## Relative Floquet monodromy -/

/-- Monodromy at exponent `1/2 + u`, divided by half-density monodromy. -/
def deningerFloquetRelativeMonodromy (p : Nat.Primes) (u : ℝ) : ℝ :=
  deningerSourceCurvedPoissonCoefficient p u 1

/-- Relative Floquet monodromy is the exact arithmetic adiabatic kernel. -/
theorem deningerFloquetRelativeMonodromy_eq_adiabatic
    (p : Nat.Primes) (u : ℝ) :
    deningerFloquetRelativeMonodromy p u =
      Real.exp (-u / deningerPrimeAdiabaticParameter p) := by
  simpa [deningerFloquetRelativeMonodromy] using
    deningerSourceCurvedPoissonCoefficient_eq_adiabatic p u 1

/-- Relative Floquet monodromy is exactly `p^{-u}` in exponential coordinates. -/
theorem deningerFloquetRelativeMonodromy_eq_exp_neg_log
    (p : Nat.Primes) (u : ℝ) :
    deningerFloquetRelativeMonodromy p u =
      Real.exp (-u * Real.log (p : ℕ)) := by
  simp [deningerFloquetRelativeMonodromy,
    deningerSourceCurvedPoissonCoefficient]

/-- Reflection of the exponent about `1/2` is inversion of relative monodromy. -/
theorem deningerFloquetRelativeMonodromy_neg
    (p : Nat.Primes) (u : ℝ) :
    deningerFloquetRelativeMonodromy p (-u) =
      (deningerFloquetRelativeMonodromy p u)⁻¹ := by
  rw [deningerFloquetRelativeMonodromy_eq_exp_neg_log,
    deningerFloquetRelativeMonodromy_eq_exp_neg_log]
  rw [show -(-u) * Real.log (p : ℕ) = -(-u * Real.log (p : ℕ)) by ring,
    Real.exp_neg]

/-- Complexified relative monodromy, used for its complete boundary jet. -/
def deningerFloquetRelativeMonodromyComplex
    (p : Nat.Primes) (u : ℂ) : ℂ :=
  deningerSourceCurvedPoissonCoefficientComplex p 1 u

/-- Every normal derivative is the corresponding signed prime-log clock power. -/
theorem iteratedDeriv_deningerFloquetRelativeMonodromyComplex_zero
    (p : Nat.Primes) (k : ℕ) :
    iteratedDeriv k (deningerFloquetRelativeMonodromyComplex p) 0 =
      (-(Real.log (p : ℕ) : ℂ)) ^ k := by
  change
    iteratedDeriv k
        (deningerSourceCurvedPoissonCoefficientComplex p 1) 0 = _
  simpa using
    iteratedDeriv_deningerSourceCurvedPoissonCoefficientComplex_zero p 1 k

/-! ## Exponential envelope of the literal Meyer source -/

/-- Every all-weight Meyer source has a global two-sided exponential envelope. -/
theorem deningerMeyerStrongLog_norm_le_exp_neg_abs
    (u : DeningerMeyerStrongLogTarget) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖(u : ℝ → ℂ) t‖ ≤ C * Real.exp (-A * |t|) := by
  obtain ⟨Cplus, hCplus⟩ :=
    (u.property.weighted_iteratedDeriv_isBounded 0 A).exists_norm_le
  obtain ⟨Cminus, hCminus⟩ :=
    (u.property.weighted_iteratedDeriv_isBounded 0 (-A)).exists_norm_le
  let C := max Cplus Cminus
  have hCplus_nonneg : 0 ≤ Cplus := by
    have h := hCplus
      (((Real.exp 0 ^ A : ℝ) : ℂ) * iteratedDeriv 0 (u : ℝ → ℂ) 0)
      (Set.mem_range_self 0)
    exact (norm_nonneg _).trans h
  have hCminus_nonneg : 0 ≤ Cminus := by
    have h := hCminus
      (((Real.exp 0 ^ (-A) : ℝ) : ℂ) * iteratedDeriv 0 (u : ℝ → ℂ) 0)
      (Set.mem_range_self 0)
    exact (norm_nonneg _).trans h
  refine ⟨C, hCplus_nonneg.trans (le_max_left _ _), ?_⟩
  intro t
  by_cases ht : 0 ≤ t
  · have hraw := hCplus
      (((Real.exp t ^ A : ℝ) : ℂ) * iteratedDeriv 0 (u : ℝ → ℂ) t)
      (Set.mem_range_self t)
    simp only [iteratedDeriv_zero, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) A)] at hraw
    rw [← Real.exp_mul] at hraw
    have hpos : 0 < Real.exp (t * A) := Real.exp_pos _
    have hdiv : ‖(u : ℝ → ℂ) t‖ ≤ Cplus / Real.exp (t * A) :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hraw)
    calc
      ‖(u : ℝ → ℂ) t‖ ≤ Cplus / Real.exp (t * A) := hdiv
      _ = Cplus * Real.exp (-A * |t|) := by
        rw [abs_of_nonneg ht, div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring
      _ ≤ C * Real.exp (-A * |t|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.exp_pos _).le
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hraw := hCminus
      (((Real.exp t ^ (-A) : ℝ) : ℂ) * iteratedDeriv 0 (u : ℝ → ℂ) t)
      (Set.mem_range_self t)
    simp only [iteratedDeriv_zero, norm_mul, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) (-A))] at hraw
    rw [← Real.exp_mul] at hraw
    have hpos : 0 < Real.exp (t * (-A)) := Real.exp_pos _
    have hdiv : ‖(u : ℝ → ℂ) t‖ ≤ Cminus / Real.exp (t * (-A)) :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hraw)
    calc
      ‖(u : ℝ → ℂ) t‖ ≤ Cminus / Real.exp (t * (-A)) := hdiv
      _ = Cminus * Real.exp (-A * |t|) := by
        rw [abs_of_nonpos ht', div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring
      _ ≤ C * Real.exp (-A * |t|) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.exp_pos _).le

/-! ## Prime-circle periodization -/

/-- Integer periodization on a logarithmic circle of circumference `L`. -/
def deningerPrimeCirclePeriodization
    (L : ℝ) (u : DeningerMeyerStrongLogTarget) (t : ℝ) : ℂ :=
  ∑' j : ℤ, (u : ℝ → ℂ) (t + (j : ℝ) * L)

/-- Geometric majorant for all translates over one prime-circle cell. -/
def deningerPrimeCircleTranslateMajorant
    (C A L : ℝ) (j : ℤ) : ℝ :=
  C * Real.exp (A * L) * Real.exp (-A * L) ^ j.natAbs

theorem summable_deningerPrimeCircleTranslateMajorant
    {C A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    Summable (deningerPrimeCircleTranslateMajorant C A L) := by
  have hq0 : 0 ≤ Real.exp (-A * L) := (Real.exp_pos _).le
  have hq1 : Real.exp (-A * L) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hA) hL
  exact ((summable_int_pow_natAbs hq0 hq1).mul_left
    (C * Real.exp (A * L))).congr (fun j => rfl)

private theorem abs_intCast_mul_sub_le_abs_add
    (t L : ℝ) (j : ℤ) :
    |(j : ℝ)| * |L| - |t| ≤ |t + (j : ℝ) * L| := by
  have htri : |(j : ℝ) * L| ≤
      |t + (j : ℝ) * L| + |t| := by
    calc
      |(j : ℝ) * L| = |(t + (j : ℝ) * L) - t| := by ring_nf
      _ ≤ |t + (j : ℝ) * L| + |t| := abs_sub _ _
  rw [abs_mul] at htri
  linarith

/-- Uniform exponential translate bound on one logarithmic circle cell. -/
theorem norm_deningerMeyerStrongLog_translate_le_majorant
    (u : DeningerMeyerStrongLogTarget)
    {C A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hu : ∀ x : ℝ,
      ‖(u : ℝ → ℂ) x‖ ≤ C * Real.exp (-A * |x|))
    {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) (j : ℤ) :
    ‖(u : ℝ → ℂ) (t + (j : ℝ) * L)‖ ≤
      deningerPrimeCircleTranslateMajorant C A L j := by
  have hC : 0 ≤ C := by
    have h := hu 0
    simpa using (norm_nonneg ((u : ℝ → ℂ) 0)).trans h
  have habsL : |L| = L := abs_of_pos hL
  have hjcast : |(j : ℝ)| = (j.natAbs : ℝ) := by
    simpa only [Int.cast_abs] using
      (Nat.cast_natAbs (α := ℝ) j).symm
  have hdistance :
      (j.natAbs : ℝ) * L - L ≤
        |t + (j : ℝ) * L| := by
    have hbase := abs_intCast_mul_sub_le_abs_add t L j
    rw [habsL, hjcast] at hbase
    linarith [abs_of_nonneg ht0, abs_le.mpr ⟨by linarith, htL⟩]
  have hexponent :
      -A * |t + (j : ℝ) * L| ≤
        A * L + (j.natAbs : ℝ) * (-A * L) := by
    have hmul := mul_le_mul_of_nonpos_left hdistance (neg_nonpos.mpr hA.le)
    nlinarith
  calc
    ‖(u : ℝ → ℂ) (t + (j : ℝ) * L)‖ ≤
        C * Real.exp (-A * |t + (j : ℝ) * L|) := hu _
    _ ≤ C * Real.exp
        (A * L + (j.natAbs : ℝ) * (-A * L)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hC
    _ = deningerPrimeCircleTranslateMajorant C A L j := by
      rw [Real.exp_add, Real.exp_nat_mul]
      simp [deningerPrimeCircleTranslateMajorant, mul_assoc]

/-- The literal all-weight Meyer source is absolutely periodizable on every positive prime
circle, uniformly over one closed fundamental cell. -/
theorem summable_norm_deningerPrimeCircle_translate
    (u : DeningerMeyerStrongLogTarget) {L : ℝ} (hL : 0 < L)
    {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    Summable (fun j : ℤ =>
      ‖(u : ℝ → ℂ) (t + (j : ℝ) * L)‖) := by
  obtain ⟨C, hC, hu⟩ :=
    deningerMeyerStrongLog_norm_le_exp_neg_abs u 1
  exact (summable_deningerPrimeCircleTranslateMajorant
      one_pos hL).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun j => norm_deningerMeyerStrongLog_translate_le_majorant
      u one_pos hL hu ht0 htL j)

/-- Absolute convergence of source periodization on the prime-circle cell. -/
theorem summable_deningerPrimeCircle_translate
    (u : DeningerMeyerStrongLogTarget) {L : ℝ} (hL : 0 < L)
    {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    Summable (fun j : ℤ =>
      (u : ℝ → ℂ) (t + (j : ℝ) * L)) :=
  (summable_norm_deningerPrimeCircle_translate u hL ht0 htL).of_norm

/-! ## Autocorrelation and exact tiling infrastructure -/

/-- Real-line autocorrelation of the logarithmic Meyer source. -/
def deningerMeyerStrongLogAutocorrelation
    (u : DeningerMeyerStrongLogTarget) (a : ℝ) : ℂ :=
  ∫ x : ℝ, (u : ℝ → ℂ) x *
    (starRingEnd ℂ) ((u : ℝ → ℂ) (x + a))

/-- The literal strong-log source is integrable on the real line. -/
theorem integrable_deningerMeyerStrongLogTarget
    (u : DeningerMeyerStrongLogTarget) :
    Integrable (u : ℝ → ℂ) := by
  have h := integrable_deningerMeyerStrongLogMellinJet
    u.property 0 (0 : ℂ)
  convert h using 1
  funext t
  simp [deningerMeyerStrongLogMellinJet]

/-- Every translated autocorrelation integrand is integrable. -/
theorem integrable_deningerMeyerStrongLogAutocorrelationIntegrand
    (u : DeningerMeyerStrongLogTarget) (a : ℝ) :
    Integrable (fun x : ℝ =>
      (u : ℝ → ℂ) x *
        (starRingEnd ℂ) ((u : ℝ → ℂ) (x + a))) := by
  obtain ⟨C, hC, hu⟩ :=
    deningerMeyerStrongLog_norm_le_exp_neg_abs u 1
  have hubound : ∀ x : ℝ, ‖(u : ℝ → ℂ) x‖ ≤ C := by
    intro x
    calc
      ‖(u : ℝ → ℂ) x‖ ≤ C * Real.exp (-1 * |x|) := hu x
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (by
          rw [Real.exp_le_one_iff]
          nlinarith [abs_nonneg x]) hC
      _ = C := mul_one C
  have hshift : Integrable (fun x : ℝ => (u : ℝ → ℂ) (x + a)) :=
    (integrable_deningerMeyerStrongLogTarget u).comp_add_right a
  have hconj : Integrable (fun x : ℝ =>
      (starRingEnd ℂ) ((u : ℝ → ℂ) (x + a))) := by
    have h := Complex.conjCLE.toContinuousLinearMap.integrable_comp hshift
    convert h using 1
    funext x
    exact Complex.conjCLE_apply _
  exact hconj.bdd_mul u.property.smooth.continuous.aestronglyMeasurable
    (ae_of_all _ hubound)

/-- Positive-length integer cells tile the real line exactly for every integrable function. -/
private theorem Integrable.hasSum_intervalIntegral_mul_int
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L) :
    HasSum (fun j : ℤ =>
      ∫ x in (j : ℝ) * L..((j : ℝ) + 1) * L, f x)
      (∫ x : ℝ, f x) := by
  let w : ℝ → ℂ := fun y => L • f (L * y)
  have hw : Integrable w := by
    have hcomp : Integrable (fun y : ℝ => f (L * y)) :=
      hf.comp_mul_left' hL.ne'
    simpa only [w, Complex.real_smul] using hcomp.const_mul (L : ℂ)
  have htotal : (∫ y : ℝ, w y) = ∫ x : ℝ, f x := by
    simp only [w, MeasureTheory.integral_smul]
    rw [Measure.integral_comp_mul_left]
    simp only [abs_of_pos hL, abs_inv]
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hcells := hw.hasSum_intervalIntegral 0
  rw [htotal] at hcells
  apply hcells.congr_fun
  intro j
  simp only [zero_add, w, intervalIntegral.integral_smul]
  rw [intervalIntegral.smul_integral_comp_mul_left]
  congr 1 <;> ring

/-! ## Prime-circle energy unfolding -/

/-- Literal prime-circle squared norm, represented in `ℂ` by `z * conj z`. -/
def deningerPrimeCircleEnergy
    (L : ℝ) (u : DeningerMeyerStrongLogTarget) : ℂ :=
  ∫ t in (0 : ℝ)..L,
    deningerPrimeCirclePeriodization L u t *
      (starRingEnd ℂ) (deningerPrimeCirclePeriodization L u t)

private def deningerPrimeCircleCrossTerm
    (L : ℝ) (u : DeningerMeyerStrongLogTarget)
    (q : ℤ × ℤ) (t : ℝ) : ℂ :=
  (u : ℝ → ℂ) (t + (q.1 : ℝ) * L) *
    (starRingEnd ℂ) ((u : ℝ → ℂ) (t + (q.2 : ℝ) * L))

/-- Difference coordinates `(m,j) ↦ (j,j+m)` on the translate-pair lattice. -/
private def deningerPrimeCircleDifferenceEquiv :
    ℤ × ℤ ≃ ℤ × ℤ where
  toFun q := (q.2, q.2 + q.1)
  invFun q := (q.2 - q.1, q.1)
  left_inv q := by
    ext <;> simp
  right_inv q := by
    ext <;> simp

/-- **Exact prime-circle autocorrelation unfolding.**  The literal circle norm is the
absolutely convergent autocorrelation lattice of the all-weight Meyer source. -/
theorem deningerPrimeCircleEnergy_eq_tsum_autocorrelation
    (u : DeningerMeyerStrongLogTarget) {L : ℝ} (hL : 0 < L) :
    deningerPrimeCircleEnergy L u =
      ∑' m : ℤ, deningerMeyerStrongLogAutocorrelation u ((m : ℝ) * L) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) L)
  obtain ⟨C, hC, hu⟩ :=
    deningerMeyerStrongLog_norm_le_exp_neg_abs u 1
  let B : ℤ → ℝ := fun j =>
    deningerPrimeCircleTranslateMajorant C 1 L j
  have hB : Summable B := by
    simpa only [B] using
      (summable_deningerPrimeCircleTranslateMajorant
        (C := C) one_pos hL)
  have hBnonneg (j : ℤ) : 0 ≤ B j := by
    simp only [B, deningerPrimeCircleTranslateMajorant]
    positivity
  have htranslate {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) (j : ℤ) :
      ‖(u : ℝ → ℂ) (t + (j : ℝ) * L)‖ ≤ B j := by
    exact norm_deningerMeyerStrongLog_translate_le_majorant
      u one_pos hL hu ht0 htL j
  have hcrossContinuous (q : ℤ × ℤ) :
      Continuous (deningerPrimeCircleCrossTerm L u q) := by
    unfold deningerPrimeCircleCrossTerm
    have hucont : Continuous (u : ℝ → ℂ) :=
      u.property.smooth.continuous
    have hleft : Continuous (fun t : ℝ => t + (q.1 : ℝ) * L) := by
      fun_prop
    have hright : Continuous (fun t : ℝ => t + (q.2 : ℝ) * L) := by
      fun_prop
    exact (hucont.comp hleft).mul (hucont.comp hright).star
  have hcrossIntegrable (q : ℤ × ℤ) :
      Integrable (deningerPrimeCircleCrossTerm L u q) μ := by
    change IntegrableOn (deningerPrimeCircleCrossTerm L u q) (Ioc 0 L)
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le]
    exact (hcrossContinuous q).intervalIntegrable 0 L
  have hcrossNormBound (q : ℤ × ℤ) (t : ℝ)
      (ht0 : 0 ≤ t) (htL : t ≤ L) :
      ‖deningerPrimeCircleCrossTerm L u q t‖ ≤ B q.1 * B q.2 := by
    rw [deningerPrimeCircleCrossTerm, norm_mul,
      Complex.norm_conj]
    exact mul_le_mul (htranslate ht0 htL q.1)
      (htranslate ht0 htL q.2) (norm_nonneg _) (hBnonneg q.1)
  have hcrossIntegralNormBound (q : ℤ × ℤ) :
      (∫ t : ℝ, ‖deningerPrimeCircleCrossTerm L u q t‖ ∂μ) ≤
        L * (B q.1 * B q.2) := by
    rw [← intervalIntegral.integral_of_le hL.le]
    calc
      (∫ t : ℝ in 0..L,
          ‖deningerPrimeCircleCrossTerm L u q t‖) ≤
          ∫ _t : ℝ in 0..L, B q.1 * B q.2 := by
        exact intervalIntegral.integral_mono_on_of_le_Ioo hL.le
          ((hcrossContinuous q).norm.intervalIntegrable 0 L)
          (continuous_const.intervalIntegrable 0 L)
          (fun t ht => hcrossNormBound q t ht.1.le ht.2.le)
      _ = L * (B q.1 * B q.2) := by simp; ring
  have hpairMajorant : Summable (fun q : ℤ × ℤ =>
      L * (B q.1 * B q.2)) := by
    exact (summable_mul_of_summable_norm hB.norm hB.norm).mul_left L
  have hcrossIntegralNorm : Summable (fun q : ℤ × ℤ =>
      ∫ t : ℝ, ‖deningerPrimeCircleCrossTerm L u q t‖ ∂μ) :=
    hpairMajorant.of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _)
      hcrossIntegralNormBound
  have hcrossIntegral : Summable (fun q : ℤ × ℤ =>
      ∫ t : ℝ, deningerPrimeCircleCrossTerm L u q t ∂μ) :=
    hcrossIntegralNorm.of_norm_bounded
      (fun q => norm_integral_le_integral_norm _)
  have hpointwise (t : ℝ) (ht0 : 0 ≤ t) (htL : t ≤ L) :
      deningerPrimeCirclePeriodization L u t *
          (starRingEnd ℂ) (deningerPrimeCirclePeriodization L u t) =
        ∑' q : ℤ × ℤ, deningerPrimeCircleCrossTerm L u q t := by
    have hs := summable_norm_deningerPrimeCircle_translate u hL ht0 htL
    have hsstar : Summable (fun j : ℤ =>
        ‖(starRingEnd ℂ) ((u : ℝ → ℂ) (t + (j : ℝ) * L))‖) := by
      exact hs.congr (fun j => (Complex.norm_conj _).symm)
    rw [deningerPrimeCirclePeriodization, Complex.conj_tsum,
      tsum_mul_tsum_of_summable_norm hs hsstar]
    rfl
  have hswap :
      (∑' q : ℤ × ℤ,
          ∫ t : ℝ, deningerPrimeCircleCrossTerm L u q t ∂μ) =
        ∫ t : ℝ,
          ∑' q : ℤ × ℤ, deningerPrimeCircleCrossTerm L u q t ∂μ :=
    integral_tsum_of_summable_integral_norm hcrossIntegrable
      hcrossIntegralNorm
  let G : ℤ × ℤ → ℂ := fun q =>
    ∫ t : ℝ in 0..L, deningerPrimeCircleCrossTerm L u q t
  have hG : Summable G := by
    apply hcrossIntegral.congr
    intro q
    simp only [G, μ, intervalIntegral.integral_of_le hL.le]
  have henergyDouble : deningerPrimeCircleEnergy L u = ∑' q, G q := by
    rw [deningerPrimeCircleEnergy,
      intervalIntegral.integral_of_le hL.le]
    change (∫ t : ℝ,
      deningerPrimeCirclePeriodization L u t *
        (starRingEnd ℂ) (deningerPrimeCirclePeriodization L u t) ∂μ) = _
    calc
      _ = ∫ t : ℝ,
          ∑' q : ℤ × ℤ, deningerPrimeCircleCrossTerm L u q t ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointwise t ht.1.le ht.2
      _ = ∑' q : ℤ × ℤ,
          ∫ t : ℝ, deningerPrimeCircleCrossTerm L u q t ∂μ := hswap.symm
      _ = ∑' q : ℤ × ℤ, G q := by
        apply tsum_congr
        intro q
        simp only [G, μ, intervalIntegral.integral_of_le hL.le]
  let e := deningerPrimeCircleDifferenceEquiv
  have hGe : Summable (G ∘ e) :=
    (e.summable_iff).2 hG
  have hinner (m : ℤ) :
      (∑' j : ℤ, G (e (m, j))) =
        deningerMeyerStrongLogAutocorrelation u ((m : ℝ) * L) := by
    let v : ℝ → ℂ := fun x =>
      (u : ℝ → ℂ) x *
        (starRingEnd ℂ) ((u : ℝ → ℂ) (x + (m : ℝ) * L))
    have hv : Integrable v := by
      simpa only [v] using
        integrable_deningerMeyerStrongLogAutocorrelationIntegrand
          u ((m : ℝ) * L)
    have htile := Integrable.hasSum_intervalIntegral_mul_int hv hL
    have hterm (j : ℤ) :
        G (e (m, j)) =
          ∫ x : ℝ in (j : ℝ) * L..((j : ℝ) + 1) * L, v x := by
      change G (j, j + m) =
        ∫ x : ℝ in (j : ℝ) * L..((j : ℝ) + 1) * L, v x
      calc
        G (j, j + m) =
            ∫ t : ℝ in 0..L, v (t + (j : ℝ) * L) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          simp only [deningerPrimeCircleCrossTerm, v]
          congr 2 <;> push_cast <;> ring
        _ = ∫ x : ℝ in (j : ℝ) * L..L + (j : ℝ) * L, v x := by
          rw [intervalIntegral.integral_comp_add_right]
          ring_nf
        _ = ∫ x : ℝ in (j : ℝ) * L..((j : ℝ) + 1) * L, v x := by
          congr 1 <;> ring
    have htile' : HasSum (fun j : ℤ => G (e (m, j)))
        (∫ x : ℝ, v x) :=
      htile.congr_fun hterm
    simpa only [deningerMeyerStrongLogAutocorrelation, v] using htile'.tsum_eq
  calc
    deningerPrimeCircleEnergy L u = ∑' q, G q := henergyDouble
    _ = ∑' q : ℤ × ℤ, G (e q) := (e.tsum_eq G).symm
    _ = ∑' m : ℤ, ∑' j : ℤ, G (e (m, j)) := hGe.tsum_prod
    _ = ∑' m : ℤ,
        deningerMeyerStrongLogAutocorrelation u ((m : ℝ) * L) := by
      apply tsum_congr
      exact hinner

/-- Absolute convergence in the exact prime-circle unfolding. -/
theorem summable_norm_deningerMeyerStrongLogAutocorrelation_int_mul
    (u : DeningerMeyerStrongLogTarget) {L : ℝ} (hL : 0 < L) :
    Summable (fun m : ℤ =>
      ‖deningerMeyerStrongLogAutocorrelation u ((m : ℝ) * L)‖) := by
  -- The proof is the norm-majorized product-lattice argument already used in the unfolding.
  obtain ⟨C, hC, hu⟩ :=
    deningerMeyerStrongLog_norm_le_exp_neg_abs u 2
  have hpoint (m : ℤ) :
      ‖deningerMeyerStrongLogAutocorrelation u ((m : ℝ) * L)‖ ≤
        C ^ 2 * Real.exp (-|((m : ℝ) * L)|) * 2 := by
    rw [deningerMeyerStrongLogAutocorrelation]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hdom : ∀ x : ℝ,
        ‖(u : ℝ → ℂ) x *
          (starRingEnd ℂ) ((u : ℝ → ℂ) (x + (m : ℝ) * L))‖ ≤
          C ^ 2 * Real.exp (-|((m : ℝ) * L)|) * Real.exp (-|x|) := by
      intro x
      rw [norm_mul, Complex.norm_conj]
      calc
        ‖(u : ℝ → ℂ) x‖ *
            ‖(u : ℝ → ℂ) (x + (m : ℝ) * L)‖ ≤
            (C * Real.exp (-2 * |x|)) *
              (C * Real.exp (-2 * |x + (m : ℝ) * L|)) :=
          mul_le_mul (hu x) (hu _) (norm_nonneg _) (by positivity)
        _ ≤ C ^ 2 * Real.exp (-|((m : ℝ) * L)|) * Real.exp (-|x|) := by
          have htri : |((m : ℝ) * L)| ≤ |x| + |x + (m : ℝ) * L| := by
            calc
              |((m : ℝ) * L)| = |(x + (m : ℝ) * L) - x| := by ring_nf
              _ ≤ |x + (m : ℝ) * L| + |x| := abs_sub _ _
              _ = |x| + |x + (m : ℝ) * L| := add_comm _ _
          have hexp :
              -2 * |x| - 2 * |x + (m : ℝ) * L| ≤
                -|((m : ℝ) * L)| - |x| := by
            linarith [abs_nonneg (x + (m : ℝ) * L)]
          calc
            (C * Real.exp (-2 * |x|)) *
                (C * Real.exp (-2 * |x + (m : ℝ) * L|)) =
                C ^ 2 * Real.exp
                  (-2 * |x| - 2 * |x + (m : ℝ) * L|) := by
              calc
                _ = C ^ 2 * (Real.exp (-2 * |x|) *
                    Real.exp (-2 * |x + (m : ℝ) * L|)) := by ring
                _ = _ := by
                  rw [← Real.exp_add]
                  congr 2
                  ring
            _ ≤ C ^ 2 * Real.exp
                (-|((m : ℝ) * L)| - |x|) :=
              mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr hexp) (sq_nonneg C)
            _ = C ^ 2 * Real.exp (-|((m : ℝ) * L)|) *
                Real.exp (-|x|) := by
              rw [show -|((m : ℝ) * L)| - |x| =
                  -|((m : ℝ) * L)| + (-|x|) by ring,
                Real.exp_add]
              ring
    have hdomInt : Integrable (fun x : ℝ =>
        C ^ 2 * Real.exp (-|((m : ℝ) * L)|) * Real.exp (-|x|)) := by
      have h := (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic one_pos).const_mul
        (C ^ 2 * Real.exp (-|((m : ℝ) * L)|))
      convert h using 1
      funext x
      simp only [one_mul]
    calc
      (∫ x : ℝ, ‖(u : ℝ → ℂ) x *
          (starRingEnd ℂ) ((u : ℝ → ℂ) (x + (m : ℝ) * L))‖) ≤
          ∫ x : ℝ,
            C ^ 2 * Real.exp (-|((m : ℝ) * L)|) * Real.exp (-|x|) := by
        exact integral_mono_ae
          (integrable_deningerMeyerStrongLogAutocorrelationIntegrand
            u ((m : ℝ) * L)).norm
          hdomInt
          (ae_of_all _ hdom)
      _ = C ^ 2 * Real.exp (-|((m : ℝ) * L)|) * 2 := by
        rw [MeasureTheory.integral_const_mul]
        have hexpabs : (∫ x : ℝ, Real.exp (-|x|)) = 2 := by
          calc
            (∫ x : ℝ, Real.exp (-|x|)) =
                2 * ∫ x : ℝ in Ioi 0, Real.exp (-x) :=
              integral_comp_abs (f := fun y : ℝ => Real.exp (-y))
            _ = 2 := by rw [integral_exp_neg_Ioi_zero, mul_one]
        rw [hexpabs]
  have hgeom : Summable (fun m : ℤ =>
      C ^ 2 * Real.exp (-|((m : ℝ) * L)|) * 2) := by
    have habs : ∀ m : ℤ,
        |((m : ℝ) * L)| = (m.natAbs : ℝ) * L := by
      intro m
      rw [abs_mul, abs_of_pos hL]
      simpa only [Int.cast_abs] using congrArg (fun x : ℝ => x * L)
        (Nat.cast_natAbs (α := ℝ) m).symm
    have hbase := summable_int_pow_natAbs
      (show 0 ≤ Real.exp (-L) by positivity)
      (by rw [Real.exp_lt_one_iff]; linarith)
    apply (hbase.mul_left (C ^ 2 * 2)).congr
    intro m
    rw [habs m]
    have hexp : Real.exp (-((m.natAbs : ℝ) * L)) =
        Real.exp (-L) ^ m.natAbs := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    ring
  exact hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint

/-! ## Short-cell support collapse -/

/-- Distinct positive-length lattice translates of a source supported in a shorter interval have
zero autocorrelation. -/
theorem deningerMeyerStrongLogAutocorrelation_int_mul_eq_zero_of_short_support
    (u : DeningerMeyerStrongLogTarget) {a b L : ℝ}
    (hL : 0 < L)
    (hsupport : Function.support (u : ℝ → ℂ) ⊆ Icc a b)
    (hshort : b - a < L) {m : ℤ} (hm : m ≠ 0) :
    deningerMeyerStrongLogAutocorrelation u ((m : ℝ) * L) = 0 := by
  rw [deningerMeyerStrongLogAutocorrelation]
  calc
    (∫ x : ℝ, (u : ℝ → ℂ) x *
        (starRingEnd ℂ) ((u : ℝ → ℂ) (x + (m : ℝ) * L))) =
        ∫ _x : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : (u : ℝ → ℂ) x = 0
      · simp only [hx, zero_mul]
      by_cases hy : (u : ℝ → ℂ) (x + (m : ℝ) * L) = 0
      · simp only [hy, map_zero, mul_zero]
      have hxs : x ∈ Icc a b := hsupport hx
      have hys : x + (m : ℝ) * L ∈ Icc a b := hsupport hy
      have hsep : |(m : ℝ) * L| ≤ b - a := by
        rw [abs_le]
        constructor <;> linarith [hxs.1, hxs.2, hys.1, hys.2]
      have hmnat : 1 ≤ m.natAbs := by
        exact (Nat.one_le_iff_ne_zero).2 (Int.natAbs_ne_zero.mpr hm)
      have hmcast : (1 : ℝ) ≤ |(m : ℝ)| := by
        have hcast : (1 : ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast hmnat
        calc
          (1 : ℝ) ≤ (m.natAbs : ℝ) := hcast
          _ = |(m : ℝ)| := by
            simpa only [Int.cast_abs] using
              (Nat.cast_natAbs (α := ℝ) m)
      have hperiod : L ≤ |(m : ℝ) * L| := by
        rw [abs_mul, abs_of_pos hL]
        nlinarith
      exfalso
      linarith
    _ = 0 := by simp

/-- A source supported in an interval shorter than the circle has no off-diagonal circle energy. -/
theorem deningerPrimeCircleEnergy_eq_autocorrelation_zero_of_short_support
    (u : DeningerMeyerStrongLogTarget) {a b L : ℝ}
    (hL : 0 < L)
    (hsupport : Function.support (u : ℝ → ℂ) ⊆ Icc a b)
    (hshort : b - a < L) :
    deningerPrimeCircleEnergy L u =
      deningerMeyerStrongLogAutocorrelation u 0 := by
  rw [deningerPrimeCircleEnergy_eq_tsum_autocorrelation u hL]
  rw [tsum_eq_single 0]
  · simp
  · intro m hm
    exact deningerMeyerStrongLogAutocorrelation_int_mul_eq_zero_of_short_support
      u hL hsupport hshort hm

/-! ## Exact von Mangoldt reindexing -/

/-- Prime and positive iterate coordinates are exactly the natural-number von Mangoldt comb for
an arbitrary time profile.  This identity is purely arithmetic and needs no convergence premise. -/
theorem tsum_prime_iterate_eq_deningerPrimePower_vonMangoldt
    (F : ℝ → ℂ) :
    (∑' pk : Nat.Primes × ℕ,
        (Real.log (pk.1 : ℕ) : ℂ) *
          F ((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ))) =
      ∑' n : DeningerPrimePowerIndex,
        (deningerPrimePowerWeight n : ℂ) *
          F (deningerPrimePowerTime n) := by
  let g : ℕ → ℂ := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℂ) * F (Real.log n)
  have hsuppTwo : Function.support g ⊆ {n : ℕ | 2 ≤ n} := by
    intro n hn
    change 2 ≤ n
    by_contra hnot
    have hnle : n ≤ 1 := by omega
    interval_cases n
    · exact hn (by simp [g])
    · exact hn (by simp [g])
  have hsuppPrimePower :
      Function.support g ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hnot
    have hzero : ArithmeticFunction.vonMangoldt n = 0 := by
      rw [← not_ne_iff]
      intro hne
      exact hnot (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne)
    exact hn (by simp [g, hzero])
  have htwo := tsum_subtype_eq_of_support_subset hsuppTwo
  have hprimePower := tsum_subtype_eq_of_support_subset hsuppPrimePower
  calc
    (∑' pk : Nat.Primes × ℕ,
        (Real.log (pk.1 : ℕ) : ℂ) *
          F ((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ))) =
        ∑' pk : Nat.Primes × ℕ,
          g (Nat.Primes.prodNatEquiv pk) := by
      apply tsum_congr
      intro pk
      have hw := deningerPrimePowerWeight_euler pk
      have hw' : ArithmeticFunction.vonMangoldt
          ((pk.1 : ℕ) ^ (pk.2 + 1)) = Real.log (pk.1 : ℕ) := by
        simpa [deningerPrimePowerWeight,
          deningerEulerPrimePowerIndex] using hw
      change (Real.log (pk.1 : ℕ) : ℂ) *
          F ((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ)) =
        (ArithmeticFunction.vonMangoldt
            ((Nat.Primes.prodNatEquiv pk : {n : ℕ // IsPrimePow n}) : ℕ) : ℂ) *
          F (Real.log
            ((Nat.Primes.prodNatEquiv pk : {n : ℕ // IsPrimePow n}) : ℕ))
      rw [Nat.Primes.coe_prodNatEquiv_apply, hw']
      congr 2
      rw [Nat.cast_pow, Real.log_pow]
      simp
    _ = ∑' n : {n : ℕ // IsPrimePow n}, g n :=
      Nat.Primes.prodNatEquiv.tsum_eq (fun n => g n)
    _ = ∑' n : ℕ, g n := hprimePower
    _ = ∑' n : DeningerPrimePowerIndex, g n := htwo.symm
    _ = ∑' n : DeningerPrimePowerIndex,
        (deningerPrimePowerWeight n : ℂ) *
          F (deningerPrimePowerTime n) := by
      rfl

/-- Real absolute convergence of the von Mangoldt Dirichlet majorant at every exponent `A > 1`. -/
theorem summable_vonMangoldt_mul_rpow_neg
    {A : ℝ} (hA : 1 < A) :
    Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-A)) := by
  have hcomplex : (1 : ℝ) < ((A : ℝ) : ℂ).re := by
    simpa using hA
  have hs : Summable (fun n =>
      ‖LSeries.term (fun m =>
        (ArithmeticFunction.vonMangoldt m : ℂ)) (A : ℂ) n‖) :=
    summable_norm_iff.mpr
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hcomplex)
  refine hs.congr (fun n => ?_)
  rw [LSeries.norm_term_eq, Complex.ofReal_re]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv]

set_option maxHeartbeats 600000 in
/-- Centering deletes exactly the zero autocorrelation mode and leaves positive/negative iterate
pairs on every prime circle. -/
theorem deningerPrimeCircleEnergy_sub_autocorrelation_zero
    (u : DeningerMeyerStrongLogTarget) {L : ℝ} (hL : 0 < L) :
    deningerPrimeCircleEnergy L u -
        deningerMeyerStrongLogAutocorrelation u 0 =
      ∑' k : ℕ,
        (deningerMeyerStrongLogAutocorrelation u
            ((k + 1 : ℝ) * L) +
          deningerMeyerStrongLogAutocorrelation u
            (-((k + 1 : ℝ) * L))) := by
  let f : ℤ → ℂ := fun m =>
    deningerMeyerStrongLogAutocorrelation u ((m : ℝ) * L)
  have hfNorm : Summable (fun m : ℤ => ‖f m‖) := by
    simpa only [f] using
      summable_norm_deningerMeyerStrongLogAutocorrelation_int_mul u hL
  have hf : Summable f := hfNorm.of_norm
  have hsplit := tsum_int_eq_zero_add_tsum_pnat hf
  rw [deningerPrimeCircleEnergy_eq_tsum_autocorrelation u hL]
  rw [show (∑' m : ℤ,
      deningerMeyerStrongLogAutocorrelation u ((m : ℝ) * L)) =
      ∑' m : ℤ, f m by rfl]
  have hfzero : deningerMeyerStrongLogAutocorrelation u 0 = f 0 := by
    simp [f]
  rw [hfzero]
  rw [hsplit]
  have hposEq : (∑' n : ℕ+, f (n : ℤ)) =
      ∑' k : ℕ, f (k + 1) := by
    simpa using
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (n : ℤ)))
  have hnegEq : (∑' n : ℕ+, f (-(n : ℤ))) =
      ∑' k : ℕ, f (-(k + 1 : ℕ)) := by
    simpa using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => f (-(n : ℤ))))
  rw [hposEq, hnegEq]
  have hpos : Summable (fun k : ℕ => f (k + 1)) :=
    hf.comp_injective (by
      intro x y hxy
      have hcast : (x : ℤ) = (y : ℤ) := add_right_cancel hxy
      exact_mod_cast hcast)
  have hneg : Summable (fun k : ℕ => f (-(k + 1 : ℕ))) := by
    exact hf.comp_injective (by
      intro x y hxy
      have hsum : (x : ℤ) + 1 = (y : ℤ) + 1 := neg_injective hxy
      have hcast : (x : ℤ) = (y : ℤ) := add_right_cancel hsum
      exact_mod_cast hcast)
  rw [show f 0 + (∑' k : ℕ, f (k + 1)) +
      (∑' k : ℕ, f (-(k + 1 : ℕ))) - f 0 =
      (∑' k : ℕ, f (k + 1)) +
        (∑' k : ℕ, f (-(k + 1 : ℕ))) by ring]
  rw [← hpos.tsum_add hneg]
  apply tsum_congr
  intro k
  simp only [f]
  push_cast
  congr 2 <;> ring

/-- Critical centered prime-circle form before archimedean completion. -/
def deningerCriticalFloquetForm
    (u : DeningerMeyerStrongLogTarget) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.log (p : ℕ) : ℂ) *
      (deningerPrimeCircleEnergy (Real.log (p : ℕ)) u -
        deningerMeyerStrongLogAutocorrelation u 0)

/-- Natural-number von Mangoldt autocorrelation current. -/
def deningerVonMangoldtAutocorrelationCurrent
    (u : DeningerMeyerStrongLogTarget) : ℂ :=
  ∑' n : DeningerPrimePowerIndex,
    (deningerPrimePowerWeight n : ℂ) *
      (deningerMeyerStrongLogAutocorrelation u
          (deningerPrimePowerTime n) +
        deningerMeyerStrongLogAutocorrelation u
          (-deningerPrimePowerTime n))

/-- The paper's exponential autocorrelation hypothesis. -/
def DeningerAutocorrelationExpBound
    (u : DeningerMeyerStrongLogTarget) (A B : ℝ) : Prop :=
  ∀ a : ℝ,
    ‖deningerMeyerStrongLogAutocorrelation u a‖ ≤
      B * Real.exp (-A * |a|)

/-- The von Mangoldt autocorrelation sequence is absolutely summable under the exact paper bound
`A > 1`. -/
theorem summable_norm_deningerVonMangoldtAutocorrelation
    (u : DeningerMeyerStrongLogTarget) {A B : ℝ}
    (hA : 1 < A) (hB : 0 ≤ B)
    (hbound : DeningerAutocorrelationExpBound u A B) :
    Summable (fun n : DeningerPrimePowerIndex =>
      ‖(deningerPrimePowerWeight n : ℂ) *
        (deningerMeyerStrongLogAutocorrelation u
            (deningerPrimePowerTime n) +
          deningerMeyerStrongLogAutocorrelation u
            (-deningerPrimePowerTime n))‖) := by
  let H : ℕ → ℝ := fun n =>
    2 * B * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-A))
  have hH : Summable H :=
    (summable_vonMangoldt_mul_rpow_neg hA).mul_left (2 * B)
  have hHnonneg (n : ℕ) : 0 ≤ H n := by
    simp only [H]
    positivity
  have hmajor (n : DeningerPrimePowerIndex) :
      ‖(deningerPrimePowerWeight n : ℂ) *
        (deningerMeyerStrongLogAutocorrelation u
            (deningerPrimePowerTime n) +
          deningerMeyerStrongLogAutocorrelation u
            (-deningerPrimePowerTime n))‖ ≤ H n := by
    have hnpos : (0 : ℝ) < (n : ℕ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two n.property
    have hnone : (1 : ℝ) ≤ (n : ℕ) := by
      have : 1 ≤ (n : ℕ) := by omega
      exact_mod_cast this
    have hlog : 0 ≤ Real.log (n : ℕ) := Real.log_nonneg hnone
    have hpow : Real.exp (-A * |Real.log (n : ℕ)|) =
        (n : ℝ) ^ (-A) := by
      rw [abs_of_nonneg hlog, Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    have hplus := hbound (deningerPrimePowerTime n)
    have hminus := hbound (-deningerPrimePowerTime n)
    simp only [deningerPrimePowerTime, abs_neg, hpow] at hplus hminus
    simp only [deningerPrimePowerWeight, deningerPrimePowerTime]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc
      deningerPrimePowerWeight n *
          ‖deningerMeyerStrongLogAutocorrelation u (Real.log (n : ℕ)) +
            deningerMeyerStrongLogAutocorrelation u (-Real.log (n : ℕ))‖ ≤
          deningerPrimePowerWeight n *
            (B * (n : ℝ) ^ (-A) + B * (n : ℝ) ^ (-A)) := by
        exact mul_le_mul_of_nonneg_left
          ((norm_add_le _ _).trans (add_le_add hplus hminus))
          ArithmeticFunction.vonMangoldt_nonneg
      _ = H n := by
        simp only [H, deningerPrimePowerWeight]
        ring
  have hsub : Summable (fun n : DeningerPrimePowerIndex => H n) :=
    hH.subtype {n : ℕ | 2 ≤ n}
  exact hsub.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor

set_option maxHeartbeats 800000 in
/-- **Critical Floquet/von Mangoldt current identity.**  Under the paper's unconditional analytic
decay hypothesis, the centered prime-circle form is exactly the natural-number von Mangoldt
prime-power autocorrelation current. -/
theorem deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent
    (u : DeningerMeyerStrongLogTarget) {A B : ℝ}
    (hA : 1 < A) (hB : 0 ≤ B)
    (hbound : DeningerAutocorrelationExpBound u A B) :
    deningerCriticalFloquetForm u =
      deningerVonMangoldtAutocorrelationCurrent u := by
  let F : ℝ → ℂ := fun a =>
    deningerMeyerStrongLogAutocorrelation u a +
      deningerMeyerStrongLogAutocorrelation u (-a)
  let H : Nat.Primes × ℕ → ℂ := fun pk =>
    (Real.log (pk.1 : ℕ) : ℂ) *
      F ((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ))
  have hNatNorm :=
    summable_norm_deningerVonMangoldtAutocorrelation
      u hA hB hbound
  have hNat : Summable (fun n : DeningerPrimePowerIndex =>
      (deningerPrimePowerWeight n : ℂ) * F (deningerPrimePowerTime n)) := by
    exact hNatNorm.of_norm.congr (fun n => rfl)
  have hH : Summable H := by
    have he := hNat.comp_injective deningerEulerPrimePowerIndex_injective
    apply he.congr
    intro pk
    simp only [H, F, Function.comp_apply]
    rw [deningerPrimePowerWeight_euler,
      deningerPrimePowerTime_euler]
  calc
    deningerCriticalFloquetForm u =
        ∑' p : Nat.Primes, ∑' k : ℕ, H (p, k) := by
      rw [deningerCriticalFloquetForm]
      apply tsum_congr
      intro p
      have hpL : 0 < Real.log (p : ℕ) :=
        Real.log_pos (by exact_mod_cast p.prop.one_lt)
      rw [deningerPrimeCircleEnergy_sub_autocorrelation_zero u hpL]
      change (Real.log (p : ℕ) : ℂ) *
          (∑' k : ℕ, F ((k + 1 : ℝ) * Real.log (p : ℕ))) = _
      have hFsum : Summable (fun k : ℕ =>
          F ((k + 1 : ℝ) * Real.log (p : ℕ))) := by
        have hposNorm :=
          summable_norm_deningerMeyerStrongLogAutocorrelation_int_mul u hpL
        have hpos : Summable (fun k : ℕ =>
            deningerMeyerStrongLogAutocorrelation u
              ((k + 1 : ℝ) * Real.log (p : ℕ))) := by
          have h := hposNorm.of_norm.comp_injective
            (i := fun k : ℕ => (k + 1 : ℤ))
            (by
              intro x y hxy
              have hcast : (x : ℤ) = (y : ℤ) := add_right_cancel hxy
              exact_mod_cast hcast)
          exact h.congr (fun k => by
            change deningerMeyerStrongLogAutocorrelation u
                ((((k : ℤ) + 1 : ℤ) : ℝ) * Real.log (p : ℕ)) = _
            congr 2
            push_cast
            rfl)
        have hneg : Summable (fun k : ℕ =>
            deningerMeyerStrongLogAutocorrelation u
              (-((k + 1 : ℝ) * Real.log (p : ℕ)))) := by
          have hnegInt : Summable (fun m : ℤ =>
              deningerMeyerStrongLogAutocorrelation u
                ((m : ℝ) * Real.log (p : ℕ))) := hposNorm.of_norm
          have h := hnegInt.comp_injective
            (i := fun k : ℕ => -(k + 1 : ℤ))
            (by
              intro x y hxy
              have hsum : (x : ℤ) + 1 = (y : ℤ) + 1 := neg_injective hxy
              have hcast : (x : ℤ) = (y : ℤ) := add_right_cancel hsum
              exact_mod_cast hcast)
          exact h.congr (fun k => by
            change deningerMeyerStrongLogAutocorrelation u
                (((-((k : ℤ) + 1) : ℤ) : ℝ) * Real.log (p : ℕ)) = _
            congr 2
            push_cast
            ring)
        exact hpos.add hneg
      exact (hFsum.tsum_mul_left (Real.log (p : ℕ) : ℂ)).symm
    _ = ∑' pk : Nat.Primes × ℕ, H pk := hH.tsum_prod.symm
    _ = ∑' n : DeningerPrimePowerIndex,
        (deningerPrimePowerWeight n : ℂ) *
          F (deningerPrimePowerTime n) :=
      tsum_prime_iterate_eq_deningerPrimePower_vonMangoldt F
    _ = deningerVonMangoldtAutocorrelationCurrent u := by
      rfl

/-! ## Constructive two-bump sign wall -/

/-- Translation in the paper's convention `τ_c u(t) = u(t+c)`. -/
def deningerMeyerStrongLogTranslate
    (c : ℝ) (u : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  ⟨fun t => (u : ℝ → ℂ) (t + c), by
    rw [mem_deningerMeyerStrongLogTarget_iff]
    simpa only [sub_neg_eq_add] using u.property.translate (-c)⟩

@[simp]
theorem deningerMeyerStrongLogTranslate_apply
    (c : ℝ) (u : DeningerMeyerStrongLogTarget) (t : ℝ) :
    (deningerMeyerStrongLogTranslate c u : ℝ → ℂ) t =
      (u : ℝ → ℂ) (t + c) :=
  rfl

/-- Coherent and anti-coherent two-bump sources one period apart. -/
def deningerFloquetTwoBumpPlus
    (L : ℝ) (v : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  v + deningerMeyerStrongLogTranslate L v

def deningerFloquetTwoBumpMinus
    (L : ℝ) (v : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  v - deningerMeyerStrongLogTranslate L v

@[simp]
theorem deningerFloquetTwoBumpPlus_apply
    (L : ℝ) (v : DeningerMeyerStrongLogTarget) (t : ℝ) :
    (deningerFloquetTwoBumpPlus L v : ℝ → ℂ) t =
      (v : ℝ → ℂ) t + (v : ℝ → ℂ) (t + L) :=
  rfl

@[simp]
theorem deningerFloquetTwoBumpMinus_apply
    (L : ℝ) (v : DeningerMeyerStrongLogTarget) (t : ℝ) :
    (deningerFloquetTwoBumpMinus L v : ℝ → ℂ) t =
      (v : ℝ → ℂ) t - (v : ℝ → ℂ) (t + L) :=
  rfl

/-- Translation by one full circle period does not change periodization. -/
theorem deningerPrimeCirclePeriodization_translate_period
    (L : ℝ) (v : DeningerMeyerStrongLogTarget) (t : ℝ) :
    deningerPrimeCirclePeriodization L
        (deningerMeyerStrongLogTranslate L v) t =
      deningerPrimeCirclePeriodization L v t := by
  have hreindex := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun j : ℤ => (v : ℝ → ℂ) (t + (j : ℝ) * L))
  rw [deningerPrimeCirclePeriodization]
  calc
    (∑' j : ℤ, (v : ℝ → ℂ) (t + (j : ℝ) * L + L)) =
        ∑' j : ℤ, (v : ℝ → ℂ)
          (t + ((Equiv.addRight (1 : ℤ) j : ℤ) : ℝ) * L) := by
      apply tsum_congr
      intro j
      simp only [Equiv.coe_addRight]
      push_cast
      congr 1
      ring
    _ = ∑' j : ℤ, (v : ℝ → ℂ) (t + (j : ℝ) * L) := hreindex

/-- On the fundamental cell, the coherent two-bump periodization doubles exactly. -/
theorem deningerPrimeCirclePeriodization_twoBumpPlus
    {L : ℝ} (hL : 0 < L) (v : DeningerMeyerStrongLogTarget)
    {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    deningerPrimeCirclePeriodization L
        (deningerFloquetTwoBumpPlus L v) t =
      2 * deningerPrimeCirclePeriodization L v t := by
  have hv := summable_deningerPrimeCircle_translate v hL ht0 htL
  have hw := summable_deningerPrimeCircle_translate
    (deningerMeyerStrongLogTranslate L v) hL ht0 htL
  rw [deningerPrimeCirclePeriodization]
  change (∑' j : ℤ,
      ((v : ℝ → ℂ) (t + (j : ℝ) * L) +
        (deningerMeyerStrongLogTranslate L v : ℝ → ℂ)
          (t + (j : ℝ) * L))) = _
  rw [hv.tsum_add hw,
    ← deningerPrimeCirclePeriodization,
    ← deningerPrimeCirclePeriodization,
    deningerPrimeCirclePeriodization_translate_period]
  ring

/-- On the fundamental cell, the anti-coherent two-bump periodization vanishes exactly. -/
theorem deningerPrimeCirclePeriodization_twoBumpMinus
    {L : ℝ} (hL : 0 < L) (v : DeningerMeyerStrongLogTarget)
    {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    deningerPrimeCirclePeriodization L
        (deningerFloquetTwoBumpMinus L v) t = 0 := by
  have hv := summable_deningerPrimeCircle_translate v hL ht0 htL
  have hw := summable_deningerPrimeCircle_translate
    (deningerMeyerStrongLogTranslate L v) hL ht0 htL
  rw [deningerPrimeCirclePeriodization]
  change (∑' j : ℤ,
      ((v : ℝ → ℂ) (t + (j : ℝ) * L) -
        (deningerMeyerStrongLogTranslate L v : ℝ → ℂ)
          (t + (j : ℝ) * L))) = _
  rw [hv.tsum_sub hw,
    ← deningerPrimeCirclePeriodization,
    ← deningerPrimeCirclePeriodization,
    deningerPrimeCirclePeriodization_translate_period,
    sub_self]

/-- Coherent two-bump circle energy is four times base energy. -/
theorem deningerPrimeCircleEnergy_twoBumpPlus
    {L : ℝ} (hL : 0 < L) (v : DeningerMeyerStrongLogTarget) :
    deningerPrimeCircleEnergy L (deningerFloquetTwoBumpPlus L v) =
      4 * deningerPrimeCircleEnergy L v := by
  rw [deningerPrimeCircleEnergy, deningerPrimeCircleEnergy,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' := uIcc_of_le hL.le ▸ ht
  dsimp only
  rw [deningerPrimeCirclePeriodization_twoBumpPlus hL v ht'.1 ht'.2]
  simp only [map_mul, map_ofNat]
  ring

/-- Anti-coherent two-bump circle energy vanishes. -/
theorem deningerPrimeCircleEnergy_twoBumpMinus
    {L : ℝ} (hL : 0 < L) (v : DeningerMeyerStrongLogTarget) :
    deningerPrimeCircleEnergy L (deningerFloquetTwoBumpMinus L v) = 0 := by
  rw [deningerPrimeCircleEnergy]
  have hzero : (∫ t in (0 : ℝ)..L,
      deningerPrimeCirclePeriodization L (deningerFloquetTwoBumpMinus L v) t *
        (starRingEnd ℂ)
          (deningerPrimeCirclePeriodization L (deningerFloquetTwoBumpMinus L v) t)) =
      ∫ _t in (0 : ℝ)..L, (0 : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' := uIcc_of_le hL.le ▸ ht
    dsimp only
    rw [deningerPrimeCirclePeriodization_twoBumpMinus hL v ht'.1 ht'.2,
      map_zero, zero_mul]
  rw [hzero, intervalIntegral.integral_zero]

/-- Translation preserves the zero-lag autocorrelation mass. -/
theorem deningerMeyerStrongLogAutocorrelation_translate_zero
    (L : ℝ) (v : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogAutocorrelation
        (deningerMeyerStrongLogTranslate L v) 0 =
      deningerMeyerStrongLogAutocorrelation v 0 := by
  rw [deningerMeyerStrongLogAutocorrelation,
    deningerMeyerStrongLogAutocorrelation]
  simpa only [deningerMeyerStrongLogTranslate_apply, add_zero] using
    (integral_add_right_eq_self
      (fun x : ℝ => (v : ℝ → ℂ) x *
        (starRingEnd ℂ) ((v : ℝ → ℂ) x)) L)

/-- Disjoint one-period translates make both coherent signs have exactly twice the base mass. -/
theorem deningerMeyerStrongLogAutocorrelation_twoBump_zero
    {a b L : ℝ} (hL : 0 < L)
    (v : DeningerMeyerStrongLogTarget)
    (hsupport : Function.support (v : ℝ → ℂ) ⊆ Icc a b)
    (hshort : b - a < L) :
    deningerMeyerStrongLogAutocorrelation
        (deningerFloquetTwoBumpPlus L v) 0 =
        2 * deningerMeyerStrongLogAutocorrelation v 0 ∧
      deningerMeyerStrongLogAutocorrelation
        (deningerFloquetTwoBumpMinus L v) 0 =
        2 * deningerMeyerStrongLogAutocorrelation v 0 := by
  let w := deningerMeyerStrongLogTranslate L v
  have hdisjoint (x : ℝ) :
      (v : ℝ → ℂ) x = 0 ∨ (w : ℝ → ℂ) x = 0 := by
    by_contra hboth
    push_neg at hboth
    have hx := hsupport hboth.1
    have hy : x + L ∈ Icc a b := hsupport hboth.2
    linarith [hx.1, hx.2, hy.1, hy.2]
  have hvint :=
    integrable_deningerMeyerStrongLogAutocorrelationIntegrand v 0
  have hwint :=
    integrable_deningerMeyerStrongLogAutocorrelationIntegrand w 0
  have hdiag (sign : Bool) :
      (∫ x : ℝ,
        ((v : ℝ → ℂ) x + if sign then (w : ℝ → ℂ) x else -(w : ℝ → ℂ) x) *
          (starRingEnd ℂ)
            ((v : ℝ → ℂ) x + if sign then (w : ℝ → ℂ) x else -(w : ℝ → ℂ) x)) =
        deningerMeyerStrongLogAutocorrelation v 0 +
          deningerMeyerStrongLogAutocorrelation w 0 := by
    calc
      _ = ∫ x : ℝ,
          ((v : ℝ → ℂ) x * (starRingEnd ℂ) ((v : ℝ → ℂ) x) +
            (w : ℝ → ℂ) x * (starRingEnd ℂ) ((w : ℝ → ℂ) x)) := by
        apply integral_congr_ae
        filter_upwards with x
        rcases hdisjoint x with hx | hx <;>
          simp only [hx, map_zero, zero_mul, mul_zero, add_zero, zero_add,
            Bool.cond_eq_ite]
        all_goals split
        all_goals try simp only [map_neg]
        all_goals ring
      _ = deningerMeyerStrongLogAutocorrelation v 0 +
          deningerMeyerStrongLogAutocorrelation w 0 := by
        simp only [add_zero] at hvint hwint
        rw [integral_add hvint hwint]
        simp only [deningerMeyerStrongLogAutocorrelation, add_zero]
  constructor
  · rw [deningerMeyerStrongLogAutocorrelation]
    simp only [add_zero]
    change (∫ x : ℝ,
        ((v : ℝ → ℂ) x + (w : ℝ → ℂ) x) *
          (starRingEnd ℂ) ((v : ℝ → ℂ) x + (w : ℝ → ℂ) x)) = _
    rw [show (∫ x : ℝ,
        ((v : ℝ → ℂ) x + (w : ℝ → ℂ) x) *
          (starRingEnd ℂ) ((v : ℝ → ℂ) x + (w : ℝ → ℂ) x)) =
        deningerMeyerStrongLogAutocorrelation v 0 +
          deningerMeyerStrongLogAutocorrelation w 0 by
      simpa using hdiag true,
      deningerMeyerStrongLogAutocorrelation_translate_zero]
    ring
  · rw [deningerMeyerStrongLogAutocorrelation]
    simp only [add_zero]
    change (∫ x : ℝ,
        ((v : ℝ → ℂ) x - (w : ℝ → ℂ) x) *
          (starRingEnd ℂ) ((v : ℝ → ℂ) x - (w : ℝ → ℂ) x)) = _
    rw [show (∫ x : ℝ,
        ((v : ℝ → ℂ) x - (w : ℝ → ℂ) x) *
          (starRingEnd ℂ) ((v : ℝ → ℂ) x - (w : ℝ → ℂ) x)) =
        deningerMeyerStrongLogAutocorrelation v 0 +
          deningerMeyerStrongLogAutocorrelation w 0 by
      simpa [sub_eq_add_neg] using hdiag false,
      deningerMeyerStrongLogAutocorrelation_translate_zero]
    ring

end

end RHTower
