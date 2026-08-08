import GaloisForLFunctions.RHTower.DeningerMertensAdiabaticCorner
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogTarget
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogMellin
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
    simp only [abs_of_pos hL, abs_inv, inv_inv]
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hcells := hw.hasSum_intervalIntegral 0
  rw [htotal] at hcells
  apply hcells.congr_fun
  intro j
  simp only [zero_add, w, intervalIntegral.integral_smul]
  rw [intervalIntegral.smul_integral_comp_mul_left]
  congr 1 <;> ring

end

end RHTower
