import GaloisForLFunctions.HTGeometry.GammaHalfPoleClearing
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.HTGeometry.BochnerLaplaceHolomorphy
import GaloisForLFunctions.HTGeometry.CausalLaplaceDelay
import GaloisForLFunctions.RHTower.ZetaPoleHalfCausalSource
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Full arithmetic Laplace transform of the pole-cleared zeta half

The exponentially damped, floor-cutoff source is exactly the locally finite sum
of its arithmetic translates. Summability of the integrals of the atom norms
justifies the infinite sum/integral exchange and identifies the original branch.
Its transform is analytic in the open initial half-plane and its square is the
shifted pole-cleared zeta function divided by the square of the original variable.

Absolute convergence of the positive half-Dirichlet series holds precisely to
the right of one. Consequently termwise absolute integration of this atom family
cannot justify continuation past that line; cancellation in the complete summed
source is a separate requirement.
-/

open MeasureTheory Set
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

private theorem half_coeff_real (n : ℕ) :
    ((zetaBinomialHalf n).re : ℂ) = zetaBinomialHalf n := by
  apply Complex.ext <;> simp [zetaBinomialHalf_apply_im]

private theorem pole_kernel_zero : poleClearedHalfKernel 0 = 0 := by
  simp [poleClearedHalfKernel, poleHalfKernel, Real.zero_rpow (by norm_num : -(1 : ℝ)/2 ≠ 0)]

private theorem damped_nonpos {t : ℝ} (ht : t ≤ 0) : dampedPoleHalfCausal t = 0 := by
  exact indicator_of_notMem (not_lt.mpr ht) _

private theorem damped_nonneg {t : ℝ} (ht : 0 ≤ t) :
    dampedPoleHalfCausal t = (Complex.Gamma (1/2 : ℂ))⁻¹ *
      Complex.exp (-(3*(t : ℂ))) * (poleClearedHalfKernel t : ℂ) := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp [damped_nonpos (le_refl 0), pole_kernel_zero]
  · exact indicator_of_mem ht _

private theorem half_term_exp (n : ℕ) (s : ℂ) :
    LSeries.term zetaBinomialHalf s n =
      zetaBinomialHalf n * Complex.exp (-(s * (Real.log n : ℂ))) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnR.le).symm
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
    hlog, div_eq_mul_inv, ← Complex.exp_neg]
  congr 2
  ring

def zetaPoleHalfDampedAtom (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term zetaBinomialHalf 3 n * dampedPoleHalfCausal (t - Real.log n)

def zetaPoleHalfDampedSource (t : ℝ) : ℂ :=
  (Complex.Gamma (1/2 : ℂ))⁻¹ * Complex.exp (-(3*(t : ℂ))) *
    (zetaPoleHalfCausalSource t : ℂ)

theorem zetaPoleHalfDampedAtom_zero_outside (n : ℕ) (t : ℝ)
    (hn : n ∉ Finset.Icc 1 ⌊Real.exp t⌋₊) : zetaPoleHalfDampedAtom n t = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [zetaPoleHalfDampedAtom]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hgt : ⌊Real.exp t⌋₊ < n := by simpa [Finset.mem_Icc, hn1] using hn
  have hlog : t < Real.log n :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast Nat.pos_of_ne_zero hn0)).mpr
      ((Nat.floor_lt (Real.exp_pos t).le).mp hgt)
  rw [zetaPoleHalfDampedAtom, damped_nonpos (by linarith), mul_zero]

theorem zetaPoleHalfDampedAtom_eq (n : ℕ) (t : ℝ)
    (hn : n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊) :
    zetaPoleHalfDampedAtom n t =
      (Complex.Gamma (1/2 : ℂ))⁻¹ * Complex.exp (-(3*(t : ℂ))) *
        ((zetaBinomialHalf n).re * poleClearedHalfKernel (t - Real.log n) : ℝ) := by
  obtain ⟨hn1, hnt⟩ := Finset.mem_Icc.mp hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
  have ht : 0 ≤ t - Real.log n := sub_nonneg.mpr <|
    (Real.log_le_iff_le_exp hnp).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hnt)
  rw [zetaPoleHalfDampedAtom, half_term_exp, damped_nonneg ht]
  rw [Complex.ofReal_mul, half_coeff_real]
  have he : Complex.exp (-(3 * (Real.log n : ℂ))) *
      Complex.exp (-(3*((t - Real.log n : ℝ) : ℂ))) =
        Complex.exp (-(3*(t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    rw [Complex.ofReal_sub]
    ring
  calc
    _ = (Complex.Gamma (1/2 : ℂ))⁻¹ *
        (Complex.exp (-(3 * (Real.log n : ℂ))) *
          Complex.exp (-(3*((t - Real.log n : ℝ) : ℂ)))) *
        (zetaBinomialHalf n * (poleClearedHalfKernel (t - Real.log n) : ℂ)) := by ring
    _ = _ := by rw [he]

theorem zetaPoleHalfDampedSource_eq_tsum (t : ℝ) :
    zetaPoleHalfDampedSource t = ∑' n, zetaPoleHalfDampedAtom n t := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp t⌋₊)
    (fun n hn => zetaPoleHalfDampedAtom_zero_outside n t hn)]
  unfold zetaPoleHalfDampedSource zetaPoleHalfCausalSource
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n hn => by
    simpa only [Complex.ofReal_mul] using (zetaPoleHalfDampedAtom_eq n t hn).symm)

theorem zetaPoleHalfDampedAtom_integrable (n : ℕ) :
    Integrable (zetaPoleHalfDampedAtom n) := by
  unfold zetaPoleHalfDampedAtom
  simpa only [sub_eq_add_neg] using
    (dampedPoleHalfCausal_integrable.comp_add_right (-Real.log n)).const_mul
      (LSeries.term zetaBinomialHalf 3 n)

theorem integral_norm_zetaPoleHalfDampedAtom (n : ℕ) :
    (∫ t, ‖zetaPoleHalfDampedAtom n t‖) =
      ‖LSeries.term zetaBinomialHalf 3 n‖ * ∫ t, ‖dampedPoleHalfCausal t‖ := by
  simp only [zetaPoleHalfDampedAtom, norm_mul, integral_const_mul, sub_eq_add_neg]
  rw [integral_add_right_eq_self (fun t : ℝ => ‖dampedPoleHalfCausal t‖) (-Real.log n)]

theorem summable_integral_norm_zetaPoleHalfDampedAtom :
    Summable (fun n => ∫ t, ‖zetaPoleHalfDampedAtom n t‖) := by
  simp_rw [integral_norm_zetaPoleHalfDampedAtom]
  exact (LSeriesSummable_zetaBinomialHalf (by norm_num : 1 < (3 : ℂ).re)).norm.mul_right _

theorem zetaPoleHalfDampedSource_integrable : Integrable zetaPoleHalfDampedSource := by
  simp_rw [show zetaPoleHalfDampedSource = (fun t => ∑' n, zetaPoleHalfDampedAtom n t)
    from funext zetaPoleHalfDampedSource_eq_tsum]
  exact integrable_tsum_of_summable_integral_norm zetaPoleHalfDampedAtom_integrable
    summable_integral_norm_zetaPoleHalfDampedAtom

theorem zetaPoleHalfDampedSource_nonpos {t : ℝ} (ht : t ≤ 0) :
    zetaPoleHalfDampedSource t = 0 := by
  rw [zetaPoleHalfDampedSource_eq_tsum]
  have hzero (n : ℕ) : zetaPoleHalfDampedAtom n t = 0 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [zetaPoleHalfDampedAtom]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    rw [zetaPoleHalfDampedAtom, damped_nonpos (sub_nonpos.mpr (ht.trans (Real.log_nonneg hnR))),
      mul_zero]
  simp only [hzero, tsum_zero]

private theorem laplace_source_eq_bochner :
    (fun s => causalComplexLaplace s zetaPoleHalfDampedSource) =
      bochnerLaplaceRay zetaPoleHalfDampedSource := by
  funext s
  unfold causalComplexLaplace bochnerLaplaceRay
  simp only [expRay, smul_eq_mul, causalComplexLaplaceWeight]
  exact (causal_integral_ray _ (fun t ht => by
    rw [zetaPoleHalfDampedSource_nonpos ht.le, mul_zero])).symm

theorem causalComplexLaplace_zetaPoleHalfDampedSource_analyticOnNhd :
    AnalyticOnNhd ℂ (fun s => causalComplexLaplace s zetaPoleHalfDampedSource)
      {s : ℂ | 0 < s.re} := by
  rw [laplace_source_eq_bochner]
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply bochnerLaplaceRay_differentiableAt zetaPoleHalfDampedSource_integrable.aestronglyMeasurable
      (c := 0) ?_ s hs
    simpa only [expRay, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_smul]
      using zetaPoleHalfDampedSource_integrable.integrableOn (s := Ioi 0)
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem LSeriesSummable_zetaBinomialHalf_iff {s : ℂ} :
    LSeriesSummable zetaBinomialHalf s ↔ 1 < s.re := by
  refine ⟨fun hs => ?_, LSeriesSummable_zetaBinomialHalf⟩
  have h := ArithmeticFunction.LSeriesSummable_mul hs hs
  rw [zetaBinomialHalf_mul_self] at h
  exact ArithmeticFunction.LSeriesSummable_zeta_iff.mp h

theorem laplaceWeight_zetaPoleHalfDampedAtom (s : ℂ) (n : ℕ) (t : ℝ) :
    causalComplexLaplaceWeight s (zetaPoleHalfDampedAtom n) t =
      LSeries.term zetaBinomialHalf (s+3) n *
        causalComplexLaplaceWeight s dampedPoleHalfCausal (t - Real.log n) := by
  simp only [causalComplexLaplaceWeight, zetaPoleHalfDampedAtom, half_term_exp]
  have he : Complex.exp (-(s * (t : ℂ))) * Complex.exp (-(3 * (Real.log n : ℂ))) =
      Complex.exp (-((s+3) * (Real.log n : ℂ))) *
        Complex.exp (-(s * ((t - Real.log n : ℝ) : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Complex.ofReal_sub]
    ring
  calc
    _ = (Complex.exp (-(s * (t : ℂ))) * Complex.exp (-(3 * (Real.log n : ℂ)))) *
        (zetaBinomialHalf n * dampedPoleHalfCausal (t - Real.log n)) := by ring
    _ = _ := by rw [he]; ring

theorem laplaceWeight_zetaPoleHalfDampedAtom_integrable {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    Integrable (causalComplexLaplaceWeight s (zetaPoleHalfDampedAtom n)) := by
  have hD := causalComplexLaplaceWeight_integrable hs dampedPoleHalfCausal_integrable
    (fun t ht => damped_nonpos ht)
  have h := (hD.comp_add_right (-Real.log n)).const_mul (LSeries.term zetaBinomialHalf (s+3) n)
  have he := funext (laplaceWeight_zetaPoleHalfDampedAtom s n)
  rw [he]
  simpa only [sub_eq_add_neg] using h

theorem integral_norm_laplaceWeight_zetaPoleHalfDampedAtom (s : ℂ) (n : ℕ) :
    (∫ t, ‖causalComplexLaplaceWeight s (zetaPoleHalfDampedAtom n) t‖) =
      ‖LSeries.term zetaBinomialHalf (s+3) n‖ *
        ∫ t, ‖causalComplexLaplaceWeight s dampedPoleHalfCausal t‖ := by
  simp_rw [laplaceWeight_zetaPoleHalfDampedAtom, norm_mul]
  rw [integral_const_mul]
  simp only [sub_eq_add_neg]
  rw [integral_add_right_eq_self
    (fun t : ℝ => ‖causalComplexLaplaceWeight s dampedPoleHalfCausal t‖) (-Real.log n)]

theorem summable_integral_norm_laplaceWeight_zetaPoleHalfDampedAtom {s : ℂ}
    (hs : 0 ≤ s.re) :
    Summable (fun n => ∫ t, ‖causalComplexLaplaceWeight s (zetaPoleHalfDampedAtom n) t‖) := by
  simp_rw [integral_norm_laplaceWeight_zetaPoleHalfDampedAtom]
  exact (LSeriesSummable_zetaBinomialHalf (by simpa using (show 1 < s.re + 3 by linarith))).norm.mul_right _

theorem causalComplexLaplace_zetaPoleHalfDampedSource {s : ℂ} (hs : 0 ≤ s.re) :
    causalComplexLaplace s zetaPoleHalfDampedSource =
      LSeries zetaBinomialHalf (s+3) * causalComplexLaplace s dampedPoleHalfCausal := by
  have he (t : ℝ) : causalComplexLaplaceWeight s zetaPoleHalfDampedSource t =
      ∑' n, causalComplexLaplaceWeight s (zetaPoleHalfDampedAtom n) t := by
    simp only [causalComplexLaplaceWeight, zetaPoleHalfDampedSource_eq_tsum, tsum_mul_left]
  unfold causalComplexLaplace
  simp_rw [he]
  rw [← integral_tsum_of_summable_integral_norm
    (laplaceWeight_zetaPoleHalfDampedAtom_integrable hs)
    (summable_integral_norm_laplaceWeight_zetaPoleHalfDampedAtom hs)]
  have hi (n : ℕ) :
      (∫ t, causalComplexLaplaceWeight s (zetaPoleHalfDampedAtom n) t) =
        LSeries.term zetaBinomialHalf (s+3) n *
          ∫ t, causalComplexLaplaceWeight s dampedPoleHalfCausal t := by
    simp_rw [laplaceWeight_zetaPoleHalfDampedAtom]
    rw [integral_const_mul]
    simp only [sub_eq_add_neg]
    rw [integral_add_right_eq_self (causalComplexLaplaceWeight s dampedPoleHalfCausal) (-Real.log n)]
  simp_rw [hi, tsum_mul_right]
  rfl

theorem causalComplexLaplace_zetaPoleHalfDampedSource_sq {s : ℂ} (hs : 0 ≤ s.re) :
    causalComplexLaplace s zetaPoleHalfDampedSource ^ 2 =
      riemannZeta (s+3) * ((s+2)/(s+3)^(2 : ℕ)) := by
  rw [causalComplexLaplace_zetaPoleHalfDampedSource hs, mul_pow,
    dampedPoleHalfCausal_laplace_sq hs]
  have hr : 1 < (s+3).re := by simpa using (show 1 < s.re + 3 by linarith)
  have hb := LSeriesSummable_zetaBinomialHalf hr
  have hz := ArithmeticFunction.LSeries_mul' hb hb
  rw [zetaBinomialHalf_mul_self] at hz
  rw [pow_two, ← hz]
  congr 1
  exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta hr

private theorem damped_not_ae_zero : ¬ dampedPoleHalfCausal =ᵐ[volume] 0 := by
  intro hz
  have hi : causalComplexLaplace 0 dampedPoleHalfCausal = 0 := by
    simp only [causalComplexLaplace, causalComplexLaplaceWeight, zero_mul, neg_zero,
      Complex.exp_zero, one_mul]
    rw [integral_congr_ae hz]
    simp
  have h := dampedPoleHalfCausal_laplace_sq (s := 0) (by norm_num)
  rw [hi] at h
  norm_num at h

private theorem weighted_damped_norm_pos (s : ℂ)
    (hi : Integrable (causalComplexLaplaceWeight s dampedPoleHalfCausal)) :
    0 < ∫ t, ‖causalComplexLaplaceWeight s dampedPoleHalfCausal t‖ := by
  apply lt_of_le_of_ne (integral_nonneg (fun _ => norm_nonneg _))
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg (fun t => norm_nonneg
    (causalComplexLaplaceWeight s dampedPoleHalfCausal t)) hi.norm).mp hz.symm
  apply damped_not_ae_zero
  filter_upwards [he] with t ht
  have hzero := norm_eq_zero.mp ht
  exact (mul_eq_zero.mp hzero).resolve_left (Complex.exp_ne_zero _)

/-- Termwise absolute integration of the full arithmetic atom family forces the
original Dirichlet variable to remain strictly to the right of one. -/
theorem zetaPoleHalfDampedAtom_absolute_interchange_requires (s : ℂ)
    (hi : ∀ n, Integrable (causalComplexLaplaceWeight s (zetaPoleHalfDampedAtom n)))
    (hs : Summable (fun n => ∫ t, ‖causalComplexLaplaceWeight s (zetaPoleHalfDampedAtom n) t‖)) :
    1 < (s+3).re := by
  have hone : zetaPoleHalfDampedAtom 1 = dampedPoleHalfCausal := by
    funext t
    simp [zetaPoleHalfDampedAtom, LSeries.term_of_ne_zero]
  have hD := hi 1
  rw [hone] at hD
  have hpos := weighted_damped_norm_pos s hD
  simp_rw [integral_norm_laplaceWeight_zetaPoleHalfDampedAtom] at hs
  have hcoeff := (summable_mul_right_iff hpos.ne').mp hs
  exact LSeriesSummable_zetaBinomialHalf_iff.mp (summable_norm_iff.mp hcoeff)

theorem zetaPoleHalfDampedAtom_no_absolute_interchange_twoThirds :
    ¬ ((∀ n, Integrable (causalComplexLaplaceWeight (-7/3) (zetaPoleHalfDampedAtom n))) ∧
      Summable (fun n => ∫ t, ‖causalComplexLaplaceWeight (-7/3) (zetaPoleHalfDampedAtom n) t‖)) := by
  rintro ⟨hi, hs⟩
  have h := zetaPoleHalfDampedAtom_absolute_interchange_requires (-7/3) hi hs
  norm_num at h

end RHTower
