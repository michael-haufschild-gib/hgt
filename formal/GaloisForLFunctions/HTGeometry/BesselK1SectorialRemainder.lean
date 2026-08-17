import GaloisForLFunctions.HTGeometry.BesselK1RayHolomorphy
import GaloisForLFunctions.HTGeometry.ComplexBinomialHalfPlane

/-!
# The sectorial remainder of the order-one Schläfli asymptotic

On the ray form the binomial argument `u/(2z)` has nonnegative real part whenever the spectral
parameter does, so the half-plane binomial remainder applies with no restriction on its size.  The
resulting expansion has a remainder controlled by the *modulus* of the spectral parameter, which is
what an asymptotic along a direction approaching the imaginary axis requires.
-/

open MeasureTheory Set Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section GammaMoments

/-- The real integrand of the ray moments. -/
def rayMomentIntegrand (k : ℕ) (u : ℝ) : ℝ := Real.exp (-u) / Real.sqrt u * u ^ k

theorem rayMomentIntegrand_eq {k : ℕ} {u : ℝ} (hu : 0 < u) :
    rayMomentIntegrand k u = Real.exp (-u) * u ^ (((k : ℝ) + 1 / 2) - 1) := by
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu
  have hexp : u ^ (((k : ℝ) + 1 / 2) - 1) = u ^ (k : ℕ) * u ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast u k, ← Real.rpow_add hu]
    congr 1
    ring
  have hhalf : u ^ (-(1 / 2 : ℝ)) = (Real.sqrt u)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hu.le]
  rw [rayMomentIntegrand, hexp, hhalf]
  ring

theorem integrableOn_rayMomentIntegrand (k : ℕ) :
    IntegrableOn (rayMomentIntegrand k) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (k : ℝ) + 1 / 2) (by positivity)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro u hu
  exact (rayMomentIntegrand_eq (k := k) hu).symm

theorem integral_rayMomentIntegrand (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), rayMomentIntegrand k u = Real.Gamma ((k : ℝ) + 1 / 2) := by
  rw [Real.Gamma_eq_integral (by positivity)]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu => rayMomentIntegrand_eq (k := k) hu

theorem rayMomentIntegrand_nonneg (k : ℕ) {u : ℝ} (hu : 0 < u) : 0 ≤ rayMomentIntegrand k u := by
  rw [rayMomentIntegrand]
  positivity

end GammaMoments

section Expansion

/-- The coefficients of the ray expansion. -/
def rayCoeff (k : ℕ) : ℝ :=
  (2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k) * Real.Gamma ((k : ℝ) + 1 / 2)

/-- The integrand of the ray remainder at order `m`. -/
def rayRemIntegrand (m : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ)
    * (2 * cbinomRem (1 / 2) m ((u : ℂ) / (2 * z))
      - cbinomRem (-1 / 2) m ((u : ℂ) / (2 * z)))

theorem besselK1RayIntegrand_split (m : ℕ) (z : ℂ) (u : ℝ) :
    besselK1RayIntegrand z u
      = rayRemIntegrand m z u
        + ∑ k ∈ Finset.range m,
            ((2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k : ℝ) : ℂ)
              * ((rayMomentIntegrand k u : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k := by
  have hmom : ∀ k : ℕ, ((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ) * ((u : ℂ) / (2 * z)) ^ k
      = ((rayMomentIntegrand k u : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k := by
    intro k
    rw [rayMomentIntegrand]
    push_cast
    ring
  have hA : rayShellPow z u (1 / 2)
      = cbinomRem (1 / 2) m ((u : ℂ) / (2 * z))
        + ∑ k ∈ Finset.range m, ((cbinomCoeff (1 / 2) k : ℝ) : ℂ) * ((u : ℂ) / (2 * z)) ^ k := by
    rw [cbinomRem, rayShellPow]
    ring
  have hB : rayShellPow z u (-1 / 2)
      = cbinomRem (-1 / 2) m ((u : ℂ) / (2 * z))
        + ∑ k ∈ Finset.range m, ((cbinomCoeff (-1 / 2) k : ℝ) : ℂ) * ((u : ℂ) / (2 * z)) ^ k := by
    rw [cbinomRem, rayShellPow]
    ring
  have hkey : ∑ k ∈ Finset.range m,
      ((2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k : ℝ) : ℂ)
        * ((rayMomentIntegrand k u : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k
      = ((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ)
        * (2 * (∑ k ∈ Finset.range m,
              ((cbinomCoeff (1 / 2) k : ℝ) : ℂ) * ((u : ℂ) / (2 * z)) ^ k)
          - ∑ k ∈ Finset.range m,
              ((cbinomCoeff (-1 / 2) k : ℝ) : ℂ) * ((u : ℂ) / (2 * z)) ^ k) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← hmom k]
    push_cast
    ring
  rw [hkey, besselK1RayIntegrand, rayRemIntegrand, hA, hB]
  ring

theorem integrableOn_rayPolyTerm (k : ℕ) (c : ℝ) (w : ℂ) :
    IntegrableOn (fun u : ℝ => ((c : ℝ) : ℂ) * ((rayMomentIntegrand k u : ℝ) : ℂ) * w ^ k)
      (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => ((rayMomentIntegrand k u : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_rayMomentIntegrand k).ofReal
  have h2 : IntegrableOn
      (fun u : ℝ => (((c : ℝ) : ℂ) * w ^ k) * ((rayMomentIntegrand k u : ℝ) : ℂ)) (Ioi 0) :=
    h.const_mul _
  refine h2.congr_fun ?_ measurableSet_Ioi
  intro u _
  ring

theorem integral_rayPolyTerm (k : ℕ) (c : ℝ) (w : ℂ) :
    (∫ u in Ioi (0 : ℝ), ((c : ℝ) : ℂ) * ((rayMomentIntegrand k u : ℝ) : ℂ) * w ^ k)
      = ((c : ℝ) : ℂ) * ((Real.Gamma ((k : ℝ) + 1 / 2) : ℝ) : ℂ) * w ^ k := by
  have h : (∫ u in Ioi (0 : ℝ), ((rayMomentIntegrand k u : ℝ) : ℂ))
      = ((Real.Gamma ((k : ℝ) + 1 / 2) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_rayMomentIntegrand]
  have hfun : (fun u : ℝ => ((c : ℝ) : ℂ) * ((rayMomentIntegrand k u : ℝ) : ℂ) * w ^ k)
      = fun u : ℝ => (((c : ℝ) : ℂ) * w ^ k) * ((rayMomentIntegrand k u : ℝ) : ℂ) := by
    funext u
    ring
  rw [hfun, MeasureTheory.integral_const_mul, h]
  ring

theorem integrableOn_rayRemIntegrand (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (rayRemIntegrand m z) (Ioi 0) := by
  have hsplit := integrableOn_besselK1RayIntegrand hz
  have hpoly : IntegrableOn (fun u : ℝ => ∑ k ∈ Finset.range m,
      ((2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k : ℝ) : ℂ)
        * ((rayMomentIntegrand k u : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k) (Ioi 0) :=
    integrable_finsetSum _ fun k _ =>
      integrableOn_rayPolyTerm k (2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k) ((2 * z)⁻¹)
  have hdiff := hsplit.sub hpoly
  refine hdiff.congr_fun ?_ measurableSet_Ioi
  intro u _
  dsimp only [Pi.sub_apply]
  rw [besselK1RayIntegrand_split m z u]
  ring

/-- **The ray expansion with its remainder**, on the right half plane. -/
theorem besselK1Ray_eq_sum_add_rem (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    besselK1Ray z
      = (∑ k ∈ Finset.range m, ((rayCoeff k : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k)
        + ∫ u in Ioi (0 : ℝ), rayRemIntegrand m z u := by
  have hpolyint : ∀ k ∈ Finset.range m, IntegrableOn
      (fun u : ℝ => ((2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k : ℝ) : ℂ)
        * ((rayMomentIntegrand k u : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k) (Ioi 0) :=
    fun k _ => integrableOn_rayPolyTerm k _ _
  have hpoly : IntegrableOn (fun u : ℝ => ∑ k ∈ Finset.range m,
      ((2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k : ℝ) : ℂ)
        * ((rayMomentIntegrand k u : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k) (Ioi 0) :=
    integrable_finsetSum _ hpolyint
  have hsplit : besselK1Ray z
      = (∫ u in Ioi (0 : ℝ), rayRemIntegrand m z u)
        + ∫ u in Ioi (0 : ℝ), ∑ k ∈ Finset.range m,
            ((2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k : ℝ) : ℂ)
              * ((rayMomentIntegrand k u : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k := by
    rw [besselK1Ray, ← MeasureTheory.integral_add (integrableOn_rayRemIntegrand m hz) hpoly]
    exact setIntegral_congr_fun measurableSet_Ioi
      fun u _ => besselK1RayIntegrand_split m z u
  rw [hsplit, MeasureTheory.integral_finsetSum _ hpolyint]
  have hterms : ∀ k ∈ Finset.range m,
      (∫ u in Ioi (0 : ℝ), ((2 * cbinomCoeff (1 / 2) k - cbinomCoeff (-1 / 2) k : ℝ) : ℂ)
        * ((rayMomentIntegrand k u : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k)
      = ((rayCoeff k : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k := by
    intro k _
    rw [integral_rayPolyTerm k _ _, rayCoeff]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterms]
  ring

end Expansion

section RemainderBound

theorem norm_rayFrac (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖(u : ℂ) / (2 * z)‖ = u / (2 * ‖z‖) := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  simp

/-- The shell-free constant of the ray remainder. -/
def rayRemConst (m : ℕ) : ℝ :=
  (2 * cbinomHalfCoeff (1 / 2) m + cbinomHalfCoeff (-1 / 2) m) * Real.Gamma ((m : ℝ) + 1 / 2)

theorem rayRemConst_nonneg (m : ℕ) : 0 ≤ rayRemConst m := by
  refine mul_nonneg ?_ (Real.Gamma_nonneg_of_nonneg (by positivity))
  have h1 := cbinomHalfCoeff_nonneg (1 / 2 : ℝ) m
  have h2 := cbinomHalfCoeff_nonneg (-1 / 2 : ℝ) m
  linarith

theorem norm_rayRemIntegrand_le (m : ℕ) {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 < u) :
    ‖rayRemIntegrand (m + 1) z u‖
      ≤ (2 * cbinomHalfCoeff (1 / 2) (m + 1) + cbinomHalfCoeff (-1 / 2) (m + 1))
        * (rayMomentIntegrand (m + 1) u / (2 * ‖z‖) ^ (m + 1)) := by
  have hre := re_ray_frac_nonneg hz hu.le
  have hA := norm_cbinomRem_succ_le_of_re_nonneg (α := (1 / 2 : ℝ)) (by norm_num) m hre
  have hB := norm_cbinomRem_le_of_re_nonneg (α := (-1 / 2 : ℝ)) (by norm_num) (m + 1) hre
  have hnorm := norm_rayFrac z hu.le
  rw [hnorm] at hA hB
  have hcoef : ‖((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ)‖ = Real.exp (-u) / Real.sqrt u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [rayRemIntegrand, norm_mul, hcoef]
  have hstep : ‖2 * cbinomRem (1 / 2) (m + 1) ((u : ℂ) / (2 * z))
      - cbinomRem (-1 / 2) (m + 1) ((u : ℂ) / (2 * z))‖
      ≤ (2 * cbinomHalfCoeff (1 / 2) (m + 1) + cbinomHalfCoeff (-1 / 2) (m + 1))
        * (u / (2 * ‖z‖)) ^ (m + 1) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
    nlinarith [hA, hB]
  refine le_trans (mul_le_mul_of_nonneg_left hstep (by positivity)) (le_of_eq ?_)
  rw [rayMomentIntegrand, div_pow]
  ring

theorem integrableOn_rayRemMajorant (m : ℕ) (z : ℂ) :
    IntegrableOn (fun u : ℝ =>
      (2 * cbinomHalfCoeff (1 / 2) (m + 1) + cbinomHalfCoeff (-1 / 2) (m + 1))
        * (rayMomentIntegrand (m + 1) u / (2 * ‖z‖) ^ (m + 1))) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ =>
      ((2 * cbinomHalfCoeff (1 / 2) (m + 1) + cbinomHalfCoeff (-1 / 2) (m + 1))
        / (2 * ‖z‖) ^ (m + 1)) * rayMomentIntegrand (m + 1) u) (Ioi 0) :=
    (integrableOn_rayMomentIntegrand (m + 1)).const_mul _
  refine h.congr_fun ?_ measurableSet_Ioi
  intro u _
  ring

/-- **The ray remainder is controlled by the modulus of the spectral parameter.** -/
theorem norm_integral_rayRem_le (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ‖∫ u in Ioi (0 : ℝ), rayRemIntegrand (m + 1) z u‖
      ≤ rayRemConst (m + 1) / (2 * ‖z‖) ^ (m + 1) := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hmono : (∫ u in Ioi (0 : ℝ), ‖rayRemIntegrand (m + 1) z u‖)
      ≤ ∫ u in Ioi (0 : ℝ),
          (2 * cbinomHalfCoeff (1 / 2) (m + 1) + cbinomHalfCoeff (-1 / 2) (m + 1))
            * (rayMomentIntegrand (m + 1) u / (2 * ‖z‖) ^ (m + 1)) := by
    refine setIntegral_mono_on ((integrableOn_rayRemIntegrand (m + 1) hz).norm)
      (integrableOn_rayRemMajorant m z) measurableSet_Ioi ?_
    intro u hu
    exact norm_rayRemIntegrand_le m hz hu
  refine le_trans hmono (le_of_eq ?_)
  have hfun : (fun u : ℝ =>
      (2 * cbinomHalfCoeff (1 / 2) (m + 1) + cbinomHalfCoeff (-1 / 2) (m + 1))
        * (rayMomentIntegrand (m + 1) u / (2 * ‖z‖) ^ (m + 1)))
      = fun u : ℝ => ((2 * cbinomHalfCoeff (1 / 2) (m + 1) + cbinomHalfCoeff (-1 / 2) (m + 1))
        / (2 * ‖z‖) ^ (m + 1)) * rayMomentIntegrand (m + 1) u := by
    funext u
    ring
  rw [hfun, MeasureTheory.integral_const_mul, integral_rayMomentIntegrand, rayRemConst]
  push_cast
  ring

end RemainderBound

section Sectorial

/-- **The order-one Schläfli asymptotic with a modulus remainder, at every order.** -/
theorem norm_besselK1C_sub_raySum_le (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ‖_root_.HTGeometry.besselK1C z
        - Complex.exp (-z) * ((((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹
          * ∑ k ∈ Finset.range (m + 1), ((rayCoeff k : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k)‖
      ≤ Real.exp (-z.re) * ((2 * ‖z‖) ^ ((1 : ℝ) / 2))⁻¹
        * (rayRemConst (m + 1) / (2 * ‖z‖) ^ (m + 1)) := by
  have hrep := besselK1C_eq_ray hz
  rw [besselK1Ray_eq_sum_add_rem (m + 1) hz] at hrep
  have hsub : _root_.HTGeometry.besselK1C z
      - Complex.exp (-z) * ((((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹
        * ∑ k ∈ Finset.range (m + 1), ((rayCoeff k : ℝ) : ℂ) * ((2 * z)⁻¹) ^ k)
      = Complex.exp (-z) * ((((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹
        * ∫ u in Ioi (0 : ℝ), rayRemIntegrand (m + 1) z u) := by
    rw [hrep]
    ring
  have hnormexp : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    rw [Complex.norm_exp]
    simp
  have hnormpow : ‖((((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹)‖
      = ((2 * ‖z‖) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [norm_inv, Complex.norm_cpow_real, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
  rw [hsub, norm_mul, norm_mul, hnormexp, hnormpow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (norm_integral_rayRem_le m hz) (by positivity)

end Sectorial

end

end GaloisForLFunctions.HTGeometry
