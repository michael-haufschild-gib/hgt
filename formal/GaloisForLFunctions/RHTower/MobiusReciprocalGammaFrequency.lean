import GaloisForLFunctions.RHTower.MobiusReciprocalPrimitiveRatio
import GaloisForLFunctions.RHTower.GammaEulerPhysicalConnector

/-!
# Gamma frequency representation of the reciprocal Möbius moment

The normalized Gamma height density has an exact hyperbolic characteristic
function. This module identifies the homogeneous reciprocal kernel with that
characteristic function and proves an exact finite Möbius-polynomial norm
identity. It supplies no uniform arithmetic bound on that norm.
-/

open Finset Complex MeasureTheory
open scoped ComplexConjugate
namespace RHTower
noncomputable section

private theorem exp_half_log_eq_sqrt_real {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf

/-- Hyperbolic distance of two positive indices in multiplicative coordinates. -/
theorem two_cosh_log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * Real.cosh ((Real.log x - Real.log y) / 2) =
      (x + y) / (Real.sqrt x * Real.sqrt y) := by
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hsy : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hy)
  have hxsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hysq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  have he : Real.exp ((Real.log x - Real.log y) / 2) =
      Real.sqrt x / Real.sqrt y := by
    rw [show (Real.log x - Real.log y) / 2 =
      Real.log x / 2 - Real.log y / 2 by ring,
      Real.exp_sub, exp_half_log_eq_sqrt_real hx, exp_half_log_eq_sqrt_real hy]
  rw [Real.cosh_eq, Real.exp_neg, he]
  field_simp
  nlinarith

/-- A homogeneous additive kernel is a power of the logarithmic-ratio cosine. -/
theorem ratio_kernel_eq_cosh {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (p : ℝ) :
    (x * y) ^ (p / 2) / (x + y) ^ p =
      (2 : ℝ) ^ (-p) *
        Real.cosh ((Real.log x - Real.log y) / 2) ^ (-p) := by
  have hxy : 0 ≤ x * y := (mul_pos hx hy).le
  have hsxy : 0 ≤ Real.sqrt x * Real.sqrt y :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum : 0 ≤ x + y := (add_pos hx hy).le
  calc
    (x * y) ^ (p / 2) / (x + y) ^ p =
        ((Real.sqrt x * Real.sqrt y) / (x + y)) ^ p := by
          rw [Real.rpow_div_two_eq_sqrt p hxy,
            Real.sqrt_mul hx.le y, Real.div_rpow hsxy hsum]
    _ = (((x + y) / (Real.sqrt x * Real.sqrt y))⁻¹) ^ p := by
          rw [inv_div]
    _ = ((x + y) / (Real.sqrt x * Real.sqrt y)) ^ (-p) := by
          rw [Real.rpow_neg_eq_inv_rpow]
    _ = (2 * Real.cosh ((Real.log x - Real.log y) / 2)) ^ (-p) := by
          rw [two_cosh_log_ratio hx hy]
    _ = (2 : ℝ) ^ (-p) *
        Real.cosh ((Real.log x - Real.log y) / 2) ^ (-p) := by
          rw [Real.mul_rpow (by norm_num) (Real.cosh_pos _).le]

/-- Exact Gamma-frequency representation of each positive-index reciprocal pair. -/
theorem reciprocalMomentStationaryKernel_eq_gammaIntegral
    (δ : ℝ) (hδ : δ < 5) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (reciprocalMomentStationaryKernel δ m n : ℂ) =
      (Real.rpow 2 (-(5 - δ)) : ℂ) *
        (∫ t : ℝ,
          Complex.exp ((((t * (Real.log (m : ℝ) - Real.log (n : ℝ))) : ℝ) : ℂ) * Complex.I) *
            (gammaHeightDensity (5 - δ) t : ℂ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < 5 - δ := by linarith
  have hk := ratio_kernel_eq_cosh hmR hnR (5 - δ)
  unfold reciprocalMomentStationaryKernel
  rw [hk, integral_cexp_mul_gammaHeightDensity hr]
  push_cast
  rfl

private theorem conj_exp_phase_mul_exp_phase (t u v : ℝ) :
    conj (Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (((t * v : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((t * (v - u) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Finite polynomial with real coefficients and arbitrary real frequencies. -/
def gammaPhasePolynomial (S : Finset ℕ) (a freq : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (a n : ℂ) * Complex.exp (((t * freq n : ℝ) : ℂ) * Complex.I)

/-- Exact finite pair expansion of a phase-polynomial squared norm. -/
theorem gammaPhasePolynomial_normSq_eq_pairSum
    (S : Finset ℕ) (a freq : ℕ → ℝ) (t : ℝ) :
    ((Complex.normSq (gammaPhasePolynomial S a freq t) : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S,
        (a m : ℂ) * (a n : ℂ) *
          Complex.exp (((t * (freq m - freq n) : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.normSq_eq_conj_mul_self]
  unfold gammaPhasePolynomial
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, Complex.conj_ofReal]
  calc
    (a n : ℂ) * conj (Complex.exp (((t * freq n : ℝ) : ℂ) * Complex.I)) *
        ((a m : ℂ) * Complex.exp (((t * freq m : ℝ) : ℂ) * Complex.I)) =
      (a m : ℂ) * (a n : ℂ) *
        (conj (Complex.exp (((t * freq n : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (((t * freq m : ℝ) : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [conj_exp_phase_mul_exp_phase]

private theorem integrable_gammaPhasePair {p : ℝ} (hp : 0 < p) (u : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
        (gammaHeightDensity p t : ℂ)) := by
  simpa [gammaEulerTiltedDensity, gammaEulerFiniteWeight] using
    integrable_cexp_mul_gammaEulerTiltedDensity hp [] u

/-- Gamma-weighted Gram identity for any finite real phase polynomial. -/
theorem integral_gammaPhasePolynomial_normSq_eq_pairSum
    (S : Finset ℕ) (a freq : ℕ → ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ t : ℝ,
      ((Complex.normSq (gammaPhasePolynomial S a freq t) : ℝ) : ℂ) *
        (gammaHeightDensity p t : ℂ)) =
      ∑ m ∈ S, ∑ n ∈ S,
        (a m : ℂ) * (a n : ℂ) *
          ((Real.cosh ((freq m - freq n) / 2) ^ (-p) : ℝ) : ℂ) := by
  have hterm (m n : ℕ) :
      Integrable (fun t : ℝ =>
        ((a m : ℂ) * (a n : ℂ)) *
          (Complex.exp (((t * (freq m - freq n) : ℝ) : ℂ) * Complex.I) *
            (gammaHeightDensity p t : ℂ))) :=
    (integrable_gammaPhasePair hp _).const_mul _
  have hpoint (t : ℝ) :
      ((Complex.normSq (gammaPhasePolynomial S a freq t) : ℝ) : ℂ) *
          (gammaHeightDensity p t : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S,
          ((a m : ℂ) * (a n : ℂ)) *
            (Complex.exp (((t * (freq m - freq n) : ℝ) : ℂ) * Complex.I) *
              (gammaHeightDensity p t : ℂ)) := by
    rw [gammaPhasePolynomial_normSq_eq_pairSum]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_finsetSum S (fun m _ =>
      integrable_finsetSum S (fun n _ => hterm m n))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MeasureTheory.integral_finsetSum S (fun n _ => hterm m n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [MeasureTheory.integral_const_mul,
    integral_cexp_mul_gammaHeightDensity hp]

/-- Möbius polynomial at abscissa `(1+δ)/2`, with finite cutoff `N`. -/
def finiteCubicMobiusPolynomial (δ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  gammaPhasePolynomial (Finset.Icc 1 N) (cubicMomentDirichletWeight δ)
    (fun n => Real.log (n : ℝ)) t

/-- Exact source-specific positive-norm representation of the finite cubic moment.
All Möbius signs remain inside the polynomial. -/
theorem cubicMomentFiniteEnergy_eq_gammaPolynomialIntegral
    (δ : ℝ) (hδ : δ < 5) (N : ℕ) :
    (cubicMomentFiniteEnergy δ N : ℂ) =
      (Real.rpow 2 (-(5 - δ)) : ℂ) *
        (∫ t : ℝ,
          ((Complex.normSq (finiteCubicMobiusPolynomial δ N t) : ℝ) : ℂ) *
            (gammaHeightDensity (5 - δ) t : ℂ)) := by
  let S := Finset.Icc 1 N
  let a := cubicMomentDirichletWeight δ
  let freq : ℕ → ℝ := fun n => Real.log (n : ℝ)
  have hp : 0 < 5 - δ := by linarith
  have hgram := integral_gammaPhasePolynomial_normSq_eq_pairSum S a freq hp
  have hkernel (m n : ℕ) (hm : m ∈ S) (hn : n ∈ S) :
      reciprocalMomentStationaryKernel δ m n =
        Real.rpow 2 (-(5 - δ)) *
          Real.cosh ((freq m - freq n) / 2) ^ (-(5 - δ)) := by
    have hmR : (0 : ℝ) < m := by
      exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast (Finset.mem_Icc.mp hn).1
    simpa [reciprocalMomentStationaryKernel, freq] using
      ratio_kernel_eq_cosh hmR hnR (5 - δ)
  change (cubicMomentFiniteEnergy δ N : ℂ) =
    (Real.rpow 2 (-(5 - δ)) : ℂ) *
      (∫ t : ℝ,
        ((Complex.normSq (gammaPhasePolynomial S a freq t) : ℝ) : ℂ) *
          (gammaHeightDensity (5 - δ) t : ℂ))
  rw [hgram]
  rw [cubicMomentFiniteEnergy_eq_stationary]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hkernel m n hm hn]
  push_cast
  ring

/-- Real version of the exact Gamma-weighted finite polynomial identity. -/
theorem cubicMomentFiniteEnergy_eq_realGammaIntegral
    (δ : ℝ) (hδ : δ < 5) (N : ℕ) :
    cubicMomentFiniteEnergy δ N =
      Real.rpow 2 (-(5 - δ)) *
        (∫ t : ℝ,
          Complex.normSq (finiteCubicMobiusPolynomial δ N t) *
            gammaHeightDensity (5 - δ) t) := by
  have h := cubicMomentFiniteEnergy_eq_gammaPolynomialIntegral δ hδ N
  have hr := congrArg Complex.re h
  simpa [integral_complex_ofReal, ← Complex.ofReal_mul] using hr

/-- The complete finite signed reciprocal moment is nonnegative. -/
theorem cubicMomentFiniteEnergy_nonneg
    (δ : ℝ) (hδ : δ < 5) (N : ℕ) :
    0 ≤ cubicMomentFiniteEnergy δ N := by
  rw [cubicMomentFiniteEnergy_eq_realGammaIntegral δ hδ]
  apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
  apply integral_nonneg
  intro t
  exact mul_nonneg (Complex.normSq_nonneg _) (gammaHeightDensity_nonneg (by linarith) t)

/-- Raising Gamma shape by two multiplies its height density by an exact quadratic. -/
theorem gammaHeightDensity_add_two {p : ℝ} (hp : 0 < p) (t : ℝ) :
    gammaHeightDensity (p + 2) t =
      ((p ^ 2 + 4 * t ^ 2) / (p * (p + 1))) * gammaHeightDensity p t := by
  let z : ℂ := (((p : ℂ) + (2 * t : ℝ) * Complex.I) / 2)
  have hzre : z.re = p / 2 := by
    simp [z, Complex.add_re, Complex.mul_re]
  have hzne : z ≠ 0 := by
    intro h
    have hz0 := congrArg Complex.re h
    simp [hzre] at hz0
    linarith
  have harg : (((p + 2 : ℝ) : ℂ) + (2 * t : ℝ) * Complex.I) / 2 = z + 1 := by
    dsimp [z]
    push_cast
    ring
  have hgamma : Real.Gamma (p + 2) = (p + 1) * p * Real.Gamma p := by
    rw [show p + 2 = (p + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith : p + 1 ≠ 0),
      Real.Gamma_add_one hp.ne']
    ring
  have hpow : (2 : ℝ) ^ (p + 1) = 4 * (2 : ℝ) ^ (p - 1) := by
    rw [show p + 1 = (p - 1) + 2 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring
  have hnormz : Complex.normSq z = (p ^ 2 + 4 * t ^ 2) / 4 := by
    simp [z, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have hG : Real.Gamma p ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hp)
  unfold gammaHeightDensity
  rw [harg, Complex.Gamma_add_one z hzne, Complex.normSq_mul,
    hnormz, hgamma, show p + 2 - 1 = p + 1 by ring, hpow]
  change 4 * (2 : ℝ) ^ (p - 1) *
      ((p ^ 2 + 4 * t ^ 2) / 4 * Complex.normSq (Complex.Gamma z)) /
        (Real.pi * ((p + 1) * p * Real.Gamma p)) =
    (p ^ 2 + 4 * t ^ 2) / (p * (p + 1)) *
      ((2 : ℝ) ^ (p - 1) * Complex.normSq (Complex.Gamma z) /
        (Real.pi * Real.Gamma p))
  field_simp [hG, hp.ne', (show p + 1 ≠ 0 by linarith), Real.pi_ne_zero]

/-- Every higher shape controls the preceding Gamma height law pointwise. -/
theorem gammaHeightDensity_le_succ_two {p : ℝ} (hp : 0 < p) (t : ℝ) :
    gammaHeightDensity p t ≤
      ((p + 1) / p) * gammaHeightDensity (p + 2) t := by
  have hfactor : ((p + 1) / p) *
      ((p ^ 2 + 4 * t ^ 2) / (p * (p + 1))) =
      (p ^ 2 + 4 * t ^ 2) / p ^ 2 := by
    field_simp [hp.ne', (show p + 1 ≠ 0 by linarith)]
  have hratio : 1 ≤ (p ^ 2 + 4 * t ^ 2) / p ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hp)]
    nlinarith [sq_nonneg t]
  rw [gammaHeightDensity_add_two hp]
  calc
    gammaHeightDensity p t = 1 * gammaHeightDensity p t := (one_mul _).symm
    _ ≤ ((p ^ 2 + 4 * t ^ 2) / p ^ 2) * gammaHeightDensity p t :=
      mul_le_mul_of_nonneg_right hratio (gammaHeightDensity_nonneg hp t)
    _ = ((p + 1) / p) *
        (((p ^ 2 + 4 * t ^ 2) / (p * (p + 1))) * gammaHeightDensity p t) := by
      rw [← mul_assoc, hfactor]

end
end RHTower
