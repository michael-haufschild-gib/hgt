import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Exact Gibbs Stein integral certificates

Exponential-polynomial primitives retain the literal theta-atom score. Their
Stein images have exact boundary integrals, so a global positive polynomial
remainder yields an inequality for the actual source moments. Polynomial
integrability and both improper endpoints are proved analytically.
-/

open Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators
namespace RHTower
noncomputable section

private theorem gibbs_poly_integrable (P : ℝ[X]) :
    IntegrableOn (fun x => P.eval x * thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have heq : (fun x => P.eval x * thetaCuspLiouvilleGibbsAtom 1 x) =
      fun x => ∑ k ∈ P.support, P.coeff k *
        (x ^ k * thetaCuspLiouvilleGibbsAtom 1 x) := by
    funext x
    rw [eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  apply integrable_finsetSum
  intro k hk
  exact (integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    k (X ^ 2) (n := 1) (by norm_num)).const_mul _

private theorem gibbs_poly_tendsto (P : ℝ[X]) :
    Tendsto (fun x => P.eval x * thetaCuspLiouvilleGibbsAtom 1 x)
      atTop (𝓝 0) := by
  have h (k : ℕ) : Tendsto (fun x => P.coeff k *
      (x ^ k * thetaCuspLiouvilleGibbsAtom 1 x)) atTop (𝓝 0) := by
    simpa only [mul_zero, thetaCuspLiouvilleGibbsAtom] using (pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
      k (X ^ 2) (n := 1) (by norm_num)).const_mul (P.coeff k)
  have hs := tendsto_finsetSum P.support (fun k _ => h k)
  simp only [Finset.sum_const_zero] at hs
  convert hs using 1
  funext x
  rw [eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem stein_exp_bounds (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.exp (-2 * (j : ℝ) * x) ∧ Real.exp (-2 * (j : ℝ) * x) ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

private theorem gibbs_poly_tilt_integrable (P : ℝ[X]) (j : ℕ) :
    IntegrableOn (fun x => P.eval x * Real.exp (-2 * (j : ℝ) * x) *
      thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have h := (gibbs_poly_integrable P).bdd_mul
    (f := fun x : ℝ => Real.exp (-2 * (j : ℝ) * x))
    (c := 1) (by fun_prop) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (stein_exp_bounds j hx.le).2)
  apply h.congr
  filter_upwards [] with x
  ring

private theorem gibbs_poly_tilt_tendsto (P : ℝ[X]) (j : ℕ) :
    Tendsto (fun x => P.eval x * Real.exp (-2 * (j : ℝ) * x) *
      thetaCuspLiouvilleGibbsAtom 1 x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [norm_zero] using (gibbs_poly_tendsto P).norm)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [show P.eval x * Real.exp (-2 * (j : ℝ) * x) *
      thetaCuspLiouvilleGibbsAtom 1 x =
      Real.exp (-2 * (j : ℝ) * x) *
        (P.eval x * thetaCuspLiouvilleGibbsAtom 1 x) by ring, norm_mul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (stein_exp_bounds j hx).2

private theorem gibbs_score (x : ℝ) :
    HasDerivAt (thetaCuspLiouvilleGibbsAtom 1)
      ((5 / 2 - 2 * Real.pi * Real.exp (2*x)) *
        thetaCuspLiouvilleGibbsAtom 1 x) x := by
  convert hasDerivAt_thetaCuspLiouvilleGibbsAtom 1 x using 1
  simp [thetaCuspLiouvilleGibbsAtom, thetaCuspPolynomialAtom,
    thetaCuspLogDerivativeStep, Real.exp_add,
    show 2*x = x+x by ring]
  ring

def thetaGibbsSteinImage (P : ℝ[X]) (j : ℕ) (x : ℝ) : ℝ :=
  2 * Real.pi * P.eval x * Real.exp (-2 * (j : ℝ) * x) -
    (P.derivative.eval x + (5/2 - 2 * (j+1 : ℕ)) * P.eval x) *
      Real.exp (-2 * (j+1 : ℕ) * x)

theorem thetaGibbsSteinImage_integrable (P : ℝ[X]) (j : ℕ) :
    IntegrableOn (fun x => thetaGibbsSteinImage P j x *
      thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have h := ((gibbs_poly_tilt_integrable P j).const_mul (2*Real.pi)).sub
    ((gibbs_poly_tilt_integrable P.derivative (j+1)).add
      ((gibbs_poly_tilt_integrable P (j+1)).const_mul (5/2-2*(j+1 : ℕ))))
  apply h.congr
  filter_upwards [] with x
  dsimp [thetaGibbsSteinImage]
  ring

theorem integral_thetaGibbsSteinImage (P : ℝ[X]) (j : ℕ) :
    (∫ x : ℝ in Ioi 0, thetaGibbsSteinImage P j x *
      thetaCuspLiouvilleGibbsAtom 1 x) = P.eval 0 * Real.exp (-Real.pi) := by
  have hd (x : ℝ) : HasDerivAt
      (fun x => P.eval x * Real.exp (-2 * (j+1 : ℕ) * x) *
        thetaCuspLiouvilleGibbsAtom 1 x)
      (-(thetaGibbsSteinImage P j x * thetaCuspLiouvilleGibbsAtom 1 x)) x := by
    have he := (((hasDerivAt_id x).const_mul (-2 * (↑(j+1) : ℝ))).exp)
    have hprod := ((P.hasDerivAt x).mul he).mul (gibbs_score x)
    have hexp : Real.exp (-2 * (j+1 : ℕ) * x) * Real.exp (2*x) =
        Real.exp (-2 * (j : ℝ) * x) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    convert hprod using 1
    all_goals try rfl
    simp only [thetaGibbsSteinImage, Pi.mul_apply, id_eq, mul_one]
    linear_combination 2 * Real.pi * P.eval x *
      thetaCuspLiouvilleGibbsAtom 1 x * hexp
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hd x) (thetaGibbsSteinImage_integrable P j).neg
    (gibbs_poly_tilt_tendsto P (j+1))
  rw [integral_neg] at hf
  simp only [mul_zero, Real.exp_zero, mul_one, zero_sub] at hf
  rw [thetaCuspLiouvilleGibbsAtom_apply] at hf
  norm_num at hf
  linarith

def thetaGibbsSteinPolynomial {n : ℕ} (a : ℝ) (P : Fin n → ℝ[X])
    (x t : ℝ) : ℝ :=
  ∑ j : Fin n, (2 * a * (P j).eval x * t ^ j.val -
    ((P j).derivative.eval x + (5/2 - 2 * (j.val+1 : ℕ)) * (P j).eval x) *
      t ^ (j.val+1))

private theorem stein_exp_pow (j : ℕ) (x : ℝ) :
    Real.exp (-2*x) ^ j = Real.exp (-2*(j : ℝ)*x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, ← Real.exp_add]
    congr 1
    push_cast
    ring

theorem thetaGibbsSteinPolynomial_eq_image {n : ℕ} (P : Fin n → ℝ[X]) (x : ℝ) :
    thetaGibbsSteinPolynomial Real.pi P x (Real.exp (-2*x)) =
      ∑ j : Fin n, thetaGibbsSteinImage (P j) j.val x := by
  simp only [thetaGibbsSteinPolynomial, stein_exp_pow, thetaGibbsSteinImage]

def thetaGibbsPolynomialIntegral (P : ℝ[X]) : ℝ :=
  ∫ x : ℝ in Ioi 0, P.eval x * thetaCuspLiouvilleGibbsAtom 1 x

theorem thetaGibbsPolynomialIntegral_add (P Q : ℝ[X]) :
    thetaGibbsPolynomialIntegral (P+Q) =
      thetaGibbsPolynomialIntegral P + thetaGibbsPolynomialIntegral Q := by
  simp only [thetaGibbsPolynomialIntegral, eval_add, add_mul]
  exact integral_add (gibbs_poly_integrable P) (gibbs_poly_integrable Q)

theorem thetaGibbsPolynomialIntegral_C_mul_pow (c : ℝ) (k : ℕ) :
    thetaGibbsPolynomialIntegral (C c * X ^ k) = c * thetaCuspLiouvilleGibbsMoment k 1 := by
  simp only [thetaGibbsPolynomialIntegral, eval_mul, eval_C, eval_pow, eval_X,
    mul_assoc, integral_const_mul, thetaCuspLiouvilleGibbsMoment]

theorem thetaGibbsPolynomialIntegral_lower_of_stein {n : ℕ}
    (Q : ℝ[X]) (P : Fin n → ℝ[X])
    (h : ∀ x : ℝ, 0 ≤ x → 0 ≤ Q.eval x -
      thetaGibbsSteinPolynomial Real.pi P x (Real.exp (-2*x))) :
    (∑ j : Fin n, (P j).eval 0) * Real.exp (-Real.pi) ≤
      thetaGibbsPolynomialIntegral Q := by
  have hsint : IntegrableOn
      (fun x => ∑ j : Fin n, thetaGibbsSteinImage (P j) j.val x *
        thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) :=
    integrable_finsetSum _ (fun j _ => thetaGibbsSteinImage_integrable (P j) j.val)
  have hle := integral_mono_ae hsint (gibbs_poly_integrable Q) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hg : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
      rw [thetaCuspLiouvilleGibbsAtom_apply]
      positivity
    have hh := h x hx.le
    rw [thetaGibbsSteinPolynomial_eq_image] at hh
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sub_nonneg.mp hh) hg)
  rw [integral_finsetSum] at hle
  · simpa only [integral_thetaGibbsSteinImage, ← Finset.sum_mul,
      thetaGibbsPolynomialIntegral] using hle
  · intro j hj
    exact thetaGibbsSteinImage_integrable (P j) j.val

end
end RHTower
