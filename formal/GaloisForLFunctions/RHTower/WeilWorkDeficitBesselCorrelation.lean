import GaloisForLFunctions.RHTower.ThetaOneSidedBernsteinGauge
import GaloisForLFunctions.RHTower.RiemannKernelCuspSeries
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct
import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact divisor--Bessel correlations for the actual Riemann kernel

The full convolution of any two polynomial theta cusp series is an absolutely
convergent divisor--Bessel series.  The proof integrates each positive monomial
pair, bounds the sum of its absolute integrals, and regroups every positive
factor pair by its product.  Finite polynomial assembly then gives all actual
mixed derivative correlations and the explicit two-channel formula for Phi.

This is the classical-parent representation in WP06 PROOF, C11b.  No sign of the
signed Bessel difference, positive cancellation family, or upper spectral-deficit
bound is assumed or concluded.
-/

open MeasureTheory Set Polynomial
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower.WeilWorkDeficitBessel
noncomputable section

private def expKernel (x h v : ℝ) : ℝ := Real.exp (-x * Real.cosh v + h * v)

private theorem expKernel_re (x h v : ℝ) :
    (besselOrderExpKernel x (h : ℂ) v).re = expKernel x h v := by
  simp [besselOrderExpKernel, expKernel, ← Complex.ofReal_cosh, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_add, ← Complex.ofReal_exp]

private theorem integrable_expKernel {x : ℝ} (hx : 0 < x) (h : ℝ) :
    Integrable (expKernel x h) := by
  simpa only [RCLike.re_eq_complex_re, expKernel_re] using (integrable_besselOrderExpKernel hx (h : ℂ)).re

private theorem integral_expKernel {x : ℝ} (hx : 0 < x) (h : ℝ) :
    (∫ v, expKernel x h v) = 2 * realModifiedBesselKOrder x h := by
  have hr := Complex.reCLM.integral_comp_comm (integrable_besselOrderExpKernel hx (h : ℂ))
  simpa [Complex.reCLM_apply, expKernel_re,
    integral_besselOrderExpKernel_eq_two_mul hx, modifiedBesselKOrder_ofReal hx] using hr

private theorem integral_expKernel_affine {x : ℝ} (hx : 0 < x) (h c : ℝ) :
    (∫ u, expKernel x h (2 * u + c)) = realModifiedBesselKOrder x h := by
  rw [Measure.integral_comp_mul_left (fun v => expKernel x h (v + c)),
    integral_add_right_eq_self, integral_expKernel hx]
  norm_num
  ring

private theorem integrable_expKernel_affine {x : ℝ} (hx : 0 < x) (h c : ℝ) :
    Integrable (fun u => expKernel x h (2 * u + c)) :=
  ((integrable_expKernel hx h).comp_add_right c).comp_mul_left' (by norm_num)

private theorem cusp_coordinate {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y u : ℝ) :
    a * b * Real.exp y * Real.exp (2 * u - y + Real.log a - Real.log b) =
      a ^ 2 * Real.exp (2 * u) := by
  rw [Real.exp_sub, Real.exp_add, Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
  field_simp

private theorem cusp_monomial_pair {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (j l : ℕ) (y u : ℝ) :
    cuspTerm (X ^ j) a u * cuspTerm (X ^ l) b (y - u) =
      Real.exp (y / 2) * ((a : ℝ) * b * Real.exp y) ^ (j + l) *
        expKernel (2 * Real.pi * ((a : ℝ) * b * Real.exp y)) ((j : ℝ) - l)
          (2 * u - y + Real.log a - Real.log b) := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  let t := (a : ℝ) * b * Real.exp y
  let v := 2 * u - y + Real.log a - Real.log b
  have hx : (a : ℝ) ^ 2 * Real.exp (2 * u) = t * Real.exp v :=
    (cusp_coordinate ha' hb' y u).symm
  have hz : (b : ℝ) ^ 2 * Real.exp (2 * (y - u)) = t * Real.exp (-v) := by
    convert (cusp_coordinate hb' ha' y (y - u)).symm using 1
    dsimp [t, v]
    congr 1
    · ring
    · congr 1; ring
  change _ = Real.exp (y / 2) * t ^ (j + l) * expKernel (2 * Real.pi * t) ((j : ℝ) - l) v
  simp only [cuspTerm, eval_pow, eval_X, hx, hz, mul_pow, expKernel]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  rw [Real.cosh_eq]
  simp only [pow_add]
  have he : u / 2 + (y - u) / 2 + ((j : ℝ) * v + (l : ℝ) * -v) +
      (-Real.pi * (t * Real.exp v) + -Real.pi * (t * Real.exp (-v))) =
      y / 2 + (-(2 * Real.pi * t) * ((Real.exp v + Real.exp (-v)) / 2) +
        ((j : ℝ) - l) * v) := by ring
  calc
    _ = t ^ j * t ^ l * Real.exp (u / 2 + (y - u) / 2 +
        ((j : ℝ) * v + (l : ℝ) * -v) +
        (-Real.pi * (t * Real.exp v) + -Real.pi * (t * Real.exp (-v)))) := by
      simp only [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring


private theorem integrable_cusp_monomial_pair {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (j l : ℕ) (y : ℝ) :
    Integrable (fun u => cuspTerm (X ^ j) a u * cuspTerm (X ^ l) b (y - u)) := by
  have hx : 0 < 2 * Real.pi * ((a : ℝ) * b * Real.exp y) := by positivity
  have h := (integrable_expKernel_affine hx ((j : ℝ) - l)
    (-y + Real.log a - Real.log b)).const_mul
      (Real.exp (y / 2) * ((a : ℝ) * b * Real.exp y) ^ (j + l))
  exact h.congr (ae_of_all _ fun u => by
    dsimp only
    rw [cusp_monomial_pair ha hb]
    congr 2; ring)

private theorem integral_cusp_monomial_pair {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (j l : ℕ) (y : ℝ) :
    (∫ u, cuspTerm (X ^ j) a u * cuspTerm (X ^ l) b (y - u)) =
      Real.exp (y / 2) * ((a : ℝ) * b * Real.exp y) ^ (j + l) *
        realModifiedBesselKOrder (2 * Real.pi * ((a : ℝ) * b * Real.exp y))
          ((j : ℝ) - l) := by
  simp_rw [cusp_monomial_pair ha hb]
  rw [integral_const_mul]
  congr 1
  convert integral_expKernel_affine (show 0 < 2 * Real.pi * ((a : ℝ) * b * Real.exp y)
    by positivity) ((j : ℝ) - l) (-y + Real.log a - Real.log b) using 1
  congr 1
  funext u
  congr 1
  ring

private theorem bessel_exp_bound {x s : ℝ} (hs : 0 < s) (hx : 2 * s ≤ x) (h : ℝ) :
    realModifiedBesselKOrder x h ≤ Real.exp (-x / 2) * realModifiedBesselKOrder s h := by
  have hx0 : 0 < x := by linarith
  rw [realModifiedBesselKOrder, realModifiedBesselKOrder, ← integral_const_mul]
  apply setIntegral_mono_on (integrableOn_realBesselOrderKernel hx0 h)
    ((integrableOn_realBesselOrderKernel hs h).const_mul _) measurableSet_Ioi
  intro v _
  simp only [realBesselOrderKernel, ← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (Real.cosh_pos _).le
  apply Real.exp_le_exp.mpr
  have hv := Real.one_le_cosh v
  nlinarith

private def pairValue (j l : ℕ) (y : ℝ) (a b : ℕ) : ℝ :=
  Real.exp (y / 2) * (((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ) * Real.exp y) ^ (j + l) *
    realModifiedBesselKOrder
      (2 * Real.pi * (((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ) * Real.exp y)) ((j : ℝ) - l)

private theorem pairValue_nonneg (j l : ℕ) (y : ℝ) (a b : ℕ) : 0 ≤ pairValue j l y a b := by
  unfold pairValue
  exact mul_nonneg (by positivity) (realModifiedBesselKOrder_pos (by positivity) _).le

private theorem summable_pairValue (j l : ℕ) (y : ℝ) :
    Summable (fun p : ℕ × ℕ => pairValue j l y p.1 p.2) := by
  let c := Real.pi * Real.exp y / 2
  let g : ℕ → ℝ := fun a => ((a + 1 : ℕ) : ℝ) ^ (j + l) *
    Real.exp (-c * ((a + 1 : ℕ) : ℝ))
  let B := Real.exp (y / 2) * Real.exp y ^ (j + l) *
    realModifiedBesselKOrder (Real.pi * Real.exp y) ((j : ℝ) - l)
  have hc : 0 < c := by dsimp [c]; positivity
  have hg : Summable g := summable_cuspTerm_bound (j + l) hc
  have hs := (summable_mul_of_summable_norm hg.norm hg.norm).mul_left B
  apply hs.of_norm_bounded
  rintro ⟨a,b⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (pairValue_nonneg _ _ _ _ _)]
  have ha : 1 ≤ ((a + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 a
  have hb : 1 ≤ ((b + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 b
  have hprod : 1 ≤ ((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ) := by nlinarith
  have he : Real.exp (-(2 * Real.pi *
      (((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ) * Real.exp y)) / 2) ≤
        Real.exp (-c * ((a + 1 : ℕ) : ℝ)) * Real.exp (-c * ((b + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hab1 : ((a + 1 : ℕ) : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ) := by nlinarith
    have hab2 : ((b + 1 : ℕ) : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ) := by nlinarith
    dsimp [c]
    nlinarith [mul_nonneg (show 0 ≤ Real.pi * Real.exp y by positivity)
      (show 0 ≤ 2 * (((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ)) -
        ((a + 1 : ℕ) : ℝ) - ((b + 1 : ℕ) : ℝ) by linarith)]
  have hk := bessel_exp_bound (show 0 < Real.pi * Real.exp y by positivity)
    (show 2 * (Real.pi * Real.exp y) ≤ 2 * Real.pi *
      (((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ) * Real.exp y) by
        have := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 2 * Real.pi * Real.exp y by positivity)
        nlinarith)
    ((j : ℝ) - l)
  have hK : 0 ≤ realModifiedBesselKOrder (Real.pi * Real.exp y) ((j : ℝ) - l) :=
    (realModifiedBesselKOrder_pos (by positivity) _).le
  unfold pairValue
  calc
    _ ≤ Real.exp (y / 2) *
        (((a + 1 : ℕ) : ℝ) * (b + 1 : ℕ) * Real.exp y) ^ (j + l) *
        ((Real.exp (-c * ((a + 1 : ℕ) : ℝ)) * Real.exp (-c * ((b + 1 : ℕ) : ℝ))) *
          realModifiedBesselKOrder (Real.pi * Real.exp y) ((j : ℝ) - l)) := by
      exact mul_le_mul_of_nonneg_left (hk.trans (mul_le_mul_of_nonneg_right he hK)) (by positivity)
    _ = B * (g a * g b) := by dsimp [B,g]; simp only [mul_pow]; ring

private theorem integral_monomial_series (j l : ℕ) (y : ℝ) :
    (∫ u, cuspSeries (X ^ j) u * cuspSeries (X ^ l) (y - u)) =
      ∑' p : ℕ × ℕ, pairValue j l y p.1 p.2 := by
  let f : (ℕ × ℕ) → ℝ → ℝ := fun p u =>
    cuspTerm (X ^ j) (p.1 + 1) u * cuspTerm (X ^ l) (p.2 + 1) (y - u)
  have hf : ∀ p, Integrable (f p) := fun p =>
    integrable_cusp_monomial_pair (by omega) (by omega) j l y
  have hnorm : ∀ p, (∫ u, ‖f p u‖) = pairValue j l y p.1 p.2 := by
    intro p
    have hp : ∀ u, 0 ≤ f p u := fun u => by dsimp [f,cuspTerm]; simp only [eval_pow, eval_X]; positivity
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hp _)]
    exact integral_cusp_monomial_pair (by omega) (by omega) j l y
  have hi := integral_tsum_of_summable_integral_norm hf
    ((summable_pairValue j l y).congr (fun p => (hnorm p).symm))
  have hsum : ∀ u, (∑' p, f p u) = cuspSeries (X ^ j) u * cuspSeries (X ^ l) (y - u) := by
    intro u
    exact ((summable_cuspTerm (X ^ j) u).tsum_mul_tsum
      (summable_cuspTerm (X ^ l) (y - u))
      (summable_mul_of_summable_norm (summable_cuspTerm (X ^ j) u).norm
        (summable_cuspTerm (X ^ l) (y - u)).norm)).symm
  rw [integral_congr_ae (ae_of_all _ hsum)] at hi
  rw [← hi]
  apply tsum_congr
  intro p
  exact integral_cusp_monomial_pair (by omega) (by omega) j l y

/-- The monomial Schlaefli contribution of one positive product index. -/
def besselMonomial (j l : ℕ) (y : ℝ) (N : ℕ) : ℝ :=
  Real.exp (y / 2) * ((N : ℝ) * Real.exp y) ^ (j + l) *
    realModifiedBesselKOrder (2 * Real.pi * ((N : ℝ) * Real.exp y)) ((j : ℝ) - l)

private theorem pairValue_eq (j l : ℕ) (y : ℝ) (a b : ℕ) :
    pairValue j l y a b = besselMonomial j l y ((a + 1) * (b + 1)) := by
  simp only [pairValue, besselMonomial, Nat.cast_mul]

private theorem divisor_bessel_hasSum (j l : ℕ) (y : ℝ) :
    HasSum (fun N : ℕ => (N.divisorsAntidiagonal.card : ℝ) * besselMonomial j l y N)
      (∑' p : ℕ × ℕ, pairValue j l y p.1 p.2) := by
  classical
  let F : ℕ × ℕ → ℝ := fun p =>
    if p.1 = 0 ∨ p.2 = 0 then 0 else besselMonomial j l y (p.1 * p.2)
  let e : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + 1, p.2 + 1)
  have hinj : Function.Injective e := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext <;> dsimp [e] at h1 h2 <;> omega
  have hrange : ∀ p, p ∉ Set.range e → F p = 0 := by
    intro p hp
    dsimp [F]
    split_ifs with h
    · rfl
    · exfalso
      apply hp
      refine ⟨(p.1 - 1, p.2 - 1), ?_⟩
      apply Prod.ext <;> dsimp [e] <;> omega
  have hcomp : F ∘ e = fun p => pairValue j l y p.1 p.2 := by
    funext p
    simp only [Function.comp_apply, F, e, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      or_self, if_false, pairValue_eq]
  have hF : Summable F := (hinj.summable_iff hrange).mp
    (hcomp.symm ▸ summable_pairValue j l y)
  have heq : (∑' p, F p) = ∑' p : ℕ × ℕ, pairValue j l y p.1 p.2 := by
    rw [← hinj.tsum_eq (fun p hp => by
      by_contra hn
      exact hp (hrange p hn))]
    exact tsum_congr (congrFun hcomp)
  have h := hasSum_divisorsAntidiagonal_regroup hF (by
    intro p hp
    simp only [F, if_pos hp])
  rw [heq] at h
  refine h.congr_fun ?_
  intro N
  symm
  calc
    (∑ p ∈ N.divisorsAntidiagonal, F p) =
        ∑ _p ∈ N.divisorsAntidiagonal, besselMonomial j l y N := by
      apply Finset.sum_congr rfl
      intro p hp
      have hm := Nat.mem_divisorsAntidiagonal.mp hp
      have h0 : ¬(p.1 = 0 ∨ p.2 = 0) := by
        intro hz
        have : p.1 * p.2 = 0 := by rcases hz with hz | hz <;> simp [hz]
        exact hm.2 (hm.1.symm.trans this)
      simp only [F, if_neg h0, hm.1]
    _ = _ := by simp

/-- Absolute convergence of the complete divisor--Bessel monomial series. -/
theorem summable_divisor_bessel (j l : ℕ) (y : ℝ) :
    Summable (fun N : ℕ => (N.divisorsAntidiagonal.card : ℝ) * besselMonomial j l y N) :=
  (divisor_bessel_hasSum j l y).summable

/-- Exact full theta-monomial correlation, with every positive factor pair retained. -/
theorem monomial_correlation_bessel (j l : ℕ) (y : ℝ) :
    (∫ u, cuspSeries (X ^ j) u * cuspSeries (X ^ l) (y - u)) =
      ∑' N : ℕ, (N.divisorsAntidiagonal.card : ℝ) * besselMonomial j l y N := by
  rw [integral_monomial_series]
  exact (divisor_bessel_hasSum j l y).tsum_eq.symm

private theorem integrable_monomial_correlation (j l : ℕ) (y : ℝ) :
    Integrable (fun u => cuspSeries (X ^ j) u * cuspSeries (X ^ l) (y - u)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_monomial_series]
  apply ne_of_gt
  have hp : 0 < pairValue j l y 0 0 := by
    unfold pairValue
    exact mul_pos (by positivity) (realModifiedBesselKOrder_pos (by positivity) _)
  exact hp.trans_le ((summable_pairValue j l y).le_tsum (0,0)
    (fun p _ => pairValue_nonneg j l y p.1 p.2))

private theorem cuspSeries_eq_sum_monomials (R : ℝ[X]) (u : ℝ) :
    cuspSeries R u = ∑ j ∈ Finset.range (R.natDegree + 1), R.coeff j * cuspSeries (X ^ j) u := by
  conv_lhs => rw [R.as_sum_range_C_mul_X_pow]
  exact cuspSeries_sum _ _ _ _

/-- Every polynomial theta-pair correlation is absolutely integrable. -/
theorem integrable_cusp_correlation (R Q : ℝ[X]) (y : ℝ) :
    Integrable (fun u => cuspSeries R u * cuspSeries Q (y - u)) := by
  simp_rw [cuspSeries_eq_sum_monomials R, cuspSeries_eq_sum_monomials Q,
    Finset.sum_mul, Finset.mul_sum]
  refine integrable_finsetSum _ (fun j _ => ?_)
  refine integrable_finsetSum _ (fun l _ => ?_)
  refine ((integrable_monomial_correlation j l y).const_mul (R.coeff j * Q.coeff l)).congr
    (ae_of_all _ fun u => ?_)
  dsimp only
  ring

/-- Full polynomial theta-pair/divisor--Bessel identity.  No finite theta truncation is used. -/
theorem cusp_correlation_bessel (R Q : ℝ[X]) (y : ℝ) :
    (∫ u, cuspSeries R u * cuspSeries Q (y - u)) =
      ∑ j ∈ Finset.range (R.natDegree + 1), ∑ l ∈ Finset.range (Q.natDegree + 1),
        R.coeff j * Q.coeff l *
          (∑' N : ℕ, (N.divisorsAntidiagonal.card : ℝ) * besselMonomial j l y N) := by
  have hint (j l : ℕ) : Integrable (fun u =>
      (R.coeff j * cuspSeries (X ^ j) u) * (Q.coeff l * cuspSeries (X ^ l) (y - u))) := by
    convert (integrable_monomial_correlation j l y).const_mul (R.coeff j * Q.coeff l) using 1
    ext u
    ring
  simp_rw [cuspSeries_eq_sum_monomials R, cuspSeries_eq_sum_monomials Q,
    Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => hint j l))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun l _ => hint j l)]
  apply Finset.sum_congr rfl
  intro l _
  calc
    _ = R.coeff j * Q.coeff l * ∫ u, cuspSeries (X ^ j) u * cuspSeries (X ^ l) (y - u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      ring
    _ = _ := by rw [monomial_correlation_bessel]

private theorem kernelDeriv_re_reflect (l : ℕ) (u : ℝ) :
    (riemannKernelDeriv l (-u)).re = (-1 : ℝ) ^ l * (riemannKernelDeriv l u).re := by
  rw [riemannKernelDeriv_neg]
  have hc : (-1 : ℂ) ^ l = (((-1 : ℝ) ^ l : ℝ) : ℂ) := by push_cast; rfl
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Exact actual derivative-correlation matrix, including mixed orders and every divisor term.
In particular, `k=l` and `y=log n` gives the matrix in conjecture C11. -/
theorem derivative_correlation_bessel (k l : ℕ) (y : ℝ) :
    (∫ u, (riemannKernelDeriv k u).re * (riemannKernelDeriv l (u - y)).re) =
      (-1 : ℝ) ^ l *
        (∑ j ∈ Finset.range ((riemannKernelPoly k).natDegree + 1),
          ∑ m ∈ Finset.range ((riemannKernelPoly l).natDegree + 1),
            (riemannKernelPoly k).coeff j * (riemannKernelPoly l).coeff m *
              (∑' N : ℕ, (N.divisorsAntidiagonal.card : ℝ) * besselMonomial j m y N)) := by
  rw [← cusp_correlation_bessel]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [show u - y = -(y - u) by ring, kernelDeriv_re_reflect]
  simp only [riemannKernelDeriv, riemannKernelPoly, Complex.ofReal_re]
  ring

/-- Integrability of every actual mixed derivative correlation. -/
theorem integrable_derivative_correlation (k l : ℕ) (y : ℝ) :
    Integrable (fun u => (riemannKernelDeriv k u).re * (riemannKernelDeriv l (u - y)).re) := by
  refine ((integrable_cusp_correlation (riemannKernelPoly k) (riemannKernelPoly l) y).const_mul
    ((-1 : ℝ) ^ l)).congr (ae_of_all _ fun u => ?_)
  dsimp only
  rw [show u - y = -(y - u) by ring, kernelDeriv_re_reflect]
  simp only [riemannKernelDeriv, riemannKernelPoly, Complex.ofReal_re]
  ring

private theorem phi_re_monomials (u : ℝ) :
    (riemannPhiKernel u).re = 4 * Real.pi ^ 2 * cuspSeries (X ^ 2) u -
      6 * Real.pi * cuspSeries (X ^ 1) u := by
  have hp : riemannCuspPoly = C (4 * Real.pi ^ 2) * X ^ 2 - C (6 * Real.pi) * X ^ 1 := by
    apply Polynomial.funext
    intro x
    simp [riemannCuspPoly, cuspDeriv]
    ring
  rw [riemannPhiKernel_eq_cuspSeries, hp, cuspSeries_sub, cuspSeries_smul, cuspSeries_smul]
  rfl

private theorem bessel_order_neg_one (x : ℝ) :
    realModifiedBesselKOrder x (-1) = realModifiedBesselKOrder x 1 := by
  simp [realModifiedBesselKOrder, realBesselOrderKernel, Real.cosh_neg]

/-- The actual Riemann-kernel correlation in its two-channel divisor--Bessel form. -/
theorem riemann_correlation_bessel (y : ℝ) :
    (∫ u, (riemannPhiKernel u).re * (riemannPhiKernel (u - y)).re) =
      Real.exp (y / 2) * ∑' N : ℕ, (N.divisorsAntidiagonal.card : ℝ) *
        (let x := 2 * Real.pi * ((N : ℝ) * Real.exp y)
         (x ^ 4 + 9 * x ^ 2) * realModifiedBesselKOrder x 0 -
           6 * x ^ 3 * realModifiedBesselKOrder x 1) := by
  let a := 4 * Real.pi ^ 2
  let b := 6 * Real.pi
  let F (j l : ℕ) (u : ℝ) := cuspSeries (X ^ j) u * cuspSeries (X ^ l) (y - u)
  let V (j l : ℕ) (N : ℕ) := (N.divisorsAntidiagonal.card : ℝ) * besselMonomial j l y N
  have hint (j l : ℕ) : Integrable (F j l) := integrable_monomial_correlation j l y
  have hs (j l : ℕ) : Summable (V j l) := summable_divisor_bessel j l y
  have hf : (fun u => (riemannPhiKernel u).re * (riemannPhiKernel (u - y)).re) =
      fun u => (a ^ 2 * F 2 2 u + b ^ 2 * F 1 1 u) - (a * b * F 2 1 u + a * b * F 1 2 u) := by
    funext u
    rw [show u - y = -(y - u) by ring, riemannPhiKernel_neg]
    simp only [phi_re_monomials]
    dsimp [a, b, F]
    ring
  have hsplit := integral_sub
    ((hint 2 2).const_mul (a ^ 2) |>.add ((hint 1 1).const_mul (b ^ 2)))
    ((hint 2 1).const_mul (a * b) |>.add ((hint 1 2).const_mul (a * b)))
  simp only [Pi.add_apply] at hsplit
  rw [hf, hsplit,
    integral_add ((hint 2 2).const_mul (a ^ 2)) ((hint 1 1).const_mul (b ^ 2)),
    integral_add ((hint 2 1).const_mul (a * b)) ((hint 1 2).const_mul (a * b))]
  simp only [integral_const_mul]
  have hF (j l : ℕ) : (∫ u, F j l u) = ∑' N, V j l N := monomial_correlation_bessel j l y
  rw [hF, hF, hF, hF]
  have hsum : (∑' N, ((a ^ 2 * V 2 2 N + b ^ 2 * V 1 1 N) -
        (a * b * V 2 1 N + a * b * V 1 2 N))) =
      (a ^ 2 * ∑' N, V 2 2 N) + (b ^ 2 * ∑' N, V 1 1 N) -
        ((a * b * ∑' N, V 2 1 N) + (a * b * ∑' N, V 1 2 N)) := by
    rw [((hs 2 2).mul_left (a ^ 2) |>.add ((hs 1 1).mul_left (b ^ 2))).tsum_sub
      ((hs 2 1).mul_left (a * b) |>.add ((hs 1 2).mul_left (a * b))),
      ((hs 2 2).mul_left (a ^ 2)).tsum_add ((hs 1 1).mul_left (b ^ 2)),
      ((hs 2 1).mul_left (a * b)).tsum_add ((hs 1 2).mul_left (a * b))]
    simp only [tsum_mul_left]
  rw [← hsum, ← tsum_mul_left]
  apply tsum_congr
  intro N
  dsimp [V, besselMonomial, a, b]
  norm_num only [Nat.cast_ofNat, sub_self, Nat.reduceAdd, show (2 : ℝ) - 1 = 1 by ring,
    show (1 : ℝ) - 2 = -1 by ring, bessel_order_neg_one]
  ring

end
end RHTower.WeilWorkDeficitBessel
