import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPeriodDefect
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoleModes

/-!
# No finite polar packet satisfies the odd weight-one period equations

A finite sum `∑ exp(-ρ log x) Pρ(log x)` with distinct exponents of positive real part
cannot satisfy both modular boundary identities unless every coefficient polynomial is zero.
Arbitrary logarithmic orders and equal real parts are retained. Decay and regularity follow
from the displayed packet; neither is assumed as an extra premise.

This closes the finite-packet receiver, not the transport of a cubic quotient to that receiver.
-/

open Complex Polynomial Filter Topology Set

noncomputable section

namespace RHTower.WeilHigherDenominator

/-- Boundedness on a half-line excludes every finite exponential mode of positive real part. -/
theorem exponential_polynomial_eq_zero_of_bounded {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℂ) (S : Finset ι) (hinj : Set.InjOn ρ ↑S)
    (hρ : ∀ i ∈ S, 0 < (ρ i).re) (p : ι → Polynomial ℂ)
    (hbounded : ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖∑ i ∈ S, (p i).eval (t : ℂ) * Complex.exp (ρ i * (t : ℂ))‖ ≤ B) :
    ∀ i ∈ S, p i = 0 := by
  let A : ℝ := ∑ i ∈ S, |(ρ i).im|
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let h : ℝ := 1 / (A + 1)
  have hh : 0 < h := by dsimp [h]; positivity
  have hh0 : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hh)
  let z : ι → ℂ := fun i => Complex.exp ((h : ℂ) * ρ i)
  let q : ι → Polynomial ℂ := fun i => (p i).comp (C (h : ℂ) * X)
  have him (i : ι) (hi : i ∈ S) : |((h : ℂ) * ρ i).im| < 1 := by
    have hb : |(ρ i).im| ≤ A := Finset.single_le_sum (fun j _ => abs_nonneg (ρ j).im) hi
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, abs_mul, abs_of_pos hh]
    calc
      h * |(ρ i).im| ≤ h * A := mul_le_mul_of_nonneg_left hb hh.le
      _ < 1 := by
        dsimp [h]
        rw [div_mul_eq_mul_div, one_mul, div_lt_one (by linarith : 0 < A + 1)]
        linarith
  have hzi : Set.InjOn z ↑S := by
    intro i hi j hj heq
    have hi' := abs_lt.mp (him i hi)
    have hj' := abs_lt.mp (him j hj)
    have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by linarith [Real.pi_gt_three] : -Real.pi < ((h : ℂ) * ρ i).im)
      (by linarith [Real.pi_gt_three] : ((h : ℂ) * ρ i).im ≤ Real.pi)
      (by linarith [Real.pi_gt_three] : -Real.pi < ((h : ℂ) * ρ j).im)
      (by linarith [Real.pi_gt_three] : ((h : ℂ) * ρ j).im ≤ Real.pi) heq
    exact hinj hi hj (mul_left_cancel₀ hh0 he)
  have hz : ∀ i ∈ S, 1 < ‖z i‖ := by
    intro i hi
    dsimp [z]
    rw [Complex.norm_exp, Real.one_lt_exp_iff]
    simpa using mul_pos hh (hρ i hi)
  obtain ⟨B, hB⟩ := hbounded
  have hqb : ∃ B : ℝ, ∀ m : ℕ, 1 ≤ m →
      ‖∑ i ∈ S, (q i).eval (m : ℂ) * z i ^ m‖ ≤ B := by
    refine ⟨B, ?_⟩
    intro m _
    have he : ∑ i ∈ S, (q i).eval (m : ℂ) * z i ^ m =
        ∑ i ∈ S, (p i).eval ((h * m : ℝ) : ℂ) * Complex.exp (ρ i * ((h * m : ℝ) : ℂ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [q, z, eval_comp, eval_mul, eval_C, eval_X, ofReal_mul, ofReal_natCast]
      rw [← Complex.exp_nat_mul]
      congr 2
      ring
    rw [he]
    exact hB _ (mul_nonneg hh.le (Nat.cast_nonneg m))
  have hqzero := polynomial_geometric_eq_zero_of_bounded z S hzi hz q hqb
  intro i hi
  rcases Polynomial.comp_eq_zero_iff.mp (hqzero i hi) with hp | ⟨_, hc⟩
  · exact hp
  · have he := congrArg (fun P : Polynomial ℂ => P.coeff 1) hc
    have : (h : ℂ) = 0 := by simpa using he
    exact (hh0 this).elim

private theorem tendsto_polynomial_mul_exp_neg {ρ : ℂ} (hρ : 0 < ρ.re) (p : Polynomial ℂ) :
    Tendsto (fun t : ℝ => p.eval (t : ℂ) * Complex.exp (-ρ * (t : ℂ))) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add, add_mul, add_zero] using hp.add hq
  | monomial n a =>
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) ρ.re hρ).const_mul ‖a‖
    simp only [Real.rpow_natCast, mul_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [eval_monomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring

/-- Finite logarithmic pole data on the positive boundary, including every pole order. -/
def finitePoleBoundary {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) (p : ι → Polynomial ℂ)
    (x : ℝ) : ℂ :=
  ∑ i ∈ S, (p i).eval (Real.log x : ℂ) * Complex.exp (-ρ i * (Real.log x : ℂ))

theorem finitePoleBoundary_contDiffOn {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    (p : ι → Polynomial ℂ) : ContDiffOn ℝ 1 (finitePoleBoundary S ρ p) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  apply ContDiffAt.contDiffWithinAt
  unfold finitePoleBoundary
  have hlog : ContDiffAt ℝ 1 (fun t : ℝ => (Real.log t : ℂ)) x := by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr (ne_of_gt hx))
  have hpoly (P : Polynomial ℂ) :
      ContDiffAt ℝ 1 (fun t : ℝ => P.eval (Real.log t : ℂ)) x := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simpa only [eval_add] using hp.add hq
    | monomial n a => simpa only [eval_monomial] using contDiffAt_const.mul (hlog.pow n)
  apply ContDiffAt.sum
  intro i _
  have hp := hpoly (p i)
  fun_prop

theorem finitePoleBoundary_tendsto_zero {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    (hρ : ∀ i ∈ S, 0 < (ρ i).re) (p : ι → Polynomial ℂ) :
    Tendsto (finitePoleBoundary S ρ p) atTop (𝓝 0) := by
  unfold finitePoleBoundary
  have hsum := tendsto_finsetSum S fun i hi =>
    (tendsto_polynomial_mul_exp_neg (hρ i hi) (p i)).comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, Finset.sum_const_zero] using hsum

/-- A finite polar packet of positive real exponents satisfying the modular boundary equations
has no nonzero coefficient, even with repeated logarithmic orders and equal real parts. -/
theorem finitePoleBoundary_eq_zero_of_period {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (ρ : ι → ℂ) (hinj : Set.InjOn ρ ↑S)
    (hρ : ∀ i ∈ S, 0 < (ρ i).re) (p : ι → Polynomial ℂ)
    (hthree : ∀ x > 0, finitePoleBoundary S ρ p x = finitePoleBoundary S ρ p (x + 1) +
      finitePoleBoundary S ρ p (x / (x + 1)) / ((x + 1 : ℝ) : ℂ))
    (hinv : ∀ x > 0, finitePoleBoundary S ρ p x = -finitePoleBoundary S ρ p x⁻¹ / (x : ℂ)) :
    ∀ i ∈ S, p i = 0 := by
  obtain ⟨B, _, hb, _⟩ := weightOne_period_bounds (finitePoleBoundary_contDiffOn S ρ p)
    hthree hinv (finitePoleBoundary_tendsto_zero S ρ hρ p)
  have hbounded : ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖∑ i ∈ S, ((p i).comp (-X)).eval (t : ℂ) * Complex.exp (ρ i * (t : ℂ))‖ ≤ B := by
    refine ⟨B, ?_⟩
    intro t ht
    have he : finitePoleBoundary S ρ p (Real.exp (-t)) =
        ∑ i ∈ S, ((p i).comp (-X)).eval (t : ℂ) * Complex.exp (ρ i * (t : ℂ)) := by
      unfold finitePoleBoundary
      simp only [Real.log_exp, ofReal_neg, eval_comp, eval_neg, eval_X, neg_mul_neg]
    rw [← he]
    exact hb _ ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)⟩
  have hp := exponential_polynomial_eq_zero_of_bounded ρ S hinj hρ
    (fun i => (p i).comp (-X)) hbounded
  exact fun i hi => Polynomial.comp_neg_X_eq_zero_iff.mp (hp i hi)

end RHTower.WeilHigherDenominator
