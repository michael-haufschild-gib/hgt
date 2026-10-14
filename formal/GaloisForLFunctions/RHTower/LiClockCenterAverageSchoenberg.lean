import GaloisForLFunctions.RHTower.LiClockCenterAverageKink
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonBoundedReproduction

/-!
# The center-averaged Li clock is a Lévy exponent exactly under RH

A real function `f` on `ℝ` is *conditionally negative definite* (`IsCondNegDef`) if
`Σ_{i,j} c_i c_j f(t_i − t_j) ≤ 0` for every finite family with `Σ_i c_i = 0`.  By Schoenberg's
theorem these are the exponents of symmetric infinitely divisible laws (`e^{−λf}` positive definite
for every `λ > 0`).

**Theorem** (`riemannHypothesis_iff_isCondNegDef_liClockCenterAverage`).  RH holds iff the
center-averaged Li clock `A(t) = Σ_q ∫ P₁(x) Re(1 − cos(t/(a_q − x))) dx` is conditionally negative
definite on `ℝ`.

* Under RH every averaged atom is `1 − e^{−α|t|} cos(βt)` with `α = 1/(1 + a²)`, `β = a/(1 + a²)`.
  Poisson reproduction of `z ↦ e^{iαxz}` gives `e^{−α|x|} = ∫ P₁(ξ) cos(αxξ) dξ`, so
  `e^{−α|x|} cos(βx) = ½ ∫ P₁(ξ) (cos(x(αξ+β)) + cos(x(αξ−β))) dξ` is positive definite and the atom
  is conditionally negative definite; so is the sum.
* Conversely, the two-point family `(1, −1)` at `(n, 0)` gives `A(n) ≥ A(0) = 0` (`A` is even), and
  nonnegativity of `A` at the integers is RH (`riemannHypothesis_iff_liClockCenterAverage_nonneg`).

Under RH the Lévy measure of `A` is `Σ_γ ½ (P_α(ξ − β) + P_α(ξ + β))`: Cauchy densities at the
reciprocal ordinates `±γ/(1 + γ²)`.

**The Euler shadow is a Lévy exponent in every world** (`isCondNegDef_liClockEulerShadow_abs`).
Each shadow atom is `1 − e^{−α|t|} cos(βt)` with `α = (1 − Im a)/|a − i|² > 0` for every zero,
on or off the line, so `t ↦ F(|t|)` is conditionally negative definite without hypothesis. Since
RH is `A = F` (`riemannHypothesis_iff_liClockCenterAverage_eq_eulerShadow`), RH says that the
critical-line clock coincides with this unconditional Lévy exponent built from Euler data.
-/

noncomputable section

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Conditional negative definiteness of a real function on `ℝ`. -/
def IsCondNegDef (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (t c : Fin n → ℝ), ∑ i, c i = 0 → ∑ i, ∑ j, c i * c j * f (t i - t j) ≤ 0

/-! ### Positive definiteness of damped cosines -/

/-- `Σ_{i,j} c_i c_j cos((t_i − t_j)η) = (Σ c_i cos(t_i η))² + (Σ c_i sin(t_i η))² ≥ 0`. -/
theorem sum_sum_mul_cos_sub_nonneg {n : ℕ} (t c : Fin n → ℝ) (η : ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * Real.cos ((t i - t j) * η) := by
  have h : ∑ i, ∑ j, c i * c j * Real.cos ((t i - t j) * η) =
      (∑ i, c i * Real.cos (t i * η)) ^ 2 + (∑ i, c i * Real.sin (t i * η)) ^ 2 := by
    simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sub_mul, Real.cos_sub]
    ring
  rw [h]
  positivity

/-- **Poisson form of the two-sided exponential.** `e^{−α|x|} = ∫ P₁(ξ) cos(αxξ) dξ`. -/
theorem exp_neg_mul_abs_eq_integral_halfPlanePoisson {α : ℝ} (hα : 0 < α) (x : ℝ) :
    Real.exp (-(α * |x|)) = ∫ ξ : ℝ, halfPlanePoisson 1 ξ * Real.cos (α * x * ξ) := by
  -- reduce to `x ≥ 0`: both sides are even in `x`
  suffices key : ∀ y : ℝ, 0 ≤ y →
      Real.exp (-(α * y)) = ∫ ξ : ℝ, halfPlanePoisson 1 ξ * Real.cos (α * y * ξ) by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact key x hx
    · rw [abs_of_nonpos hx, key (-x) (by linarith)]
      congr 1; funext ξ
      rw [show α * -x * ξ = -(α * x * ξ) by ring, Real.cos_neg]
  intro y hy
  set F : ℂ → ℂ := fun z => Complex.exp (I * ((α * y : ℝ) : ℂ) * z) with hF
  have hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ F z := fun z _ => by
    simp only [hF]; fun_prop
  have hbd : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ 1 := by
    intro z hz
    simp only [hF, Complex.norm_exp]
    rw [Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, zero_mul, one_mul, zero_sub, sub_zero, zero_add]
    have : 0 ≤ α * y := mul_nonneg hα.le hy
    nlinarith
  have hrep := integral_halfPlanePoisson_one_mul_eq_apply_I hdiff hbd
  have hFI : F I = (Real.exp (-(α * y)) : ℂ) := by
    simp only [hF]
    rw [show I * ((α * y : ℝ) : ℂ) * I = ((-(α * y) : ℝ) : ℂ) by
      push_cast; ring_nf; rw [Complex.I_sq]; ring, ← Complex.ofReal_exp]
  rw [hFI] at hrep
  have hint : Integrable (fun ξ : ℝ => (halfPlanePoisson 1 ξ : ℂ) * F ξ) := by
    refine (integrable_halfPlanePoisson one_pos).ofReal.mul_bdd
      (Continuous.aestronglyMeasurable (by simp only [hF]; fun_prop))
      (Filter.Eventually.of_forall fun ξ => hbd ξ (by simp))
  have hre := congrArg Complex.re hrep
  rw [Complex.ofReal_re] at hre
  rw [← hre, show (∫ ξ : ℝ, (halfPlanePoisson 1 ξ : ℂ) * F ξ).re =
      RCLike.re (∫ ξ : ℝ, (halfPlanePoisson 1 ξ : ℂ) * F ξ) from rfl, ← integral_re hint]
  congr 1; funext ξ
  simp only [hF, RCLike.re_to_complex]
  rw [show I * ((α * y : ℝ) : ℂ) * (ξ : ℂ) = ((α * y * ξ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Damped cosines are positive definite.** For `α > 0`,
`Σ_{i,j} c_i c_j e^{−α|t_i − t_j|} cos(β(t_i − t_j)) ≥ 0`. -/
theorem sum_sum_mul_exp_abs_cos_nonneg {α : ℝ} (hα : 0 < α) (β : ℝ) {n : ℕ} (t c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (Real.exp (-(α * |t i - t j|)) * Real.cos (β * (t i - t j))) := by
  have hP := integrable_halfPlanePoisson (c := 1) one_pos
  have hcosint : ∀ s η : ℝ, Integrable fun ξ : ℝ => halfPlanePoisson 1 ξ * Real.cos (s * ξ + η) :=
    fun s η => hP.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  -- pointwise integral representation of each kernel value
  have hker : ∀ x : ℝ, Real.exp (-(α * |x|)) * Real.cos (β * x) =
      ∫ ξ : ℝ, halfPlanePoisson 1 ξ *
        ((Real.cos (x * (α * ξ + β)) + Real.cos (x * (α * ξ - β))) / 2) := by
    intro x
    rw [exp_neg_mul_abs_eq_integral_halfPlanePoisson hα x, ← integral_mul_const]
    congr 1; funext ξ
    rw [show x * (α * ξ + β) = α * x * ξ + β * x by ring,
      show x * (α * ξ - β) = α * x * ξ - β * x by ring, Real.cos_add, Real.cos_sub]
    ring
  have hint : ∀ x : ℝ, Integrable fun ξ : ℝ => halfPlanePoisson 1 ξ *
      ((Real.cos (x * (α * ξ + β)) + Real.cos (x * (α * ξ - β))) / 2) := by
    intro x
    have h1 := hcosint (x * α) (x * β)
    have h2 := hcosint (x * α) (-(x * β))
    refine ((h1.add h2).div_const 2).congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply]
    rw [show x * α * ξ + x * β = x * (α * ξ + β) by ring,
      show x * α * ξ + -(x * β) = x * (α * ξ - β) by ring]
    ring
  simp_rw [hker]
  have hswap : ∑ i, ∑ j, c i * c j * ∫ ξ : ℝ, halfPlanePoisson 1 ξ *
        ((Real.cos ((t i - t j) * (α * ξ + β)) + Real.cos ((t i - t j) * (α * ξ - β))) / 2) =
      ∫ ξ : ℝ, halfPlanePoisson 1 ξ * ((∑ i, ∑ j, c i * c j * Real.cos ((t i - t j) * (α * ξ + β)) +
        ∑ i, ∑ j, c i * c j * Real.cos ((t i - t j) * (α * ξ - β))) / 2) := by
    have hpt : ∀ ξ : ℝ, halfPlanePoisson 1 ξ *
        ((∑ i, ∑ j, c i * c j * Real.cos ((t i - t j) * (α * ξ + β)) +
          ∑ i, ∑ j, c i * c j * Real.cos ((t i - t j) * (α * ξ - β))) / 2) =
        ∑ i, ∑ j, c i * c j * (halfPlanePoisson 1 ξ *
          ((Real.cos ((t i - t j) * (α * ξ + β)) + Real.cos ((t i - t j) * (α * ξ - β))) / 2)) := by
      intro ξ
      rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
      (hint (t i - t j)).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hint (t i - t j)).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul (c i * c j) _).symm
  rw [hswap]
  refine integral_nonneg fun ξ => mul_nonneg (halfPlanePoisson_pos one_pos ξ).le ?_
  have h1 := sum_sum_mul_cos_sub_nonneg t c (α * ξ + β)
  have h2 := sum_sum_mul_cos_sub_nonneg t c (α * ξ - β)
  positivity

/-! ### The on-line atom -/

/-- For real `a`, `i t/(a − i) = −t/(a² + 1) + i ta/(a² + 1)`. -/
private theorem I_mul_div_real_sub_I' (t a : ℝ) :
    I * t / ((a : ℂ) - I) = ((-t / (a ^ 2 + 1) : ℝ) : ℂ) + ((t * a / (a ^ 2 + 1) : ℝ) : ℂ) * I := by
  have hne : (a : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hd' : (a ^ 2 + 1 : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hne]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    field_simp
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    field_simp
    ring

/-- On the line the averaged atom is `1 − e^{−α|t|} cos(βt)`, `α = 1/(a² + 1)`, `β = a/(a² + 1)`. -/
theorem centerClockAverage_eq_damped_cos {a : ℂ} (ha : a.im = 0) (t : ℝ) :
    centerClockAverage t a =
      1 - Real.exp (-((1 / (a.re ^ 2 + 1)) * |t|)) * Real.cos ((a.re / (a.re ^ 2 + 1)) * t) := by
  have haα : a = (a.re : ℂ) := by apply Complex.ext <;> simp [ha]
  have heven : centerClockAverage t a = centerClockAverage |t| a := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, centerClockAverage_neg]
  rw [heven, centerClockAverage_eq_of_im_eq_zero ha (abs_nonneg t), haα,
    I_mul_div_real_sub_I', Complex.sub_re, Complex.one_re, Complex.exp_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, mul_one, zero_add, add_zero]
  have h1 : -|t| / (a.re ^ 2 + 1) = -(1 / (a.re ^ 2 + 1) * |t|) := by ring
  have h2 : Real.cos (|t| * a.re / (a.re ^ 2 + 1)) = Real.cos (a.re / (a.re ^ 2 + 1) * t) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]; ring_nf
    · rw [abs_of_nonpos ht, show -t * a.re / (a.re ^ 2 + 1) = -(a.re / (a.re ^ 2 + 1) * t) by ring,
        Real.cos_neg]
  rw [h1, h2]

/-- **Each on-line averaged atom is conditionally negative definite.** -/
theorem isCondNegDef_centerClockAverage_of_im_eq_zero {a : ℂ} (ha : a.im = 0) :
    IsCondNegDef fun t => centerClockAverage t a := by
  intro n t c hc
  have hα : 0 < 1 / (a.re ^ 2 + 1) := by positivity
  have hpd := sum_sum_mul_exp_abs_cos_nonneg hα (a.re / (a.re ^ 2 + 1)) t c
  simp_rw [centerClockAverage_eq_damped_cos ha]
  have hsplit : ∑ i, ∑ j, c i * c j * (1 - Real.exp (-(1 / (a.re ^ 2 + 1) * |t i - t j|)) *
        Real.cos (a.re / (a.re ^ 2 + 1) * (t i - t j))) =
      (∑ i, c i) * (∑ j, c j) - ∑ i, ∑ j, c i * c j *
        (Real.exp (-(1 / (a.re ^ 2 + 1) * |t i - t j|)) *
          Real.cos (a.re / (a.re ^ 2 + 1) * (t i - t j))) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hc, zero_mul]
  linarith

/-! ### The averaged clock -/

private theorem xiSpectralPoint_im_eq_zero_of_rh' (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 0 := by
  have h := (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) _
    (xi_eq_zero_of_mem_divisor_support q.1)
  have hs : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    rw [xiSpectralPoint]; simp [Complex.mul_im]
  rw [hs, h]
  norm_num

private theorem summable_centerClockAverage (t : ℝ) :
    Summable fun q : XiZeroCopy => centerClockAverage t (xiSpectralPoint q) := by
  have h := summable_centerClockAtomExt |t|
  refine h.congr fun q => ?_
  rw [← centerClockAverage_eq_atomExt (abs_nonneg t)]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, centerClockAverage_neg]

/-- Under RH the averaged clock is conditionally negative definite. -/
theorem isCondNegDef_liClockCenterAverage_of_rh (hRH : RiemannHypothesis) :
    IsCondNegDef liClockCenterAverage := by
  intro n t c hc
  have hterm : ∀ q : XiZeroCopy,
      ∑ i, ∑ j, c i * c j * centerClockAverage (t i - t j) (xiSpectralPoint q) ≤ 0 :=
    fun q => isCondNegDef_centerClockAverage_of_im_eq_zero (xiSpectralPoint_im_eq_zero_of_rh' hRH q)
      n t c hc
  have hsum : ∑ i, ∑ j, c i * c j * liClockCenterAverage (t i - t j) =
      ∑' q : XiZeroCopy, ∑ i, ∑ j, c i * c j * centerClockAverage (t i - t j) (xiSpectralPoint q) := by
    unfold liClockCenterAverage
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ =>
      (summable_centerClockAverage (t i - t j)).mul_left _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun j _ => (summable_centerClockAverage (t i - t j)).mul_left _)]
    exact Finset.sum_congr rfl fun j _ =>
      ((summable_centerClockAverage (t i - t j)).tsum_mul_left (c i * c j)).symm
  rw [hsum]
  exact tsum_nonpos hterm

private theorem liClockCenterAverage_zero : liClockCenterAverage 0 = 0 := by
  unfold liClockCenterAverage centerClockAverage centerClockAtom
  simp

/-- **RH ⟺ the center-averaged Li clock is conditionally negative definite** (a symmetric Lévy
exponent). -/
theorem riemannHypothesis_iff_isCondNegDef_liClockCenterAverage :
    RiemannHypothesis ↔ IsCondNegDef liClockCenterAverage := by
  refine ⟨isCondNegDef_liClockCenterAverage_of_rh, fun hC => ?_⟩
  rw [riemannHypothesis_iff_liClockCenterAverage_nonneg]
  intro m
  have h := hC 2 ![(m : ℝ), 0] ![1, -1] (by simp)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sub_self, sub_zero, zero_sub, liClockCenterAverage_zero, liClockCenterAverage_neg] at h
  linarith

/-! ### The Euler shadow is a Lévy exponent in every world -/

/-- `i t/(a − i) = t(Im a − 1)/D + i t Re a/D` with `D = |a − i|²`. -/
private theorem I_mul_div_sub_I_eq (t : ℝ) (a : ℂ) (hD : Complex.normSq (a - I) ≠ 0) :
    I * t / (a - I) = ((t * (a.im - 1) / Complex.normSq (a - I) : ℝ) : ℂ) +
      ((t * a.re / Complex.normSq (a - I) : ℝ) : ℂ) * I := by
  have hne : a - I ≠ 0 := fun h => hD (by rw [h, map_zero])
  have hD' : Complex.normSq (a - I) = a.re ^ 2 + (a.im - 1) ^ 2 := by
    rw [Complex.normSq_apply]; simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im,
      Complex.I_im]; ring
  rw [div_eq_iff hne, hD']
  have hpos : a.re ^ 2 + (a.im - 1) ^ 2 ≠ 0 := by rw [← hD']; exact hD
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    field_simp
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    field_simp
    ring

/-- At `|t|` the shadow atom is the damped cosine `1 − e^{−α|t|} cos(βt)` with
`α = (1 − Im a)/|a − i|²`, `β = Re a/|a − i|²`. -/
theorem centerClockShadowAtom_abs_eq {a : ℂ} (ha : a.im < 1) (t : ℝ) :
    centerClockShadowAtom |t| a =
      1 - Real.exp (-((1 - a.im) / Complex.normSq (a - I) * |t|)) *
        Real.cos (a.re / Complex.normSq (a - I) * t) := by
  have hD : Complex.normSq (a - I) ≠ 0 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im]
    nlinarith [sq_nonneg a.re]
  unfold centerClockShadowAtom
  rw [I_mul_div_sub_I_eq |t| a hD, Complex.sub_re, Complex.one_re, Complex.exp_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, mul_one, zero_add, add_zero]
  have h1 : |t| * (a.im - 1) / Complex.normSq (a - I) =
      -((1 - a.im) / Complex.normSq (a - I) * |t|) := by ring
  have h2 : Real.cos (|t| * a.re / Complex.normSq (a - I)) =
      Real.cos (a.re / Complex.normSq (a - I) * t) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]; ring_nf
    · rw [abs_of_nonpos ht, show -t * a.re / Complex.normSq (a - I) =
        -(a.re / Complex.normSq (a - I) * t) by ring, Real.cos_neg]
  rw [h1, h2]

/-- Every shadow atom is conditionally negative definite in `|t|`, on or off the line. -/
theorem isCondNegDef_centerClockShadowAtom_abs {a : ℂ} (ha : a.im < 1) :
    IsCondNegDef fun t => centerClockShadowAtom |t| a := by
  intro n t c hc
  have hD : 0 < Complex.normSq (a - I) := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im]
    nlinarith [sq_nonneg a.re]
  have hα : 0 < (1 - a.im) / Complex.normSq (a - I) := div_pos (by linarith) hD
  have hpd := sum_sum_mul_exp_abs_cos_nonneg hα (a.re / Complex.normSq (a - I)) t c
  simp_rw [centerClockShadowAtom_abs_eq ha]
  have hsplit : ∑ i, ∑ j, c i * c j *
        (1 - Real.exp (-((1 - a.im) / Complex.normSq (a - I) * |t i - t j|)) *
          Real.cos (a.re / Complex.normSq (a - I) * (t i - t j))) =
      (∑ i, c i) * (∑ j, c j) - ∑ i, ∑ j, c i * c j *
        (Real.exp (-((1 - a.im) / Complex.normSq (a - I) * |t i - t j|)) *
          Real.cos (a.re / Complex.normSq (a - I) * (t i - t j))) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hc, zero_mul]
  linarith

/-- A shadow atom of a zero copy at a nonnegative clock lies in `[0, (2t + t²)/‖a‖²]`. -/
private theorem abs_centerClockShadowAtom_le (q : XiZeroCopy) {t : ℝ} (ht : 0 ≤ t) :
    |centerClockShadowAtom t (xiSpectralPoint q)| ≤ (2 * t + t ^ 2) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  set a := xiSpectralPoint q
  have hs : a.im = 1 / 2 - ((q.1 : ℂ)).re := by
    show (xiSpectralPoint q).im = _
    rw [xiSpectralPoint]; simp [Complex.mul_im]
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hy : a.im ≤ 1 / 2 := by rw [hs]; linarith
  have hy' : -(1 / 2) ≤ a.im := by rw [hs]; linarith
  have h150 := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  have hna : ‖a‖ ^ (2 : ℕ) = a.re ^ 2 + a.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hDdef : Complex.normSq (a - I) = a.re ^ 2 + (a.im - 1) ^ 2 := by
    rw [Complex.normSq_apply]; simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im,
      Complex.I_im]; ring
  have hDge : ‖a‖ ^ (2 : ℕ) ≤ Complex.normSq (a - I) := by rw [hna, hDdef]; nlinarith
  have hapos : 0 < ‖a‖ ^ (2 : ℕ) := by linarith
  have hDpos : 0 < Complex.normSq (a - I) := lt_of_lt_of_le hapos hDge
  have heq := centerClockShadowAtom_abs_eq (a := a) (by linarith) t
  rw [abs_of_nonneg ht] at heq
  rw [heq]
  set α := (1 - a.im) / Complex.normSq (a - I)
  set β := a.re / Complex.normSq (a - I)
  have hα0 : 0 ≤ α := div_nonneg (by linarith) hDpos.le
  have hα1 : α ≤ 2 / ‖a‖ ^ (2 : ℕ) := by
    simp only [α]
    rw [div_le_div_iff₀ hDpos hapos]; nlinarith
  have hβ2 : β ^ 2 ≤ 1 / ‖a‖ ^ (2 : ℕ) := by
    simp only [β, div_pow]
    rw [div_le_div_iff₀ (by positivity) hapos]
    have : a.re ^ 2 ≤ Complex.normSq (a - I) := by rw [hDdef]; nlinarith
    nlinarith [sq_nonneg (Complex.normSq (a - I)), mul_le_mul this hDge (by positivity) hDpos.le]
  have hx : -(α * t) ≤ 0 := by nlinarith
  have hE : Real.exp (-(α * t)) ≤ 1 := Real.exp_le_one_iff.mpr hx
  have hE0 : 0 < Real.exp (-(α * t)) := Real.exp_pos _
  have hlin : 1 - Real.exp (-(α * t)) ≤ α * t := by
    have := Real.add_one_le_exp (-(α * t)); linarith
  have hcos0 : 0 ≤ 1 - Real.cos (β * t) := by linarith [Real.cos_le_one (β * t)]
  have hcos : 1 - Real.cos (β * t) ≤ (β * t) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := β * t); linarith
  have hsplit : 1 - Real.exp (-(α * t)) * Real.cos (β * t) =
      (1 - Real.exp (-(α * t))) + Real.exp (-(α * t)) * (1 - Real.cos (β * t)) := by ring
  have hnn : 0 ≤ 1 - Real.exp (-(α * t)) * Real.cos (β * t) := by
    rw [hsplit]; have := mul_nonneg hE0.le hcos0; linarith
  rw [abs_of_nonneg hnn, hsplit]
  have hb : Real.exp (-(α * t)) * (1 - Real.cos (β * t)) ≤ (β * t) ^ 2 / 2 :=
    (mul_le_of_le_one_left hcos0 hE).trans hcos
  have ht2 : (β * t) ^ 2 / 2 ≤ t ^ 2 / ‖a‖ ^ (2 : ℕ) := by
    have h1 : (β * t) ^ 2 ≤ t ^ 2 / ‖a‖ ^ (2 : ℕ) := by
      rw [mul_pow, div_eq_mul_inv, mul_comm (t ^ 2)]
      exact mul_le_mul_of_nonneg_right (by rwa [one_div] at hβ2) (sq_nonneg t)
    have h2 : 0 ≤ (β * t) ^ 2 := sq_nonneg _
    linarith
  have hat : α * t ≤ 2 * t / ‖a‖ ^ (2 : ℕ) :=
    calc α * t ≤ 2 / ‖a‖ ^ (2 : ℕ) * t := mul_le_mul_of_nonneg_right hα1 ht
      _ = 2 * t / ‖a‖ ^ (2 : ℕ) := by ring
  calc (1 - Real.exp (-(α * t))) + Real.exp (-(α * t)) * (1 - Real.cos (β * t))
      ≤ α * t + (β * t) ^ 2 / 2 := add_le_add hlin hb
    _ ≤ 2 * t / ‖a‖ ^ (2 : ℕ) + t ^ 2 / ‖a‖ ^ (2 : ℕ) := add_le_add hat ht2
    _ = (2 * t + t ^ 2) / ‖a‖ ^ (2 : ℕ) := by ring

private theorem summable_centerClockShadowAtom {t : ℝ} (ht : 0 ≤ t) :
    Summable fun q : XiZeroCopy => centerClockShadowAtom t (xiSpectralPoint q) := by
  refine Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left (2 * t + t ^ 2)) fun q => ?_
  rw [Real.norm_eq_abs, mul_one_div]
  exact abs_centerClockShadowAtom_le q ht

/-- **The Euler shadow is a Lévy exponent in every world.** `t ↦ F(|t|)` is conditionally negative
definite, without any hypothesis on the zeros: every zero, on or off the line, contributes a damped
cosine with damping `(1 − Im a)/|a − i|² > 0`. -/
theorem isCondNegDef_liClockEulerShadow_abs :
    IsCondNegDef fun t => liClockEulerShadow |t| := by
  intro n t c hc
  have hterm : ∀ q : XiZeroCopy,
      ∑ i, ∑ j, c i * c j * centerClockShadowAtom |t i - t j| (xiSpectralPoint q) ≤ 0 := by
    intro q
    have hs : (xiSpectralPoint q).im = 1 / 2 - ((q.1 : ℂ)).re := by
      rw [xiSpectralPoint]; simp [Complex.mul_im]
    obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
    exact isCondNegDef_centerClockShadowAtom_abs (a := xiSpectralPoint q) (by rw [hs]; linarith)
      n t c hc
  have hsum : ∑ i, ∑ j, c i * c j * liClockEulerShadow |t i - t j| =
      ∑' q : XiZeroCopy, ∑ i, ∑ j, c i * c j * centerClockShadowAtom |t i - t j| (xiSpectralPoint q) := by
    unfold liClockEulerShadow
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ =>
      (summable_centerClockShadowAtom (abs_nonneg (t i - t j))).mul_left _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun j _ =>
      (summable_centerClockShadowAtom (abs_nonneg (t i - t j))).mul_left _)]
    exact Finset.sum_congr rfl fun j _ =>
      ((summable_centerClockShadowAtom (abs_nonneg (t i - t j))).tsum_mul_left (c i * c j)).symm
  rw [hsum]
  exact tsum_nonpos hterm

end RHTower
