import GaloisForLFunctions.FloorFreeArithmetic.QuantileDiscretizationOfAPrimeDensity
import GaloisForLFunctions.FloorFreeArithmetic.PositivityAdmitsEveryFiniteDatum
import GaloisForLFunctions.ArithmeticPositiveDuality.ATwoScaleIntegerNormOneOff

/-!
# Finite layers in discrete Euler products

For an abscissa `½ < Θ < 1`, ordinates `γ_j` and multiplicities `m_j`, the density

`w(t) = (e^t − Σ_j 2 m_j e^{Θt} cos(γ_j t))/t` for `t ≥ A`, `w(t) = 0` for `t < A`,

is a prime density once the cut `A` is beyond the length at which `e^t` dominates the layer. Its
Laplace transform is a combination of cut-off Frullani integrals, so the zeta function of the
continuous primes is explicit: with `F_A` the entire function with the single zero `0` and
`F_A(z) = exp(−∫_A^∞ e^{−zt}/t dt)` on `Re z > 0`,

`exp ∫ e^{−st} w(t) dt = ∏_j (F_A(s − ρ_j) F_A(s − ρ̄_j))^{m_j} / F_A(s − 1)`, `ρ_j = Θ + iγ_j`.

Quantile discretization gives discrete primes `p_k = e^{t_k} > 1` whose Euler product
`∏_k (1 − p_k^{−s})^{−1}` is, on `Re s > 1`, a function `G(s)/(s − 1)` with `G` holomorphic on
`Re s > ½` and vanishing there exactly at the points `Θ ± iγ_j` with `m_j ≠ 0`.

So an Euler product over a discrete set of primes, with a simple pole at `1`, can have any
prescribed finite set of zeros right of the critical line, at every depth, and no others there.

* `layerPrimeDensity`: the density as a prime density.
* `integral_cexp_mul_layerLogDensity`, `cexp_layer_eq`: its Laplace transform and zeta function.
* `layerRegular_eq_zero_iff`: the zeros of the regular factor.
* `exists_discrete_euler_product_with_layer`: the realization theorem.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.TwoScaleIntegerNormOneOff

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

variable {ι : Type*} [Fintype ι]

/-! ### The numerator of a layer -/

/-- The Chebyshev numerator of a layer: `e^t − Σ_j 2 m_j e^{Θt} cos(γ_j t)`. -/
def layerNumer (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (t : ℝ) : ℝ :=
  Real.exp t - ∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * t) * Real.cos (γ j * t))

theorem continuous_layerNumer (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) :
    Continuous (layerNumer Θ γ m) :=
  Real.continuous_exp.sub (continuous_finsetSum _ fun _ _ => continuous_const.mul
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))))

/-- The layer is at most `2M e^{Θt}` in modulus. -/
theorem abs_sum_layer_le (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (t : ℝ) :
    |∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * t) * Real.cos (γ j * t))| ≤
      2 * (∑ j, (m j : ℝ)) * Real.exp (Θ * t) := by
  have hE : 0 < Real.exp (Θ * t) := Real.exp_pos _
  calc |∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * t) * Real.cos (γ j * t))|
      ≤ ∑ j, |2 * (m j : ℝ) * (Real.exp (Θ * t) * Real.cos (γ j * t))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, 2 * (m j : ℝ) * Real.exp (Θ * t) := Finset.sum_le_sum fun j _ => by
        rw [abs_mul (2 * (m j : ℝ)), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (m j : ℝ)),
          abs_mul (Real.exp (Θ * t)), abs_of_pos hE]
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right hE.le (Real.abs_cos_le_one _)) (by positivity)
    _ = 2 * (∑ j, (m j : ℝ)) * Real.exp (Θ * t) := by rw [Finset.mul_sum, Finset.sum_mul]

/-- Beyond the domination length the numerator is at least `2 e^{Θt}`. -/
theorem two_mul_exp_le_layerNumer {Θ : ℝ} (hΘ : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ) {t : ℝ}
    (ht : dominationLength Θ (∑ j, (m j : ℝ)) ≤ t) :
    2 * Real.exp (Θ * t) ≤ layerNumer Θ γ m t := by
  have hM0 : (0 : ℝ) ≤ ∑ j, (m j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j)
  have hE : 0 < Real.exp (Θ * t) := Real.exp_pos _
  have h1Θ : 0 < 1 - Θ := by linarith only [hΘ]
  have h1 : Real.log (2 * (∑ j, (m j : ℝ)) + 2) ≤ t * (1 - Θ) := (div_le_iff₀ h1Θ).mp ht
  have h2 : 2 * (∑ j, (m j : ℝ)) + 2 ≤ Real.exp (t * (1 - Θ)) := by
    have h3 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by linarith only [hM0])] at h3
  have h4 : Real.exp t = Real.exp (Θ * t) * Real.exp (t * (1 - Θ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h5 := (abs_le.mp (abs_sum_layer_le Θ γ m t)).2
  have h6 : Real.exp (Θ * t) * (2 * (∑ j, (m j : ℝ)) + 2) ≤
      Real.exp (Θ * t) * Real.exp (t * (1 - Θ)) := mul_le_mul_of_nonneg_left h2 hE.le
  unfold layerNumer
  rw [h4]
  linarith only [h5, h6, mul_add (Real.exp (Θ * t)) (2 * (∑ j, (m j : ℝ))) 2,
    mul_comm (Real.exp (Θ * t)) (2 * (∑ j, (m j : ℝ)))]

/-- For `t ≥ 0` and `Θ ≤ 1` the numerator is at most `(1 + 2M) e^t`. -/
theorem layerNumer_le {Θ : ℝ} (hΘ : Θ ≤ 1) (γ : ι → ℝ) (m : ι → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    layerNumer Θ γ m t ≤ (1 + 2 * ∑ j, (m j : ℝ)) * Real.exp t := by
  have hM0 : (0 : ℝ) ≤ ∑ j, (m j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j)
  have h5 := (abs_le.mp (abs_sum_layer_le Θ γ m t)).1
  have h6 : Real.exp (Θ * t) ≤ Real.exp t :=
    Real.exp_le_exp.mpr (by nlinarith only [ht, hΘ])
  have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 2 * ∑ j, (m j : ℝ))
  unfold layerNumer
  linarith only [h5, h7, add_mul 1 (2 * ∑ j, (m j : ℝ)) (Real.exp t), one_mul (Real.exp t)]

/-- The numerator as a combination of complex exponentials. -/
theorem ofReal_layerNumer (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (u : ℝ) :
    ((layerNumer Θ γ m u : ℝ) : ℂ) = cexp u -
      ∑ j, (m j : ℂ) * (cexp (((Θ : ℂ) + γ j * I) * u) + cexp (((Θ : ℂ) - γ j * I) * u)) := by
  unfold layerNumer
  rw [Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← two_exp_cos Θ (γ j) u]
  push_cast
  ring

/-! ### The prime density of a layer -/

/-- The cut of a layer: one beyond the domination length. -/
def layerCut (Θ : ℝ) (m : ι → ℕ) : ℝ := dominationLength Θ (∑ j, (m j : ℝ)) + 1

theorem layerCut_pos {Θ : ℝ} (hΘ : Θ < 1) (m : ι → ℕ) : 0 < layerCut Θ m := by
  have h := dominationLength_pos hΘ
    (Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j) : (0 : ℝ) ≤ ∑ j, (m j : ℝ))
  unfold layerCut
  linarith only [h]

/-- The logarithmic prime density of a layer: `layerNumer/t` from the cut on. -/
def layerLogDensity (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (t : ℝ) : ℝ :=
  (Ici (layerCut Θ m)).indicator (fun t => layerNumer Θ γ m t / t) t

theorem measurable_layerLogDensity (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) :
    Measurable (layerLogDensity Θ γ m) :=
  ((continuous_layerNumer Θ γ m).measurable.div measurable_id).indicator measurableSet_Ici

theorem layerLogDensity_of_lt {Θ : ℝ} (γ : ι → ℝ) (m : ι → ℕ) {u : ℝ} (hu : u < layerCut Θ m) :
    layerLogDensity Θ γ m u = 0 :=
  Set.indicator_of_notMem (fun h => not_le.mpr hu (mem_Ici.mp h)) _

theorem layerLogDensity_of_le (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) {u : ℝ} (hu : layerCut Θ m ≤ u) :
    layerLogDensity Θ γ m u = layerNumer Θ γ m u / u :=
  Set.indicator_of_mem (mem_Ici.mpr hu) _

/-- From the cut on the density is at least `2Θ`. -/
theorem two_mul_le_layerLogDensity {Θ : ℝ} (h1 : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ)
    {u : ℝ} (hu : layerCut Θ m ≤ u) : 2 * Θ ≤ layerLogDensity Θ γ m u := by
  have hu0 : 0 < u := (layerCut_pos h1 m).trans_le hu
  rw [layerLogDensity_of_le Θ γ m hu, le_div_iff₀ hu0]
  have hdom : dominationLength Θ (∑ j, (m j : ℝ)) ≤ u := by
    unfold layerCut at hu
    linarith only [hu]
  have h2 := two_mul_exp_le_layerNumer h1 γ m hdom
  have h3 := Real.add_one_le_exp (Θ * u)
  linarith only [h2, h3]

theorem layerLogDensity_nonneg {Θ : ℝ} (h0 : 0 < Θ) (h1 : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ)
    (u : ℝ) : 0 ≤ layerLogDensity Θ γ m u := by
  rcases lt_or_ge u (layerCut Θ m) with h | h
  · rw [layerLogDensity_of_lt γ m h]
  · exact (mul_pos two_pos h0).le.trans (two_mul_le_layerLogDensity h1 γ m h)

/-- The density is at most `(1 + 2M) e^u / A`. -/
theorem layerLogDensity_le {Θ : ℝ} (h1 : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ) (u : ℝ) :
    layerLogDensity Θ γ m u ≤ (1 + 2 * ∑ j, (m j : ℝ)) / layerCut Θ m * Real.exp u := by
  have hA := layerCut_pos h1 m
  have hM0 : (0 : ℝ) ≤ ∑ j, (m j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j)
  rcases lt_or_ge u (layerCut Θ m) with h | h
  · rw [layerLogDensity_of_lt γ m h]
    positivity
  · have hu0 : 0 < u := hA.trans_le h
    rw [layerLogDensity_of_le Θ γ m h, div_mul_eq_mul_div]
    have hnum := layerNumer_le h1.le γ m hu0.le
    have hpos : 0 ≤ (1 + 2 * ∑ j, (m j : ℝ)) * Real.exp u := by positivity
    exact (div_le_div_of_nonneg_right hnum hu0.le).trans
      (div_le_div_of_nonneg_left hpos hA h)

/-- **The layer density is a prime density.** -/
def layerPrimeDensity {Θ : ℝ} (h0 : 0 < Θ) (h1 : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ) :
    PrimeDensity where
  w := layerLogDensity Θ γ m
  cut := layerCut Θ m
  floor := 2 * Θ
  cut_pos := layerCut_pos h1 m
  floor_pos := mul_pos two_pos h0
  measurable_w := measurable_layerLogDensity Θ γ m
  zero_of_lt := fun _ hu => layerLogDensity_of_lt γ m hu
  floor_le := fun _ hu => two_mul_le_layerLogDensity h1 γ m hu
  integrable := by
    intro σ hσ
    have hb : IntegrableOn (fun u : ℝ =>
        (1 + 2 * ∑ j, (m j : ℝ)) / layerCut Θ m * Real.exp (-(σ - 1) * u)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith only [hσ] : -(σ - 1) < 0) 0).const_mul _
    refine hb.mono' ?_ (Eventually.of_forall fun u => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable.mul
        (measurable_layerLogDensity Θ γ m)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (layerLogDensity_nonneg h0 h1 γ m u))]
      have h2 := mul_le_mul_of_nonneg_left (layerLogDensity_le h1 γ m u)
        (Real.exp_pos (-(σ * u))).le
      have e : Real.exp (-(σ * u)) * ((1 + 2 * ∑ j, (m j : ℝ)) / layerCut Θ m * Real.exp u) =
          (1 + 2 * ∑ j, (m j : ℝ)) / layerCut Θ m * Real.exp (-(σ - 1) * u) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      rw [e] at h2
      exact h2

/-! ### The Laplace transform of the layer density -/

/-- `e^{−zt}/t` is integrable beyond a positive cut, for `Re z > 0`. -/
theorem integrableOn_cexp_neg_mul_div {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => cexp (-(z * t)) / t) (Ioi A) := by
  have hb : IntegrableOn (fun t : ℝ => Real.exp (-z.re * t) / A) (Ioi A) :=
    (integrableOn_exp_mul_Ioi (by linarith only [hz] : -z.re < 0) A).div_const A
  refine hb.mono' ?_ ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
  · exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(z * t))).measurable.div
      Complex.measurable_ofReal).aestronglyMeasurable
  · have ht0 : 0 < t := hA.trans ht
    rw [norm_div, norm_cexp_neg_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le,
      show -z.re * t = -(z.re * t) by ring]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hA (le_of_lt ht)

/-- The Frullani integral beyond the cut. -/
theorem integral_cexp_neg_mul_div {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi A, cexp (-(z * t)) / t = -frullaniCutoffLog A z := by
  rw [frullaniCutoffLog_eq_neg_integral_of_re_pos hA hz, neg_neg]

/-- **The Laplace transform of the layer density** is a combination of cut-off Frullani
logarithms. -/
theorem integral_cexp_mul_layerLogDensity {Θ : ℝ} (h1 : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (layerLogDensity Θ γ m u : ℂ) =
      -frullaniCutoffLog (layerCut Θ m) (s - 1) +
        ∑ j, (m j : ℂ) * (frullaniCutoffLog (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) +
          frullaniCutoffLog (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I))) := by
  have hA := layerCut_pos h1 m
  have hre1 : 0 < (s - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have hρ : ∀ j, 0 < (s - ((Θ : ℂ) + γ j * I)).re := fun j => by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith only [hs, h1]
  have hρ' : ∀ j, 0 < (s - ((Θ : ℂ) - γ j * I)).re := fun j => by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero]
    linarith only [hs, h1]
  -- the integrand, beyond the cut, as a combination of the functions `e^{−zu}/u`
  have hfun : ∀ u : ℝ, cexp (-(s * u)) * (layerLogDensity Θ γ m u : ℂ) =
      (Ici (layerCut Θ m)).indicator (fun u : ℝ => cexp (-((s - 1) * u)) / u -
        ∑ j, (m j : ℂ) * (cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u +
          cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u)) u := by
    intro u
    by_cases hu : u ∈ Ici (layerCut Θ m)
    · have e1 : cexp (-(s * u)) * cexp u = cexp (-((s - 1) * u)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      have e2 : ∀ w : ℂ, cexp (-(s * u)) * cexp (w * u) = cexp (-((s - w) * u)) := fun w => by
        rw [← Complex.exp_add]
        congr 1
        ring
      simp only [Set.indicator_of_mem hu]
      rw [layerLogDensity_of_le Θ γ m (mem_Ici.mp hu), Complex.ofReal_div, ofReal_layerNumer,
        mul_div_assoc', mul_sub, e1, Finset.mul_sum, sub_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, mul_add, e2, e2, mul_div_assoc, add_div]
    · simp only [Set.indicator_of_notMem hu]
      rw [layerLogDensity_of_lt γ m (not_le.mp fun h => hu (mem_Ici.mpr h)), Complex.ofReal_zero,
        mul_zero]
  have hinter : Ioi (0 : ℝ) ∩ Ici (layerCut Θ m) = Ici (layerCut Θ m) :=
    inter_eq_right.mpr (Ici_subset_Ioi.mpr hA)
  rw [setIntegral_congr_fun measurableSet_Ioi fun u _ => hfun u,
    setIntegral_indicator measurableSet_Ici, hinter, integral_Ici_eq_integral_Ioi]
  -- the three kinds of integrals
  have hI1 := integrableOn_cexp_neg_mul_div hA hre1
  have hIj : ∀ j, IntegrableOn (fun u : ℝ => (m j : ℂ) *
      (cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u +
        cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u)) (Ioi (layerCut Θ m)) := fun j =>
    ((integrableOn_cexp_neg_mul_div hA (hρ j)).add
      (integrableOn_cexp_neg_mul_div hA (hρ' j))).const_mul _
  have hIS : IntegrableOn (fun u : ℝ => ∑ j, (m j : ℂ) *
      (cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u +
        cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u)) (Ioi (layerCut Θ m)) :=
    integrable_finsetSum _ fun j _ => hIj j
  have ej : ∀ j, ∫ u in Ioi (layerCut Θ m), (m j : ℂ) *
      (cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u +
        cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u) =
      (m j : ℂ) * (-frullaniCutoffLog (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) +
        -frullaniCutoffLog (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I))) := by
    intro j
    have hadd : ∫ u in Ioi (layerCut Θ m),
        (cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u +
          cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u) =
        (∫ u in Ioi (layerCut Θ m), cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u) +
          ∫ u in Ioi (layerCut Θ m), cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u :=
      integral_add (integrableOn_cexp_neg_mul_div hA (hρ j))
        (integrableOn_cexp_neg_mul_div hA (hρ' j))
    rw [integral_const_mul, hadd, integral_cexp_neg_mul_div hA (hρ j),
      integral_cexp_neg_mul_div hA (hρ' j)]
  have eS : ∫ u in Ioi (layerCut Θ m), ∑ j, (m j : ℂ) *
      (cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u +
        cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u) =
      ∑ j, (m j : ℂ) * (-frullaniCutoffLog (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) +
        -frullaniCutoffLog (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I))) := by
    rw [integral_finsetSum _ fun j _ => hIj j]
    exact Finset.sum_congr rfl fun j _ => ej j
  have e12 : ∫ u in Ioi (layerCut Θ m), (cexp (-((s - 1) * u)) / u -
      ∑ j, (m j : ℂ) * (cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u +
        cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u)) =
      (∫ u in Ioi (layerCut Θ m), cexp (-((s - 1) * u)) / u) -
        ∫ u in Ioi (layerCut Θ m), ∑ j, (m j : ℂ) *
          (cexp (-((s - ((Θ : ℂ) + γ j * I)) * u)) / u +
            cexp (-((s - ((Θ : ℂ) - γ j * I)) * u)) / u) :=
    integral_sub hI1 hIS
  rw [e12, integral_cexp_neg_mul_div hA hre1, eS, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The zeta function of the continuous primes -/

/-- The nonvanishing entire factor of the cut-off Frullani function: `F_A(z) = z · U_A(z)`. -/
def frullaniUnit (A : ℝ) (z : ℂ) : ℂ := cexp (-frullaniHead A z - (frullaniTailConst A : ℂ))

theorem frullaniCutoffFactor_eq_mul_unit (A : ℝ) (z : ℂ) :
    frullaniCutoffFactor A z = z * frullaniUnit A z := rfl

theorem frullaniUnit_ne_zero (A : ℝ) (z : ℂ) : frullaniUnit A z ≠ 0 := Complex.exp_ne_zero _

theorem differentiable_frullaniUnit {A : ℝ} (hA : 0 < A) : Differentiable ℂ (frullaniUnit A) :=
  ((differentiable_frullaniHead hA).neg.sub_const _).cexp

/-- The regular factor of the zeta function of a layer:
`∏_j (F_A(s − ρ_j) F_A(s − ρ̄_j))^{m_j} / U_A(s − 1)`. -/
def layerRegular (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (s : ℂ) : ℂ :=
  (∏ j, (frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) *
    frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I))) ^ m j) *
    (frullaniUnit (layerCut Θ m) (s - 1))⁻¹

theorem differentiable_layerRegular {Θ : ℝ} (h1 : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ) :
    Differentiable ℂ (layerRegular Θ γ m) := by
  have hA := layerCut_pos h1 m
  have hF := differentiable_frullaniCutoffFactor hA
  have hU := differentiable_frullaniUnit hA
  have hprod : Differentiable ℂ (∏ j, fun s : ℂ =>
      (frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) *
        frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I))) ^ m j) :=
    Differentiable.finsetProd fun j _ => ((hF.comp (differentiable_id.sub_const _)).mul
      (hF.comp (differentiable_id.sub_const _))).pow _
  rw [Finset.prod_fn] at hprod
  unfold layerRegular
  exact hprod.mul ((hU.comp (differentiable_id.sub_const _)).inv fun s =>
    frullaniUnit_ne_zero _ _)

/-- **The zeros of the regular factor are the points of the layer.** -/
theorem layerRegular_eq_zero_iff (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (s : ℂ) :
    layerRegular Θ γ m s = 0 ↔
      ∃ j, m j ≠ 0 ∧ (s = (Θ : ℂ) + γ j * I ∨ s = (Θ : ℂ) - γ j * I) := by
  rw [layerRegular, mul_eq_zero, or_iff_left (inv_ne_zero (frullaniUnit_ne_zero _ _)),
    Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, -, hj⟩
    have hm : m j ≠ 0 := fun h => by
      rw [h, pow_zero] at hj
      exact one_ne_zero hj
    rcases mul_eq_zero.mp ((pow_eq_zero_iff hm).mp hj) with h | h
    · exact ⟨j, hm, Or.inl (sub_eq_zero.mp ((frullaniCutoffFactor_eq_zero_iff _ _).mp h))⟩
    · exact ⟨j, hm, Or.inr (sub_eq_zero.mp ((frullaniCutoffFactor_eq_zero_iff _ _).mp h))⟩
  · rintro ⟨j, hm, h | h⟩
    · exact ⟨j, Finset.mem_univ j, (pow_eq_zero_iff hm).mpr (mul_eq_zero.mpr
        (Or.inl ((frullaniCutoffFactor_eq_zero_iff _ _).mpr (sub_eq_zero.mpr h))))⟩
    · exact ⟨j, Finset.mem_univ j, (pow_eq_zero_iff hm).mpr (mul_eq_zero.mpr
        (Or.inr ((frullaniCutoffFactor_eq_zero_iff _ _).mpr (sub_eq_zero.mpr h))))⟩

/-- **The zeta function of the continuous primes of a layer** is the regular factor over
`s − 1`, on `Re s > 1`. -/
theorem cexp_layer_eq {Θ : ℝ} (h1 : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ) {s : ℂ} (hs : 1 < s.re) :
    cexp (∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (layerLogDensity Θ γ m u : ℂ)) =
      layerRegular Θ γ m s / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := fun h => by
    have hr := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith only [hr, hs]
  have hne : ∀ j, s - ((Θ : ℂ) + γ j * I) ≠ 0 := fun j h => by
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero,
      Complex.zero_re] at hr
    linarith only [hr, hs, h1]
  have hne' : ∀ j, s - ((Θ : ℂ) - γ j * I) ≠ 0 := fun j h => by
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, Complex.zero_re] at hr
    linarith only [hr, hs, h1]
  have hFj : ∀ j, cexp ((m j : ℂ) *
      (frullaniCutoffLog (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) +
        frullaniCutoffLog (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I)))) =
      (frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) *
        frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I))) ^ m j := fun j => by
    rw [Complex.exp_nat_mul, Complex.exp_add,
      frullaniCutoffFactor_eq_cexp_of_ne_zero _ (hne j),
      frullaniCutoffFactor_eq_cexp_of_ne_zero _ (hne' j)]
  rw [integral_cexp_mul_layerLogDensity h1 γ m hs, Complex.exp_add, Complex.exp_neg,
    Complex.exp_sum, Finset.prod_congr rfl fun j _ => hFj j,
    ← frullaniCutoffFactor_eq_cexp_of_ne_zero _ hs1, frullaniCutoffFactor_eq_mul_unit,
    layerRegular, mul_inv, div_eq_mul_inv]
  ring

/-! ### The realization theorem -/

/-- **Discrete Euler products admit every finite layer.** For `½ < Θ < 1`, ordinates `γ_j` and
multiplicities `m_j` there are discrete primes `p_k = e^{t_k} > 1`, strictly increasing, and a
function `G` holomorphic on `Re s > ½`, such that the Euler product `∏_k (1 − p_k^{−s})^{−1}` is
`G(s)/(s − 1)` on `Re s > 1`, and `G` vanishes on `Re s > ½` exactly at the points `Θ ± iγ_j`
with `m_j ≠ 0`. -/
theorem exists_discrete_euler_product_with_layer {Θ : ℝ} (h0 : 1 / 2 < Θ) (h1 : Θ < 1)
    (γ : ι → ℝ) (m : ι → ℕ) :
    ∃ (t : ℕ → ℝ) (G : ℂ → ℂ), StrictMono t ∧ (∀ k, 0 < t k) ∧
      DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → ∏' k, (1 - cexp (-(s * t k)))⁻¹ = G s / (s - 1)) ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        (G s = 0 ↔ ∃ j, m j ≠ 0 ∧ (s = (Θ : ℂ) + γ j * I ∨ s = (Θ : ℂ) - γ j * I)) := by
  have hΘ0 : 0 < Θ := by linarith only [h0]
  obtain ⟨P, hP⟩ : ∃ P : PrimeDensity, P = layerPrimeDensity hΘ0 h1 γ m := ⟨_, rfl⟩
  have hw : P.w = layerLogDensity Θ γ m := by rw [hP]; rfl
  refine ⟨P.atom, fun s => layerRegular Θ γ m s * cexp (P.correction s), P.atom_strictMono,
    P.atom_pos, ?_, ?_, ?_⟩
  · exact (differentiable_layerRegular h1 γ m).differentiableOn.mul
      P.differentiableOn_correction.cexp
  · intro s hs
    rw [← P.discreteZeta_eq_tprod hs, P.discreteZeta_eq hs, hw, cexp_layer_eq h1 γ m hs]
    ring
  · intro s _
    rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), layerRegular_eq_zero_iff]

end GaloisForLFunctions.FloorFreeArithmetic
