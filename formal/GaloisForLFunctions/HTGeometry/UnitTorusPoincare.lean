import Mathlib

/-!
# The sharp Poincaré inequality on the unit torus

Translating a function on the unit torus multiplies each Fourier coefficient by the corresponding
character value, so Parseval turns the squared translate difference into a weighted sum of squared
coefficients.  Dividing by the square of the shift and letting the shift vanish replaces each weight
by the square of the frequency, which is the exact Fourier form of the Dirichlet energy.

Because every nonzero frequency has squared length at least one, the resulting inequality is the
Poincaré inequality with constant one for the torus of circumference one: the variance of a function
is bounded by its Dirichlet energy divided by `4π²`.  No smoothness is assumed beyond the bound on
the translate differences, which is the form supplied by an almost-everywhere gradient bound.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance unitTorusPoincareLocalInst1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitTorusPoincareLocalInst2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance unitTorusPoincareLocalInst3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section Characters

private theorem mFourier_add_point (n : d → ℤ) (x y : UnitAddTorus d) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [fourier_apply, smul_add, AddCircle.toCircle_add]

theorem mFourier_neg_neg (n : d → ℤ) (a : UnitAddTorus d) :
    mFourier (-n) (-a) = mFourier n a := by
  simp only [mFourier, ContinuousMap.coe_mk]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [fourier_apply]

/-- The shift of the torus by a real amount in a single coordinate direction. -/
def coordShift (j : d) (h : ℝ) : UnitAddTorus d :=
  Pi.single j ((h : ℝ) : UnitAddCircle)

theorem mFourier_coordShift (n : d → ℤ) (j : d) (h : ℝ) :
    mFourier n (coordShift j h) = fourier (n j) ((h : ℝ) : UnitAddCircle) := by
  simp only [mFourier, ContinuousMap.coe_mk, coordShift]
  rw [Finset.prod_eq_single j]
  · rw [Pi.single_eq_same]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    exact fourier_eval_zero _
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem fourier_coe_eq_exp (m : ℤ) (h : ℝ) :
    fourier m ((h : ℝ) : UnitAddCircle) = Complex.exp (2 * Real.pi * Complex.I * m * h) := by
  rw [fourier_coe_apply]
  norm_num

/-- The squared modulus of a character increment, divided by the squared shift, converges to the
squared frequency. -/
theorem tendsto_norm_fourier_sub_one_sq_div (m : ℤ) :
    Tendsto (fun h : ℝ => ‖fourier m ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (4 * Real.pi ^ 2 * (m : ℝ) ^ 2)) := by
  have hderiv : HasDerivAt (fun h : ℝ => Complex.exp (2 * Real.pi * Complex.I * m * h))
      (2 * Real.pi * Complex.I * m) 0 := by
    have hlin : HasDerivAt (fun h : ℝ => (2 * Real.pi * Complex.I * m) * (h : ℂ))
        (2 * Real.pi * Complex.I * m) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul
        (2 * Real.pi * Complex.I * m)
    have := hlin.cexp
    simpa using this
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hnormsq : Tendsto
      (fun h : ℝ => ‖slope (fun h : ℝ => Complex.exp (2 * Real.pi * Complex.I * m * h)) 0 h‖ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖(2 * Real.pi * Complex.I * m : ℂ)‖ ^ 2)) :=
    ((continuous_norm.pow 2).tendsto _).comp hslope
  have hval : ‖(2 * Real.pi * Complex.I * m : ℂ)‖ ^ 2 = 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 := by
    have hnorm : ‖(2 * Real.pi * Complex.I * m : ℂ)‖ = 2 * Real.pi * |(m : ℝ)| := by
      simp [abs_of_nonneg Real.pi_pos.le]
    rw [hnorm, mul_pow, mul_pow, sq_abs]
    ring
  rw [hval] at hnormsq
  refine hnormsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := hh
  have hzero : Complex.exp (2 * Real.pi * Complex.I * m * ((0 : ℝ) : ℂ)) = 1 := by
    simp
  rw [slope_def_module, hzero, sub_zero, norm_smul, mul_pow, ← fourier_coe_eq_exp]
  rw [norm_inv, Real.norm_eq_abs, inv_pow, sq_abs]
  rw [div_eq_inv_mul]

end Characters

section Coefficients

private theorem mFourierCoeff_translate (f : UnitAddTorus d → ℂ) (a : UnitAddTorus d) (n : d → ℤ) :
    mFourierCoeff (fun t => f (t + a)) n = mFourier n a * mFourierCoeff f n := by
  have hshift : (∫ t, mFourier (-n) t • f (t + a)) =
      ∫ t, mFourier (-n) (t - a) • f t := by
    rw [← integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus d)))
      (fun t : UnitAddTorus d => mFourier (-n) (t - a) • f t) a]
    simp
  have hsplit : ∀ t : UnitAddTorus d, mFourier (-n) (t - a) • f t =
      mFourier n a • (mFourier (-n) t • f t) := by
    intro t
    rw [sub_eq_add_neg, mFourier_add_point, mFourier_neg_neg, smul_smul]
    congr 1
    ring
  rw [mFourierCoeff, mFourierCoeff, hshift, integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_smul]
  rfl

theorem hasSum_sq_mFourierCoeff_continuous (g : C(UnitAddTorus d, ℂ)) :
    HasSum (fun n : d → ℤ => ‖mFourierCoeff g n‖ ^ 2) (∫ t, ‖g t‖ ^ 2) := by
  have h := hasSum_sq_mFourierCoeff (g.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp] at h
  have hint : (∫ t, ‖(g.toLp 2 volume ℂ) t‖ ^ 2) = ∫ t, ‖g t‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := (volume : Measure (UnitAddTorus d))) (𝕜 := ℂ) g] with t ht
    rw [ht]
  rwa [hint] at h

private theorem mFourierCoeff_sub (f g : C(UnitAddTorus d, ℂ)) (n : d → ℤ) :
    mFourierCoeff (fun t => f t - g t) n = mFourierCoeff f n - mFourierCoeff g n := by
  have hcongr : ∀ t : UnitAddTorus d, mFourier (-n) t • (f t - g t) =
      mFourier (-n) t • f t - mFourier (-n) t • g t := fun t => smul_sub _ _ _
  rw [mFourierCoeff, mFourierCoeff, mFourierCoeff,
    integral_congr_ae (Filter.Eventually.of_forall hcongr), integral_sub]
  · exact ((map_continuous (mFourier (-n))).smul (map_continuous f)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((map_continuous (mFourier (-n))).smul (map_continuous g)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The translate of a continuous function, as a continuous function. -/
def translateMap (f : C(UnitAddTorus d, ℂ)) (a : UnitAddTorus d) : C(UnitAddTorus d, ℂ) :=
  ⟨fun t => f (t + a), by fun_prop⟩

/-- **Parseval for a translate difference.**  The squared `L²` norm of a translate difference is the
character-weighted sum of squared Fourier coefficients. -/
theorem hasSum_sq_translate_diff (f : C(UnitAddTorus d, ℂ)) (a : UnitAddTorus d) :
    HasSum (fun n : d → ℤ => ‖mFourier n a - 1‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
      (∫ t, ‖f (t + a) - f t‖ ^ 2) := by
  have hdiff : ∀ n : d → ℤ,
      mFourierCoeff (fun t => translateMap f a t - f t) n =
        (mFourier n a - 1) * mFourierCoeff f n := by
    intro n
    rw [mFourierCoeff_sub (translateMap f a) f n]
    have h1 : mFourierCoeff (translateMap f a) n = mFourier n a * mFourierCoeff f n :=
      mFourierCoeff_translate f a n
    rw [h1, sub_mul, one_mul]
  have hcont : HasSum (fun n : d → ℤ =>
      ‖mFourierCoeff (fun t => translateMap f a t - f t) n‖ ^ 2)
      (∫ t, ‖translateMap f a t - f t‖ ^ 2) :=
    hasSum_sq_mFourierCoeff_continuous ⟨fun t => translateMap f a t - f t, by fun_prop⟩
  refine hcont.congr_fun ?_
  intro n
  rw [hdiff n, norm_mul, mul_pow]

end Coefficients

section Poincare

/-- **Fourier form of the torus Poincaré inequality.**  A quadratic bound on translate differences
bounds every finite frequency-weighted sum of squared Fourier coefficients. -/
theorem sum_freq_sq_mul_sq_mFourierCoeff_le (f : C(UnitAddTorus d, ℂ)) {C : ℝ}
    (hC : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ),
      ∑ j : d, (∫ t, ‖f (t + coordShift j h) - f t‖ ^ 2) ≤ C * h ^ 2)
    (S : Finset (d → ℤ)) :
    ∑ n ∈ S, (4 * Real.pi ^ 2 * ∑ j : d, ((n j : ℝ)) ^ 2) * ‖mFourierCoeff f n‖ ^ 2 ≤ C := by
  have key : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ),
      ∑ n ∈ S, (∑ j : d, ‖fourier (n j) ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 / h ^ 2) *
        ‖mFourierCoeff f n‖ ^ 2 ≤ C := by
    filter_upwards [hC, self_mem_nhdsWithin] with h hh hh0
    have hne : h ≠ 0 := hh0
    have hh2 : (0 : ℝ) < h ^ 2 := by positivity
    have hslice : ∀ j : d, ∑ n ∈ S, ‖fourier (n j) ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 *
        ‖mFourierCoeff f n‖ ^ 2 ≤ ∫ t, ‖f (t + coordShift j h) - f t‖ ^ 2 := by
      intro j
      have hsum := hasSum_sq_translate_diff f (coordShift j h)
      refine le_trans (le_of_eq ?_) (sum_le_hasSum S (fun n _ => by positivity) hsum)
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mFourier_coordShift]
    have h1 : ∀ n ∈ S, (∑ j : d, ‖fourier (n j) ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 / h ^ 2) *
        ‖mFourierCoeff f n‖ ^ 2 =
        ∑ j : d, (‖fourier (n j) ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 *
          ‖mFourierCoeff f n‖ ^ 2) / h ^ 2 := by
      intro n _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hswap : ∑ n ∈ S, (∑ j : d, ‖fourier (n j) ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 / h ^ 2) *
        ‖mFourierCoeff f n‖ ^ 2 =
        (∑ j : d, ∑ n ∈ S, ‖fourier (n j) ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 *
          ‖mFourierCoeff f n‖ ^ 2) / h ^ 2 := by
      rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => (Finset.sum_div _ _ _).symm
    rw [hswap, div_le_iff₀ hh2]
    calc ∑ j : d, ∑ n ∈ S, ‖fourier (n j) ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 *
          ‖mFourierCoeff f n‖ ^ 2
        ≤ ∑ j : d, ∫ t, ‖f (t + coordShift j h) - f t‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hslice j
      _ ≤ C * h ^ 2 := hh
  have hlim : Tendsto (fun h : ℝ => ∑ n ∈ S,
      (∑ j : d, ‖fourier (n j) ((h : ℝ) : UnitAddCircle) - 1‖ ^ 2 / h ^ 2) *
        ‖mFourierCoeff f n‖ ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ n ∈ S, (4 * Real.pi ^ 2 * ∑ j : d, ((n j : ℝ)) ^ 2) * ‖mFourierCoeff f n‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun n _ => ?_
    refine Tendsto.mul_const _ ?_
    rw [Finset.mul_sum]
    exact tendsto_finsetSum _ fun j _ => tendsto_norm_fourier_sub_one_sq_div (n j)
  exact le_of_tendsto hlim key

/-- **Poincaré inequality on the unit torus.**  A quadratic bound on translate differences bounds
the variance by that constant divided by `4π²`. -/
theorem integral_sq_sub_sq_integral_le (f : C(UnitAddTorus d, ℂ)) {C : ℝ}
    (hC : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ),
      ∑ j : d, (∫ t, ‖f (t + coordShift j h) - f t‖ ^ 2) ≤ C * h ^ 2) :
    (∫ t, ‖f t‖ ^ 2) - ‖∫ t, f t‖ ^ 2 ≤ C / (4 * Real.pi ^ 2) := by
  classical
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  have hparseval := hasSum_sq_mFourierCoeff_continuous f
  have hzero : mFourierCoeff f 0 = ∫ t, f t := by
    rw [mFourierCoeff]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [neg_zero, mFourier_zero]
    simp
  set g : (d → ℤ) → ℝ := fun n => if n = 0 then 0 else ‖mFourierCoeff f n‖ ^ 2 with hg
  have hgsum : Summable g := by
    refine hparseval.summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · by_cases hn : n = 0 <;> simp [hg, hn]
    · by_cases hn : n = 0 <;> simp [hg, hn]
  have hone : ∀ n : d → ℤ, n ≠ 0 → (1 : ℝ) ≤ ∑ j : d, ((n j : ℝ)) ^ 2 := by
    intro n hn
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hn
    rw [Pi.zero_apply] at hj
    have hj1 : (1 : ℝ) ≤ ((n j : ℝ)) ^ 2 := by
      have hint : (1 : ℤ) ≤ (n j) ^ 2 := by
        rcases lt_trichotomy (n j) 0 with hlt | heq | hgt
        · nlinarith
        · exact absurd heq hj
        · nlinarith
      exact_mod_cast hint
    refine le_trans hj1 ?_
    exact Finset.single_le_sum (f := fun j : d => ((n j : ℝ)) ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ j)
  have hgbound : ∀ S : Finset (d → ℤ), ∑ n ∈ S, g n ≤ C / (4 * Real.pi ^ 2) := by
    intro S
    rw [le_div_iff₀ hpi]
    have hterm : ∀ n ∈ S, g n * (4 * Real.pi ^ 2) ≤
        (4 * Real.pi ^ 2 * ∑ j : d, ((n j : ℝ)) ^ 2) * ‖mFourierCoeff f n‖ ^ 2 := by
      intro n _
      by_cases hn : n = 0
      · simp only [hg, if_pos hn, zero_mul]
        positivity
      · simp only [hg, if_neg hn]
        have h1 := hone n hn
        have hnn : (0 : ℝ) ≤ ‖mFourierCoeff f n‖ ^ 2 := by positivity
        have hprod : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * ‖mFourierCoeff f n‖ ^ 2 *
            ((∑ j : d, ((n j : ℝ)) ^ 2) - 1) := by
          refine mul_nonneg (by positivity) ?_
          linarith
        nlinarith [hprod]
    calc (∑ n ∈ S, g n) * (4 * Real.pi ^ 2)
        = ∑ n ∈ S, g n * (4 * Real.pi ^ 2) := by rw [Finset.sum_mul]
      _ ≤ ∑ n ∈ S, (4 * Real.pi ^ 2 * ∑ j : d, ((n j : ℝ)) ^ 2) * ‖mFourierCoeff f n‖ ^ 2 :=
          Finset.sum_le_sum hterm
      _ ≤ C := sum_freq_sq_mul_sq_mFourierCoeff_le f hC S
  have hgle : ∑' n, g n ≤ C / (4 * Real.pi ^ 2) :=
    le_of_tendsto hgsum.hasSum (Filter.Eventually.of_forall hgbound)
  have hsplit : (∫ t, ‖f t‖ ^ 2) = ‖mFourierCoeff f 0‖ ^ 2 + ∑' n, g n := by
    rw [← hparseval.tsum_eq]
    exact hparseval.summable.tsum_eq_add_tsum_ite 0
  rw [hsplit, hzero]
  linarith

/-- The Poincaré inequality in the form supplied by an approximate translate bound: if for every
positive slack the translate differences are eventually bounded by the slackened constant, the
variance obeys the sharp bound. -/
theorem integral_sq_sub_sq_integral_le_of_slack (f : C(UnitAddTorus d, ℂ)) {C : ℝ}
    (hC : ∀ ε > 0, ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ),
      ∑ j : d, (∫ t, ‖f (t + coordShift j h) - f t‖ ^ 2) ≤ (C + ε) * h ^ 2) :
    (∫ t, ‖f t‖ ^ 2) - ‖∫ t, f t‖ ^ 2 ≤ C / (4 * Real.pi ^ 2) := by
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hslack := integral_sq_sub_sq_integral_le f (C := C + ε * (4 * Real.pi ^ 2))
    (hC (ε * (4 * Real.pi ^ 2)) (by positivity))
  rw [add_div, mul_div_assoc, div_self hpi.ne', mul_one] at hslack
  exact hslack

end Poincare

end GaloisForLFunctions.HTGeometry
