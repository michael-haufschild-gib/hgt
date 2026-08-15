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

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section Characters

theorem mFourier_add_point (n : d → ℤ) (x y : UnitAddTorus d) :
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

theorem mFourierCoeff_translate (f : UnitAddTorus d → ℂ) (a : UnitAddTorus d) (n : d → ℤ) :
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

theorem mFourierCoeff_sub (f g : C(UnitAddTorus d, ℂ)) (n : d → ℤ) :
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

end GaloisForLFunctions.HTGeometry
