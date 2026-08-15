import GaloisForLFunctions.RHTower.PoissonDigammaReproduction
import GaloisForLFunctions.HTGeometry.CauchyKernelStripDecay
import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean

/-!
# The archimedean density of the completed source

The archimedean rate of the completed zeta on the critical line is

`theta(x) = (1/2)·(Re psi(1/4 + i x/2) − log pi)`,

which is exactly the real part of `logDeriv Gamma_R` there.  Pairing it with the mass kernel of
order zero and mass `a²` reproduces the rate at the interior point, so

`∫ theta(x)/(a² + x²) dx = (pi/a)·Re logDeriv Gamma_R(1/2 + a)`,

which is the archimedean term of the completed source formula in density coordinates.  Since the
rate has at most logarithmic growth, every higher mass moment is a mass derivative of this one.

The rate is also coercive: `theta(x) ≥ (1/2)·log(2+|x|) − B` with an explicit constant, which is the
confining potential of the completed source.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The vertical digamma point of the completed archimedean factor. -/
def routeUArchimedeanPoint (x : ℝ) : ℂ :=
  (((1 : ℝ) / 4 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I

/-- The archimedean rate of the completed zeta on the critical line. -/
def routeUArchimedeanRate (x : ℝ) : ℝ :=
  (1 / 2) * ((Complex.digamma (routeUArchimedeanPoint x)).re - Real.log Real.pi)

/-- The archimedean rate as a complex-valued weight. -/
def routeUArchimedeanWeight (x : ℝ) : ℂ := ((routeUArchimedeanRate x : ℝ) : ℂ)

theorem continuous_routeUArchimedeanRate : Continuous routeUArchimedeanRate := by
  unfold routeUArchimedeanRate routeUArchimedeanPoint
  exact continuous_const.mul
    ((continuous_re_digamma_half (c := (1 : ℝ) / 4) (by norm_num)).sub continuous_const)

theorem continuous_routeUArchimedeanWeight : Continuous routeUArchimedeanWeight := by
  unfold routeUArchimedeanWeight
  exact Complex.continuous_ofReal.comp continuous_routeUArchimedeanRate

/-- The archimedean growth constant of the rate. -/
def routeUArchimedeanGrowthConst : ℝ :=
  (1 / 2) * (digammaVerticalGrowthConst ((1 : ℝ) / 4) + |Real.log Real.pi|)

theorem norm_routeUArchimedeanWeight_le (x : ℝ) :
    ‖routeUArchimedeanWeight x‖ ≤ routeUArchimedeanGrowthConst + Real.log (2 + |x|) := by
  have hlog0 : 0 ≤ Real.log (2 + |x|) := Real.log_nonneg (by
    have := abs_nonneg x
    linarith)
  have hhalf : |x / 2| ≤ |x| := by
    rw [abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have := abs_nonneg x
    linarith
  have hmono : Real.log (2 + |x / 2|) ≤ Real.log (2 + |x|) := by
    refine Real.log_le_log (by positivity) ?_
    linarith
  have hdig := abs_re_digamma_vertical_le (c := (1 : ℝ) / 4) (by norm_num) (x / 2)
  obtain ⟨h1, h2⟩ := abs_le.mp hdig
  have hpi := le_abs_self (Real.log Real.pi)
  have hpi' := neg_abs_le (Real.log Real.pi)
  rw [routeUArchimedeanWeight, Complex.norm_real, Real.norm_eq_abs, routeUArchimedeanRate,
    routeUArchimedeanPoint, routeUArchimedeanGrowthConst, abs_le]
  constructor
  · linarith
  · linarith

/-! ## Coercivity -/

/-- The archimedean confinement constant. -/
def routeUArchimedeanFloorConst : ℝ :=
  (1 / 2) * (digammaVerticalCoercivityConst ((1 : ℝ) / 4) + Real.log Real.pi + Real.log 2)

/-- **(CSHC.7) in the completed normalisation.**  The archimedean rate grows at least
logarithmically. -/
theorem routeUArchimedeanRate_ge (x : ℝ) :
    (1 / 2) * Real.log (2 + |x|) - routeUArchimedeanFloorConst ≤ routeUArchimedeanRate x := by
  have hdig := re_digamma_vertical_ge (a := (1 : ℝ) / 4) (by norm_num) (by norm_num) (x / 2)
  have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hhalf : Real.log (2 + |x|) - Real.log 2 ≤ Real.log (2 + |x / 2|) := by
    have hle : 2 + |x| ≤ 2 * (2 + |x / 2|) := by
      rw [abs_div]
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      linarith
    have hlog : Real.log (2 + |x|) ≤ Real.log (2 * (2 + |x / 2|)) :=
      Real.log_le_log (by linarith) hle
    rw [Real.log_mul (by norm_num) (by positivity)] at hlog
    linarith
  rw [routeUArchimedeanRate, routeUArchimedeanPoint, routeUArchimedeanFloorConst]
  linarith

/-! ## The archimedean mass moments -/

/-- The archimedean moments of the completed source. -/
def routeUArchimedeanMoment (n : ℕ) (X : ℝ) : ℂ :=
  massPairing routeUArchimedeanWeight n X

theorem hasDerivAt_routeUArchimedeanMoment (n : ℕ) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (routeUArchimedeanMoment n)
      (-((n : ℂ) + 1) * routeUArchimedeanMoment (n + 1) X) X :=
  hasDerivAt_massPairing continuous_routeUArchimedeanWeight norm_routeUArchimedeanWeight_le n hX

theorem iteratedDeriv_routeUArchimedeanMoment (n : ℕ) {X : ℝ} (hX : 0 < X) :
    iteratedDeriv n (routeUArchimedeanMoment 0) X
      = (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * routeUArchimedeanMoment n X :=
  iteratedDeriv_massPairing continuous_routeUArchimedeanWeight norm_routeUArchimedeanWeight_le n hX

theorem routeU_re_div_two (z : ℂ) : (z / 2).re = z.re / 2 := by
  simp

/-- **The archimedean term of the completed source in density coordinates.** -/
theorem routeUArchimedeanMoment_zero_eq {a : ℝ} (ha : 0 < a) :
    routeUArchimedeanMoment 0 (a ^ 2)
      = ((Real.pi / a * (logDeriv Complex.Gammaℝ (((1 / 2 + a : ℝ)) : ℂ)).re : ℝ) : ℂ) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkernel : ∀ x : ℝ, ((a ^ 2 + x ^ 2 : ℝ))⁻¹ = (Real.pi / a) * poissonWeight a x := by
    intro x
    rw [poissonWeight_eq]
    field_simp
  have hrewrite : routeUArchimedeanMoment 0 (a ^ 2)
      = ((Real.pi / a : ℝ) : ℂ)
        * ((∫ x : ℝ, poissonWeight a x * routeUArchimedeanRate x : ℝ) : ℂ) := by
    have hcast : ((∫ x : ℝ, poissonWeight a x * routeUArchimedeanRate x : ℝ) : ℂ)
        = ∫ x : ℝ, ((poissonWeight a x * routeUArchimedeanRate x : ℝ) : ℂ) :=
      (_root_.integral_ofReal).symm
    rw [hcast, routeUArchimedeanMoment, massPairing, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hx : ((a ^ 2 + x ^ 2 : ℝ)) ≠ 0 := by positivity
    simp only [routeUArchimedeanWeight]
    rw [pow_one, ← Complex.ofReal_inv, hkernel x]
    push_cast
    ring
  have hmass : (∫ x : ℝ, poissonWeight a x * routeUArchimedeanRate x)
      = (logDeriv Complex.Gammaℝ (((1 / 2 + a : ℝ)) : ℂ)).re := by
    have hsplit : ∀ x : ℝ, poissonWeight a x * routeUArchimedeanRate x
        = (1 / 2) * (poissonWeight a x
            * (Complex.digamma ((((1 : ℝ) / 4 : ℝ) : ℂ)
                + ((x / 2 : ℝ) : ℂ) * Complex.I)).re)
          - ((1 / 2) * Real.log Real.pi) * poissonWeight a x := by
      intro x
      rw [routeUArchimedeanRate, routeUArchimedeanPoint]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
      MeasureTheory.integral_sub
        ((integrable_poissonWeight_mul_re_digamma_half ha (c := (1 : ℝ) / 4)
          (by norm_num)).const_mul _)
        ((integrable_poissonWeight ha).const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_poissonWeight_mul_re_digamma_half ha (c := (1 : ℝ) / 4) (by norm_num),
      integral_poissonWeight ha, mul_one]
    have hre : (0 : ℝ) < ((((1 / 2 + a : ℝ)) : ℂ)).re := by
      simp only [Complex.ofReal_re]
      linarith
    rw [logDeriv_Gammaℝ_of_re_pos hre]
    have hhalf : ((((1 / 2 + a : ℝ)) : ℂ)) / 2 = ((((1 : ℝ) / 4 + a / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hhalf, Complex.sub_re, routeU_re_div_two, routeU_re_div_two, Complex.ofReal_re]
    ring
  rw [hrewrite, hmass, Complex.ofReal_mul]

end RHTower

end
