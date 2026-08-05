import GaloisForLFunctions.HTGeometry.CompactMomentWeakConvergence
import GaloisForLFunctions.HTGeometry.DiscreteHalfLineLaw

/-!
# The exponential compactification of a half-line law

The substitution `y = e^{-x}` carries a law on `[0,∞)` to a law on the compact interval `[0,1]`,
and it carries the Laplace transform at an integer argument to the corresponding moment.  Combined
with the fact that moments determine and control laws on a compact interval, convergence of the
Laplace transforms at the natural numbers therefore forces weak convergence of the compactified
laws.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exponential compactification map of the half line. -/
def expProj (x : ℝ) : Icc (0 : ℝ) 1 := Set.projIcc 0 1 (by norm_num) (Real.exp (-x))

theorem continuous_expProj : Continuous expProj :=
  continuous_projIcc.comp (Real.continuous_exp.comp continuous_neg)

theorem measurable_expProj : Measurable expProj := continuous_expProj.measurable

/-- On the half line the compactification map is the exponential itself. -/
theorem coe_expProj_of_nonneg {x : ℝ} (hx : 0 ≤ x) : (expProj x : ℝ) = Real.exp (-x) := by
  have h0 : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have h1 : Real.exp (-x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  rw [expProj, Set.coe_projIcc, min_eq_right h1, max_eq_right h0]

/-- The compactified law of a law on the half line. -/
def expPush (μ : Measure ℝ) : Measure (Icc (0 : ℝ) 1) := Measure.map expProj μ

instance instIsProbabilityMeasureExpPush (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (expPush μ) := by
  rw [expPush]
  exact Measure.isProbabilityMeasure_map measurable_expProj.aemeasurable

/-- **The compactification carries the Laplace transform to the moments.** -/
theorem integral_pow_expPush (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0)
    (k : ℕ) :
    (∫ y, ((y : ℝ) ^ k) ∂(expPush μ)) = ∫ x, Real.exp (-((k : ℝ) * x)) ∂μ := by
  have hae : ∀ᵐ x ∂μ, ((expProj x : ℝ) ^ k) = Real.exp (-((k : ℝ) * x)) := by
    have hnn : ∀ᵐ x ∂μ, 0 ≤ x := by
      refine MeasureTheory.ae_iff.mpr ?_
      have hset : {x : ℝ | ¬ 0 ≤ x} = Iio (0 : ℝ) := by
        ext x
        simp
      rwa [hset]
    filter_upwards [hnn] with x hx
    rw [coe_expProj_of_nonneg hx, ← Real.exp_nat_mul]
    ring_nf
  have hmap : (∫ y, ((y : ℝ) ^ k) ∂(expPush μ)) = ∫ x, ((expProj x : ℝ) ^ k) ∂μ := by
    rw [expPush]
    exact integral_map measurable_expProj.aemeasurable
      ((by fun_prop : Continuous fun y : Icc (0 : ℝ) 1 => ((y : ℝ) ^ k)).aestronglyMeasurable)
  rw [hmap]
  exact integral_congr_ae hae

/-- The compactified law, bundled as a law on the compact interval. -/
def expPushProb (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ProbabilityMeasure (Icc (0 : ℝ) 1) := ⟨expPush μ, inferInstance⟩

@[simp] theorem expPushProb_toMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((expPushProb μ : ProbabilityMeasure (Icc (0 : ℝ) 1)) : Measure (Icc (0 : ℝ) 1))
      = expPush μ := rfl

instance : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩

/-- **Laplace convergence compactifies to weak convergence.**  If the Laplace transforms of a
family of half-line laws converge at every natural argument, the compactified laws converge
weakly. -/
theorem tendsto_expPushProb_of_tendsto_laplace {ι : Type*} {l : Filter ι}
    (μs : ι → Measure ℝ) (μ : Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    [IsProbabilityMeasure μ]
    (hsupp : ∀ i, (μs i) (Iio 0) = 0) (hsuppμ : μ (Iio 0) = 0)
    (hlap : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(μs i)) l
      (𝓝 (∫ x, Real.exp (-((k : ℝ) * x)) ∂μ))) :
    Tendsto (fun i => expPushProb (μs i)) l (𝓝 (expPushProb μ)) := by
  refine probabilityMeasure_tendsto_of_integral_pow_tendsto _ _ fun k => ?_
  simp only [expPushProb_toMeasure]
  rw [integral_pow_expPush μ hsuppμ k]
  exact (hlap k).congr fun i => (integral_pow_expPush (μs i) (hsupp i) k).symm

end

end GaloisForLFunctions.HTGeometry
