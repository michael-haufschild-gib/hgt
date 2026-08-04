import GaloisForLFunctions.HTGeometry.WienerConvolutionOperator

/-!
# Time-dependent potentials: the family of convolvers

A potential that varies in time is a *family* of densities, and the evolution it drives has a Duhamel
kernel whose convolving factor moves with the integration variable. The Volterra theory already
allows that — its kernel has two time arguments — so what is needed is the operator-norm behaviour of
the family: a uniform bound, and continuity.

Both follow from the weighted `L¹` data of the family, because convolution is linear in the density:
the operator norm of a difference of convolvers is bounded by the weighted `L¹` norm of the
difference of the densities.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## The difference of two densities -/

theorem integrable_weight_sub (a b : WienerDensity E N) :
    Integrable (fun η : E => kgFreq η ^ N * ‖a η - b η‖) (volume : Measure E) := by
  refine Integrable.mono' (a.integrable_weight.add b.integrable_weight)
    (((continuous_kgFreq.pow N).aestronglyMeasurable).mul
      ((a.aestronglyMeasurable.sub b.aestronglyMeasurable).norm)) ?_
  filter_upwards with η
  have hpos : (0 : ℝ) < kgFreq η ^ N := pow_pos (kgFreq_pos η) N
  have htri : ‖a η - b η‖ ≤ ‖a η‖ + ‖b η‖ := norm_sub_le _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le (norm_nonneg _))]
  calc kgFreq η ^ N * ‖a η - b η‖
      ≤ kgFreq η ^ N * (‖a η‖ + ‖b η‖) := mul_le_mul_of_nonneg_left htri hpos.le
    _ = kgFreq η ^ N * ‖a η‖ + kgFreq η ^ N * ‖b η‖ := by ring

/-- **The convolution operator is Lipschitz in the density.** -/
theorem norm_kgConvCLM_sub_le (a b : WienerDensity E N) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : (∫ η : E, kgFreq η ^ N * ‖a η - b η‖) ≤ D) :
    ‖kgConvCLM a - kgConvCLM b‖ ≤ Real.sqrt 2 ^ N * D := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) hD0) fun G => ?_
  have hpoint : ∀ ξ : E, ‖kgConv N a G ξ - kgConv N b G ξ‖
      ≤ Real.sqrt 2 ^ N * ‖G‖ * D := by
    intro ξ
    have hsub : kgConv N a G ξ - kgConv N b G ξ
        = ∫ η : E, (kgConvIntegrand N a G ξ η - kgConvIntegrand N b G ξ η) := by
      rw [integral_sub (integrable_kgConvIntegrand a G ξ) (integrable_kgConvIntegrand b G ξ)]
      rfl
    have hbound : ∀ η : E, ‖kgConvIntegrand N a G ξ η - kgConvIntegrand N b G ξ η‖
        ≤ Real.sqrt 2 ^ N * ‖G‖ * (kgFreq η ^ N * ‖a η - b η‖) := by
      intro η
      have hrw : kgConvIntegrand N a G ξ η - kgConvIntegrand N b G ξ η
          = kgConvIntegrand N (fun ζ : E => a ζ - b ζ) G ξ η := by
        simp only [kgConvIntegrand]
        ring
      rw [hrw]
      exact norm_kgConvIntegrand_le (fun ζ : E => a ζ - b ζ) G ξ η
    have hint : Integrable
        (fun η : E => Real.sqrt 2 ^ N * ‖G‖ * (kgFreq η ^ N * ‖a η - b η‖))
        (volume : Measure E) := (integrable_weight_sub a b).const_mul _
    rw [hsub]
    have hle := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbound)
    refine hle.trans ?_
    rw [integral_const_mul]
    have hG : (0 : ℝ) ≤ Real.sqrt 2 ^ N * ‖G‖ :=
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left hD hG
  have hnorm : ‖(kgConvCLM a - kgConvCLM b) G‖ ≤ Real.sqrt 2 ^ N * ‖G‖ * D := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun ξ => ?_
    have hval : (kgConvCLM a - kgConvCLM b) G ξ = kgConv N a G ξ - kgConv N b G ξ := rfl
    rw [hval]
    exact hpoint ξ
  refine hnorm.trans_eq ?_
  ring

/-! ## Families of densities -/

/-- A time-dependent admissible density: a curve of densities with a uniform weighted `L¹` bound
and a Lipschitz modulus in that norm. -/
structure WienerFamily (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (N : ℕ) where
  /-- The density at each time. -/
  density : ℝ → WienerDensity E N
  /-- A uniform bound on the weighted norms. -/
  bound : ℝ
  /-- Which is a bound. -/
  norm_le : ∀ s : ℝ, (density s).norm' ≤ bound
  /-- A Lipschitz modulus in the weighted norm. -/
  lip : ℝ
  /-- The modulus is nonnegative. -/
  lip_nonneg : 0 ≤ lip
  /-- And it is a modulus. -/
  lip_le : ∀ s s' : ℝ,
    (∫ η : E, kgFreq η ^ N * ‖density s η - density s' η‖) ≤ lip * |s - s'|

namespace WienerFamily

variable (A : WienerFamily E N)

theorem bound_nonneg : 0 ≤ A.bound :=
  le_trans (A.density 0).norm'_nonneg (A.norm_le 0)

/-- **The convolvers of a family are uniformly bounded.** -/
theorem norm_convCLM_le (s : ℝ) :
    ‖kgConvCLM (A.density s)‖ ≤ Real.sqrt 2 ^ N * A.bound := by
  refine (norm_kgConvCLM_le (A.density s)).trans ?_
  exact mul_le_mul_of_nonneg_left (A.norm_le s) (pow_nonneg (Real.sqrt_nonneg 2) N)

/-- **The convolvers of a family are continuous in time**, in the operator norm. -/
theorem continuous_convCLM : Continuous fun s : ℝ => kgConvCLM (A.density s) := by
  have hK : (0 : ℝ) ≤ Real.sqrt 2 ^ N * A.lip :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) A.lip_nonneg
  refine (LipschitzWith.of_dist_le_mul
    (K := (Real.sqrt 2 ^ N * A.lip).toNNReal) ?_).continuous
  intro s s'
  rw [Real.coe_toNNReal _ hK, dist_eq_norm, Real.dist_eq]
  have hD : (∫ η : E, kgFreq η ^ N * ‖A.density s η - A.density s' η‖)
      ≤ A.lip * |s - s'| := A.lip_le s s'
  have hD0 : (0 : ℝ) ≤ A.lip * |s - s'| := mul_nonneg A.lip_nonneg (abs_nonneg _)
  have hmain := norm_kgConvCLM_sub_le (A.density s) (A.density s') hD0 hD
  refine hmain.trans_eq ?_
  ring

end WienerFamily

/-! ## The constant family -/

/-- A static potential, as a family. -/
noncomputable def WienerDensity.constFamily (a : WienerDensity E N) : WienerFamily E N where
  density := fun _ => a
  bound := a.norm'
  norm_le := fun _ => le_refl _
  lip := 0
  lip_nonneg := le_refl 0
  lip_le := fun s s' => by
    have hzero : (∫ η : E, kgFreq η ^ N * ‖a η - a η‖) = 0 := by
      have hfun : (fun η : E => kgFreq η ^ N * ‖a η - a η‖) = fun _ : E => (0 : ℝ) := by
        funext η
        rw [sub_self, norm_zero, mul_zero]
      rw [hfun, integral_zero]
    rw [hzero, zero_mul]

end GaloisForLFunctions.HTGeometry
