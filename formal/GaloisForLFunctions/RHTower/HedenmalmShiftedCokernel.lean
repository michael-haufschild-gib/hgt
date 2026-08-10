import GaloisForLFunctions.RHTower.HedenmalmShiftedClosedWeightedDerivative
import GaloisForLFunctions.HTGeometry.CompactHyperplanePerturbation

/-!
# Actual cokernel line of every translated Hedenmalm derivative

The source conormal `k(x) exp(-i conj(α)x)` belongs to the weighted Hilbert space for every
complex parameter because the theta source has all exponential moments.  This file packages that
function as an actual Hilbert vector before identifying the full translated range.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmClosedWeightedDerivative

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource
  HedenmalmFredholmRange

private abbrev H := Lp ℂ 2 unitIntervalMeasure

private abbrev HS := SourceSpace thetaSource

private abbrev sourceMeasure : Measure ℝ :=
  volume.withDensity (realDensity (sourceWeight thetaSource))

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance : CompleteSpace thetaCentered := thetaCentered_isClosed.completeSpace_coe

theorem cokernelVector_eq_k_mul_sourceChar (α : ℂ) (x : ℝ) :
    cokernelVector thetaSource α x =
      (thetaSource.k x : ℂ) * sourceChar (-(starRingEnd ℂ) α) x := by
  rw [cokernelVector, sourceChar]
  congr 2
  ring

theorem memLp_thetaCokernelSource (α : ℂ) :
    MemLp (cokernelVector thetaSource α) 2 sourceMeasure := by
  rw [sourceMeasure]
  apply (memLp_two_withDensity_iff (measurable_sourceWeight thetaSource)
    (sourceWeight_pos thetaSource)).mpr
  let z : ℂ := -(starRingEnd ℂ) α
  let q : ℝ → ℂ := fun x =>
    ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) * sourceChar z x
  have hqcont : Continuous q :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp thetaSource.continuous_k)).mul
        (continuous_sourceChar z)
  have hq : MemLp q 2 (volume : Measure ℝ) := by
    apply (memLp_two_iff_integrable_sq_norm hqcont.aestronglyMeasurable).mpr
    refine (HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource
      (-2 * α.im)).congr ?_
    filter_upwards with x
    simp only [q]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_sourceChar, mul_pow,
      Real.sq_sqrt (thetaSource.pos_k x).le, thetaSource_k]
    have hzIm : z.im = α.im := by
      simp [z]
    rw [hzIm]
    have hexp : Real.exp (-α.im * x) ^ 2 =
        Real.exp ((-2 * α.im) * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    ring
  have hfun : (fun x => sqrtWeight (sourceWeight thetaSource) x *
      cokernelVector thetaSource α x) = q := by
    funext x
    have hk : 0 < thetaSource.k x := thetaSource.pos_k x
    have hsqrt : Real.sqrt (thetaSource.k x) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
    have hsqrtC : ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hsqrt
    have hsw : sqrtWeight (sourceWeight thetaSource) x =
        (((Real.sqrt (thetaSource.k x))⁻¹ : ℝ) : ℂ) := by
      rw [sqrtWeight]
      norm_cast
      rw [show sourceWeight thetaSource x = (thetaSource.k x)⁻¹ from rfl,
        Real.sqrt_inv]
    rw [cokernelVector_eq_k_mul_sourceChar, hsw]
    rw [← mul_assoc]
    change ((((Real.sqrt (thetaSource.k x))⁻¹ : ℝ) : ℂ) *
        ((thetaSource.k x : ℝ) : ℂ)) * sourceChar z x = q x
    simp only [q]
    congr 1
    push_cast
    field_simp [hsqrtC]
    exact_mod_cast (Real.sq_sqrt hk.le).symm
  rw [hfun]
  exact hq

/-- Source-space representative of the translated cokernel conormal. -/
def thetaCokernelSourceVector (α : ℂ) : HS :=
  (memLp_thetaCokernelSource α).toLp (cokernelVector thetaSource α)

theorem thetaCokernelSourceVector_ae (α : ℂ) :
    (thetaCokernelSourceVector α : ℝ → ℂ) =ᵐ[sourceMeasure]
      cokernelVector thetaSource α :=
  (memLp_thetaCokernelSource α).coeFn_toLp

theorem thetaCokernelSourceVector_ne_zero (α : ℂ) :
    thetaCokernelSourceVector α ≠ 0 := by
  intro hzero
  have hzeroWeighted :
      ((0 : HS) : ℝ → ℂ) =ᵐ[sourceMeasure] fun _ => 0 :=
    Lp.coeFn_zero ℂ 2 sourceMeasure
  have hzeroAEμ :
      cokernelVector thetaSource α =ᵐ[sourceMeasure] fun _ => 0 := by
    have hrep := thetaCokernelSourceVector_ae α
    rw [hzero] at hrep
    exact hrep.symm.trans hzeroWeighted
  have hzeroAE :
      cokernelVector thetaSource α =ᵐ[(volume : Measure ℝ)] fun _ => 0 :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (by simpa [sourceMeasure] using hzeroAEμ)
  have hcont : Continuous (cokernelVector thetaSource α) := by
    rw [show cokernelVector thetaSource α = fun x =>
      (thetaSource.k x : ℂ) * sourceChar (-(starRingEnd ℂ) α) x by
        funext x
        exact cokernelVector_eq_k_mul_sourceChar α x]
    exact (Complex.continuous_ofReal.comp thetaSource.continuous_k).mul
      (continuous_sourceChar (-(starRingEnd ℂ) α))
  have hall : cokernelVector thetaSource α = fun _ : ℝ => 0 :=
    Measure.eq_of_ae_eq hzeroAE hcont continuous_zero
  have hzeroAt := congrFun hall 0
  rw [cokernelVector] at hzeroAt
  exact (mul_ne_zero (by exact_mod_cast (thetaSource.pos_k 0).ne')
    (Complex.exp_ne_zero _)) hzeroAt

/-- Quantile-space vector spanning the translated cokernel line. -/
def thetaCokernelVector (α : ℂ) : H :=
  quantileUnitary thetaSource (thetaCokernelSourceVector α)

theorem thetaCokernelVector_ne_zero (α : ℂ) : thetaCokernelVector α ≠ 0 := by
  intro hzero
  apply thetaCokernelSourceVector_ne_zero α
  apply (quantileUnitary thetaSource).injective
  simpa [thetaCokernelVector] using hzero

/-- Concrete integral formula for the weighted source-space inner product. -/
theorem inner_sourceSpace_eq_integral_div
    {u v : HS} {f g : ℝ → ℂ}
    (huf : (u : ℝ → ℂ) =ᵐ[sourceMeasure] f)
    (hvg : (v : ℝ → ℂ) =ᵐ[sourceMeasure] g) :
    inner ℂ u v = ∫ x, (starRingEnd ℂ) (f x) * g x / (thetaSource.k x : ℂ) := by
  rw [L2.inner_def]
  calc
    (∫ x, inner ℂ (u x) (v x) ∂sourceMeasure) =
        ∫ x, (starRingEnd ℂ) (u x) * v x ∂sourceMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      exact RCLike.inner_apply' _ _
    _ =
        ∫ x, (starRingEnd ℂ) (f x) * g x ∂sourceMeasure := by
      apply integral_congr_ae
      filter_upwards [huf, hvg] with x hux hvx
      rw [hux, hvx]
    _ = ∫ x, (starRingEnd ℂ) (f x) * g x / (thetaSource.k x : ℂ) := by
      rw [sourceMeasure, integral_withDensity_eq_integral_toReal_smul
        (measurable_realDensity (measurable_sourceWeight thetaSource))
        (Filter.Eventually.of_forall fun x => by simp [realDensity])]
      apply integral_congr_ae
      filter_upwards with x
      rw [show realDensity (sourceWeight thetaSource) x =
        ENNReal.ofReal (sourceWeight thetaSource x) from rfl,
        ENNReal.toReal_ofReal (sourceWeight_pos thetaSource x).le]
      change ((sourceWeight thetaSource x : ℝ) : ℂ) *
        ((starRingEnd ℂ) (f x) * g x) =
          (starRingEnd ℂ) (f x) * g x / (thetaSource.k x : ℂ)
      rw [show sourceWeight thetaSource x = (thetaSource.k x)⁻¹ from rfl]
      push_cast
      field_simp [show (thetaSource.k x : ℂ) ≠ 0 by
        exact_mod_cast (thetaSource.pos_k x).ne']

/-- The actual cokernel conormal annihilates every literal compactly supported smooth range
vector of the translated operator. -/
theorem inner_thetaCokernelVector_thetaShiftedRangeMap_core
    (α : ℂ) {g : ℝ → ℂ} (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hgs : HasCompactSupport g) :
    let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
    let k : thetaCentered :=
      ⟨quantileUnitary thetaSource f, quantile_sourceD_mem_centered hg hgs⟩
    inner ℂ (thetaCokernelVector α) (thetaShiftedRangeMap α k) = 0 := by
  let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
  let u : HS := (memLp_smooth hg hgs).toLp g
  let k : thetaCentered :=
    ⟨quantileUnitary thetaSource f, quantile_sourceD_mem_centered hg hgs⟩
  have hB : thetaCenteredSourceInverse k = quantileUnitary thetaSource u := by
    exact thetaCompactSourceInverse_quantile_sourceD hg hgs
  have hJ : thetaShiftedRangeMap α k =
      quantileUnitary thetaSource (f + α • u) := by
    rw [thetaShiftedRangeMap_apply, hB, map_add, map_smul]
  have hfAE : (f : ℝ → ℂ) =ᵐ[sourceMeasure] sourceD g :=
    (memLp_sourceD hg hgs).coeFn_toLp
  have huAE : (u : ℝ → ℂ) =ᵐ[sourceMeasure] g :=
    (memLp_smooth hg hgs).coeFn_toLp
  have hsumAE : ((f + α • u : HS) : ℝ → ℂ) =ᵐ[sourceMeasure]
      fun x => sourceD g x + α * g x := by
    filter_upwards [Lp.coeFn_add f (α • u), Lp.coeFn_smul α u,
      hfAE, huAE] with x hadd hsmul hfx hux
    rw [hadd]
    rw [Pi.add_apply, hsmul]
    change f x + α * u x = sourceD g x + α * g x
    rw [hfx, hux]
  change inner ℂ (thetaCokernelVector α) (thetaShiftedRangeMap α k) = 0
  rw [hJ, thetaCokernelVector,
    (quantileUnitary thetaSource).inner_map_map]
  rw [inner_sourceSpace_eq_integral_div (thetaCokernelSourceVector_ae α) hsumAE]
  have hpoint : ∀ x : ℝ,
      (starRingEnd ℂ) (cokernelVector thetaSource α x) *
          (sourceD g x + α * g x) / (thetaSource.k x : ℂ) =
        (-Complex.I * deriv g x + α * g x) * sourceChar α x := by
    intro x
    have hk : (thetaSource.k x : ℂ) ≠ 0 := by
      exact_mod_cast (thetaSource.pos_k x).ne'
    rw [sourceD]
    calc
      (starRingEnd ℂ) (cokernelVector thetaSource α x) *
            (-Complex.I * deriv g x + α * g x) / (thetaSource.k x : ℂ) =
          (-Complex.I * deriv g x + α * g x) *
            ((starRingEnd ℂ) (cokernelVector thetaSource α x) /
              (thetaSource.k x : ℂ)) := by
        field_simp [hk]
      _ = (-Complex.I * deriv g x + α * g x) * sourceChar α x := by
        rw [conj_cokernelVector_div]
  rw [integral_congr_ae (ae_of_all _ hpoint)]
  have hderiv : ∀ x : ℝ, HasDerivAt g (deriv g x) x :=
    fun x => (hg.differentiable (by simp) x).hasDerivAt
  have hprodSupport : HasCompactSupport (fun x => g x * sourceChar α x) :=
    hgs.mul_right
  have hzeroInf := hprodSupport.is_zero_at_infty
  rw [cocompact_eq_atBot_atTop] at hzeroInf
  have hbot : Tendsto (fun x => g x * sourceChar α x) atBot (𝓝 0) :=
    hzeroInf.mono_left le_sup_left
  have htop : Tendsto (fun x => g x * sourceChar α x) atTop (𝓝 0) :=
    hzeroInf.mono_left le_sup_right
  have hderivCont : Continuous (deriv g) :=
    (hg.of_le (by simp)).continuous_deriv le_rfl
  have hintCont : Continuous (fun x =>
      (-Complex.I * deriv g x + α * g x) * sourceChar α x) :=
    ((continuous_const.mul hderivCont).add
      (continuous_const.mul hg.continuous)).mul (continuous_sourceChar α)
  have hintSupport : HasCompactSupport (fun x =>
      (-Complex.I * deriv g x + α * g x) * sourceChar α x) :=
    (HasCompactSupport.add hgs.deriv.mul_left hgs.mul_left).mul_right
  exact integral_range_pairing hderiv hbot htop
    (hintCont.integrable_of_hasCompactSupport hintSupport)

/-- The translated range map has the actual conormal in its orthogonal complement. -/
theorem thetaCokernelVector_mem_orthogonal_range (α : ℂ) :
    thetaCokernelVector α ∈
      (LinearMap.range (thetaShiftedRangeMap α).toLinearMap)ᗮ := by
  rw [(thetaShiftedRangeMap α).orthogonal_range]
  apply dense_thetaDerivativeCoreOutput.eq_of_inner_right ℂ
  intro k hk
  rcases hk with ⟨g, hg, hgs, hk⟩
  have hcore := inner_thetaCokernelVector_thetaShiftedRangeMap_core α hg hgs
  let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
  let k' : thetaCentered :=
    ⟨quantileUnitary thetaSource f, quantile_sourceD_mem_centered hg hgs⟩
  have hkk : k = k' := Subtype.ext hk
  calc
    inner ℂ k ((thetaShiftedRangeMap α).adjoint (thetaCokernelVector α)) =
        inner ℂ (thetaShiftedRangeMap α k) (thetaCokernelVector α) :=
      (thetaShiftedRangeMap α).adjoint_inner_right k (thetaCokernelVector α)
    _ = inner ℂ (thetaShiftedRangeMap α k') (thetaCokernelVector α) := by rw [hkk]
    _ = (starRingEnd ℂ)
        (inner ℂ (thetaCokernelVector α) (thetaShiftedRangeMap α k')) :=
      (inner_conj_symm _ _).symm
    _ = 0 := by rw [hcore, map_zero]
    _ = inner ℂ k (0 : thetaCentered) := by simp

/-! ### Exact translated range, cokernel, and Fredholm index -/

/-- Every translated bounded range map has exactly the hyperplane annihilated by its concrete
cokernel vector as range. -/
theorem thetaShiftedRangeMap_range_eq_orthogonal (α : ℂ) :
    LinearMap.range (thetaShiftedRangeMap α).toLinearMap =
      (ℂ ∙ thetaCokernelVector α)ᗮ := by
  have hcompact : IsCompactOperator (α • thetaCenteredSourceInverse) :=
    isCompactOperator_thetaCompactSourceInverse.comp_clm
      thetaCentered.subtypeL |>.smul α
  have hcenterOrth : thetaCenteredᗮ = ℂ ∙ pinnedOne := by
    rw [thetaCentered, Submodule.orthogonal_orthogonal]
  have hrange := compact_hyperplane_perturbation_range_eq_orthogonal
    thetaCentered thetaCentered_isClosed pinnedOne pinnedOne_ne_zero hcenterOrth
    (α • thetaCenteredSourceInverse) hcompact
    (by simpa only [thetaShiftedRangeMap] using thetaShiftedRangeMap_injective α)
    (by
      change IsClosed (Set.range (thetaCentered.subtypeL +
        α • thetaCenteredSourceInverse))
      simpa only [thetaShiftedRangeMap] using thetaShiftedRangeMap_isClosed_range α)
    (thetaCokernelVector α) (thetaCokernelVector_ne_zero α)
    (by simpa only [thetaShiftedRangeMap] using
      thetaCokernelVector_mem_orthogonal_range α)
  simpa only [thetaShiftedRangeMap] using hrange

/-- Scalar functional whose kernel is the exact translated range. -/
def thetaCokernelFunctional (α : ℂ) : H →L[ℂ] ℂ :=
  innerSL ℂ (thetaCokernelVector α)

theorem thetaCokernelFunctional_surjective (α : ℂ) :
    Function.Surjective (thetaCokernelFunctional α) := by
  intro c
  let q : ℂ := inner ℂ (thetaCokernelVector α) (thetaCokernelVector α)
  have hq : q ≠ 0 := inner_self_ne_zero.mpr (thetaCokernelVector_ne_zero α)
  refine ⟨(c / q) • thetaCokernelVector α, ?_⟩
  rw [thetaCokernelFunctional, innerSL_apply_apply, inner_smul_right]
  exact div_mul_cancel₀ c hq

theorem thetaShiftedRangeMap_range_eq_ker_cokernelFunctional (α : ℂ) :
    LinearMap.range (thetaShiftedRangeMap α).toLinearMap =
      LinearMap.ker (thetaCokernelFunctional α).toLinearMap := by
  rw [thetaShiftedRangeMap_range_eq_orthogonal]
  ext y
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, LinearMap.mem_ker]
  rfl

theorem thetaShiftedWeightedDerivative_range_eq_ker_cokernelFunctional (α : ℂ) :
    (thetaShiftedWeightedDerivative α).rangeSubmodule =
      LinearMap.ker (thetaCokernelFunctional α).toLinearMap := by
  rw [thetaShiftedWeightedDerivative_range,
    thetaShiftedRangeMap_range_eq_ker_cokernelFunctional]

theorem thetaShiftedWeightedDerivative_isFredholm (α : ℂ) :
    (thetaShiftedWeightedDerivative α).IsFredholm := by
  apply LinearPMap.isFredholm_of_injective_of_range_eq_ker
    (thetaCokernelFunctional α).continuous
    (thetaShiftedWeightedDerivative_kernel_eq_bot α)
    (thetaCokernelFunctional_surjective α)
    (thetaShiftedWeightedDerivative_range_eq_ker_cokernelFunctional α)

theorem thetaShiftedWeightedDerivative_index_eq_neg_one (α : ℂ) :
    (thetaShiftedWeightedDerivative α).index = -1 :=
  LinearPMap.index_eq_neg_one_of_injective_of_range_eq_ker
    (thetaShiftedWeightedDerivative_kernel_eq_bot α)
    (thetaCokernelFunctional_surjective α)
    (thetaShiftedWeightedDerivative_range_eq_ker_cokernelFunctional α)

theorem thetaShiftedWeightedDerivative_adjoint_kernel (α : ℂ) :
    (thetaShiftedWeightedDerivative α).adjoint.kernel =
      ℂ ∙ thetaCokernelVector α := by
  rw [LinearPMap.adjoint_kernel_eq_orthogonal_range
    (thetaShiftedWeightedDerivative α)
      (thetaShiftedWeightedDerivative_dense_domain α)]
  rw [thetaShiftedWeightedDerivative_range,
    thetaShiftedRangeMap_range_eq_orthogonal,
    Submodule.orthogonal_orthogonal]

end HedenmalmClosedWeightedDerivative

end

end RHTower
