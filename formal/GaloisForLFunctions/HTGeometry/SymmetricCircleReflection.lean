import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity
import GaloisForLFunctions.HTGeometry.ModularFormationDoubleMeasures
import GaloisForLFunctions.HTGeometry.SzegoMonomialShift

/-!
# Reflection and coordinate unitary for symmetric circle states

An absolutely summable real Fourier tail defines an inversion-even circle density.  This file
builds the resulting linear unitary reflection on weighted `L²`, bundles multiplication by the
circle coordinate as a unitary, proves `Θ U Θ = U⁻¹`, and identifies the reflected monomial Gram
kernel with the positive-index moments of the underlying measure.

The construction is generic: no prime source, zero-location premise, or reflected positivity
assumption occurs here.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex
open scoped BigOperators ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

/-- A symmetric real Fourier density is invariant under inversion of the circle. -/
theorem symmetricCircleFourierDensity_inv (a : ℕ → ℝ) (z : Circle) :
    symmetricCircleFourierDensity a z⁻¹ = symmetricCircleFourierDensity a z := by
  unfold symmetricCircleFourierDensity
  congr 2
  apply tsum_congr
  intro n
  rw [Circle.coe_inv_eq_conj, ← map_pow, conj_re]

/-- Normalized circle Lebesgue measure is invariant under circle inversion. -/
theorem map_inv_circleLebesgue :
    Measure.map Inv.inv circleLebesgue = circleLebesgue := by
  rw [circleLebesgue, Measure.map_map measurable_inv
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.measurable]
  have hfun :
      Inv.inv ∘ (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) =
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) ∘ Neg.neg := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, AddCircle.homeomorphCircle_apply,
      AddCircle.homeomorphCircle_apply, AddCircle.toCircle_neg]
  rw [hfun, ← Measure.map_map
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.measurable
    measurable_neg, (Measure.measurePreserving_neg
      (AddCircle.haarAddCircle (T := (1 : ℝ)))).map_eq]

/-- The measure defined by a symmetric real Fourier density is inversion invariant. -/
theorem map_inv_symmetricCircleFourierDensityMeasure (a : ℕ → ℝ) :
    Measure.map Inv.inv (symmetricCircleFourierDensityMeasure a) =
      symmetricCircleFourierDensityMeasure a := by
  rw [symmetricCircleFourierDensityMeasure]
  rw [map_withDensity_of_involution measurable_inv inv_inv map_inv_circleLebesgue
    ((measurable_symmetricCircleFourierDensity a).ennreal_ofReal)]
  congr 1
  funext z
  rw [symmetricCircleFourierDensity_inv]

/-- Pullback by circle inversion as a complex-linear `L²` isometry. -/
def circleInvReflectionLI (mu : Measure Circle)
    (hmu : MeasurePreserving Inv.inv mu mu) :
    Lp ℂ 2 mu →ₗᵢ[ℂ] Lp ℂ 2 mu where
  toLinearMap := Lp.compMeasurePreservingₗ ℂ Inv.inv hmu
  norm_map' f := Lp.norm_compMeasurePreserving f hmu

/-- Almost-everywhere formula for the circle reflection. -/
theorem circleInvReflectionLI_coeFn (mu : Measure Circle)
    (hmu : MeasurePreserving Inv.inv mu mu) (f : Lp ℂ 2 mu) :
    ⇑(circleInvReflectionLI mu hmu f) =ᵐ[mu]
      fun z : Circle => f z⁻¹ := by
  exact Lp.coeFn_compMeasurePreserving f hmu

/-- Circle reflection is an involution. -/
theorem circleInvReflectionLI_apply_self (mu : Measure Circle)
    (hmu : MeasurePreserving Inv.inv mu mu) (f : Lp ℂ 2 mu) :
    circleInvReflectionLI mu hmu (circleInvReflectionLI mu hmu f) = f := by
  apply Lp.ext
  have h1 := circleInvReflectionLI_coeFn mu hmu (circleInvReflectionLI mu hmu f)
  have h2 := circleInvReflectionLI_coeFn mu hmu f
  have h3 : (fun z : Circle => (circleInvReflectionLI mu hmu f) z⁻¹)
      =ᵐ[mu] fun z : Circle => f (z⁻¹)⁻¹ :=
    hmu.quasiMeasurePreserving.ae (p := fun y : Circle =>
      (circleInvReflectionLI mu hmu f) y = f y⁻¹) h2
  filter_upwards [h1, h3] with z hz hz'
  rw [hz, hz', inv_inv]

/-- Circle reflection bundled as a linear isometric equivalence. -/
def circleInvReflectionLIE (mu : Measure Circle)
    (hmu : MeasurePreserving Inv.inv mu mu) :
    Lp ℂ 2 mu ≃ₗᵢ[ℂ] Lp ℂ 2 mu :=
  LinearIsometryEquiv.ofSurjective (circleInvReflectionLI mu hmu) fun f =>
    ⟨circleInvReflectionLI mu hmu f, circleInvReflectionLI_apply_self mu hmu f⟩

/-- Reflected analytic monomials have the Hankel-oriented Gram kernel. -/
theorem circleInvReflectionLI_monomial_inner
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hmu : MeasurePreserving Inv.inv mu mu) (i j : ℕ) :
    inner ℂ (circleInvReflectionLI mu hmu (circleMonomialLp mu i))
        (circleMonomialLp mu j) =
      ∫ z : Circle, (z : ℂ) ^ (i + j) ∂mu := by
  have hiInv : (fun z : Circle => (circleMonomialLp mu i) z⁻¹)
      =ᵐ[mu] fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ i :=
    hmu.quasiMeasurePreserving.ae (p := fun y : Circle =>
      (circleMonomialLp mu i) y = (y : ℂ) ^ i)
      (circleMonomialLp_coeFn_ae mu i)
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleInvReflectionLI_coeFn mu hmu (circleMonomialLp mu i),
    hiInv, circleMonomialLp_coeFn_ae mu j] with z hR hi hj
  rw [hR, hj, RCLike.inner_apply]
  rw [hi, Circle.coe_inv_eq_conj, ← map_pow]
  simp only [starRingEnd_apply, star_star]
  rw [mul_comm, pow_add]

/-- A finite analytic polynomial with real coefficients, represented in `L²(mu)`. -/
def finiteRealCirclePolynomialLp (mu : Measure Circle) [IsFiniteMeasure mu]
    {n : ℕ} (v : Fin n → ℝ) : Lp ℂ 2 mu :=
  ∑ i : Fin n, (v i : ℂ) • circleMonomialLp mu i

/-- Reflected Gram value of a finite real analytic polynomial as the moment double sum. -/
theorem circleInvReflectionLI_finitePolynomial_inner
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hmu : MeasurePreserving Inv.inv mu mu) {n : ℕ} (v : Fin n → ℝ) :
    inner ℂ
        (circleInvReflectionLI mu hmu (finiteRealCirclePolynomialLp mu v))
        (finiteRealCirclePolynomialLp mu v) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((v i * v j : ℝ) : ℂ) *
          ∫ z : Circle, (z : ℂ) ^ ((i : ℕ) + (j : ℕ)) ∂mu := by
  simp only [finiteRealCirclePolynomialLp, map_sum, map_smul, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [circleInvReflectionLI_monomial_inner mu hmu j i]
  rw [show (j : ℕ) + (i : ℕ) = (i : ℕ) + (j : ℕ) by omega]
  push_cast
  simp
  ring

/-- Even channel of a vector relative to a linear isometric reflection. -/
def circleReflectionCosineChannel {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (R : E →ₗᵢ[ℂ] E) (f : E) : E :=
  (2 : ℂ)⁻¹ • (f + R f)

/-- Odd channel of a vector relative to a linear isometric reflection. -/
def circleReflectionSineChannel {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (R : E →ₗᵢ[ℂ] E) (f : E) : E :=
  ((2 : ℂ) * Complex.I)⁻¹ • (f - R f)

/-- Exact cosine-minus-sine polarization of a reflected Hilbert value. -/
theorem norm_circleReflectionCosineChannel_sq_sub_sine
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (R : E →ₗᵢ[ℂ] E) (f : E) :
    ‖circleReflectionCosineChannel R f‖ ^ 2 -
        ‖circleReflectionSineChannel R f‖ ^ 2 =
      (inner ℂ (R f) f).re := by
  have hre : (inner ℂ f (R f)).re = (inner ℂ (R f) f).re := by
    rw [← inner_conj_symm, conj_re]
  have hre' : RCLike.re (inner ℂ f (R f)) = RCLike.re (inner ℂ (R f) f) := hre
  rw [circleReflectionCosineChannel, circleReflectionSineChannel,
    norm_smul, norm_smul, norm_inv, norm_inv, norm_mul, Complex.norm_I,
    mul_one, norm_ofNat]
  rw [mul_pow, mul_pow, norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), R.norm_map]
  rw [hre']
  norm_num
  ring

/-- Coordinate multiplication, bundled as a linear isometry. -/
def circleZMulLI (mu : Measure Circle) [IsFiniteMeasure mu] :
    Lp ℂ 2 mu →ₗᵢ[ℂ] Lp ℂ 2 mu where
  toLinearMap := circleZMulLpHom mu
  norm_map' := circleZMulLp_norm mu

/-- Coordinate multiplication on circle `L²` is surjective. -/
theorem circleZMulLI_surjective (mu : Measure Circle) [IsFiniteMeasure mu] :
    Function.Surjective (circleZMulLI mu) := by
  intro f
  have hgmem : MemLp (fun z : Circle => conj (z : ℂ) * f z) 2 mu := by
    have hconj : AEStronglyMeasurable (fun z : Circle => conj (z : ℂ)) mu := by
      have hcont : Continuous (fun z : Circle => conj (z : ℂ)) :=
        Complex.continuous_conj.comp continuous_subtype_val
      exact hcont.aestronglyMeasurable
    have hmeas : AEStronglyMeasurable (fun z : Circle => conj (z : ℂ) * f z) mu :=
      hconj.mul (Lp.aestronglyMeasurable f)
    refine ⟨hmeas, ?_⟩
    rw [show eLpNorm (fun z : Circle => conj (z : ℂ) * f z) 2 mu =
        eLpNorm (⇑f) 2 mu from eLpNorm_congr_norm_ae
          (Filter.Eventually.of_forall fun z => by
            rw [norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul])]
    exact (Lp.memLp f).2
  let g : Lp ℂ 2 mu := MemLp.toLp (fun z : Circle => conj (z : ℂ) * f z) hgmem
  refine ⟨g, ?_⟩
  apply Lp.ext
  filter_upwards [circleZMulLp_coeFn_ae mu g, hgmem.coeFn_toLp] with z hz hg
  change (circleZMulLp mu g) z = f z
  rw [hz, hg, ← mul_assoc, Complex.mul_conj]
  have hnormSq : Complex.normSq (z : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  rw [hnormSq]
  norm_num

/-- Multiplication by the circle coordinate as a linear isometric equivalence, hence a unitary. -/
def circleZMulLIE (mu : Measure Circle) [IsFiniteMeasure mu] :
    Lp ℂ 2 mu ≃ₗᵢ[ℂ] Lp ℂ 2 mu :=
  LinearIsometryEquiv.ofSurjective (circleZMulLI mu) (circleZMulLI_surjective mu)

@[simp] theorem circleZMulLIE_apply (mu : Measure Circle) [IsFiniteMeasure mu]
    (f : Lp ℂ 2 mu) :
    circleZMulLIE mu f = circleZMulLp mu f := rfl

/-- `U Θ U Θ = 1`, the pointwise left-inverse form of the reflection relation. -/
theorem circleZMulLp_reflection_conj_leftInverse
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hmu : MeasurePreserving Inv.inv mu mu) (f : Lp ℂ 2 mu) :
    circleZMulLp mu
        (circleInvReflectionLI mu hmu
          (circleZMulLp mu (circleInvReflectionLI mu hmu f))) = f := by
  let R := circleInvReflectionLI mu hmu
  have hRf : (fun z : Circle => (R f) z) =ᵐ[mu] fun z => f z⁻¹ :=
    circleInvReflectionLI_coeFn mu hmu f
  have hURf : (fun z : Circle => (circleZMulLp mu (R f)) z) =ᵐ[mu]
      fun z => (z : ℂ) * (R f) z := circleZMulLp_coeFn_ae mu (R f)
  have hURfInv : (fun z : Circle => (circleZMulLp mu (R f)) z⁻¹) =ᵐ[mu]
      fun z => ((z⁻¹ : Circle) : ℂ) * (R f) z⁻¹ :=
    hmu.quasiMeasurePreserving.ae (p := fun y : Circle =>
      (circleZMulLp mu (R f)) y = (y : ℂ) * (R f) y) hURf
  have hRfInv0 : (fun z : Circle => (R f) z⁻¹) =ᵐ[mu]
      fun z => f (z⁻¹)⁻¹ :=
    hmu.quasiMeasurePreserving.ae (p := fun y : Circle => (R f) y = f y⁻¹) hRf
  have hRfInv : (fun z : Circle => (R f) z⁻¹) =ᵐ[mu] fun z => f z := by
    filter_upwards [hRfInv0] with z hz
    simpa using hz
  have hRURf := circleInvReflectionLI_coeFn mu hmu (circleZMulLp mu (R f))
  have hFinal := circleZMulLp_coeFn_ae mu (R (circleZMulLp mu (R f)))
  apply Lp.ext
  filter_upwards [hFinal, hRURf, hURfInv, hRfInv] with z h1 h2 h3 h4
  rw [h1, h2, h3, h4, Circle.coe_inv]
  field_simp

/-- **`Θ U Θ = U⁻¹`.** Circle inversion conjugates coordinate multiplication to its inverse. -/
theorem circleInvReflectionLI_circleZMulLp_circleInvReflectionLI
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hmu : MeasurePreserving Inv.inv mu mu) (f : Lp ℂ 2 mu) :
    circleInvReflectionLI mu hmu
        (circleZMulLp mu (circleInvReflectionLI mu hmu f)) =
      (circleZMulLIE mu).symm f := by
  apply (circleZMulLIE mu).injective
  rw [circleZMulLIE_apply, LinearIsometryEquiv.apply_symm_apply]
  exact circleZMulLp_reflection_conj_leftInverse mu hmu f

end

end GaloisForLFunctions.HTGeometry
