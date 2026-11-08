import GaloisForLFunctions.SelbergClass.Primon.KestenEvenSector

/-!
# Orthogonal projection onto prime likelihoods

Averaging a semicircle observable with its reflection projects exactly onto
the closed likelihood space. The antisymmetric remainder is orthogonal to
every likelihood. This gives the exact approximation error and the unique
nearest likelihood-space observable.
-/

open MeasureTheory
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Reflection averaging as a bounded linear operator. -/
def semicircleEvenPart : SemicircleL2 →L[ℝ] SemicircleL2 :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ SemicircleL2 + semicircleReflection.toContinuousLinearMap)

/-- The antisymmetric remainder as a bounded linear operator. -/
def semicircleOddPart : SemicircleL2 →L[ℝ] SemicircleL2 :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ SemicircleL2 - semicircleReflection.toContinuousLinearMap)

@[simp] theorem semicircleEvenPart_apply (f : SemicircleL2) :
    semicircleEvenPart f = (1 / 2 : ℝ) • (f + semicircleReflection f) := rfl

@[simp] theorem semicircleOddPart_apply (f : SemicircleL2) :
    semicircleOddPart f = (1 / 2 : ℝ) • (f - semicircleReflection f) := rfl

/-- Symmetric and antisymmetric parts reconstruct the original observable. -/
theorem semicircleEvenPart_add_oddPart (f : SemicircleL2) :
    semicircleEvenPart f + semicircleOddPart f = f := by
  rw [semicircleEvenPart_apply, semicircleOddPart_apply]
  module

/-- Reflection averaging is fixed by reflection. -/
theorem semicircleReflection_evenPart (f : SemicircleL2) :
    semicircleReflection (semicircleEvenPart f) = semicircleEvenPart f := by
  rw [semicircleEvenPart_apply, map_smul, map_add, semicircleReflection_involutive]
  rw [add_comm]

/-- The antisymmetric remainder changes sign under reflection. -/
theorem semicircleReflection_oddPart (f : SemicircleL2) :
    semicircleReflection (semicircleOddPart f) = -semicircleOddPart f := by
  rw [semicircleOddPart_apply, map_smul, map_sub, semicircleReflection_involutive]
  module

/-- Reflection averaging lands in the actual closed likelihood span. -/
theorem semicircleEvenPart_mem_likelihoodHilbert (f : SemicircleL2) :
    semicircleEvenPart f ∈ KestenLikelihoodHilbert :=
  (mem_likelihoodHilbert_iff_reflection_fixed _).2 (semicircleReflection_evenPart f)

/-- The antisymmetric remainder is orthogonal to every prime likelihood. -/
theorem semicircleOddPart_mem_orthogonal (f : SemicircleL2) :
    semicircleOddPart f ∈ KestenLikelihoodHilbertᗮ :=
  (mem_orthogonal_likelihood_iff_reflection_neg _).2 (semicircleReflection_oddPart f)

/-- Reflection averaging fixes every vector in the likelihood Hilbert space. -/
theorem semicircleEvenPart_on_likelihoodHilbert (g : KestenLikelihoodHilbert) :
    semicircleEvenPart g = (g : SemicircleL2) := by
  rw [semicircleEvenPart_apply, (mem_likelihoodHilbert_iff_reflection_fixed g).1 g.property]
  module

/-- Reflection averaging is an idempotent projection. -/
theorem semicircleEvenPart_idempotent (f : SemicircleL2) :
    semicircleEvenPart (semicircleEvenPart f) = semicircleEvenPart f :=
  semicircleEvenPart_on_likelihoodHilbert ⟨_, semicircleEvenPart_mem_likelihoodHilbert f⟩

private theorem norm_sq_even_add_odd (u : KestenLikelihoodHilbert) (v : KestenLikelihoodHilbertᗮ) :
    ‖(u : SemicircleL2) + (v : SemicircleL2)‖ ^ 2 =
      ‖(u : SemicircleL2)‖ ^ 2 + ‖(v : SemicircleL2)‖ ^ 2 := by
  have huv : inner ℝ (u : SemicircleL2) (v : SemicircleL2) = 0 := v.property _ u.property
  have hvu : inner ℝ (v : SemicircleL2) (u : SemicircleL2) = 0 := by
    rw [real_inner_comm, huv]
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
  simp only [huv, hvu, add_zero, zero_add, real_inner_self_eq_norm_sq]

/-- The even and odd sectors satisfy the exact Pythagorean energy decomposition. -/
theorem norm_sq_semicircle_parity (f : SemicircleL2) :
    ‖f‖ ^ 2 = ‖semicircleEvenPart f‖ ^ 2 + ‖semicircleOddPart f‖ ^ 2 := by
  calc
    _ = ‖semicircleEvenPart f + semicircleOddPart f‖ ^ 2 := by rw [semicircleEvenPart_add_oddPart]
    _ = _ := norm_sq_even_add_odd ⟨_, semicircleEvenPart_mem_likelihoodHilbert f⟩
      ⟨_, semicircleOddPart_mem_orthogonal f⟩

/-- Every likelihood-space approximation error splits into its unavoidable odd part and even error. -/
theorem norm_sq_likelihood_approximation (f : SemicircleL2) (g : KestenLikelihoodHilbert) :
    ‖f - (g : SemicircleL2)‖ ^ 2 =
      ‖semicircleOddPart f‖ ^ 2 + ‖semicircleEvenPart f - (g : SemicircleL2)‖ ^ 2 := by
  have he : f - (g : SemicircleL2) =
      (semicircleEvenPart f - (g : SemicircleL2)) + semicircleOddPart f := by
    calc
      _ = (semicircleEvenPart f + semicircleOddPart f) - (g : SemicircleL2) := by
        rw [semicircleEvenPart_add_oddPart]
      _ = _ := by abel
  rw [he]
  have hu := KestenLikelihoodHilbert.sub_mem (semicircleEvenPart_mem_likelihoodHilbert f) g.property
  rw [norm_sq_even_add_odd ⟨_, hu⟩ ⟨_, semicircleOddPart_mem_orthogonal f⟩, add_comm]

/-- The residual of reflection averaging is exactly the odd component. -/
theorem sub_semicircleEvenPart (f : SemicircleL2) : f - semicircleEvenPart f = semicircleOddPart f := by
  calc
    _ = (semicircleEvenPart f + semicircleOddPart f) - semicircleEvenPart f := by
      rw [semicircleEvenPart_add_oddPart]
    _ = _ := add_sub_cancel_left _ _

/-- Reflection averaging minimizes distance to the closed prime-likelihood space. -/
theorem semicircleEvenPart_best_approximation (f : SemicircleL2) (g : KestenLikelihoodHilbert) :
    ‖f - semicircleEvenPart f‖ ≤ ‖f - (g : SemicircleL2)‖ := by
  rw [sub_semicircleEvenPart]
  have h := norm_sq_likelihood_approximation f g
  nlinarith only [h, sq_nonneg ‖semicircleEvenPart f - (g : SemicircleL2)‖,
    norm_nonneg (semicircleOddPart f), norm_nonneg (f - (g : SemicircleL2))]

/-- The nearest likelihood-space observable is unique. -/
theorem semicircleEvenPart_unique_best (f : SemicircleL2) (g : KestenLikelihoodHilbert) :
    ‖f - (g : SemicircleL2)‖ = ‖f - semicircleEvenPart f‖ ↔
      (g : SemicircleL2) = semicircleEvenPart f := by
  constructor
  · intro h
    rw [sub_semicircleEvenPart] at h
    have he := norm_sq_likelihood_approximation f g
    rw [h] at he
    have hz : ‖semicircleEvenPart f - (g : SemicircleL2)‖ = 0 := by
      nlinarith only [he, norm_nonneg (semicircleEvenPart f - (g : SemicircleL2))]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · intro h
    rw [h]


/-- The nearest likelihood-space observable is the pointwise reflection average almost everywhere. -/
theorem semicircleEvenPart_ae (f : SemicircleL2) :
    semicircleEvenPart f =ᵐ[(semicircleSpectralLaw : Measure ℝ)]
      fun x => (f x + f (-x)) / 2 := by
  change ((1 / 2 : ℝ) • (f + semicircleReflection f) : SemicircleL2) =ᵐ[_] _
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (f + semicircleReflection f),
    Lp.coeFn_add f (semicircleReflection f), semicircleReflection_ae f] with x hs ha hr
  calc
    _ = (1 / 2 : ℝ) * ((f + semicircleReflection f) x) := hs
    _ = _ := by
      rw [ha]
      change (1 / 2 : ℝ) * (f x + semicircleReflection f x) = _
      rw [hr]
      ring

/-- The unavoidable approximation residual is the pointwise antisymmetric part almost everywhere. -/
theorem semicircleOddPart_ae (f : SemicircleL2) :
    semicircleOddPart f =ᵐ[(semicircleSpectralLaw : Measure ℝ)]
      fun x => (f x - f (-x)) / 2 := by
  change ((1 / 2 : ℝ) • (f - semicircleReflection f) : SemicircleL2) =ᵐ[_] _
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (f - semicircleReflection f),
    Lp.coeFn_sub f (semicircleReflection f), semicircleReflection_ae f] with x hs ha hr
  calc
    _ = (1 / 2 : ℝ) * ((f - semicircleReflection f) x) := hs
    _ = _ := by
      rw [ha]
      change (1 / 2 : ℝ) * (f x - semicircleReflection f x) = _
      rw [hr]
      ring

end
end GaloisForLFunctions.SelbergClass.Primon

