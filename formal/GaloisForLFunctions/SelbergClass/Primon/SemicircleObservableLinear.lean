import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodHardy

/-!
# Linear realization of continuous semicircle observables

Compact support makes every continuous spectral function square-integrable.
Its almost-everywhere class respects linear combinations and depends only
on its restriction to the spectral interval.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Passing a continuous observable to semicircle `L²` is a real linear map. -/
def semicircleObservableMap : C(ℝ, ℝ) →ₗ[ℝ] SemicircleL2 where
  toFun := semicircleL2Observable
  map_add' f g := (memLp_semicircle_continuous f).toLp_add (memLp_semicircle_continuous g)
  map_smul' c f := (memLp_semicircle_continuous f).toLp_const_smul c

@[simp] theorem semicircleObservableMap_apply (f : C(ℝ, ℝ)) :
    semicircleObservableMap f = semicircleL2Observable f := rfl

/-- Equal values on the spectral interval give the same Hilbert-space observable. -/
theorem semicircleL2Observable_eq_of_interval (f g : C(ℝ, ℝ))
    (h : ∀ x : Icc (-2 : ℝ) 2, f x = g x) :
    semicircleL2Observable f = semicircleL2Observable g := by
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  have ha : ∀ᵐ x ∂(semicircleSpectralLaw : Measure ℝ), x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact semicircleSpectralLaw_carried
  filter_upwards [ha] with x hx
  exact h ⟨x, hx⟩

/-- A continuous function's squared `L²` norm is its actual semicircle square integral. -/
theorem norm_sq_semicircleL2Observable (f : C(ℝ, ℝ)) :
    ‖semicircleL2Observable f‖ ^ 2 =
      ∫ x, (f x) ^ 2 ∂(semicircleSpectralLaw : Measure ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_semicircleL2Observable]
  simp only [pow_two]

end
end GaloisForLFunctions.SelbergClass.Primon

