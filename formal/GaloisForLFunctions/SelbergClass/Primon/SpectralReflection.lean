import GaloisForLFunctions.SelbergClass.Primon.SpectralCharacterAlgebra
import GaloisForLFunctions.SelbergClass.Primon.SemicircleObservableLinear
import GaloisForLFunctions.SelbergClass.Primon.KestenMomentRecurrence
import GaloisForLFunctions.HTGeometry.CompactMomentReflectionSymmetry

/-!
# Reflection of the actual spectral laws

Vanishing odd moments and compact support force reflection invariance of
both prime laws and the semicircle law. Reflection therefore acts as an
isometric involution on the actual semicircle Hilbert space.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem reflected_moments_of_odd_zero (μ : Measure ℝ)
    (hodd : ∀ n : ℕ, (∫ x, x ^ (2 * n + 1) ∂μ) = 0) (k : ℕ) :
    (∫ x : ℝ, (-x) ^ k ∂μ) = ∫ x : ℝ, x ^ k ∂μ := by
  rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with he | ho
  · have hk : k = 2 * (k / 2) := by omega
    have hf : (fun x : ℝ => (-x) ^ k) = fun x : ℝ => x ^ k := by
      funext x
      rw [hk]
      simp only [pow_mul, neg_sq]
    rw [hf]
  · have hk : k = 2 * (k / 2) + 1 := by omega
    have hf : (fun x : ℝ => (-x) ^ k) = fun x : ℝ => -(x ^ k) := by
      funext x
      rw [hk]
      simp only [pow_add, pow_mul, pow_one, neg_sq, mul_neg]
    rw [hf, integral_neg, hk, hodd, neg_zero]

/-- The semicircle probability measure is invariant under sign reversal. -/
theorem map_neg_semicircleSpectralLaw :
    Measure.map (fun x : ℝ => -x) (semicircleSpectralLaw : Measure ℝ) =
      (semicircleSpectralLaw : Measure ℝ) := by
  apply _root_.HTGeometry.map_neg_eq_self_of_compact_moments (by norm_num : (0 : ℝ) < 2)
    semicircleSpectralLaw_carried (fun k => (semicircleSpectralLaw_hasMoments k).1)
  apply reflected_moments_of_odd_zero
  intro n
  rw [(semicircleSpectralLaw_hasMoments _).2, semicircleMoment_odd]

/-- Every prime spectral probability measure is invariant under sign reversal. -/
theorem map_neg_kestenSpectralLaw (p : Nat.Primes) :
    Measure.map (fun x : ℝ => -x) (kestenSpectralLaw p : Measure ℝ) =
      (kestenSpectralLaw p : Measure ℝ) := by
  apply _root_.HTGeometry.map_neg_eq_self_of_compact_moments (by norm_num : (0 : ℝ) < 2)
    (kestenSpectralLaw_carried p) (fun k => (kestenSpectralLaw_hasMoments p k).1)
  apply reflected_moments_of_odd_zero
  intro n
  rw [(kestenSpectralLaw_hasMoments p _).2, kestenMoment_odd]

/-- Sign reversal preserves the semicircle law as a measurable transformation. -/
theorem measurePreserving_neg_semicircle :
    MeasurePreserving (fun x : ℝ => -x) (semicircleSpectralLaw : Measure ℝ)
      (semicircleSpectralLaw : Measure ℝ) :=
  ⟨measurable_neg, map_neg_semicircleSpectralLaw⟩

/-- Sign reversal preserves every prime spectral law. -/
theorem measurePreserving_neg_kesten (p : Nat.Primes) :
    MeasurePreserving (fun x : ℝ => -x) (kestenSpectralLaw p : Measure ℝ)
      (kestenSpectralLaw p : Measure ℝ) :=
  ⟨measurable_neg, map_neg_kestenSpectralLaw p⟩

/-- Reflection of square-integrable semicircle observables. -/
def semicircleReflection : SemicircleL2 →ₗᵢ[ℝ] SemicircleL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ => -x) measurePreserving_neg_semicircle

/-- The Hilbert-space reflection is actual composition with `x ↦ -x` almost everywhere. -/
theorem semicircleReflection_ae (f : SemicircleL2) :
    semicircleReflection f =ᵐ[(semicircleSpectralLaw : Measure ℝ)] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_neg_semicircle

/-- Applying reflection twice is the identity on every semicircle observable. -/
theorem semicircleReflection_involutive (f : SemicircleL2) :
    semicircleReflection (semicircleReflection f) = f := by
  have h := Lp.compMeasurePreserving_comp_apply f
    measurePreserving_neg_semicircle measurePreserving_neg_semicircle
  have he : (fun x : ℝ => -x) ∘ (fun x : ℝ => -x) = id := by
    funext x
    simp
  simp only [he, Lp.compMeasurePreserving_id_apply] at h
  exact h.symm

/-- Fixed vectors of reflection are exactly the almost-everywhere even observables. -/
theorem semicircleReflection_fixed_iff (f : SemicircleL2) :
    semicircleReflection f = f ↔
      (fun x => f (-x)) =ᵐ[(semicircleSpectralLaw : Measure ℝ)] f := by
  constructor
  · intro h
    have ha := semicircleReflection_ae f
    rw [h] at ha
    exact ha.symm
  · intro h
    exact Lp.ext ((semicircleReflection_ae f).trans h)

/-- Reflection is self-adjoint because it is an isometric involution. -/
theorem inner_semicircleReflection (f g : SemicircleL2) :
    inner ℝ (semicircleReflection f) g = inner ℝ f (semicircleReflection g) := by
  have h := semicircleReflection.inner_map_map f (semicircleReflection g)
  rw [semicircleReflection_involutive] at h
  exact h


/-- On continuous observables, Hilbert reflection is pointwise sign reversal. -/
theorem semicircleReflection_observable (f : C(ℝ, ℝ)) :
    semicircleReflection (semicircleL2Observable f) =
      semicircleL2Observable ⟨fun x => f (-x), f.continuous.comp continuous_neg⟩ := by
  change Lp.compMeasurePreserving (fun x : ℝ => -x) measurePreserving_neg_semicircle
    ((memLp_semicircle_continuous f).toLp f) = _
  rw [Lp.toLp_compMeasurePreserving]
  rfl

/-- Spectral characters have their degree parity under sign reversal. -/
theorem spectralCharacter_reflection (n : ℕ) (x : ℝ) :
    spectralCharacter n (-x) = (-1 : ℝ) ^ n * spectralCharacter n x := by
  change (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval ((-x) / 2) =
    (-1 : ℝ) ^ n * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (x / 2)
  rw [neg_div, Polynomial.Chebyshev.U_eval_neg, Int.cast_negOnePow_natCast]

/-- Reflection is diagonal in the complete character family. -/
theorem semicircleReflection_character (n : ℕ) :
    semicircleReflection (spectralCharacterVector n) =
      (-1 : ℝ) ^ n • spectralCharacterVector n := by
  simp only [spectralCharacterVector]
  rw [semicircleReflection_observable]
  change semicircleObservableMap _ = (-1 : ℝ) ^ n • semicircleObservableMap (spectralCharacter n)
  rw [← map_smul]
  congr 1
  ext x
  exact spectralCharacter_reflection n x

/-- Every even character is fixed by actual spectral reflection. -/
theorem semicircleReflection_evenCharacter (n : ℕ) :
    semicircleReflection (spectralCharacterVector (2 * n)) = spectralCharacterVector (2 * n) := by
  rw [semicircleReflection_character]
  simp [pow_mul]

/-- Every odd character changes sign under actual spectral reflection. -/
theorem semicircleReflection_oddCharacter (n : ℕ) :
    semicircleReflection (spectralCharacterVector (2 * n + 1)) =
      -spectralCharacterVector (2 * n + 1) := by
  rw [semicircleReflection_character]
  simp [pow_add, pow_mul]

end
end GaloisForLFunctions.SelbergClass.Primon

