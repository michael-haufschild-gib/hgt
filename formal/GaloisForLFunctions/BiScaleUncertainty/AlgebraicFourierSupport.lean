import GaloisForLFunctions.HTGeometry.SphereHomogeneousNullSet
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Algebraic Fourier support in `L²`

Proper real algebraic sets have Lebesgue measure zero. Plancherel therefore
excludes them, and countable unions of them, as the essential Fourier
support of a nonzero square-integrable source. This gives the `p = 2`
case of Bi–Sun's support theorem and applies to every polynomial relation
among frequency coordinates.
-/

open MeasureTheory
open scoped FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty.AlgebraicFourierSupport
noncomputable section

abbrev Ambient (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Source (m : ℕ) := Lp ℂ 2 (volume : Measure (Ambient m))

private theorem zero_of_fourier_ae_zero {m : ℕ} (f : Source m)
    (h : (⇑(𝓕 f : Source m)) =ᵐ[volume] (0 : Ambient m → ℂ)) : f = 0 := by
  have hF : (𝓕 f : Source m) = 0 := Lp.ext (h.trans (Lp.coeFn_zero ℂ 2 volume).symm)
  apply norm_eq_zero.mp
  rw [← Lp.norm_fourier_eq f, hF, norm_zero]

/-- Essential Fourier support in a countable union of polynomial zero sets is possible
only for a zero source or a family containing the zero polynomial. -/
theorem countable_polynomial_support_iff {m : ℕ} (f : Source m)
    (P : ℕ → MvPolynomial (Fin m) ℝ) :
    (∀ᵐ ξ : Ambient m, (∀ n, MvPolynomial.eval (WithLp.ofLp ξ) (P n) ≠ 0) →
      (𝓕 f : Source m) ξ = 0) ↔ (∃ n, P n = 0) ∨ f = 0 := by
  constructor
  · intro hs
    by_cases hP : ∃ n, P n = 0
    · exact Or.inl hP
    right
    apply zero_of_fourier_ae_zero f
    have hp (n : ℕ) : ∀ᵐ ξ : Ambient m, MvPolynomial.eval (WithLp.ofLp ξ) (P n) ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using
        HTGeometry.volume_euclidean_zeroSet_eq_zero (fun hn => hP ⟨n, hn⟩)
    filter_upwards [hs, ae_all_iff.mpr hp] with ξ hξ havoid
    exact hξ havoid
  · rintro (⟨n, hn⟩ | hf)
    · filter_upwards with ξ hξ
      have hzero : MvPolynomial.eval (WithLp.ofLp ξ) (P n) = 0 := by rw [hn]; simp
      exact (hξ n hzero).elim
    · have hF : (𝓕 f : Source m) = 0 := by rw [hf]; simp
      rw [hF]
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (Ambient m))] with ξ hξ
      exact fun _ => hξ

/-- A single algebraic relation cannot contain nonzero `L²` Fourier mass. -/
theorem polynomial_support_iff {m : ℕ} (f : Source m) (P : MvPolynomial (Fin m) ℝ) :
    (∀ᵐ ξ : Ambient m, MvPolynomial.eval (WithLp.ofLp ξ) P ≠ 0 →
      (𝓕 f : Source m) ξ = 0) ↔ P = 0 ∨ f = 0 := by
  simpa using countable_polynomial_support_iff f (fun _ => P)

private theorem quadratic_relation_ne_zero (m : ℕ) :
    (MvPolynomial.X (0 : Fin (m + 2)) - MvPolynomial.X (1 : Fin (m + 2)) ^ 2 :
      MvPolynomial (Fin (m + 2)) ℝ) ≠ 0 := by
  intro hp
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    norm_num at h'
  have h := congrArg (MvPolynomial.eval (fun j : Fin (m + 2) => if j = 0 then (1 : ℝ) else 0)) hp
  simp [h10] at h

/-- The quadratic frequency relation present in every degree-at-least-two moment surface
forces an `L²` source to vanish. -/
theorem quadratic_graph_support_iff (m : ℕ) (f : Source (m + 2)) :
    (∀ᵐ ξ : Ambient (m + 2), ξ 0 ≠ (ξ 1) ^ 2 → (𝓕 f : Source (m + 2)) ξ = 0) ↔
      f = 0 := by
  have h := polynomial_support_iff f
    (MvPolynomial.X (0 : Fin (m + 2)) - MvPolynomial.X (1 : Fin (m + 2)) ^ 2)
  simpa only [map_sub, map_pow, MvPolynomial.eval_X, sub_ne_zero,
    or_iff_right (quadratic_relation_ne_zero m)] using h

#print axioms countable_polynomial_support_iff
#print axioms polynomial_support_iff
#print axioms quadratic_graph_support_iff

end
end GaloisForLFunctions.BiScaleUncertainty.AlgebraicFourierSupport
