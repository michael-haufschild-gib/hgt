import GaloisForLFunctions.Core
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Holomorphic Schwarz polarization

Pointwise coefficient conjugation is antiholomorphic.  Consequently a coefficient family and its
pointwise conjugate cannot both vary holomorphically in the same complex parameter: if both are
entire, the family is constant.  This rules out a nonconstant one-variable holomorphic OPUC
terminal whose reversed coefficients are formed by conjugating at the same parameter.

The positive replacement is polarization.  The Schwarz partner of `f` is placed in an independent
variable,

`f♯(w) = conj (f (conj w))`.

It is holomorphic whenever `f` is, and restriction to the Schwarz diagonal `w = conj z` recovers
the required pointwise conjugate `conj (f z)`.  Coefficientwise, this is the analytic interface for
a two-variable polarized OPUC or Bezoutian terminal.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The holomorphic Schwarz partner, with its own independent complex variable. -/
def schwarzPolarizedPartner (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  star (f (star w))

/-- On the Schwarz diagonal, polarization recovers ordinary pointwise conjugation. -/
@[simp] theorem schwarzPolarizedPartner_star
    (f : ℂ → ℂ) (z : ℂ) :
    schwarzPolarizedPartner f (star z) = star (f z) := by
  simp [schwarzPolarizedPartner]

/-- Schwarz polarization preserves holomorphic dependence on the independent partner variable. -/
theorem differentiable_schwarzPolarizedPartner
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (schwarzPolarizedPartner f) := by
  intro w
  rw [show schwarzPolarizedPartner f = star ∘ f ∘ ⇑(starRingEnd ℂ) by
    funext z
    rfl]
  have hw : (starRingEnd ℂ) (star w) = w := by simp
  rw [← hw]
  exact (hf (star w)).star_conj

/-- **One-variable conjugation obstruction.**  If both an entire coefficient family and its
pointwise conjugate are holomorphic in the same parameter, then the family is constant. -/
theorem eq_of_differentiable_pointwiseStar
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hstar : Differentiable ℂ (fun z => star (f z)))
    (z : ℂ) :
    f z = f 0 := by
  let plus : ℂ → ℂ := fun w => f w + star (f w)
  let minus : ℂ → ℂ := fun w => f w - star (f w)
  have hplus : Differentiable ℂ plus := hf.add hstar
  have hminus : Differentiable ℂ minus := hf.sub hstar
  obtain ⟨cplus, hcplus⟩ := AnalyticOnNhd.eq_const_of_im_eq_const
    (c₀ := 0)
    (hplus.differentiableOn.analyticOnNhd isOpen_univ)
    (fun w _ => by simp [plus]) isOpen_univ isConnected_univ
  obtain ⟨cminus, hcminus⟩ := AnalyticOnNhd.eq_const_of_re_eq_const
    (c₀ := 0)
    (hminus.differentiableOn.analyticOnNhd isOpen_univ)
    (fun w _ => by simp [minus]) isOpen_univ isConnected_univ
  have hp : plus z = plus 0 :=
    (hcplus z (mem_univ z)).trans (hcplus 0 (mem_univ 0)).symm
  have hm : minus z = minus 0 :=
    (hcminus z (mem_univ z)).trans (hcminus 0 (mem_univ 0)).symm
  dsimp [plus] at hp
  dsimp [minus] at hm
  linear_combination (hp + hm) / 2

/-- Exact dichotomy for an entire coefficient family: its pointwise conjugate is holomorphic in
the same variable exactly when the coefficient family is constant. -/
theorem differentiable_pointwiseStar_iff_constant
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => star (f z)) ↔ ∀ z, f z = f 0 := by
  constructor
  · intro hstar z
    exact eq_of_differentiable_pointwiseStar hf hstar z
  · intro hconst
    have heq : (fun z => star (f z)) = fun _ => star (f 0) := by
      funext z
      rw [hconst z]
    rw [heq]
    exact differentiable_const _

end

end GaloisForLFunctions.HTGeometry
