import GaloisForLFunctions.RHTower.DivisorGaloisNorm
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# The slices are finite `ℤ/2`-sets

The Hermitian reflection preserves the ordinate, so the `ℤ/2`-action whose triviality is the
hypothesis is fibred over the height.  This module supplies the finiteness that the genus-theoretic
programme needs: each **slice**

  `xiSlice t = {ρ : XiDivisorSupport | (ρ : ℂ).im = t}`

is a **finite** set, stable under the reflection.  So the hypothesis is a statement about a family
of genuinely finite `ℤ/2`-sets, one per height — the category in which Chevalley's ambiguous class
number formula lives — rather than about an infinite divisor group.

The sharp form proved here is

  `RiemannHypothesis ↔ ∀ t, (xiSlice t).Subsingleton`,

each slice being finite, so this is a statement about a finite cardinality at each height.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The horizontal slice of the divisor support at height `t`. -/
def xiSlice (t : ℝ) : Set XiDivisorSupport := {ρ | (ρ : ℂ).im = t}

/-- **Each slice is finite.**  Gate G2 of the genus programme. -/
theorem xiSlice_finite (t : ℝ) : (xiSlice t).Finite := by
  refine (finite_xiDivisorSupport_band t (le_refl (0 : ℝ))).subset ?_
  intro ρ hρ
  have hρ' : (ρ : ℂ).im = t := hρ
  simp only [Set.mem_setOf_eq, hρ', sub_self, abs_zero, le_refl]

/-- The reflection preserves the ordinate. -/
theorem supportPartner_im (ρ : XiDivisorSupport) :
    ((supportPartner ρ : XiDivisorSupport) : ℂ).im = (ρ : ℂ).im := by
  rw [supportPartner_coe]
  simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
  ring

/-- Each slice is stable under the reflection: the `ℤ/2`-action is fibred over the height. -/
theorem supportPartner_mem_xiSlice {t : ℝ} {ρ : XiDivisorSupport} (h : ρ ∈ xiSlice t) :
    supportPartner ρ ∈ xiSlice t := by
  have h' : (ρ : ℂ).im = t := h
  show ((supportPartner ρ : XiDivisorSupport) : ℂ).im = t
  rw [supportPartner_im]; exact h'

theorem self_mem_xiSlice (ρ : XiDivisorSupport) : ρ ∈ xiSlice ((ρ : ℂ).im) := rfl

/-- **The hypothesis is the subsingleton-ness of every slice**, and every slice is finite. -/
theorem riemannHypothesis_iff_forall_xiSlice_subsingleton :
    RiemannHypothesis ↔ ∀ t : ℝ, (xiSlice t).Subsingleton := by
  rw [riemannHypothesis_iff_supportPartner_eq_id]
  constructor
  · intro h t ρ hρ ρ' hρ'
    have hρi : (ρ : ℂ).im = t := hρ
    have hρi' : (ρ' : ℂ).im = t := hρ'
    apply Subtype.ext
    apply Complex.ext
    · rw [(supportPartner_eq_self_iff ρ).mp (h ρ), (supportPartner_eq_self_iff ρ').mp (h ρ')]
    · rw [hρi, hρi']
  · intro h ρ
    exact h ((ρ : ℂ).im) (supportPartner_mem_xiSlice (self_mem_xiSlice ρ)) (self_mem_xiSlice ρ)

/-- Failure of the hypothesis is a slice with at least two points: an exact ordinate collision
inside one finite `ℤ/2`-set. -/
theorem exists_xiSlice_not_subsingleton_of_not_riemannHypothesis (h : ¬ RiemannHypothesis) :
    ∃ t : ℝ, ¬ (xiSlice t).Subsingleton := by
  by_contra hc
  push Not at hc
  exact h (riemannHypothesis_iff_forall_xiSlice_subsingleton.mpr hc)

end

end RHTower
