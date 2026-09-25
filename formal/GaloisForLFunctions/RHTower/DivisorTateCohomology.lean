import GaloisForLFunctions.RHTower.DivisorGaloisNorm
import GaloisForLFunctions.RHTower.DivisorSliceFreePart

/-!
# Where the free orbits live: the coboundary, not the cohomology

The hypothesis is the vanishing of the free-orbit count of the reflection involution on the divisor.
The natural home for an invariant of a ℤ/2-action is its Tate cohomology, and this lane has
repeatedly found that cohomological and localised methods are blind to the free part. This module
computes the obstruction exactly and says where it actually sits.

Over `𝔽₂` the norm of the involution is `N f = f + f∘σ`, and `N ∘ N = 0`. The computation here is
that the coboundary is **surjective onto the functions that vanish on the critical line**, with an
explicit and canonical preimage: the left half of the strip is a section of the involution, since `σ`
exchanges the two halves and fixes the line, so

  `N (f · 1_{Re < 1/2}) = f`

for every invariant `f` vanishing on the fixed locus. No choice is used — the section is the geometry
of the strip. Consequently the Tate cohomology of the divisor is the functions on the critical line
alone: **the free orbits are exactly what the cohomology discards.**

The sharp form is a single cochain. The coboundary of the left-half indicator is the characteristic
function of the off-line part:

  `N (1_{Re < 1/2}) = 1_{Re ≠ 1/2}`,

so the hypothesis is precisely the vanishing of the coboundary of one explicit cochain. That is the
answer to whether the ambient symmetric class can be made to force the result cohomologically: it
cannot, and not for want of a better group. The hypothesis is not a cohomology class at all — it is
the statement that a coboundary vanishes, and passing to cohomology is exactly the operation that
throws it away. Any producer built from an equivariant invariant, a localisation, or a completion
computes cohomology and will be blind by construction; what must be controlled is the boundary map
itself.
-/

namespace RHTower

noncomputable section

/-- The canonical section of the reflection action: restrict a cochain to the left half of the
strip. The involution exchanges the halves and fixes the critical line, so this picks exactly one
point of each free orbit, with no choice. -/
def leftSection (f : XiDivisorSupport → ZMod 2) : XiDivisorSupport → ZMod 2 :=
  fun ρ => if (ρ : ℂ).re < 1 / 2 then f ρ else 0

theorem supportPartner_re_lt_iff (ρ : XiDivisorSupport) :
    ((supportPartner ρ : XiDivisorSupport) : ℂ).re < 1 / 2 ↔ 1 / 2 < (ρ : ℂ).re := by
  rw [supportPartner_re]
  constructor <;> intro h <;> linarith

/-- The coboundary vanishes on the critical line. -/
theorem divisorNorm_eq_zero_of_fixed (g : XiDivisorSupport → ZMod 2) {ρ : XiDivisorSupport}
    (h : (ρ : ℂ).re = 1 / 2) : divisorNorm g ρ = 0 := by
  rw [divisorNorm, (supportPartner_eq_self_iff ρ).mpr h]
  exact CharTwo.add_self_eq_zero _

/-- A cochain killed by the norm is invariant. -/
theorem eq_of_divisorNorm_eq_zero {f : XiDivisorSupport → ZMod 2} (h : divisorNorm f = 0)
    (ρ : XiDivisorSupport) : f (supportPartner ρ) = f ρ := by
  have hρ : f ρ + f (supportPartner ρ) = 0 := congrFun h ρ
  have h2 : f (supportPartner ρ) = -f ρ := by linear_combination hρ
  rw [h2, CharTwo.neg_eq]

/-- **The coboundary is surjective onto the cochains vanishing on the critical line**, with the
left half of the strip as an explicit preimage. -/
theorem divisorNorm_leftSection {f : XiDivisorSupport → ZMod 2}
    (hinv : ∀ ρ : XiDivisorSupport, f (supportPartner ρ) = f ρ)
    (hfix : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2 → f ρ = 0) :
    divisorNorm (leftSection f) = f := by
  funext ρ
  rw [divisorNorm, leftSection, leftSection]
  rcases lt_trichotomy ((ρ : ℂ).re) (1 / 2) with hlt | heq | hgt
  · rw [if_pos hlt, if_neg (by rw [supportPartner_re]; intro hc; linarith)]
    exact add_zero _
  · rw [if_neg (by rw [heq]; exact lt_irrefl _),
      if_neg (by rw [supportPartner_re, heq]; intro hc; linarith), hfix ρ heq]
    exact add_zero _
  · rw [if_neg (not_lt.mpr (le_of_lt hgt)),
      if_pos ((supportPartner_re_lt_iff ρ).mpr hgt), hinv ρ]
    exact zero_add _

/-- **The single cochain.** The coboundary of the left-half indicator is the characteristic function
of the off-line part of the divisor. -/
theorem divisorNorm_leftSection_one (ρ : XiDivisorSupport) :
    divisorNorm (leftSection (fun _ => 1)) ρ = if (ρ : ℂ).re = 1 / 2 then 0 else 1 := by
  rw [divisorNorm, leftSection, leftSection]
  rcases lt_trichotomy ((ρ : ℂ).re) (1 / 2) with hlt | heq | hgt
  · rw [if_pos hlt, if_neg (by rw [supportPartner_re]; intro hc; linarith),
      if_neg (by intro hc; linarith)]
    exact add_zero _
  · rw [if_neg (by rw [heq]; exact lt_irrefl _),
      if_neg (by rw [supportPartner_re, heq]; intro hc; linarith), if_pos heq]
    exact add_zero _
  · rw [if_neg (not_lt.mpr (le_of_lt hgt)),
      if_pos ((supportPartner_re_lt_iff ρ).mpr hgt), if_neg (by intro hc; linarith)]
    exact zero_add _

/-- **The hypothesis is the vanishing of one explicit coboundary.** -/
theorem riemannHypothesis_iff_divisorNorm_leftSection_one_eq_zero :
    RiemannHypothesis ↔ divisorNorm (leftSection (fun _ => 1)) = 0 := by
  constructor
  · intro h
    funext ρ
    have hhalf : (ρ : ℂ).re = 1 / 2 :=
      (supportPartner_eq_self_iff ρ).mp (riemannHypothesis_iff_supportPartner_eq_id.mp h ρ)
    rw [divisorNorm_leftSection_one, if_pos hhalf]
    rfl
  · intro h
    refine riemannHypothesis_iff_supportPartner_eq_id.mpr fun ρ => ?_
    refine (supportPartner_eq_self_iff ρ).mpr ?_
    by_contra hc
    have hval := congrFun h ρ
    rw [divisorNorm_leftSection_one, if_neg hc] at hval
    simp only [Pi.zero_apply] at hval
    exact one_ne_zero hval

end

end RHTower
