/-
# `λ` descends to a local homeomorphism `λ̄ : ℍ/PΓ(2) → ℂ∖{0,1}`

With `ℍ → ℍ/PΓ(2)` now a covering map (`Gamma2QuotientCovering.isCoveringMap_quotientMk_pgamma2`), the
modular `λ` — being `Γ(2)`-invariant (`ModularLambdaUnconditional.modularLambda_smul`) — descends through
the quotient to

  `λ̄ : ℍ/PΓ(2) → ℂ∖{0,1}`,   `λ = λ̄ ∘ q`.

This file constructs `λ̄` and proves it is a **local homeomorphism**. The key move is `of_comp_right`: a
factorisation `g ∘ f` that is a local homeo, with `f = q` itself a (surjective) local homeo, forces the
outer map `g = λ̄` to be a local homeo too — no analytic input beyond what `λ` already supplies
(`isLocalHomeomorph_lambdaPunct`, from `λ' ≠ 0`).

What remains to make `λ : ℍ → ℂ∖{0,1}` a covering map is a *single* further fact, isolated cleanly here:

  **`λ̄` is a proper map.**

Granting it, `λ̄` is a proper local homeomorphism, hence a covering
(`ProperLocalHomeoCovering.isCoveringMap_of_isProperMap_of_isLocalHomeomorph`), and then
`λ = λ̄ ∘ q` is a composition of covering maps (`IsCoveringMap.comp`) — exactly the input the three-value
Montel lift (`#30`) consumes. Properness is the cusp-escape statement: it follows from the three cusp
limits `λ → {0,1,∞}` already proven, the engine being `ModularLambdaCovering.isClosed_range_lambdaPunct`
(truncated-fundamental-domain compactness + `anharm_cusp_ne`). Note we never need `λ̄` *injective* (degree 1):
a covering of any degree suffices, which sidesteps the argument-principle crux entirely.
-/
import Mathlib.Tactic
import GaloisForLFunctions.Bottcher.Gamma2QuotientCovering
import GaloisForLFunctions.Bottcher.ModularLambdaCovering
import GaloisForLFunctions.Bottcher.ModularLambdaUnconditional
import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering

open UpperHalfPlane CongruenceSubgroup MulAction
open scoped MatrixGroups

namespace Bottcher

/-- `λ` is `Γ(2)`-invariant on `ℍ`: `λ(γ • z) = λ(z)` for `γ ∈ Γ(2)`. -/
theorem lambdaPunct_invariant (γ : Gamma 2) (z : ℍ) : lambdaPunct (γ • z) = lambdaPunct z :=
  Subtype.ext (modularLambda_smul γ.2 z)

/-- **The descended modular lambda** `λ̄ : ℍ/PΓ(2) → ℂ∖{0,1}`. Well-defined because `λ` is constant on
`PΓ(2)`-orbits (a `PΓ(2)`-orbit is a `Γ(2)`-orbit, on which `λ` is invariant). -/
noncomputable def lambdaBar : Quotient (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ) → Punctured :=
  Quotient.lift lambdaPunct (by
    intro a b hab
    have hmem : a ∈ MulAction.orbit (Gamma 2 ⧸ projKer) b := hab
    obtain ⟨g, hg⟩ := hmem
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← hg]
    show lambdaPunct ((↑γ : Gamma 2 ⧸ projKer) • b) = lambdaPunct b
    rw [mk_smul, lambdaPunct_invariant])

/-- `λ = λ̄ ∘ q` — the defining factorisation through the quotient map `q = Quotient.mk`. -/
theorem lambdaBar_comp_mk :
    lambdaBar ∘ (Quotient.mk (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ)) = lambdaPunct := rfl

/-- `λ̄` is continuous (universal property of the quotient applied to the continuous `λ`). -/
theorem continuous_lambdaBar : Continuous lambdaBar :=
  continuous_lambdaPunct.quotient_lift _

/-- **`λ̄` is a local homeomorphism.** Since `λ = λ̄ ∘ q` is a local homeo and the quotient map `q` is a
surjective local homeo (it is a covering), `of_comp_right` forces `λ̄` to be a local homeo. -/
theorem isLocalHomeomorph_lambdaBar : IsLocalHomeomorph lambdaBar := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  have hq : IsLocalHomeomorph (Quotient.mk (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ)) :=
    isCoveringMap_quotientMk_pgamma2.isLocalHomeomorph
  have h1 : IsLocalHomeomorphOn
      (lambdaBar ∘ (Quotient.mk (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ))) Set.univ := by
    rw [lambdaBar_comp_mk]; exact isLocalHomeomorph_lambdaPunct.isLocalHomeomorphOn
  have h3 := h1.of_comp_right hq.isLocalHomeomorphOn
  rwa [Set.image_univ, Quotient.mk_surjective.range_eq] at h3

/-- **`λ̄` is a covering map, granted properness.** A proper local homeomorphism with Hausdorff source is
a covering (`isCoveringMap_of_isProperMap_of_isLocalHomeomorph`); `ℍ/PΓ(2)` is Hausdorff (free properly
discontinuous action). This is the exact reduction of the modular-curve covering to the cusp-escape
properness statement — no degree-1 / injectivity input required. -/
theorem isCoveringMap_lambdaBar (hproper : IsProperMap lambdaBar) : IsCoveringMap lambdaBar :=
  isCoveringMap_of_isProperMap_of_isLocalHomeomorph isLocalHomeomorph_lambdaBar hproper

end Bottcher
