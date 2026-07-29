# Positive-cone colour-Gram weak–Lorentz lock no-go (2026-07-29)

## Exact result

New Lean module: `formal/GaloisForLFunctions/HTGeometry/ColorGramWeakLorentzLock.lean`.
Stage-3 card: `docs/drafts/pipeline/3-formalized/color-gram-weak-lorentz-lock-no-go.md`.

Let `U=diag(i,-i)`, so `UᴴU=I` and `det U=1`. Let the one-row event be
`X=[[1,1],[0,0],[0,0]]`. Then
`G_X=XᴴX=[[1,1],[1,1]]`, the future-null vector `(1,1,0,0)`. Right action gives
`G_{XUᴴ}=U G_X Uᴴ=[[1,-1],[-1,1]]`, the distinct future-null vector `(1,-1,0,0)`.

Lean proves both events are null, the entire right orbit of every one-row event is null, the Gram matrices differ, and `U` is not in the pointwise kernel of the event-to-Gram map. Focused source check/build pass; axiom audit only `propext`, `Classical.choice`, `Quot.sound`.

This strengthens `mem:research/color-blind-event-gram-spacetime-law` and the older same-H2 Pauli witness: nontriviality occurs inside the actual PSD Gram future cone, not only on an indefinite Hermitian direction.

## Physical boundary

One `M_{3,2}(ℂ)` carrier cannot treat its right SU2 simultaneously as internal weak isospin and as the spatial-frame action of derived spacetime. Quotienting full right U2 collapses the four-carrier to two singular values.

Strongest positive survivor: viable theory needs source-selected second Lorentz spinor action or a noninvertible event interface with weak transport on kernel and Lorentz transport on cokernel. It cannot insert an unrelated product group/tetrad.

Underlying SU2/H2 action is standard; no scientific novelty claimed. Current physical open core remains EXCEPTIONAL GRAM DESCENT.