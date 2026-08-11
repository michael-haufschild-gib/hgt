# Functional-equation packet lift

Constructed universal split-formation action in `docs/drafts/pipeline/2-fully-proven/universal-law-field/packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md` and Lean module `formal/GaloisForLFunctions/HTGeometry/ConstitutiveFunctionalEquationPacketLift.lean`.

Core law: `E_K(μ)=μ ⊗ₘ K`; first projection recovers μ; common Markov kernel preserves extended KL exactly. Observer action A lifts stochastically by applying A to recovered observer and regenerating latent history from K. Lift is natural, composes strictly on formed laws, involutive there for involutive A, and preserves KL/Jeffreys for measurable embeddings.

Key correction: information-neutral means isometry, not zero reflected separation. For even theta exponential family ν_a, reflection gives ν_-a, directed KL chirality vanishes for all a, while Jeffreys work is `4 a F'(a)>0` off center. Missing RH selector must annihilate conserved symmetric work.

Raw Hasse/Fermi base is not even in log scale. Canonical Hellinger midpoint plus modular half-cocycle creates two sheets; reflection sends `(a,+)` to `(-a,-)`, not same-sheet `(-a,+)`. Lean certifies generic sheet-swap algebra.

Audits passed: direct Lean, module build, umbrella check, formal lint, axioms only `propext`, `Classical.choice`, `Quot.sound`.