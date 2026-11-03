# The source Hecke correspondence across window stages

- **ID:** f2-hecke-window-mellin-correspondence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** F2; `MayerScattering/HeckeWindowMellinBridge.lean`.
- **Statement:** The actual period Hecke operator realizes an expanded-stage adjoint shift, scales complete Weil energy by two, and transports reflection with its necessary conjugation and twist.

## Correspondence

Let `L=log2`, `F₂H(u)=√2 H(u+L)`, `V₂H(u)=√2 H(u)`. Write `E_s` for the actual completed Eisenstein Lewis period and

`Φ_H(s,a)=tr(H)(2s)E_s(a)/E_s(1)`,
`tr(H)(z)=∫H(u)exp((z−1/2)u)du`.

For `0<Re s<1/2`, `E_s(1)=2ζ(2s−1)≠0`, so

`Φ_H(s,1)=tr(H)(2s)`,
`(T₂,s−Id)Φ_H(s,a)=Φ_(F₂H)(s,a)` for every `a>0`.

Both `F₂` and `V₂` carry smooth stage-`A` tests into stage `A+L`. On functions supported in `[−A,0]`,

`F₂H=√2·adjointShift(A+L,L)H`.

The actual expanded-stage cutoff loses nothing. Complete Weil energy satisfies

`Q(F₂H)=Q(V₂H)=2Q(H)`.

## Reflection

The stage reflections exchange the two embeddings:

`σ_(A+L)F₂=V₂σ_A`, `σ_(A+L)V₂=F₂σ_A`.

On real Mellin data, writing `s♯=1/2−conjugate(s)`,

`Φ_(σ_AH)(s,1)=exp(−A(2s−1/2)) Φ_H(1/2−s,1)`
`=exp(−A(2s−1/2)) conjugate(Φ_H(s♯,1))`.

Thus window reflection is the conjugate-linear, exponentially twisted PM parameter reflection. It is not fixed-parameter modular inversion or the bare linear PM coefficient reflection.

## Complete form

For every real compactly supported C² test,

`Q(H)=Re Σ_(ρ a nontrivial ζ-zero) m_ρ Φ_H(ρ/2,1)`
`                                   ·conjugate(Φ_H((1−conjugateρ)/2,1))`.

This is the existing complete explicit formula with its coefficients recovered from actual normalized periods. Prime, archimedean and polar terms remain intact; multiplicity is retained.

## Proof

Translation of the existing Mellin transform gives multiplier
`√2 exp(−(2s−1/2)log2)=2·2^(−2s)`. Combine this with the [source-derived global period eigenvalue](f2-global-lewis-hecke-eigenvalue.md). Support inequalities identify the expanded-stage WTZ adjoint shift. Translation invariance and real quadratic homogeneity give the complete Weil similitude.

Both stage-reflection identities are exact substitutions. Changing variables in the Mellin integral gives the parameter reflection and exponential factor; conjugating the integral of a real test gives the upper-half-plane PM parameter reflection. Evaluation at `1` cancels the nonzero normalization, and substitution into the bilinear explicit formula proves the complete-form identity.

## Lean audit

- `heckeWindowPull_mem`, `heckeWindowPush_mem`, `heckeWindowPull_eq_adjointShift`
- `lewisHeckeT2_windowMellinPeriod`
- `weilQuad_heckeWindowPull`, `weilQuad_heckeWindowPush`
- `windowInvolution_heckeWindowPull`, `windowInvolution_heckeWindowPush`
- `windowMellinPeriod_reflection_one`, `windowMellinPeriod_krein_reflection_one`
- `weilQuad_eq_windowMellinPeriod`

Final check: `lake --old env lean GaloisForLFunctions/RenormalizedIntersectionTheory/MayerScattering/HeckeWindowMellinBridge.lean`.
Audited endpoints use only `propext`, `Classical.choice`, `Quot.sound`. Imported by `RenormalizedIntersectionTheory.lean`.

## Remaining sign

This is a signed-form correspondence, not a positivity theorem. The finite-energy PM core has a separate boundary correction. Identifying its coefficient pairing and proving the missing arithmetic sign remain open.
