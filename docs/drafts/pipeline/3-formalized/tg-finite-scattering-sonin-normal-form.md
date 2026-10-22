# TG C9.11f — joint finite scattering on the physical Sonin carrier

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG, actual joint prime–Gamma construction.

## Source and target

Use the existing `fieldOneFiniteStageSphericalScatteringUnitary S`: the literal
Gamma phase times every finite Euler ratio at places in S. Remove the Gamma factor
by its actual unitary inverse and transport the remaining Euler unitary by the
existing Mellin unitary; call the result V_S. This construction uses full operators,
not a scalar completion remainder.

The transported logarithmic projection differential of the full product
has exact normal form `D_S=V_S* R₁ V_S+A₁-1`. This retains all mixed prime–Gamma terms.
On Q_b for b≥1, its negative compression is exactly the Gram of
`(1-R₁)V_S Q_b`. Across a lost Sonin layer E, the entire transition is
`E V_S* R₁ V_S Q_b`, a Gram cross term of actual finite Euler-ratio channels.

## Dependency-closed paper proof [PROVED HERE]

Write full scattering U=UΓ V. C9.11e gives
`M⁻¹ UΓ* P UΓ M=R₁` and `M⁻¹ P M=1-A₁`.
Conjugating P by U immediately gives the claimed normal form. On Q_b, A₁ vanishes;
unitarity of V and idempotence of R₁ give the complement Gram factorization.
No passage to the infinite prime product or assertion of compactness is implicit.

## Hard gap this addresses

Replace the failed bare additive repair by an exact source-derived nonlinear
joint comparison. Cofinal operator-ideal control and its cubic Hardy index remain
the next analytic problems; generic Gram positivity alone supplies no sub-unit bound.

## Log

- 2026-10-02: corpus deep search partial; exact lexical search located the finite
  spherical unitary and its AE literal product theorem. Sources inspected directly.
- 2026-10-02: `CCMFiniteScatteringSoninNormalForm.lean` passes final foreground
  `lake --old env lean GaloisForLFunctions/RHTower/CCM/CCMFiniteScatteringSoninNormalForm.lean
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCM/CCMFiniteScatteringSoninNormalForm.olean`.
  Four definitions and six public theorems: actual finite Euler spectral/physical
  unitaries, AE literal product provenance, full mixed logarithmic differential,
  exact normal form, complementary residual Gram, its positive sign, and the exact
  lost-channel cross term. Default heartbeats; expensive adjoint rewriting replaced
  by explicit composition congruences. Wired into RHTower; no umbrella build.
  Separate `/tmp` axiom audit passes for all ten public declarations, with exactly
  `propext`, `Classical.choice`, `Quot.sound`. Final lint reports thirteen unrelated
  unwired modules, none in this leaf. Corpus index refreshed after source changes.

## Precise limit of the result

The sign is the negative compression of this particular full scattering
differential. It is not an RH Weil-positivity theorem and supplies no strict
sub-unit bound. No compactness of the untested projection difference, no infinite
Euler-product limit and no cubic-index invariance is asserted.

Next: [Euler denominator current](../1-in-progress/tg-scattering-euler-denominator-current.md).
The literal prime ratio should give `V_p A_p=A_p*`, hence the inverse-free four-leg
identity `A_p* (V_p* R₁ V_p-R₁) A_p=A_p R₁ A_p*-A_p* R₁ A_p`.
