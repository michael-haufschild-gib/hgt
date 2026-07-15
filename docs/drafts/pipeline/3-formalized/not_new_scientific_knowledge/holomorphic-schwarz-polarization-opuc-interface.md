# Holomorphic Schwarz polarization is the analytic OPUC family interface

- **ID:** `holomorphic-schwarz-polarization-opuc-interface`
- **Stage:** 3-formalized
- **Type:** POSITIVE NO-GO / ANALYTIC INTERFACE
- **Scientific status:** `[FORMALIZED] [CLASSICAL] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/HolomorphicSchwarzPolarization.lean`
- **Parents:** `xi-cayley-paraorthogonal-opuc-rh.md`,
  `xi-opuc-paraorthogonal-logarithmic-phase-gate.md`
- **Statement:** A nonconstant entire coefficient family cannot have its pointwise coefficient
  conjugate holomorphic in the same complex parameter.  The source-compatible positive replacement
  is the two-variable Schwarz polarization `fSharp(w)=conj(f(conj(w)))`, which is holomorphic in
  `w` and recovers `conj(f(z))` on the Schwarz diagonal `w=conj(z)`.

## The obstruction

Let `f : C -> C` be entire.  If the pointwise conjugate

```text
z |-> conj(f(z))
```

is also entire, then `f` is constant.  Indeed, both

```text
f + conj(f) = 2 Re(f),
f - conj(f) = 2 i Im(f)
```

would be holomorphic with image in a real line.  The open mapping theorem makes both constant, and
therefore makes `f` constant.

Applied coefficientwise, this excludes a nonconstant one-variable holomorphic OPUC family in
which the reversed polynomial is formed by pointwise conjugating the coefficients at the same
spectral parameter.  Ordinary paraorthogonal reversal remains correct for each fixed parameter;
the obstruction concerns holomorphic variation of the resulting family.

## Positive replacement

Define the independent-variable Schwarz partner

```text
fSharp(w)=conj(f(conj(w))).
```

Then `fSharp` is entire whenever `f` is, and

```text
fSharp(conj(z))=conj(f(z)).
```

Thus a source-faithful analytic terminal must be polarized before restricting to the Schwarz
diagonal.  Coefficientwise, the admissible shape is

```text
T(z,w;X)=X p_z(X)-tau q_w(X),
q_(conj z)(X)=the conjugate reversal of p_z(X),
```

not a one-variable family that silently treats coefficient conjugation as holomorphic.

The paired-Cauchy and translated-Bezoutian cards already provide natural bivariate Xi source
objects.  The remaining arithmetic obligation is an exact source terminal identity or zero
implication for this polarized family; polarization itself supplies no positivity and assumes no
zero location.

## Formal theorem surface

The Lean module proves:

- `schwarzPolarizedPartner_star`;
- `differentiable_schwarzPolarizedPartner`;
- `eq_of_differentiable_pointwiseStar`;
- `differentiable_pointwiseStar_iff_constant`.

The implementation is axiom-clean apart from Lean/mathlib's standard classical quotient axioms.

## Gates

- [x] one-variable analytic obstruction proved
- [x] positive two-variable successor stated and formalized
- [x] no RH-equivalent positivity or divisor-selected object used
- [ ] build a source-defined polarized polynomial/colligation family
- [ ] derive its terminal Xi value identity
- [ ] combine the diagonal terminal with paraorthogonal root exclusion
