# Geometric Källén--Lehmann self-similarity and infinite spectral width

- **ID:** `geometric-kallen-lehmann-self-similar-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/GeometricKallenLehmannResponse.lean`
- **Parent paper theorem:**
  `../../2-fully-proven/not_new_scientific_knowledge/q-geometric-generalized-free-field-hypertranscendence.md`
- **Statement:** A positive geometric atomic mass-squared spectrum has the exact moment law
  `(1-a)/(1-a b^n)`, satisfies a static source-rescaling constraint, has every finite moment Hankel
  determinant strictly positive, and escapes every fixed finite spectral-width model.

## Exact theorem

Fix real parameters

```text
0 < a < 1,   0 < b < 1.
```

Define

```text
w_k = (1-a)a^k,
x_k = b^k,
m_n = (1-a)/(1-a b^n).                                    (1)
```

Lean proves the atomic realization

```text
m_n = sum_(k>=0) w_k x_k^n.                                (2)
```

Every `w_k` is positive, the nodes `x_k` are distinct, and every absolute moment is summable.
Therefore the complete positive moment theorem gives

```text
det [m_(i+j)]_(0<=i,j<N) > 0                               (3)
```

for every finite size `N`.

If `R(X)=sum_n m_n X^n` is the formal mass-resolvent response, its coefficients satisfy

```text
(1-a b^n)m_n = 1-a,                                       (4)
```

and hence Lean proves the power-series identity

```text
R(X) = (1-a)/(1-X) + a R(bX).                              (5)
```

Equation `(5)` is a fixed self-similarity constraint on one positive spectrum.  It is not a time
propagation law.

Finally, `(3)` rules out

```text
FixedSpectralWidthLocalClosure d m
```

for every `d`: even local approximation of arbitrarily long finite moment blocks cannot use one
uniform finite spectral-width bound.

## Physical meaning and exact limit

The sequence `(1)` is the Källén--Lehmann moment sequence of the probability measure

```text
(1-a) sum_(k>=0) a^k delta_(b^k).
```

It gives a positive, compact mass-squared reservoir with exact discrete self-similarity.  The
strict Hankel tower certifies irreducible infinite spectral width.  It does not certify interaction:
the associated generalized free field is Gaussian.

The companion paper card uses the published rational-or-hypertranscendental theorem for linear
`q`-difference equations to prove that the analytic response is HT.  That conclusion is not hidden
inside this Lean module.  Formalizing it requires the full external difference-Galois theorem and
ramified-rational descent.

## Lean surface

- `geometricKallenLehmannWeight`
- `geometricKallenLehmannNode`
- `geometricKallenLehmannMoment`
- `geometricKallenLehmannMoment_eq_tsum`
- `geometricKallenLehmannMoment_constraint`
- `geometricKallenLehmann_infiniteSupport`
- `det_momentHankelMatrix_geometricKallenLehmannMoment_pos`
- `geometricKallenLehmannMoment_not_fixedSpectralWidthLocalClosure`
- `geometricKallenLehmannResponse`
- `geometricKallenLehmannResponse_selfSimilarity`

## Anti-theatre verdict

All ingredients formalized here are parent mathematics: geometric series, positive atomic moment
representations, strict Hankel positivity, and a first-order scale constraint.  The module is
valuable because it gives the general HT/QFT program one literal positive spectral negative
control.  It is not advertised as new scientific knowledge.

## Verification

- [x] exact module cache build passed in one foreground process
- [x] direct touched-file Lean check passed
- [x] no numerical computation used
- [x] axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [x] module imported by the HTGeometry umbrella
- [ ] full tree lint is green after concurrent agents finish registering their new modules

The formal lint currently reports many independently created HTGeometry and RHTower modules as
unreachable from their umbrellas.  The present module was added to the HTGeometry umbrella; the
remaining lint failures are outside this card's files and belong to concurrent work.

## Next target

Formalize the finite Wick-reduced relative transcendence profile from the parent program card.
The first theorem must be derivation-preserving embedding invariance; a QFT interpretation is not
promoted before that algebraic invariance is proved.
