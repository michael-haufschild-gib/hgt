# Polygamma multiplication value law

- **ID:** `polygamma-multiplication-value-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Gauss multiplication for Gamma differentiates into an exact finite-orbit law for
  digamma and every positive polygamma order.

## Exact relations

For `n > 0` and `s` outside the nonpositive-integer pole lattice,

```text
sum_{0 <= k < n} psi((s+k)/n)
  = n psi(s) - n log n.                                      (1)
```

For every `r >= 0`,

```text
sum_{0 <= k < n} psi^(r+1)((s+k)/n)
  = n^(r+2) psi^(r+1)(s).                                   (2)
```

Equivalently, in the standard orbit coordinates,

```text
sum_{0 <= k < n} psi(z+k/n)
  = n psi(nz) - n log n,                                    (3)

sum_{0 <= k < n} psi^(r+1)(z+k/n)
  = n^(r+2) psi^(r+1)(nz).                                  (4)
```

The case `r=0` of `(2)` and `(4)` is trigamma multiplication.

## Proof

The existing reciprocal-Gamma multiplication theorem is an equality of globally defined complex
functions.  Its logarithmic derivative is taken at a regular point.  The logarithmic derivative of
the finite product is the sum of the factor logarithmic derivatives; the affine maps contribute
`1/n`, while the factor `n^s` contributes `log n`.  Cancelling the common scale gives `(1)`.

Continuity of Gamma makes the regular locus a neighbourhood of every admissible point, so `(1)` is
an eventual equality there.  Differentiating gives trigamma multiplication.  Repeating this local
argument proves `(2)` by induction.  At every step the proof derives differentiability of the
current iterated digamma derivative from the exact off-pole `ContDiffAt` theorem, so no global
smoothness claim is made across the pole lattice.  Rescaling `s=nz` gives `(3)` and `(4)`.

## Parent classification

`[SEARCH]` Formula `(2)` is the classical polygamma multiplication theorem, NIST DLMF 5.15.7:

- https://dlmf.nist.gov/5.15.E7

The underlying Gamma multiplication theorem was already formalized locally in
`GammaMultiplication.lean`.  The differentiated finite-orbit laws were absent from the local tree
and the pinned mathlib checkout.  Their formalization is nontrivial infrastructure, but the
relations are not new scientific knowledge.

## Lean certificate

File: `formal/GaloisForLFunctions/PolygammaMultiplication.lean`.

- `digamma_multiplication`: scaled digamma law `(1)`;
- `trigamma_multiplication`: first positive-order case of `(2)`;
- `polygamma_multiplication`: complete positive-order family `(2)`;
- `digamma_multiplication_rescaled`: standard argument form `(3)`;
- `trigamma_multiplication_rescaled`: standard trigamma form;
- `polygamma_multiplication_rescaled`: complete standard family `(4)`.

The module is imported by `GaloisForLFunctions`.

## RHTower and parent integration audit

The exact argument patterns of `(1)`--`(4)` were checked against all digamma, trigamma,
iterated-digamma, and Gamma-multiplication consumers in `formal/GaloisForLFunctions/RHTower` and
its parent tree.

1. `ArchimedeanGamma.lean` uses the unit recurrence
   `psi(s/2+1)=psi(s/2)+2/s`.  This is a translation pair, not a complete multiplication orbit;
   the existing recurrence is the exact native relation.
2. `ReflectionCocycleArchimedean.lean` contains the pair `psi(s/2)` and `psi((1-s)/2)`.  Their
   separation varies with `s`, whereas a two-point Gauss orbit has fixed separation `1/2`.
   Consequently multiplication does not replace its reflected cocycle or strict-curvature input.
3. The same file compares `psi'(3/8)` and `psi'(1/8)`.  These points differ by `1/4`, not the
   `1/2` required by duplication, and only a difference and its strict sign are needed.  The
   multiplication sum would not supply that order information.
4. `DigammaBounds.lean`, `DigammaAsymptotic.lean`, `TrigammaVertical.lean`, and their winding and
   envelope consumers use integer translations or one-sided vertical estimates rather than full
   residue-class orbits.  Replacing those native estimates would lose the information they consume.
5. `GammaMultiplication.lean` is the genuine upstream consumer boundary: its exact product now has
   a formally certified logarithmic-derivative tower.  Paper cards using Gamma multiplication may
   invoke these value laws directly when derivatives of the orbit product arise.

The positive integration conclusion is therefore exact: the parent multiplication theorem now
supports its complete digamma/polygamma value tower.  No current RHTower hypothesis has the finite
orbit shape required for direct discharge, so no unrelated consumer was rewritten.

## Gates

- [x] exact parent relation identified in the literature
- [x] local and mathlib declaration search confirms the differentiated relations were absent
- [x] digamma and trigamma multiplication formalized
- [x] all positive polygamma orders formalized
- [x] scaled and standard argument forms formalized
- [x] RHTower and parent consumer audit completed
- [x] targeted source verification passes
- [x] generated indexes, axiom audit, and formal lint gate pass

All six public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
