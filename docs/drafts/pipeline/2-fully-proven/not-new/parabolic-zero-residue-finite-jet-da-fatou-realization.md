# Zero-residue parabolic finite jets are realized by algebraic germs with rational Fatou coordinate

- **ID:** parabolic-zero-residue-finite-jet-da-fatou-realization
- **Stage:** 2-fully-proven
- **Type:** THEOREM / FINITE-JET NONIDENTIFIABILITY FOR PARABOLIC FATOU HT
- **Source:** Haiku, extending `parabolic-da-fatou-nonrational-exception`
- **Priority:** HIGH as a gatekeeper for parabolic Fatou-coordinate HT claims

## Statement

Fix `N >= 4` and a formal finite jet

```text
h(z)=z+z^2+z^3+a_4 z^4+...+a_N z^N+O(z^(N+1)).
```

Then there is a polynomial `P(z)` of degree at most `N-3` such that, for

```text
Phi_P(z) = -1/z + P(z),
```

the local branch `f_P` defined by

```text
Phi_P(f_P(z)) = Phi_P(z)+1,    f_P(z)->0 as z->0,
```

is an algebraic analytic parabolic germ with rational/DA Fatou coordinate `Phi_P`, and its Taylor expansion
agrees with `h` through order `N`.

Thus every finite jet in the normalized zero-residue simple parabolic class is compatible with a DA Fatou
coordinate.

## Promptability audit

No computation is used. The theorem asks whether finite parabolic jet data can distinguish HT Fatou coordinates
from DA Fatou coordinates. The new bit is the triangular pullback mechanism

```text
P(h(z))-P(z),    h(z)=z+z^2+...
```

whose leading action sends `z^k` to `k z^(k+1)`.

Once this is seen, the construction is forced. The theorem is a guardrail: finite parabolic jet computations
cannot certify Fatou-coordinate HT in the zero-residue class.

## Proof

We want

```text
Phi_P(h(z))-Phi_P(z)-1 = O(z^(N-1)).
```

If this holds, then the exact branch `f_P` solving `Phi_P(f_P)=Phi_P+1` has the same Taylor coefficients as `h`
through order `N`: if the first difference were `f_P-h = b z^r+O(z^(r+1))` with `r <= N`, then
`Phi_P'(z)=z^(-2)+O(1)` would give

```text
Phi_P(f_P)-Phi_P(h) = b z^(r-2)+O(z^(r-1)),
```

which cannot be absorbed by an `O(z^(N-1))` residual unless `r >= N+1`.

Now compute the residual for the target jet:

```text
R_P(z)=Phi_P(h(z))-Phi_P(z)-1
      = (-1/h(z)+1/z-1) + (P(h(z))-P(z)).
```

Because

```text
h(z)=z+z^2+z^3+O(z^4),
```

the coefficient of `z` in `-1/h+1/z-1` vanishes. Hence the base residual starts at order `z^2`.

Consider the linear map on polynomials of degree at most `N-3`,

```text
L(P)=P(h(z))-P(z)   mod z^(N-1).
```

For monomials,

```text
h(z)^k - z^k = k z^(k+1)+O(z^(k+2)).
```

Therefore, in the bases

```text
z, z^2, ..., z^(N-3)
```

for the source and

```text
z^2, z^3, ..., z^(N-2)
```

for the target residual coefficients, the map `L` is upper triangular with diagonal

```text
1,2,...,N-3.
```

This diagonal is nonzero over `C`, so `L` is an isomorphism onto the residual coefficients from `z^2` through
`z^(N-2)`. Choose `P` uniquely modulo terms of degree `>N-3` so that

```text
R_P(z)=O(z^(N-1)).
```

The branch `f_P` is algebraic because it satisfies the rational equation

```text
-1/f_P(z)+P(f_P(z)) = -1/z+P(z)+1,
```

after clearing denominators. The branch tending to `0` exists and is analytic since the left side has a simple
pole at `0`. Its expansion begins `z+z^2+z^3+O(z^4)`, so it is parabolic, and by construction `Phi_P` is a
rational Fatou coordinate. The first paragraph proves its `N`-jet is the prescribed jet `h`. ∎

## Consequences

1. **Finite parabolic jets do not certify HT.** In the zero-residue class, any finite jet can be completed by an
   algebraic germ with rational Fatou coordinate.
2. **Local algebraicity is not enough.** Even algebraic non-rational local parabolic germs can carry DA Fatou
   coordinates.
3. **The live invariant is global/sectorial.** A parabolic Fatou-coordinate HT theorem must use rational-map
   degree, finite global dynamics, Écalle--Voronin modulus, or another nonlocal constraint. It cannot be a theorem
   about finite local jets.

## Source and novelty boundary

This theorem is elementary formal local dynamics plus triangular linear algebra. It may be folklore to specialists
in parabolic germs: choosing a Fatou coordinate and pulling back translation is the standard normal-form move.
The project value is the explicit finite-jet nonidentifiability conclusion for HT claims.

Grade: **BRIDGE / gatekeeper**, not final goal-level knowledge unless a later audit finds that the finite-jet
realization statement has a consequence-bearing novelty beyond standard local parabolic theory.

## Gates

- [x] 0 -> 1 in-progress: finite-jet target and triangular mechanism identified.
- [x] 1 -> 2 fully-proven: proof written with algebraic branch and jet-matching argument.
- [ ] 2 -> 3 formalized: possible as formal-power-series triangular linear algebra.
- [ ] 3 -> 4 publication-ready: only as a warning lemma in a parabolic HT note.

## Log

- 2026-06-24 - Created by Haiku after the non-rational DA-Fatou countermodel. This strengthens the warning from
  one explicit algebraic germ to finite-jet realization throughout the zero-residue simple parabolic class.

## 2026-06-24 proof wording correction

In the triangular proof, the polynomial `P` is unique only after fixing its constant term, since constants cancel in
`P(h)-P(z)` and only add an irrelevant constant to the Fatou coordinate. The intended source basis is

```text
z, z^2, ..., z^(N-3),
```

not including `1`. Thus the theorem should be read as: there is a polynomial `P` with `P(0)=0` and degree at most
`N-3`; adding an arbitrary constant to `P` changes no germ and no Fatou equation.

## 2026-06-24 source-risk update -- Resman / Ecalle-Voronin boundary

A targeted source search found close prior-art context in Maja Resman's work on parabolic diffeomorphisms.
In `arXiv:1307.0780`, the introduction states that the analytic class of a parabolic diffeomorphism is given by
Ecalle--Voronin moduli and cannot be read from any finite jet of the parabolic germ. This directly matches the
finite-jet warning here, although not in HT language.

A related Resman text on cohomological equations states that Fatou coordinates glue to a global Fatou coordinate
on a punctured neighborhood iff the germ belongs to the model analytic class / is the time-one map of a
holomorphic vector field. It also gives the Abel-equation normal form for globally analytic solutions. This is
very close to the construction `Phi_P(f)=Phi_P+1`: we are choosing a global Fatou coordinate and pulling back
translation.

Therefore the theorem remains correct, but its novelty is downgraded further: it is best read as an HT-facing
translation of standard parabolic local-dynamics facts. The project-specific value is the explicit warning that
finite parabolic jets cannot serve as evidence for Fatou-coordinate HT.

Sources found:

- Resman, `arXiv:1307.0780`, introduction: analytic class is Ecalle--Voronin modulus data and cannot be read from
  any finite jet.
- Resman, `parabolic diffeomorphisms, classification` notes/PDF: Abel equation `Psi(f)-Psi=1`, Fatou coordinates,
  and the global-solution normal form.

Disposition unchanged: **BRIDGE / gatekeeper**, not goal-completing new knowledge.
