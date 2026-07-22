# Completed seam compact Thorin exponent capstone

- **ID:** `completed-seam-compact-thorin-exponent-capstone`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH PROOF]`
- **Source:** `completed-seam-thorin-subordinator-rh.md`;
  `completed-seam-compact-markov-germ-capstone.md`;
  `XiSquaredSeamCassiniResolventSourceLaw.lean`
- **Statement:** A local positive compact Thorin logarithmic representation of the canonical
  centered Cassini source exponent differentiates to a compact Markov representation of every
  completed prime--archimedean moment and therefore proves RH.

## Exact objects

Let `C(u)=xiSquaredSeamCassiniSource(u)` and

```text
E_src(z) = -2 log(C(1+z)/C(1)).
```

The corpus identity `C(1+w^2)=XiC(w)` and its exact reciprocal-resolvent theorem give, near `z=0`,

```text
E_src'(z) = -2 C'(1+z)/C(1+z) = completedSeamMomentGerm(z).       (1)
```

For a finite positive measure `mu` supported in `[0,B]`, define the zero-node-extended logarithmic
kernel

```text
kappa(x,z) = z                              if x=0,
             -log(1-xz)/x                  if x!=0,
E_mu(z)    = integral kappa(x,z) dmu(x).
```

On `|z|<1/(2B)`, the principal branch is valid and

```text
partial_z kappa(x,z) = 1/(1-xz),
E_mu'(z) = integral 1/(1-xz) dmu(x) = compactMarkovTransform(mu,z).  (2)
```

The source premise is the genuine local exponent identity

```text
E_src = E_mu near 0.                                             (3)
```

Differentiating `(3)` and applying `(1)`--`(2)` gives the existing
`PrimeArchCompactMarkovGermRepresentation`, hence RH.

## Paper proof

1. `C(1)=XiC(0)!=0`, so `C(1+z)/C(1)` stays in the principal-log slit plane near zero and
   `E_src` is analytic there.
2. On a punctured neighborhood, choose `w` with `w^2=z`. The exact Cassini resolvent theorem says
   `-2 logDeriv C(1+z)` is the sum of the shift-one Möbius resolvents. The corpus Möbius identity
   converts each term to `lambda/(1-z lambda)`, where `lambda` is the centered reciprocal square.
   The completed-seam power-series/resolvent identity sums these terms to
   `completedSeamMomentGerm(z)`. Analytic removability extends equality to `z=0`, proving `(1)`.
3. If `|x|<=B` and `|z|<1/(2B)`, then `|xz|<1/2`; hence `1-xz` is in the principal slit plane and
   `|(1-xz)^(-1)|<=2`.
4. For `x!=0`, the chain rule for the principal logarithm gives
   `partial_z[-log(1-xz)/x]=(1-xz)^(-1)`; the `x=0` branch has the same derivative `1`.
5. The log remainder bound
   `|log(1-u)^(-1)-u| <= |u|^2/(2(1-|u|))` for `|u|<1` yields
   `|kappa(x,z)|<=2|z|` when `|u|<1/2`. Thus both kernel and derivative are dominated by constants
   against finite `mu`; differentiation under the integral proves `(2)`.
6. Local equality `(3)` implies local equality of derivatives. Equations `(1)` and `(2)` produce
   the compact Markov germ premise already formalized to imply RH.

No zero localization, positivity theorem, or estimate is hidden in this bridge. Positivity and exact
source identification of `mu` remain the RH-strength producer premise.

## Hostile audit

- The zero-node branch is necessary: it carries deterministic drift and is the continuous limit of
  the logarithmic kernel.
- Finite jets do not suffice; premise `(3)` is equality on a complex neighborhood.
- Compactness is stronger than general Thorin theory but matches the already-proved compact Markov
  consumer. General noncompact Thorin measures require separate tail domination.
- The source exponent is centered at `u=1`, not the Euler-safe shift-one germ at `u=0`; this avoids
  a false normalization weld.
- This theorem is an exact calculus/interface bridge. It does not make the positive Thorin measure
  unconditional and therefore does not prove RH.

## Gates

- [x] 0 → 1 in-progress: exact source object, branch, drift, support, and consumer fixed
- [x] 1 → 2 fully-proven: dependency-closed paper proof above
- [x] 2 → 3 formalized: `CompletedSeamCompactThorinExponentCapstone.lean`
- [ ] 3 → 4 publication-ready: not applicable unless included as supporting proposition

## Literature classification

The logarithmic Thorin exponent and its Stieltjes derivative are classical GGC/Bondesson calculus;
the 2023 Thorin--Bernstein literature likewise characterizes the class through a generalized
Stieltjes derivative. Novelty claim: none. Corpus-specific contribution is exact normalization to
the canonical centered Cassini source and composition with the formal RH capstone.

## Log

- 2026-07-22 — exact centered source normalization isolated; paper proof closed before Lean work.
- 2026-07-22 — source derivative identity, compact Thorin differentiation, exponent-to-Markov
  interface, and RH connector formalized and imported by the `RHTower` umbrella.
