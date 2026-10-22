# Gamma--Euler finite-block eventual-sign parity universality law

- **ID:** `gamma-euler-finite-block-eventual-sign-parity-universality-law`
- **Law:** LAW501
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/GammaEulerFiniteBlockEventualSignParityUniversalityLaw.lean`

## Theorem

Let `r>0` and let `L` be any nonempty finite list of positive Euler scales.  Apply the
Gamma--Euler central differences indexed by `L` to the Gamma characteristic

```text
phi_r(u) = cosh(u/2)^(-r).
```

Then the eventual sign is classified exactly by the parity of the number of channels:

```text
Odd  |L|  iff  D_L phi_r(u) > 0 for all sufficiently large u;
Even |L|  iff  D_L phi_r(u) < 0 for all sufficiently large u.
```

In particular, every additional positive Euler channel reverses the far-tail sign.  There is no
third-channel recovery: odd blocks are eventually positive, even blocks eventually negative,
for arbitrary block length.

## Theorem-generated derivation

Whole-corpus same-folder theorem-leaf pairing exposed:

- `gammaEulerDifferenceList_asymptotic`, the exact arbitrary-list asymptotic;
- `gammaEulerEigenvalueList_prod_sign`, the parity of its eigenvalue product;
- `gammaEulerDifferenceList_eventually_neg`, the existing even-block consumer;
- `gammaEulerManyDifferenceNextCoefficient_signed_pos`, the finite-set coefficient analogue.

The existing module consumes only the even branch.  Reading the limiting coefficient together
with the full product-sign theorem forces the missing odd branch and the two converse
classifications.  No target law was predicted before these declarations were inspected.

## Dependency-closed paper proof

For nonempty `L`,

```text
exp((r/2+1)u) D_L phi_r(u)
  -> -r 2^r product_{h in L} d_{r,h}(r/2+1).
```

Every next-mode eigenvalue `d_{r,h}(r/2+1)` is strictly negative when `r,h>0`.  Hence their
product is negative for odd `|L|` and positive for even `|L|`.  Since `-r2^r<0`, the limiting
coefficient is positive for odd blocks and negative for even blocks.  An open positive or
negative neighborhood of that nonzero limit gives the corresponding eventual sign; the
exponential prefactor is everywhere positive, so it can be removed without changing sign.

For each converse, natural-number parity is exhaustive.  If an eventually positive block had
even length, the existing even-block theorem would make it eventually negative as well, an
impossibility on the nontrivial filter `atTop`.  The negative-to-even converse is symmetric using
the newly proved odd branch.

No numerical computation is used.

## Strict corpus delta

The corpus proves arbitrary-list asymptotic transport, arbitrary-list eigenvalue-product parity,
and eventual negativity for nonempty even blocks.  It does not prove eventual positivity for odd
blocks or state that eventual sign determines parity.  The new law closes both missing directions
and upgrades a one-sided no-go into an exact finite-channel classification.

## Lean result

`formal/GaloisForLFunctions/RHTower/GammaEulerFiniteBlockEventualSignParityUniversalityLaw.lean`
proves:

- `gammaEulerDifferenceList_eventually_pos`;
- `gammaEulerDifferenceList_eventualSign_iff_parity`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/GammaEulerFiniteBlockEventualSignParityUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after the dependency-closed Lean proof passed.

- Wynn, *Central Difference and Other Forms of the Euler Transformation* (1956), develops central
  difference forms of Euler transformation and alternating asymptotic-series coefficients, but
  not this normalized Euler-factor operator on a Gamma characteristic.
- Dowker, *Central differences, Euler numbers and symbolic methods* (arXiv:1305.0500), treats
  central-difference calculus and powers of `sech`, but the searches found no arbitrary
  positive-scale block theorem identifying eventual strict sign iff channel-count parity.
- Targeted searches for Gamma--Euler central differences, iterated `sech`-power differences, and
  eventual parity reversal found no statement matching the exact law.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is not claimed for classical
central-difference calculus or `sech` expansions; it is limited to the exact normalized
Gamma--Euler operator, arbitrary positive scales, and both eventual-sign iff parity directions.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
