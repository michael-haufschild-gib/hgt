# Sonin reporter--physical codiagonal splice

- **ID:** `sonin-reporter-physical-codiagonal-splice`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CROSS-ROUTE SPLICE / SHARP NO-GO
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NOVEL] [NOT RH]`
- **Statement:** Positive cofinal Sonin pullbacks recover the exact Möbius Fisher coefficient and
  admit one diagonal landing on Route E's literal lower one-corner codiagonal; at positive
  aperture both carriers are eventually strictly positive.

## Goal

Test whether Sonin transport, countable Hardy reporting, Galerkin diagonal selection, and Route E
physical codiagonal recovery can be composed on one actual source carrier without an equivariance
assumption. Identify exactly whether this composition can supply the reflection-orientation
annihilator required by the Frankenstein RH route.

## Gates

- [x] 0 → 1: common `ell²` carrier and exact coefficient consumer identified
- [x] 1 → 2: strong-pullback, commutator, diagonal, and one-corner paper proofs closed
- [x] 2 → 3: Lean module built; capstones axiom-audited
- [ ] 3 → 4: publication-ready extraction

## Result

For Sonin corner `A_N`, put `D_N=A_N†A_N`. Lean proves `D_N x → x` for every source vector
and, for every bounded complex arithmetic clock `S_u`,

```text
[D_N,S_u]x → 0.
```

Consequently the transported complex Fisher score equals the reporter-selected clock term plus
one explicit commutator coefficient. At real aperture it converges to the physical Möbius
coefficient. Diagonalizing Sonin depth against

```text
sigma_j = 1 + 1/(j+1)
```

gives cofinal depths `N_j>j`, tracking error below `1/(j+1)`, and

```text
score(j,N_j) → 2u/(1+u)^2.
```

The same diagonal lands on Route E's literal prime-labelled lower one-corner Fisher codiagonal:

```text
score(j,N_j) - oneCorner(sigma_j,u) → 0.
```

For every `u>0`, both real parts are eventually strictly positive.

## Conjecture → proof/failure loop

1. **Literal finite-depth clock equivariance.** False in general; exact defect is `[D_N,S_u]`.
2. **Asymptotic fixed-source equivariance.** Proved: strong `D_N→I` forces commutator convergence
   without an equivariance premise.
3. **Coefficient-faithful critical diagonal.** Proved by composing Sonin recovery, Route-G
   Galerkin diagonal selection, and squarefree Euler boundary coefficient.
4. **Physical source landing.** Proved: same diagonal converges to Route E's literal lower
   codiagonal, not an abstract reporter.
5. **Use common positive scalar to annihilate reflected off-neutral classes.** Falsified sharply:
   at every `u>0` both realized currents are eventually strictly positive.

## No-go closure

- **Exact killing mechanism:** Fisher scalarization maps the common cofinal Sonin/Route-E current
  to the positive profile `2u/(1+u)^2`; it cannot orient or annihilate a nonzero aperture.
- **Strongest positive survivor:** unconditional non-equivariant source conversion and physical
  one-corner landing on one cofinal diagonal.
- **New insight:** carrier compatibility is not the remaining obstruction. Sign is lost exactly
  at positive Fisher scalarization. Any live Frankenstein splice must retain a reflection-odd,
  Krein, phase, or comparable signed coordinate before this landing.
- **Status:** dependency-closed and formalized.

## Lean realization

Module:

```text
GaloisForLFunctions.RHTower.SoninCofinalReporterClockCommutatorSeam
```

Capstones:

```text
tendsto_soninCofinal_complexFisherScore_ofReal
exists_soninCofinalCriticalFisherScore_diagonal
exists_soninCofinalCriticalFisherScore_oneCorner_landing
exists_soninCofinalCriticalFisherScore_eventually_positive
```

## Verification

- `lake env lean GaloisForLFunctions/RHTower/SoninCofinalReporterClockCommutatorSeam.lean`: pass
- `lake build GaloisForLFunctions.RHTower.SoninCofinalReporterClockCommutatorSeam`: pass
- umbrella import: present
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- global lint currently blocked by unrelated concurrently unwired Bourgain/Sieve/Suzuki modules;
  this module is not among unreachable-module failures

## Log

- 2026-08-12 — source/clock commutator seam, critical diagonal, Route-E landing, and positive wall
  proved and formalized
