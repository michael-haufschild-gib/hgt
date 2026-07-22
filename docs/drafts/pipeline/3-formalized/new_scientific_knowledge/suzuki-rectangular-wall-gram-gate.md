# Suzuki rectangular wall-Gram gate

- **ID:** `suzuki-rectangular-wall-gram-gate`
- **Stage:** 3 — formalized in Lean 4
- **Type:** SOURCE-TYPE CORRECTION / SHARP TRACE CELL / POSITIVE OBSTRUCTION SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Formal module:**
  `GaloisForLFunctions.RHTower.SuzukiRectangularWallGramGate`
- **RH used:** no
- **Computation used:** no

## Formal theorem package

For `n=p^(e+1)`, let

```text
A=R_(L,a)(log n),
K_e(t,u)=omega_e(t) conjugate(omega_e(u)),
G_(L,a,e)(t,u)=A K_e(t,u).
```

Lean proves unconditionally:

1. `R_(L,a)(h)>=0` for all real `L,a,h`, directly from exact four-tent formula;
2. `G` is Hermitian and has exact difference-character formula;
3. diagonal is literal sharp prime-power cell
   `R_(L,a)(log n) Lambda(n)/sqrt(n)>=0`;
4. FE anti-diagonal is same cell times full phase `exp(i t log n)`;
5. every finite height section is positive semidefinite;
6. if `0<=L<=a` and `2a<log n`, then entire block is exactly zero;
7. under positive S64 observer parameters and `2a<log p`, Gamma-boundary fused rectangle cannot
   equal sharp depth-zero wall cell: former has strictly positive real part, latter is zero.

## Principal declarations

```text
rectangularTwoEdgeAutocorrelation_nonneg_unconditional
suzukiRectangularWallGramGate_nonneg
suzukiRectangularPrimePowerWallCell_nonneg
star_suzukiRectangularWallGramKernel_swap
suzukiRectangularWallGramKernel_eq_differenceCharacter
suzukiRectangularWallGramKernel_diagonal_eq_primeCell
suzukiRectangularWallGramKernel_antidiagonal
suzukiRectangularWallGramMatrix_posSemidef
suzukiRectangularWallGramKernel_eq_zero_of_two_mul_a_lt
xiGammaBoundary_fusedRectangle_ne_suzukiRectangularWallGramKernel_diagonal
```

## Representation correction

Direct S64-to-sharp-trace conjecture is false for two independent exact reasons:

- fused observer ray has nonzero tails while sharp cell has compact causal support;
- fused ray is linear in observer-dressed wall field while von Mangoldt cell is quadratic in bare
  observer-free wall field.

Strongest positive survivor is gated Hermitian wall Gram.  It solves local prime-cell
identification without claiming global Weil positivity.  Full formula subtracts twice these
positive cells and adds polar--Gamma terms, so global compensation remains RH-bearing step.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiRectangularWallGramGate.lean` — PASS;
- final audit:
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` — PASS, `9480/9480`;
- axiom surface of six capstones:
  `propext`, `Classical.choice`, `Quot.sound` only;
- forbidden declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- repository lint reaches module; current failures are 22 unrelated shared-tree unreachable modules.

## Novelty boundary

Generic rank-one character kernels and nonnegative scalar Gram gating are classical.  Candidate
novelty is exact Suzuki/Gamma/von-Mangoldt/sharp-support/FE weld and formal support mismatch, not
general Gram mechanism.  Current primary audit of Suzuki arXiv:2606.09096 and Groskin
arXiv:2607.02828 found no matching local source theorem; independent priority audit remains open.

## Remaining RH frontier

### `SUZUKI-GATED-WALL-GLOBAL-COMPENSATION` `[CONJECTURE]`

Prove actual restricted-Weil resolvent and Robin boundary trace transport finite compactly gated
wall blocks into observer response, assemble finite prime diagonal with polar--Gamma, marked Robin,
and holonomy channels, and show resulting fixed-width Ward residual uniformly lower bounded on a
cofinal aperture mesh.  This would feed existing unconditional RH connector.  Corpus does not
currently prove this global compensation.

## Gates

- [x] 0 -> 1: source-pure conjecture, competitors, falsifiers
- [x] 1 -> 2: dependency-closed paper proof and hostile audit
- [x] 2 -> 3: unconditional Lean formalization and final build
- [ ] independent primary-literature priority audit
- [ ] global compensated restricted-Weil/Robin/Gamma/holonomy assembly
- [ ] RH
