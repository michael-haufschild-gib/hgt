# Route U repeated-root prime-wall no-birth

- **ID:** `route-u-repeated-root-prime-wall-no-birth`
- **Stage:** 3-formalized
- **Type:** THEOREM / repeated-root source-wall rigidity
- **Routes:** U primary
- **Source:** compact symmetric-root division, Suzuki logarithmic form domain, prime-wall endpoint orthogonality

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Theorem U-REPEAT

Let `h : R -> C` be integrable, supported in `[-a,a]`, and suppose for `c != 0`

```text
routeURealFourier(h)(w) = (w^2-c^2)^m G(w)
```

with continuous `G`. Define the depth-`k` source by recursively dividing the compact time-domain
source by the symmetric Fourier roots `±c`. Then, for every `k <= m`, the divided source remains
integrable, remains supported in `[-a,a]`, and has exact pointwise Fourier transform

```text
(w^2-c^2)^(m-k) G(w).                                      (1)
```

For every `k<m`, both its next even quotient and its odd twin are exact elements of Suzuki's
logarithmic form domain at the unchanged aperture. If `G(w)=K(w^2)` for a continuous real `K`, the
odd twin is represented by the literal real hard-edge profile

```text
w K_k(w^2),    K_k(u)=(u-c^2)^(m-k-1) K(u).                 (2)
```

At a prime-power wall `a=log(n)/(4 pi)`, every mixed entering response between depths `k,l<m`
vanishes:

```text
PrimeJumpOddResponse(n,K_k,K_l)=0.                          (3)
```

Consequently the complete admitted odd Gram matrix is identical in the incoming chamber and at
the wall. Any odd jet with strictly positive incoming quadratic value cannot become wall-null.

All Lean theorems are unconditional and closed. They assume the displayed analytic source data;
they do not assume RH, add axioms, or assert that the current Route-U first-contact limit already
satisfies those source hypotheses.

## Heavy conjecture loop

### U-R1 — division loses residual multiplicity at the divided root

**Conjecture.** One compact division proves the quotient formula only away from `±c`, so recursive
division cannot recover the next exact zero without derivative or computation.

**Attack.** Both sides of the proposed quotient identity are continuous. Equality holds off the
finite root set, whose complement is dense. Continuity extends the identity to both roots and
retains the exact residual factor `(w^2-c^2)^(m-1)`.

**Verdict:** false. Lean proves `(1)` recursively, including values at `±c`.

### U-R2 — repeated-root descendants may leave the critical form domain

**Conjecture.** Repeated division may preserve an algebraic Fourier factor while destroying
integrability, compact support, or exact Suzuki admission.

**Attack.** The compact two-root division theorem returns all three invariants at each step.
Induction feeds its endpoint zeros from the residual factor established in U-R1. The existing
even and odd admission constructors then realize every depth before exhaustion at the original
aperture.

**Verdict:** false. All even quotients and odd twins are Lean-admitted with exact Fourier formulas.

### U-R3 — diagonal endpoint invisibility may miss mixed multiplicity directions

**Conjecture.** Each repeated-root odd jet can have zero diagonal prime response while mixed
responses alter the Gram matrix and create a new null combination at the wall.

**Attack.** Identify every complex descendant with a real squared-variable profile as in `(2)`.
Bilinear endpoint Paley--Wiener orthogonality applies to every pair of admitted profiles, not only
one profile with itself, proving `(3)` for arbitrary depths.

**Verdict:** false. Whole repeated-root odd Gram update is zero.

### U-R4 — repeated multiplicity creates a distinct first-wall birth mechanism

**Conjecture.** Parity-doubled multiplicity could create a wall kernel even after simple-root
prime-wall invisibility.

**Attack.** Wall Gram matrix equals incoming Gram matrix entrywise. Thus wall nullity cannot be
new inside admitted compact factorized repeated-root flag; strictly positive incoming directions
remain nonzero.

**Verdict:** false inside proved source class. Subsequent U-BANDSOURCE closes literal compact-source
selection and exact factor transport from any continuous factorized representative.
`XiShiftedHardEdgeLocallyUniformL2Source.lean` further identifies same-subsequence locally uniform
and strong-L2 limits and derives physical reality. `XiShiftedHardEdgeEntireRootFactorization.lean`
then derives positive finite root order and global entire quotient directly from literal
source-selected first-contact packets. Surviving obstruction is incoming positivity.

## Higher universal principle

**Multiplicity is transported, while arithmetic wall action is band-edge blind.** Symmetric root
division does not consume support aperture; it converts multiplicity into a finite parity-doubled
flag inside one fixed Paley--Wiener space. Prime wall sits at twice that bandwidth, so its quadratic
action vanishes on entire flag, including mixed entries. Apparent degenerate wall birth was shadow
of failing to separate formation of null flag before wall from arithmetic action at wall.

This principle forbids another wall-local sign search. Any genuine Route-U counterstate must be
born before prime wall, fail compact factorized admission, or violate required incoming positivity.

## Positive survivor and remaining bridge

Strongest positive survivor is exact no-birth theorem for every finite repeated-root odd flag.
`XiShiftedHardEdgeBandlimitedCompactSource.lean` subsequently supplies a literal compact `L1 cap
L2` source, endpoint support, and exact multiplicity transport once the actual limit has a
continuous factorized representative. `XiShiftedHardEdgeLocallyUniformL2Source.lean` automatically
supplies that representative's L2 identity and physical reality from common local-uniform/strong-
L2 extraction. Escaping-pole entireness and unit-norm noncollapse now supply the source-derived
global squared-variable root quotient/factorization with full multiplicity. Remaining source
theorem must establish incoming strictness or semidefinite control on generated odd flag.

Once those are obtained, repeated-root branch is excluded at prime wall without new arithmetic
jump estimate. Until then, no RH claim follows.

## External novelty audit

Existing Route-U audit found classical Paley--Wiener support and endpoint orthogonality results but
no theorem coupling compact symmetric-root division, exact residual multiplicity, Suzuki form-domain
admission, and entrywise vanishing of shifted-Xi repeated-root prime-wall Gram update. No external
priority claim is made; novelty remains unverified.

## Gates

- [x] 0 -> 1: repeated-root admission and mixed-wall conjectures attacked
- [x] 1 -> 2: dependency-closed proof and corpus collision audit
- [x] 2 -> 3: unconditional Lean proofs, direct checks, exact leaf builds, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Modules:

- `formal/GaloisForLFunctions/RHTower/CompactL2FourierRootDivision.lean`;
- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeRepeatedRootSuzukiAdmission.lean`;
- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeRepeatedRootPrimeWallNoBirth.lean`.

Capstones:

- `routeURealTwiceRootDividedTime_fourier_factor_pow`;
- `routeURealRepeatedRootDividedTime_invariants`;
- `exists_routeURealRepeatedRootEvenSuzukiAdmission`;
- `exists_routeURealRepeatedRootOddSuzukiAdmission`;
- `exists_routeURepeatedRootOddSquaredProfile_suzukiAdmission`;
- `routeURepeatedRootMixedPrimeJumpOddResponse_eq_zero`;
- `routeURepeatedRootOddForm_wall_eq_incoming`;
- `routeURepeatedRootOddJet_not_new_wall_kernel`.

Each new/modified module passed direct `lake env lean`; exact leaf targets passed `lake build`.
Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Targeted forbidden
declaration scan is clean. Finished modules are imported by `RHTower.lean`; no umbrella or
full-project build was run.

## Log

- 2026-08-16 — Exact residual multiplicity after compact symmetric division proved at roots.
- 2026-08-16 — Recursive even/odd Suzuki admission proved at unchanged aperture.
- 2026-08-16 — Real-profile bridge and full mixed prime-wall Gram invisibility proved.
- 2026-08-16 — Repeated-root wall-birth mechanism retired inside compact factorized source class.
