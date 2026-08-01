# Suzuki–Xi first-defect jet gap

- **ID:** `suzuki-xi-first-defect-jet-gap`
- **Stage:** 2-fully-proven; unconditional Lean formalization compiled
- **Type:** THEOREM (paper) / THEOREM (Lean) / SOURCE NECESSITY LAW
- **Scientific status:** `[PROVED HERE] [UNCONDITIONAL] [NO COMPUTATION]`
  `[CANDIDATE NEW SOURCE-SPECIFIC SYNTHESIS] [EXTERNAL PRIORITY UNVERIFIED]`
  `[NOT SOURCE ADMISSION] [NOT AN RH PROOF]`
- **Statement:** The exact normalized Xi Livšic target has real first anchored defect jet
  `κ_Xi∈(77/85,1)`. Every Xi-identifying Suzuki family must converge to this scalar, place more
  than `81/85` of normalized defect energy in the even channel, less than `4/85` in the odd
  channel, and retain a fixed positive ground-leakage floor.

## Goal

Replace the generic “some anchored jet must survive” condition by an unconditional, quantitative,
target-exact source obligation. This changes the live Suzuki problem: neither higher-order-only
survival, far-negative free collapse, nor ground-edge Cayley saturation can identify Xi.

This theorem does not construct an arithmetic source map. The updated
`riemann-source-modular-superselection/main-universal.tex` admission--separation ledger forbids
using a target-fitted moment or interface as source provenance.

## Definitions

Let

```text
L(w) = Re ((xi'/xi)(1/2+w)),        w>0,
s_Xi = L(1)>0.
```

Let `m_Xi` be the Donoghue function normalized by `s_Xi` and anchored by `m_Xi(i)=i`, and let

```text
Theta_Xi = (m_Xi-i)/(m_Xi+i),
kappa_Xi = Re(2i Theta_Xi'(i)).
```

The proof shows the complex number `2i Theta_Xi'(i)` is itself real, so taking its real part loses
nothing.

For a multiplicity copy `q` of a nontrivial Xi zero, set

```text
t_q = Im(rho_q)^2-(Re(rho_q)-1/2)^2,
r_q = (1+t_q+i b_q)^(-1),
M_0 = sum_q r_q,
M_1 = sum_q r_q^2.
```

Here `b_q` is the imaginary coordinate of the centered squared spectral point. Sums retain exact
zero multiplicities.

## Theorem and proof

### 1. Atomwise divisor gap

Every nontrivial zero satisfies, unconditionally,

```text
Im(rho_q)^2 > 41/2,
(Re(rho_q)-1/2)^2 < 1/4.
```

Hence `t_q>81/4`. Put `A=1+t_q>85/4` and write `r_q=(A+iB)^(-1)`. Direct real-part algebra gives

```text
Re(r_q)   = A/(A^2+B^2),
Re(r_q^2) = (A^2-B^2)/(A^2+B^2)^2.
```

Since

```text
85A < 4(A^2+B^2),
```

one obtains the strict atomwise inequality

```text
85 Re(r_q^2) < 4 Re(r_q).                         (1)
```

### 2. Multiplicity-exact moment inequality

Both reciprocal-square series are absolutely summable. Summing `(1)` over every multiplicity copy
and using nonemptiness of the Xi divisor gives

```text
85 Re(M_1) < 4 Re(M_0).                           (2)
```

The already proved shifted squared-zero moment law also gives `Re(M_0)>0` and `Re(M_1)>0`.

### 3. Exact logarithmic jet

On the positive real ray,

```text
L(1)  = Re(M_0),
L'(1) = Re(M_0)-2 Re(M_1).
```

Equation `(2)` and positivity of `Re(M_1)` therefore yield

```text
(77/85)L(1) < L'(1) < L(1).                       (3)
```

Because `s_Xi=L(1)>0`, the normalized Donoghue derivative is `L'(1)/L(1)`. Cayley differentiation
at the anchor gives

```text
2i Theta_Xi'(i) = L'(1)/L(1) in R.
```

Dividing `(3)` by `L(1)` proves

```text
77/85 < kappa_Xi < 1.                             (4)
```

No Riemann-hypothesis assumption occurs.

## Exact Suzuki source consequences

For finite Suzuki even/odd resolvent energies `E_e,E_o`, the exact defect angle is

```text
kappa = (E_e-E_o)/(E_e+E_o).
```

If `kappa=kappa_Xi`, its normalized parity shares are

```text
p_even=(1+kappa_Xi)/2 ∈ (81/85,1),
p_odd =(1-kappa_Xi)/2 ∈ (0,4/85).                 (5)
```

If the actual disk-conjugated finite Suzuki Livšic quotients converge locally uniformly to the
normalized Xi target and are eventually holomorphic on the disk, Weierstrass derivative
convergence and the exact endpoint identity force

```text
kappa_j -> kappa_Xi.                              (6)
```

Thus a nonzero limit with only a higher anchored jet cannot be Xi.

For ground-centered data the exact resolvent estimate is

```text
0 <= 1-kappa_j <= 2 rho_j,
```

where `rho_j` is Suzuki's dimensionless odd-channel ground leakage. Combining this with `(6)` and
the strict upper bound in `(4)` gives the fixed eventual floor

```text
(1-kappa_Xi)/4 < rho_j,
(1-kappa_Xi)/4 > 0.                               (7)
```

The factor `1/4` is a convenient strict margin; asymptotically `(1-kappa_Xi)/2` is the sharp lower
barrier supplied by this one-sided inequality.

## What changed at the frontier

Before `(4)`, the exact Xi target could generically have escaped through a higher-order zero at the
anchor. That possibility is now impossible. A live Suzuki source schedule must simultaneously:

1. avoid the free endpoint `kappa→0`;
2. avoid ground saturation `kappa→1` and vanishing leakage;
3. enter the narrow parity cone `(5)`;
4. make its source defect angle converge to the target-exact scalar `(6)`;
5. identify the full meromorphic Xi target from arithmetic source data.

Matching only `(4)` or `(5)` is not evidence for item 5. It is one scalar necessary condition and
can be fitted from the target. The next frontier theorem must be source-only: construct a canonical
cofinal schedule whose dynamics force this cone and the remaining target moments, or prove actual
Suzuki dynamics cannot remain in it.

## Incorporation of the updated biaxial superselection paper

The publication-ready theorem closes only the conjunction:

```text
same unit response on every positive shell
+ orthogonal ell2 or Bessel shell modes
+ reflected valuation sewing at finite Rees grade
+ terminal sign after reflection-invariant scalar fusion.
```

Its exact survivor is singular or relation-valued in breadth, beyond every finite Rees order in
reflected depth, source-pointed before scalarization, and label-retaining. Equations `(4)`--`(7)`
constrain any Suzuki realization in or outside that survivor class, but do not prove its source
admission. In particular, the exact Xi Donoghue target is a terminal consumer; selecting it first
and reverse-engineering source data would be the source-provenance theatre explicitly excluded by
the paper.

## Novelty and collision audit

Known ingredients, not claimed novel:

- functional-equation and conjugation symmetries of Xi;
- critical-strip support and explicit first-zero-height lower bounds;
- Hadamard/logarithmic-derivative zero expansions;
- Donoghue/Herglotz normalization and Livšic Cayley transforms;
- locally uniform convergence implying derivative convergence.

Repo/corpus searches found complete-monotonicity moment towers, positive Euler responses, generic
defect-angle formulas, free collapse, and ground-edge Cayley universality, but no exact
`77/85` Xi first-defect ratio, parity cone, or source leakage consequence. Targeted literature
searches for the ratio, the corresponding Xi logarithmic-derivative inequality at `3/2`, and a
Suzuki/Livšic first-jet statement found no collision. The candidate-new content is the exact
source-specific synthesis `(1)`--`(7)`, not any ingredient separately. External specialist
priority review remains required before publication.

## Lean certificate

Unconditional modules:

- `formal/GaloisForLFunctions/RHTower/SuzukiXiFirstDefectJet.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiXiFirstDefectJetSource.lean`

Main declarations:

```text
eightyFive_mul_re_xiShiftedReciprocalSquare_sq_lt_four_mul_re
eightyFive_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero
seventySeven_div_eightyFive_mul_xiRealLogDeriv_one_lt_deriv
xiHedenmalmLivsicFirstDefectJet_mem_Ioo
xiHedenmalmLivsic_firstDefectJet_tendsto_of_locallyUniform
xiHedenmalmLivsic_matching_source_parity_shares
suzuki_defectAngle_tendsto_xiHedenmalmLivsicFirstDefectJet
xiHedenmalmLivsicFirstDefectJet_groundLeakageFloor_pos
suzukiGroundLeakage_eventually_gt_xiHedenmalmLivsicFirstDefectJet_floor
```

Both files pass direct foreground `lake env lean`. Targeted module builds pass. Final umbrella,
lint, and axiom audit remain the promotion gate; no full build is required or permitted for this
route audit.

## Gates

- [x] 0 → 1: source-facing quantity and falsifiable target interval isolated
- [x] 1 → 2: dependency-closed paper proof, hostile provenance audit, no computation
- [x] exact theorem and source connectors formalized unconditionally in Lean
- [x] direct foreground Lean checks and targeted module builds green
- [ ] umbrella imports, formal lint, and `#print axioms` audit
- [ ] source-only cofinal schedule enters the strict cone and identifies full Xi target
- [ ] RH or class-complete no-go

## Log

- 2026-08-01 — derived atomwise `85`-to-`4` inequality from unconditional divisor geometry,
  summed it over multiplicity-exact squared-zero moments, and proved `77/85<kappa_Xi<1`.
- 2026-08-01 — proved compact-open derivative/source convergence, strict parity shares, and
  positive ground-leakage floor in Lean. Updated source-provenance audit records these as necessary
  source constraints, not source admission.
