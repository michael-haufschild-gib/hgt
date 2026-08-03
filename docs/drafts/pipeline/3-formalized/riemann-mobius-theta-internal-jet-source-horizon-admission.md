# Möbius--theta internal-jet source horizon admission

- **Status:** dependency-closed theorem; Lean-formalized
- **Parent:** `rh-current-frontier-map.md`, Route R
- **Open core:** `INTERNAL_JET_PHYSICAL_HORIZON_ADMISSION`

## Exact conjecture

For every internal jet order `k`, let

```text
Delta_k(0)     = Psi_{k,3},
Delta_k(j + 1) = Psi_{k,j+4} - Psi_{k,j+3},
```

where `Psi_{k,m}` is the target-free, internally promoted physical
Möbius--theta rung. Then, unconditionally,

```text
sum_j ||Delta_k(j)||_{L2} < infinity,
sum_j ||Delta_k(j)||_{L2}^2 < infinity,
sum'_j Delta_k(j) = thetaJetSource_k,
Fourier(sum'_j Delta_k(j)) = XiC^(k)  in L2.
```

Consequently `j |-> Delta_k(j)` is a literal element of
`ell2(N; L2(R))`. Its grade is forced by physical exponent cofaces; no Xi
zero, divisor enumeration, Gaussian residue normalization, or arbitrary
external horizon weight occurs.

## Proof mechanism

The post-head tail at exponent `m` is bounded in physical `L2` by

```text
(1/2)^((m-3)/2) * C_k,
```

where `C_k` is the summable source majorant built from the actual internal
theta-jet norm. Adjacent cofaces are differences of successive tails, so
their norms are dominated by two shifted geometric sequences. This gives
absolute summability, hence square summability. Finite coface sums telescope
exactly to `Psi_{k,3+N}`; the already-proved strong physical landing then
identifies the infinite codiagonal with `thetaJetSource_k`. Plancherel gives
the exact Xi-jet landing.

## Hostile gate

This theorem advances Route R only as a source-space admission theorem. It
does not orient the Hodge/Green defect and does not imply the Ward sign. A
proof that inserts a divisor-indexed weight, uses only finite support, or
states convergence only after spectral evaluation fails the gate.

## Novelty audit

- Zeroth-order absolute physical codiagonal: already formalized.
- All-order strong physical landing: already formalized.
- Abstract `ell1 subset ell2`: standard infrastructure.
- New corpus content: all multiplicity jets simultaneously admit the actual
  physical exponent-coface horizon before divisor evaluation, with exact
  source codiagonal and Plancherel landing.

## Formal target

- Module:
  `formal/GaloisForLFunctions/RHTower/MobiusThetaInternalJetPhysicalHorizonAdmission.lean`
- Wire into `formal/GaloisForLFunctions/RHTower.lean`.

## Gates

- [x] exact conjecture stated before Lean
- [x] corpus duplicate/no-go audit
- [x] divisor-independent source definition
- [x] dependency-closed paper proof
- [x] direct Lean check
- [x] targeted module build
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)

## Formal certificate

- `lake env lean GaloisForLFunctions/RHTower/MobiusThetaInternalJetPhysicalHorizonAdmission.lean`
  passed.
- `lake build GaloisForLFunctions.RHTower.MobiusThetaInternalJetPhysicalHorizonAdmission`
  passed.
- Module is imported by the `RHTower` umbrella.
- Principal declarations:
  `summable_norm_mobiusThetaInternalJetCompletePhysicalChannel_three`,
  `tsum_mobiusThetaInternalJetCompletePhysicalChannel_three`,
  `mobiusThetaInternalJetPhysicalHorizon`, and
  `fourier_tsum_mobiusThetaInternalJetPhysicalHorizon`.

## Frontier delta

Route R no longer lacks a source-derived countable completion grade for the physical
Möbius--theta multiplicity jets. Remaining open theorem is the polarized
Gamma/co-Poisson/Hodge comparison: transport this admitted physical horizon to the resolved
Hellinger--Green antidiagonal, identify its Laplace boundary column with the strict-right Xi Ward
response, and prove the transport does not increase the four-unit source energy.
