# Gamma even-boundary parity floor no-go

- **ID:** `gamma-even-boundary-parity-floor-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-CLASS NO-GO
- **Scientific status:** `[PROVED ON PAPER] [LEAN 4] [NOVELTY PROVISIONAL] [NOT RH]`
- **Terminal role:** eliminates the growing *even* Gamma/Jacobi boundary-capacity survivor left by
  `SR-35`; it does not eliminate odd boundary channels or signed principal-relative subtraction.
- **Lean core:**
  `formal/GaloisForLFunctions/HTGeometry/ParityProtectedSchurFloor.lean` and
  `formal/GaloisForLFunctions/RHTower/GammaEvenBoundaryParityNoGo.lean`.
- **Corpus parents:**
  `gamma-damped-mobius-clock-critical-amplification.md` (odd Gamma kernel),
  `semilocal-all-even-jacobi-prolate-residue-tower.md` (source all-even Jacobi tower),
  `GammaConductorSchurCapacity.lean` (nonsummable prime Schur costs), and
  `ResolvedChannelWardLaw.lean` / `PrimeMellinJetResolvedChannelNoGo.lean` (`SR-35`).

## Universal parity-protected Schur floor

Let `H` be a real or complex Hilbert space, let `J` be self-adjoint, and let

```text
J e_i=e_i,       J o_i=-o_i,       J b_i=b_i.            (1)
```

The vectors `b_i` are arbitrary corrections in the even sector. They need not be projections,
optimal Schur corrections, finite-rank, or contained in one finite-dimensional subspace. For every
finite coefficient family `z_i`, one has the exact identity

```text
||sum_i z_i ((e_i+o_i)-b_i)||^2
 =||sum_i z_i (e_i-b_i)||^2+||sum_i z_i o_i||^2.         (2)
```

In particular,

```text
||sum_i z_i o_i||^2
 <=||sum_i z_i ((e_i+o_i)-b_i)||^2.                      (3)
```

Thus the odd-sector Gram is a capacity-independent lower floor for every even-sector Schur
correction.

### Proof

Self-adjointness and `(1)` give, for every `i,j`,

```text
<e_i-b_i,o_j>
 =<J(e_i-b_i),o_j>
 =<e_i-b_i,J o_j>
 =-<e_i-b_i,o_j>,
```

so the inner product is zero. Hence the two finite sums

```text
E=sum_i z_i(e_i-b_i),       O=sum_i z_i o_i
```

are orthogonal. Since the total residual is `E+O`, Pythagoras proves `(2)`, and `(3)` follows from
nonnegativity of `||E||^2`. No closure, rank, or dimension premise occurs. `QED`

## Exact Gamma odd kernel

For the normalized archimedean Gamma measure

```text
dmu_Gamma(s)=(2 pi)^(-3/2)|Gamma(1/4+i s/2)|^2 ds,
phi(t)=int exp(i t s)dmu_Gamma(s)=(cosh t)^(-1/2),         (4)
```

define

```text
O(t,u)=(phi(t-u)-phi(t+u))/2.                             (5)
```

Then

```text
O(t,u)=int sin(t s)sin(u s)dmu_Gamma(s).                  (6)
```

For `t,u>0`,

```text
O(t,u)>0.                                                 (7)
```

Indeed, the product-to-sum formula and `(4)` prove `(6)`. Moreover,

```text
cosh(t+u)-cosh(t-u)=2 sinh(t)sinh(u)>0.
```

The function `x |-> x^(-1/2)` is strictly decreasing on the positive axis, so
`phi(t-u)>phi(t+u)`, which proves `(7)`.

On the diagonal,

```text
O(t,t)=(1-phi(2t))/2.                                     (8)
```

## Prime-log floor and divergence

For every prime `p`, the existing Gamma bound gives

```text
phi(2 log p)<=sqrt(2) exp(-log p)=sqrt(2)/p<=sqrt(2)/2.
```

Therefore

```text
O(log p,log p)>=c_Gamma:=(1-sqrt(2)/2)/2>0.              (9)
```

Let `R_p` be the actual one-prime Gamma conductor Schur cost. The existing unconditional theorem
states

```text
R_p>=9/(512p),        not Summable_p R_p.                 (10)
```

Define the protected residual cost

```text
E_p=R_p O(log p,log p).                                   (11)
```

Equations `(9)`--`(10)` give

```text
E_p>=c_Gamma R_p,       not Summable_p E_p.               (12)
```

Since every `E_p` is nonnegative, nonsummability is equivalent to the cofinal packet statement

```text
for every M in R, exists finite prime packet F,
M<sum_(p in F) E_p.                                      (13)
```

Combining `(3)` with `(6)` and `(12)` proves the source-class no-go:

> No family of reflection-even Gamma/Jacobi boundary corrections, regardless of growing rank or
> capacity, can make the Schur-cost-weighted prime residual trace cofinally bounded.

This is the positive survivor of the obstruction: odd Gamma covariance is a symmetry-protected
arithmetic energy channel.

## What changed at the Suzuki frontier

`SR-35` forced either growing Gamma/polar capacity or source-fixed principal-relative subtraction.
The explicit all-even Gamma/Jacobi capacity is now class-completely excluded: increasing the number
of even Jacobi modes cannot touch the exact odd floor `(6)`, while its actual prime weight diverges.

Two mechanisms remain:

1. a source-derived odd or parity-mixing boundary channel;
2. a signed principal-relative finite part that is not a positive Hilbert-space Schur projection.

The theorem is therefore genuine source-side progress, but not RH, not not-RH, and not a complete
Suzuki no-go.

## General law and significance

The containing topic is **symmetry-protected residual energy in renormalized Schur complements**:
if admissible counterterms live in one isotypic component of a unitary involution, the opposite
component is an exact lower floor independent of counterterm capacity. The arithmetic question is
then whether the protected sector is summable under source-forced weights. Here it is not.

The universal theorem is broader than the Gamma application: it applies to arbitrary Hilbert
spaces, arbitrary self-adjoint parities, arbitrary finite packets, and arbitrary even corrections.
The Gamma specialization is what makes it a Suzuki-lane advance rather than a generic parity
identity.

## Collision and literature audit

- **Corpus collision:** `(5)`--`(6)` already appeared at paper level in
  `gamma-damped-mobius-clock-critical-amplification.md`; it is not claimed new by itself.
- **Corpus collision:** the all-even Jacobi residue tower and `(10)` were already formalized; neither
  is claimed new here.
- **Advance:** the arbitrary-capacity quantifier in `(2)`--`(3)`, composed with the actual prime
  weights to obtain `(12)`--`(13)`, was absent from the searched corpus.
- **Primary literature:** Connes--Consani--Moscovici construct the semilocal Gamma/Jacobi measure and
  prolate framework, while Suzuki records the decisive even/odd split of localized Weil forms. A
  targeted search found no statement of the capacity-independent odd Schur floor composed with
  nonsummable prime Gamma conductor costs. Specialist novelty review remains required.

## Formalization map

`ParityProtectedSchurFloor.lean` proves:

- `inner_eq_zero_of_selfAdjointParity_even_odd`;
- `orthogonalBoundaryResidualEnergy_eq` and `_lower`;
- `parityBoundaryResidualNormSq_eq`;
- `parityBoundaryResidualEnergy_eq` and `_lower`.

`GammaEvenBoundaryParityNoGo.lean` proves:

- `integral_cos_semilocalArchimedeanGammaMeasure`;
- `integral_sin_mul_sin_semilocalArchimedeanGammaMeasure`;
- `gammaOddCovarianceKernel_pos` and `_self`;
- `gammaOddPrimeFloor_pos`;
- `gammaOddCovarianceKernel_log_prime_self_lower`;
- `gammaEvenBoundaryPrimeResidualCost_lower`;
- `not_summable_gammaEvenBoundaryPrimeResidualCost`;
- `exists_finset_gammaEvenBoundaryPrimeResidualCost_gt`.

All proofs are unconditional. No zeta-zero location, RH premise, numerical experiment, free
counterterm, `sorry`, `admit`, project axiom, `opaque`, or `unsafe` declaration is used.

## Formal audit

- direct `lake env lean` checks pass for both new leaf modules;
- targeted cached build
  `lake build GaloisForLFunctions.RHTower.GammaEvenBoundaryParityNoGo` passes `3588/3588`, compiling
  only the two new leaves and replaying one cached dependency with pre-existing linter warnings;
- repository formal lint passes with large-file warnings only;
- six capstone axiom surfaces contain only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-declaration and stale-process scans are clean.

## Gates

- [x] internal collision audit
- [x] primary-source literature audit
- [x] hostile odd-channel and signed-relative controls
- [x] universal paper proof
- [x] exact Gamma source proof
- [x] unconditional Lean 4 formalization
- [ ] independent specialist novelty review
- [ ] construct or refute source-derived odd/parity-mixing boundary
- [ ] construct or refute source-fixed principal-relative subtraction
- [ ] RH, not-RH, or whole-lane no-go
