# Boundary-channel completion law for finite CCM divided-difference systems

- **ID:** `ccm-boundary-channel-completion-trichotomy`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL THEOREM / FINITE CCM ALGEBRAIC OBSTRUCTION CLOSURE
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Formal modules:**
  - `formal/GaloisForLFunctions/RHTower/CCMBoundaryChannelCompletion.lean`
  - `formal/GaloisForLFunctions/RHTower/CCMDividedDifferenceInstantiation.lean`
- **Manuscript:** `docs/drafts/manuscripts/ccm-boundary-channel-completion/main.tex`
- **Parent sources:** Connes--Consani--Moscovici, *Zeta Spectral Triples*;
  Connes--van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*.

## Result

For finite real matrices with

```text
T^T=T,  D^T=D,  Gamma^T=Gamma,  T Gamma=Gamma T,
Gamma eta=eta,  Gamma beta=-beta,
D T-T D=|beta><eta|-|eta><beta|,
```

let `K=ker T`. Exactly one boundary activity occurs:

1. `eta` is nonzero on `K`. A normalized `eta`-channel vector `e` exists, `beta` vanishes on all
   of `K`, and
   `A_E=D-|De><eta|` satisfies `T A_E=A_E^T T`, `A_E e=0`, and `A_E K subset K`.
2. `eta` vanishes on `K` but `beta` does not. A normalized `beta`-channel vector `o` exists,
   `eta` vanishes on all of `K`, and
   `A_O=D-|Do><beta|` satisfies `T A_O=A_O^T T`, `A_O o=0`, and `A_O K subset K`.
3. Both functionals vanish on `K`. Lean proves existence of `y` with `Ty=beta`; then
   `A_N=D+|y><eta|` satisfies `T A_N=A_N^T T` and `A_N K subset K`.

No positivity, kernel dimension, kernel parity, source estimate, zeta-zero statement, or RH premise
is used. The neutral source solution is a conclusion, not a supplied witness.

The common existence consumer is:

```text
ccmBoundaryChannelCompletion_exists:
  exists A, T*A=A^T*T and A(ker T) subset ker T.
```

## Concrete divided-difference connector

For finite injective clock coordinates `c_i`, source `b_i`, and diagonal `a_i`, define

```text
Q_ii=a_i,
Q_ij=(b_i-b_j)/(c_i-c_j)  for i!=j,
D=diag(c),  eta_i=1.
```

Lean proves, without a supplied displacement premise,

```text
Q^T=Q,
D Q-Q D=|b><eta|-|eta><b|.
```

For an involution `rho` satisfying

```text
c_(rho i)=-c_i,  b_(rho i)=-b_i,  a_(rho i)=a_i,
```

Lean constructs its reflection matrix `Gamma` and proves

```text
Gamma^T=Gamma,
Q Gamma=Gamma Q,
Gamma eta=eta,
Gamma b=-b.
```

Scalar shifts preserve the full package. Therefore
`ccmDividedDifferenceShift_boundaryCompletion_exists` proves that for every `mu`,
`T=Q-mu I` has a completed clock satisfying metric adjointness and full-radical preservation.
This is the formal CCM connector; no parity or multiplicity premise remains.

## Core proof mechanism

For `k in K`, displacement gives the radical transport identity

```text
T Dk=-beta <eta,k>+eta <beta,k>.
```

An active `eta` vector gives `TDe=-beta`; symmetry forces `beta` orthogonal to every radical
vector. The rank-one correction cancels both radical transport and metric-adjoint defect. The
`beta` channel is dual. If neither functional sees the radical, finite-dimensional dual
annihilator theory proves `beta in range T`, producing the neutral source solution.

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| radical transport | `ccmRadicalTransport` |
| normalized channel vectors | `ccm_exists_normalized_even_radical`, `ccm_exists_normalized_odd_radical` |
| source solution from radical orthogonality | `ccm_exists_source_solution_of_orthogonal_radical` |
| active incompatibility | `ccmBoundaryActive_mutuallyExclusive` |
| full trichotomy | `ccmBoundaryChannelCompletion_trichotomy` |
| completion existence | `ccmBoundaryChannelCompletion_exists` |
| divided-difference displacement | `ccmDividedDifference_displacement` |
| reflection package | `ccmReflectionMatrix_transpose`, `ccmReflectionMatrix_commutes_dividedDifference`, `ccmReflectionMatrix_constantBoundary_even`, `ccmReflectionMatrix_source_odd` |
| scalar-shift connector | `ccmDividedDifferenceShift_boundaryCompletion_exists` |

## What is deliberately not claimed

Current module pair does not formalize:

- specialized quotient Hilbert-space construction;
- quotient characteristic polynomial or real-rootedness;
- actual special-function definition of `Q_lambda^N`;
- simple-evenness of actual finite-Weil ground states;
- normalized determinant convergence to `Xi`;
- finite-Weil divisor transfer or RH.

Earlier draft claims about quotient spectra, parity-dual real-root determinants, and direct
application to the actual special-function matrix were removed. They remain research topics until
their own Lean declarations exist.

## Significance and exact frontier

The new universal law replaces a preferred simple-even kernel vector by an exhaustive
source/radical classification. It closes the finite **metric-adjoint completion** obstruction for
the whole reflection-graded divided-difference class.

It does not prove the stronger source-selected theorem needed for RH. Corpus frontier remains a
formal bridge from an actual special-function finite-Weil family and a selected boundary channel
to divisor-preserving cofinal convergence toward `Xi`. Neither simple-evenness nor finite-Weil
transfer is smuggled into this theorem.

## Novelty audit

Targeted corpus and primary-source searches found the published one-dimensional even correction
and odd/multiple-kernel examples, but no all-radical three-channel completion with neutral source
existence and a concrete divided-difference scalar-shift connector. External priority remains
unverified pending expert review.

## Gates

- [x] paper proof
- [x] universal trichotomy formalized
- [x] neutral source existence formalized
- [x] active incompatibility formalized
- [x] divided-difference displacement formalized
- [x] reflection/scalar-shift connector formalized
- [x] manuscript restricted to formalized claims
- [ ] independent mathematical audit
- [ ] external priority audit
- [ ] publication formatting/copy edit
- [ ] actual special-function `Q_lambda^N` connector
- [ ] cofinal divisor transfer

## References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- A. Connes, W. D. van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*,
  arXiv:2511.23257.

## Log

- 2026-07-22 -- Derived active-even, active-odd, and neutral rank-one corrections.
- 2026-07-22 -- Proved neutral source existence from dual annihilator theory in Lean.
- 2026-07-22 -- Formalized full trichotomy, incompatibility, and completion existence.
- 2026-07-22 -- Formalized divided-difference displacement, reflection, scalar-shift preservation,
  and concrete completion connector.
- 2026-07-22 -- Removed every manuscript claim lacking a Lean declaration.
