# CCM graded-index determinant balance law

- **ID:** `ccm-graded-index-determinant-balance-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL THEOREM / CCM COFINAL DETERMINANT OBSTRUCTION
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN] [CANDIDATE NOVEL] [NOT RH]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CCM/CCMGradedIndexDeterminantBalance.lean`

## Universal law

Let a finite complex vector space have grading `E directSum O`, and let an odd operator have block
form

```text
A(e,o)=(B o,C e).
```

Lean proves the exact central-kernel identity

```text
ker A = ker C directSum ker B
```

as a linear equivalence. Consequently

```text
dim ker A = dim ker C + dim ker B
          >= |dim E-dim O|.
```

Thus every grading imbalance is a protected central zero mode. This requires no self-adjointness,
positivity, displacement identity, rank-one correction, or chosen radical vector.

## Cofinal determinant theorem

Let `A_k` be any cofinal family of finite odd graded operators, and let `u_k(z)` be arbitrary
scalar normalizers. If

```text
u_k(z) charpoly(A_k)(z) -> XiC(z)
```

locally uniformly, then

```text
dim E_k = dim O_k
```

eventually. The proof uses only the protected zero at `z=0` and `XiC(0) != 0`; the normalizers
need not be holomorphic or nonvanishing.

For CCM ambient grading `(N+1,N)`, quotienting a graded radical with dimensions
`(rEven,rOdd)` leaves grading

```text
(N+1-rEven, N-rOdd).
```

The quotient balances exactly when

```text
rEven=rOdd+1.
```

Therefore determinant convergence to Xi forces radical parity index one eventually. If the
radical is one-dimensional, convergence forces

```text
rEven=1, rOdd=0.
```

The radical must be even. An odd one-dimensional radical leaves two units of grading imbalance,
hence at least two residual central zero modes.

## CCM correction

The arbitrary-radical boundary-channel trichotomy removes the finite metric-adjoint completion
obstruction. It does **not** remove the simple-even requirement from a determinant route to Xi.
Parity reappears as a protected grading index before any analytic convergence estimate. A viable
CCM determinant program must prove eventual radical index one and then prove divisor-tight reduced
determinant convergence.

This closes the parity-free quotient proposal. It does not prove RH or kill all CCM approaches;
the even balanced channel remains live.

## Universal active-even collapse

The displacement identity sharpens parity balance into boundary selection. Let `KEven` and `KOdd`
be the even and odd radical sectors. Suppose the clock `D` maps every `eta`-inactive vector of
`KEven` into `KOdd`, and is injective on that inactive sector. Then

```text
eta|KEven = 0  implies  dim KEven <= dim KOdd.
```

Hence radical index one forces an active even boundary vector:

```text
dim KEven = dim KOdd+1  implies  exists e in KEven, eta(e) != 0.
```

In CCM displacement form this follows directly from

```text
TOdd(D e) = -eta(e) beta.
```

Combined with cofinal Xi convergence, this holds eventually for arbitrary radical dimension.
Therefore odd-active and boundary-neutral completions cannot be divisor-faithful cofinally. The
three formal completion branches collapse to one surviving branch: balanced active-even response.
This does not prove convergence on that branch.

## Formal declarations

- `ccmGradedIndexOperatorKernelEquiv`;
- `ccmGradedIndexOperator_ker_finrank`;
- `ccm_evenImbalance_le_gradedIndexOperator_ker_finrank`;
- `ccm_oddImbalance_le_gradedIndexOperator_ker_finrank`;
- `ccmGradedIndexOperator_charpoly_eval_zero_of_dim_ne`;
- `eventually_ccmGradedIndex_balanced_of_normalizedCharpoly_tendstoLocallyUniformly_XiC`;
- `ccm_radicalParity_balance_iff`;
- `eventually_ccm_radicalParityIndex_one_of_normalizedCharpoly_convergence`;
- `eventually_ccm_oneDimensionalRadical_even_of_normalizedCharpoly_convergence`;
- `ccm_radicalIndex_one_forces_evenBoundaryActive`;
- `ccm_displacementRadicalIndex_one_forces_evenBoundaryActive`;
- `eventually_ccm_evenBoundaryActive_of_normalizedCharpoly_convergence`.

## Gates

- [x] exact kernel decomposition
- [x] sharp geometric-nullity lower bounds in both grading orientations
- [x] arbitrary-normalizer central-zero theorem
- [x] cofinal eventual-balance theorem
- [x] CCM radical parity-index specialization
- [x] one-dimensional radical forces even channel
- [x] arbitrary-dimensional radical forces active-even boundary channel
- [x] exclude odd-active and boundary-neutral branches cofinally
- [x] Lean check, module build, axiom audit, and lint
- [ ] prove the surviving balanced even-channel reduced determinant converges to Xi, or kill it
- [ ] RH or CCM death theorem
