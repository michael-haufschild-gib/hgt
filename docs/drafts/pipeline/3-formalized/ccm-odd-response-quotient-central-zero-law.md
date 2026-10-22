# CCM odd-response quotient central-zero law

- **ID:** `ccm-odd-response-quotient-central-zero-law`
- **Stage:** 3-formalized
- **Status:** `[UNCONDITIONAL] [LEAN-FORMALIZED] [COFINAL RESPONSE ROUTE KILLED] [NOT RH]`
- **Parent:** `ccm-source-response-determinant-dichotomy.md`

## Theorem

A `2N+1` CCM clock truncation has reflection grading

```text
dim(Even) = N+1,                 dim(Odd) = N.
```

Write any grading-odd completed clock as

```text
A(e,o) = (B o, C e).
```

If `o_0` is the selected odd radical vector, `B o_0=0`, and the odd response construction cancels
the line `C(0,o_0)`, the induced operator on

```text
(Even x Odd) / C(0,o_0)
```

still has a nonzero zero mode.  Indeed `dim(Even)>dim(Odd)` forces a nonzero `e` with `C e=0`.
The class of `(e,0)` is nonzero modulo the odd line and is killed by the quotient operator.
Therefore its characteristic polynomial vanishes at zero.

Since centered `Xi(0) != 0`, no scalar normalization of a cofinal family of these odd-response
quotient characteristic polynomials can converge locally uniformly to `Xi`.  This remains true
for arbitrary scalar normalizers; holomorphy and nonvanishing are unnecessary.

The full-characteristic variant fails even before the parity argument: every pinned completion
retains its selected radical vector as a zero mode.  Hence full characteristic polynomials also
have a fixed zero at the origin and cannot converge to centered `Xi`.

## Consequence for CCM

Odd response is not a parity-free determinant route to RH.  Any CCM determinant program converging
to `Xi` must eventually use an even source channel, or introduce a non-scalar reduction that
removes every residual central zero and then separately prove divisor-tight convergence.  Thus
cofinal even-channel selection remains a necessary source theorem.

## Lean

- `formal/GaloisForLFunctions/RHTower/CCM/CCMFullCharpolyCentralZeroNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/CCM/CCMOddResponseQuotientCentralZero.lean`

Key declarations:

- `not_tendstoLocallyUniformly_XiC_of_central_zero`;
- `not_normalizedCharpoly_tendstoLocallyUniformly_XiC_of_nontrivial_kernel`;
- `exists_nonzero_kernel_ccmOddRadicalQuotientCompletion`;
- `ccmOddRadicalQuotientCompletion_charpoly_eval_zero`;
- `not_ccmOddRadicalQuotientCharpoly_tendstoLocallyUniformly_XiC`.

Verification:

- targeted `lake env lean` checks passed;
- targeted module builds passed (`8600/8600`, `8601/8601`);
- axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`;
- `scripts/formal_tools.py lint` passed.

## Do not retry

- full characteristic-polynomial convergence to centered `Xi` while a pinned zero mode remains;
- odd-response quotient convergence after cancelling only selected odd radical;
- nowhere-zero entire normalization as a way to remove a fixed polynomial zero.
