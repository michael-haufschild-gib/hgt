# Li Kernel Is Not Coefficientwise Positive

- **ID:** li-kernel-not-coefficient-positive
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Formalized companion:** `li-kernel-not-coefficient-positive-formalized.md`
- **Source:** `li-reciprocal-chebyshev-kernel`; `docs/consolidated/gpt/proof-route.md`
- **Statement:** In the reciprocal seam moment basis, every nontrivial Li Chebyshev kernel has a negative Taylor coefficient. Therefore Li positivity cannot be transferred to shifted square-test positivity by a coefficientwise-positive moment-kernel argument.

## Goal

Close a false bridge from the Li chart to the shifted `Q_0/Q_1` chart. The Li coefficients are positive under RH and are a zero-divisor chart, but their reciprocal-moment expansion is not a positive linear combination of the `T_k`.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: exact reciprocal-seam Chebyshev kernel, both displayed Taylor
  coefficients, both strict signs, and the coefficientwise-nonnegative contradiction certified
  in `RHTower.liReciprocalKernel_coefficient_sign_obstruction`.
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

From `li-reciprocal-chebyshev-kernel`, the FE-folded Li kernel is

```text
L_n(y) = 2 - 2 C_n((4-y)/(4+y)),
```

where `C_n` is the Chebyshev polynomial of the first kind. Write

```text
L_n(y) = sum_{k>=1} c_{n,k} y^k.
```

Use

```text
(4-y)/(4+y) = 1 - y/2 + y^2/8 + O(y^3).
```

Also

```text
C_n'(1)=n^2,
qquad
C_n''(1)=n^2(n^2-1)/3.
```

Substituting into the Taylor expansion of `2-2C_n(x)` at `x=1` gives

```text
c_{n,1}=n^2,
```

and

```text
c_{n,2}= -n^2/4 - n^2(n^2-1)/12
        = -n^2(n^2+2)/12.
```

For every `n>=1`, `c_{n,1}>0` and `c_{n,2}<0`. Hence no nontrivial Li kernel is coefficientwise nonnegative in the reciprocal seam moment basis.

For example,

```text
L_1(y) = 4y/(4+y)
       = y - y^2/4 + y^3/16 - ...
```

already alternates signs.

## Computation

Symbolic checks are archived in:

- `computations/2026-06-21-conway-li-kernel-not-coefficient-positive.py`
- `computations/2026-06-21-conway-li-kernel-not-coefficient-positive.txt`

## Route Consequence

A proof of shifted square-test positivity cannot be obtained from Li positivity by saying that Li coefficients are positive sums of reciprocal moments. The Li kernel is positive as a function on positive on-line atoms, but its expansion in the `T_k` basis has signed coefficients.

Thus the Li-to-`T_k` bridge must use the full rational kernel or another positivity-preserving argument. Coefficientwise moment positivity is a false shortcut.

## Log

- 2026-06-21 -- Conway: created as Step-12 follow-up to `li-reciprocal-chebyshev-kernel`.
- 2026-08-15 -- Codex: promoted after direct Lean certification of the literal kernel and its
  first two reciprocal-seam Taylor coefficients.

## Lean formalization

`GaloisForLFunctions.RHTower.LiReciprocalKernelCoefficientSign` defines the exact real kernel

```text
2 - 2 * T_n((4-y)/(4+y)),
```

where mathlib's `Polynomial.Chebyshev.T` is the first-kind polynomial denoted `C_n` above.  Its
Taylor coefficient is defined literally as `iteratedDeriv k L_n 0 / k!`; it is not a sampled or
finite-difference surrogate.

The closed declaration `RHTower.liReciprocalKernel_coefficient_sign_obstruction` proves for every
natural `n` with `1 <= n` the two displayed identities, `c_(n,1) > 0`,
`c_(n,2) < 0`, and failure of coefficientwise nonnegativity.  The companion certificate records
the `n = 1` rational identity and its `1, -1/4` coefficient instance.

Direct source checking and the targeted leaf build are green.  The two certificate declarations'
foundation audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
