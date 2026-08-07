# Mass–Xi balanced adjacent-prime difference summability

- **ID:** `mass-xi-balanced-adjacent-prime-difference-summability`
- **Stage:** 3-formalized
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `mass-xi-balanced-adjacent-prime-difference-ideal.md`, C38-A/B/C
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Exact theorem

Let `p_n` be the increasing prime enumeration, put

```text
t_n = LSeries.term(vonMangoldt, 1/2, p_n),
F_u(v) = stripFourier(xiMassAnalyticTest(a, sigma + iu), v),
B_n(u) = (t_(2n+1)/t_(2n)) A_(2n)(u) - A_(2n+1)(u),
A_n(u) = t_n F_u(log p_n).
```

For every `a>0` and `sigma>0`, `sum_n ‖B_n(u)‖` converges for every `u`, and

```text
‖sum_n B_n(u)‖
  <= 16 * (integral_R |x| exp(-sigma |x|) dx)
       * exp(-log(p_0)/4),
```

uniformly for all real `u`.

## Dependency-closed proof

The prime coefficient `t_n` is nonzero. Exact coefficient cancellation gives

```text
B_n(u) = t_(2n+1) * (F_u(log p_(2n)) - F_u(log p_(2n+1))).
```

C38-A, already proved for the actual mass integral, gives

```text
‖F_u(v)-F_u(w)‖ <= |v-w| J_sigma,
J_sigma = integral_R |x| exp(-sigma |x|) dx.
```

Set `lambda_n=log p_n` and `E_n=exp(-lambda_n/4)`. For `0<=x<=y`,

```text
y exp(-y/2) (y-x) <= 16 (exp(-x/4)-exp(-y/4)).
```

Indeed, `y<=4 exp(y/4)` follows from `1+y/4<=exp(y/4)`, while
`y-x<=4(exp((y-x)/4)-1)` follows from the same inequality. Multiplication and
`exp(-x/4)=exp(-y/4)exp((y-x)/4)` prove the display. Therefore

```text
‖B_n(u)‖ <= 16 J_sigma (E_(2n)-E_(2n+1))
          <= 16 J_sigma (E_(2n)-E_(2n+2)).
```

The last terms are nonnegative and their first `N` partial sum is exactly
`E_0-E_(2N)<=E_0`. Hence they are summable; comparison proves absolute
summability of `B_n(u)`, and the norm of its sum has the displayed bound.
No prime-gap theorem, PNT estimate, numerical input, or RH-strength assumption occurs.

## Hostile audit

- This is a genuinely cross-prime bounded direction, beyond valuation-only and Euler-power
  dilation masks.
- It does **not** control the scalar prime mask. Pair differences annihilate a local constant
  mode; their existence enlarges the bounded ideal but leaves its global cohomology class.
- New Hedenmalm frame results independently rule out finite and summably weighted diagonal
  coercivity by simultaneous prime-log recurrence. They support cross-prime coupling as the right
  representation, but do not supply the missing scalar estimate.
- Targeted corpus and primary-source searches found no exact mass-Fourier adjacent-prime theorem.
  Priority remains unverified; no novelty claim is made.

## C38-C: actual bounded prime mask and exact quotient

The initial paired atom uses the even coefficient `t_(2n+1)/t_(2n)`, which need not be bounded
without an extra argument. Reverse its normalization:

```text
U_n(u) = A_(2n)(u) - (t_(2n)/t_(2n+1)) A_(2n+1)(u)
       = (t_(2n)/t_(2n+1)) B_n(u).
```

Bertrand gives `p_(m+1) <= 2 p_m`. Since `log p_m <= log p_(m+1)` and
`sqrt(p_(m+1)) <= 2 sqrt(p_m)`, the critical weights obey

```text
|t_m| <= 2 |t_(m+1)|.
```

Thus the actual prime mask

```text
v_adj(p_(2n))   = 1,
v_adj(p_(2n+1)) = -t_(2n)/t_(2n+1)
```

satisfies `‖v_adj(p)‖ <= 2`. Its prime-indexed atom family is absolutely summable at every
`Re tau>0`; unconditional reindexing by `Nat.divModEquiv 2` proves exactly

```text
xiMassPrimeMaskedLayer(v_adj,a,tau) = sum'_n U_n(a,tau).
```

The C38-B estimate therefore yields the uniform bound

```text
‖xiMassPrimeMaskedLayer(v_adj,a,sigma+iu)‖
  <= 32 J_sigma exp(-log(p_0)/4).
```

For any prime mask `w`, scalars `b,c`, and critical-weight `ℓ¹` deviation

```text
sum_p ‖w(p) - b v_adj(p) - c‖ log(p)/sqrt(p) < infinity,
```

Lean proves:

```text
FixedLineBound(w) <-> FixedLineBound(w - b v_adj),
c = 0  -> FixedLineBound(w),
c != 0 -> (FixedLineBound(w) <-> ValuationOneFixedLineBound),
c != 0 -> (RH <-> FixedLineBound(w)).
```

So C38 is a genuine new cross-prime bounded direction, but its exact quotient theorem is also a
no-go: adjoining it to the critical-`ℓ¹` ideal leaves the primitive scalar class unchanged.

## Lean realization

- `formal/GaloisForLFunctions/RHTower/XiMassStripFourierLipschitz.lean`
- `formal/GaloisForLFunctions/RHTower/XiMassAdjacentPrimeDifference.lean`
- `formal/GaloisForLFunctions/RHTower/XiMassAdjacentPrimeMask.lean`
- `formal/GaloisForLFunctions/RHTower/XiMassAdjacentPrimeQuotient.lean`

All proofs are unconditional. Direct `lake env lean` checks and targeted module builds pass; the
modules are wired into `GaloisForLFunctions/RHTower.lean`.
