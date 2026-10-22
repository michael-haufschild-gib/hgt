# The completed critical-Mellin error is a normalized Chebyshev potential

- **ID:** `ccm-completed-critical-mellin-chebyshev-potential-law`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinCompletedError`

## Statement

Let

```text
E(X)=sum_(k<=X) Lambda(k)-X
```

and, for `h>=0`, define the completed critical-Mellin prime-polar error

```text
R(h)=4sinh(h/2)-sum_(k<=exp(h)) Lambda(k)k^(-1/2).
```

Then

```text
R(h)
 =1-2/sqrt(exp(h))-E(exp(h))/sqrt(exp(h))
  -(1/2) integral_[1,exp(h)] E(t)t^(-3/2)dt.               (1)
```

Equivalently, with the critical-scale logarithmic error

```text
e(h)=E(exp(h))/sqrt(exp(h)),
```

the same value is the causal Volterra potential

```text
R(h)=1-2exp(-h/2)-e(h)-(1/2)integral_[0,h]e(u)du.          (1')
```

For `L>=0` and `x>=2L`, put

```text
D_L(x)=integral_[x-L,x]R(h)dh-integral_[x-2L,x-L]R(h)dh. (2)
```

Replacing `R` in `(2)` by the right side of `(1)` leaves `D_L(x)` unchanged.  Consequently the
all-epsilon one-sided subpower lower problem for `D_L(log n)` is equivalent, with the same tail and
the same constants, to the corresponding lower problem for the normalized Chebyshev potential in
`(1)`.

## Lean surface

- `criticalMellinCompletedError`
- `criticalMellinChebyshevPotential`
- `criticalMellinCompletedError_eq_chebyshevPotential`
- `criticalMellinNormalizedChebyshevError`
- `criticalMellinError_integral_exp_substitution`
- `criticalMellinChebyshevVolterraPotential`
- `criticalMellinCompletedError_eq_volterraPotential`
- `criticalMellinAdjacentBlock`
- `criticalMellinChebyshevAdjacentBlock`
- `criticalMellinAdjacentBlock_eq_chebyshevAdjacentBlock`
- `completedAdjacentBlock_subpowerLower_iff_chebyshevAdjacentBlock`
- `completedAdjacentBlock_subpowerLower_iff_volterraAdjacentBlock`

## Proof

The formalized Abel identity gives

```text
sum_(k<=X) Lambda(k)k^(-1/2)
 =2sqrt(X)-1+E(X)/sqrt(X)
  +(1/2) integral_[1,X] E(t)t^(-3/2)dt.
```

The exact polar identity gives

```text
4sinh(h/2)=2sqrt(exp(h))-2/sqrt(exp(h)).
```

Subtracting proves `(1)`.  The change of variables `t=exp(u)` proves `(1')`.  Pointwise equality on
the two nonnegative logarithmic blocks proves the integral identities and then the direct
quantifier equivalences.

## RH relevance

This theorem removes the separate square-root polar and von Mangoldt main terms from the open
estimate.  The remaining RH-bearing statement is a one-sided subpower lower bound for one fixed
causal Volterra--Haar filter of the normalized logarithmic Chebyshev error.  It does not prove that
bound.

The piecewise-linear Guinand--Weil identification with the rectangular Xi--Weil coefficient is a
separate formal bridge.  Suzuki's continuous screw-kernel formulation and Bombieri's localized
quadratic-form framework confirm that this bridge belongs to established parent theory; they do
not supply a Lean proof in the present codebase.

## Verification

- [x] target module elaborates
- [x] dedicated Lake target builds
- [ ] exact Guinand--Weil rectangular source identification formalized
- [ ] one-sided subpower lower estimate proved

## Parent literature

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- E. Bombieri, *Remarks on Weil's quadratic functional in the theory of prime numbers, I*,
  Rend. Lincei Mat. Appl. 11 (2000), 183--233.
