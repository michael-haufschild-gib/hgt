# Cubic log-moment Euler-admissible positive-shift separator

- **ID:** `cubic-log-moment-euler-admissible-positive-shift-separator`
- **Stage:** 3-formalized
- **Type:** SOURCE-ADMISSIBLE SEPARATOR / EXACT DENSITY RECEIVER / BRIDGE
- **RH used:** no
- **Computation used:** no
- **Parent:** `../../1-in-progress/zeta23-beyond-bandwidth-one-proportion.md`
- **Lean modules:**
  `../../../../../formal/GaloisForLFunctions/RHTower/XiWardCubicLogMomentHellingerCauchySeparator.lean`,
  `../../../../../formal/GaloisForLFunctions/RHTower/XiWardCubicLogMomentEulerSource.lean`

## Statement

For positive horizontal shifts, the cubic log-moment Gram

```text
C(a,b)=integral_0^infinity r^2
  (exp(-ar)-exp(-2ar))(exp(-br)-exp(-2br)) dr
```

has manifestly positive closed form

```text
C(a,b)=9ab(20(a+b)^4+6(a+b)^2ab+(ab)^2)
  / [4(a+b)^3(2(a+b)^2+ab)^3]
```

and exact diagonal

```text
C(a,a)=115/(864a^3).
```

Totalizing the kernel to zero when either displacement is zero excludes critical-line diagonal
multiplicity.  Since strict-right centered zeta depths satisfy `0<a<1/2`, every such copy has
horizontal charge greater than `115/108`; charge diverges as `a->0+`.

After tensoring with `h/[h^2+(gamma-eta)^2]`, every mixed packet entry is positive and

```text
sum_j m_j <= (108h/115) E_h.
```

Consequently

```text
(108h/115)E_h <= N/8  ==>  3N/4 <= N_0
```

whenever `N=N_0+2R` and the strict-right multiplicity `R` is bounded by the packet energy.

On the literal balanced primitive Euler carrier, `n=p^(e+1)` and `lambda=log n`.  The same
diagonal becomes

```text
C(lambda,lambda) Lambda(n)/n
 = 115/[864(e+1)^3 p^(e+1)(log p)^2].
```

It is positive and summable, with pointwise majorant

```text
(115/864) [1/(p(log p)^2)] (1/2)^e.
```

Thus cubic weighting removes the exact nonsummability obstruction of the scale-invariant
`log(9/8)` diagonal without losing, smoothing, or merely bounding away the submicroscopic zero
response.

## Lean certificate

Zero-side capstones:

- `integral_cubicLogMomentHellingerHorizontalKernel`
- `cubicLogMomentHellingerHorizontalKernel_eq_laplace`
- `cubicLogMomentHellingerHorizontalKernel_pos`
- `cubicLogMomentHellingerHorizontalKernel_self`
- `cubicLogMomentHellingerHorizontalKernel_self_ge`
- `finiteCubicLogMomentHellingerCauchyEnergy_ge_diagonal`
- `sum_multiplicity_le_finiteCubicLogMomentHellingerCauchyEnergy`
- `xiRight_card_le_finiteCubicLogMomentHellingerCauchyEnergy`
- `three_quarters_line_of_cubicLogMomentHellingerCauchyEnergy`

Source capstones:

- `xiGammaEulerPrimitiveCubicLogMomentWeight_le`
- `summable_xiGammaEulerPrimitiveCubicLogMomentWeight`
- `xiGammaEulerPrimitiveCubicLogMomentDiagonal_eq_weight`
- `summable_xiGammaEulerPrimitiveCubicLogMomentDiagonal`

Targeted builds pass.  Principal declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.

## Scope and open dependency

This result does **not** prove a new zeta-zero proportion.  It proves two previously incompatible
local requirements in one kernel:

1. uniform and submicroscopically increasing charge on every positive real zero shift, with
   critical displacement absent;
2. a finite positive diagonal on the complete balanced prime-power Euler source.

Still missing is a completed, source-faithful, dyadic-height Euler--Gamma trace identity or
inequality that identifies/dominates the zero-pair Gram by the finite source trace at the constant
required by the `75%` receiver.  Summability is the admission theorem for that construction, not
the construction itself.

## Scientific classification

The Laplace integral and convergence comparison are elementary.  No novelty claim is made for
them in isolation.  Route contribution is architectural: cubic log-moment weighting is the first
audited separator in this density branch to survive both finite-band collision and balanced Euler
source-norm tests.  Classified as a formal bridge pending a broader literature and parent-theory
audit.

## Log

- 2026-08-13 — paper proof completed; exact kernel, zero-side census, `75%` receiver, primitive
  Euler coefficient, and full prime-depth summability formalized in Lean 4.
