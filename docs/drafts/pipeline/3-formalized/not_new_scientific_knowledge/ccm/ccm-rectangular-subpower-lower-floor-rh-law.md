# A subpower lower floor for one rectangular family already proves RH

- **ID:** `ccm-rectangular-subpower-lower-floor-rh-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT SOURCE TARGET]`
- **Parents:** fixed-width rectangular completeness, the rectangular shifted-zeta carrier, and
  Landau's theorem for Dirichlet series with nonnegative coefficients

## Statement

Fix `L>0` and write

```text
Q_L(n)=Re Q_Xi(chi_((log n)/2,L),chi_((log n)/2,L)).       (1)
```

Let `alpha>=0`.  If there are `C>=0` and `N` such that

```text
Q_L(n)>=-C n^alpha                                        (2)
```

whenever `n>=N` and `L<=log(n)/2`, then every nontrivial zeta zero satisfies

```text
Re rho<=1/2+alpha.                                        (3)
```

Consequently each of the following source-side estimates implies RH:

```text
for every alpha>0, Q_L(n)>=-C_alpha n^alpha eventually;   (4)

Q_L(n)>=-exp(o(log n)) eventually;                        (5)

Q_L(n)>=-C(1+log n)^A eventually                          (6)
```

for any fixed finite `A`.  In aperture coordinates `h=log n`, any lower loss
`exp(o(h))` is therefore harmless.  The source construction does not need the constant floor used
in the strongest rectangular criterion.

The same conclusions hold with `Q_L(n)` replaced by the adjacent-block critical-Mellin readout
from `ccm-rectangular-critical-mellin-tent-floor-law.md`, because the remaining Gamma and fixed-tent
terms are uniformly bounded in `n`.

## Proof

Let

```text
S_L(n)=2 sum_(w in Z_right) m_w A_L(w)^2 n^w             (7)
```

be the multiplicity-exact right-divisor carrier.  The rectangular remainder theorem gives a
constant `K_L` such that

```text
|Q_L(n)-S_L(n)|<=K_L                                     (8)
```

on the admissible logarithmic samples.  Since `n^alpha>=1`, `(2)` and `(8)` imply

```text
S_L(n)>=-(C+K_L)n^alpha                                  (9)
```

eventually.

Define the nonnegative tail coefficients

```text
a_n=1_(n>=N)[n^(-alpha)S_L(n)+(C+K_L)].                  (10)
```

On its initial half-plane of absolute convergence, the ordinary Dirichlet series of `(10)` is

```text
sum_n a_n n^(-s)
 =2 sum_(w in Z_right)m_w A_L(w)^2 zeta(s+alpha-w)
   +(C+K_L)zeta(s)-P_N(s),                               (11)
```

where `P_N` is a finite Dirichlet polynomial.  Thus the power weight translates every right-zero
pole from `1+w` to

```text
s=1+w-alpha.                                             (12)
```

The scale-local Landau continuation argument used by the fixed-floor theorem applies verbatim to
the nonnegative coefficients `(10)`.  On the real axis above `1`, the shifted-zeta sum has no pole:
a real pole in `(12)` would give a real nontrivial zeta zero, which does not exist.  The added zeta
term has its first real singularity at `s=1`.  Hence Landau's theorem forces the abscissa of
convergence of `(11)` to be at most `1`.

The Xi-cancelled normal sum then crosses all shifted poles simultaneously.  At a right zero `w` of
multiplicity `m`, the numerator has exact order `m-1` while the Xi factor has order `m`; therefore
the pole in `(12)` is genuine and simple after multiplicities are combined.  Since the L-series of
the nonnegative coefficients is holomorphic on `Re s>1`, no such pole may lie there.  Therefore

```text
Re(1+w-alpha)<=1,
Re w<=alpha.                                             (13)
```

Functional-equation reflection gives `(3)` for every nontrivial zero.

If `(4)` holds, apply `(3)` for every positive `alpha` and let `alpha` decrease to zero.  Equations
`(5)` and `(6)` imply `(4)`, proving the remaining claims. `QED`

## Positive consequence of the critical mass-escape no-go

The direct Möbius coisometry loses a fixed fraction of its norm when the visible aperture obeys
`omega log X ->0`.  The theorem above shows that a successful proof need not recover a uniform
critical norm or a constant rectangular floor.  It is enough to construct a diagonal
shift--aperture estimate with any subexponential loss:

```text
positive-shift Euler--Möbius contraction
  -> completed prime--polar readout at h=log X
  -> lower loss exp(o(h))
  -> no positive transverse exponent
  -> RH.                                                  (14)
```

In particular, losses polynomial in `h`, losses caused by finitely many logarithmic derivatives,
and reciprocal powers of a diagonal regulator `omega=h^(-B)` remain admissible.  This is the
positive dual of the mass-escape obstruction: constant-fraction critical transport is unnecessary;
subexponential control of the distinguished zero-mean boundary readout suffices.

## Boundary

An absolute-value estimate for the dominant carrier is not enough: `(2)` is one-sided.  Nor may
the subpower floor be assumed through a holomorphic continuation or a positive Xi Bezoutian, since
either would already contain the conclusion.  The remaining theorem must derive `(4)` from the
prime--Gamma, Möbius, Sonin, theta, or prolate source before divisor-side continuation is used.

## Lean decision

The concurrently completed module `CCMRectangularSubpowerLowerGate.lean` formalizes the full
subpower corollary `(4)` and its observable bounded-remainder transport.  It uses the equivalent
power-correction normalization `S_L(n)+C n^alpha`, runs the scale-local Landau transfer, and proves

```text
riemannHypothesis_of_xiRectangularRightSubpowerLower
riemannHypothesis_of_xiRectangularWeilTailSubpowerLower.
```

`CCMRectangularPowerLowerZeroFree.lean` now also exposes the fixed-exponent quantitative conclusion
on the divisor carrier, without duplicating the power-corrected continuation machinery.
`CCMRectangularObservablePowerLowerZeroFree.lean` absorbs the bounded remainder and exposes the
literal source-facing endpoint `xi rho = 0 -> re rho <= 1/2 + alpha` for the actual observable
rectangular Weil values.

## Gates

- [x] bounded rectangular remainder absorbed into a power floor
- [x] power-shifted nonnegative Landau coefficient constructed on paper
- [x] power-corrected tail, Landau continuation, and subpower RH gate formalized concurrently
- [x] translated shifted-zeta pole locations identified
- [x] one-sided power floor converted to a horizontal zero-free region
- [x] subpower and polylogarithmic lower floors proved sufficient for RH
- [x] positive diagonal-regulator consequence extracted from the Möbius mass-escape no-go
- [x] fixed-exponent horizontal zero-free conclusion `(3)` formalized
- [ ] derive one source-defined subpower lower floor
- [ ] RH

## Lean status

`[FORMALIZED]` — verified complete. The three modules named in the "Lean decision" section above
exist, are wired into `formal/GaloisForLFunctions/RHTower.lean`, and every declaration in them is
unconditional with axioms exactly `[propext, Classical.choice, Quot.sound]` (18 theorems audited):

- `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularSubpowerLowerGate.lean` —
  `riemannHypothesis_of_xiRectangularRightSubpowerLower` and
  `riemannHypothesis_of_xiRectangularWeilTailSubpowerLower`, together with the power-corrected
  Landau coefficient, its Dirichlet-series continuation
  (`LSeries_xiRectangularPowerLandauCoefficient_eq_continuation`), the differentiability of the
  continuation on the Landau ball, and the left-summability transfer.  This is `(4)`, `(10)`–`(12)`
  and the scale-local Landau step.
- `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularPowerLowerZeroFree.lean` —
  `xiRightTransverseSup_le_of_xiRectangularRightPowerLower` and
  `xiRightCenteredZero_re_le_of_xiRectangularRightPowerLower`, the fixed-exponent quantitative
  conclusion `(3)`/`(13)` on the divisor carrier.
- `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularObservablePowerLowerZeroFree.lean` — the
  bounded-remainder absorption `(8)`–`(9)` and the source-facing endpoint
  `ξ ρ = 0 → re ρ ≤ 1/2 + α` for the observable rectangular Weil values.

All checked gates of this card are therefore Lean-certified; the two unchecked gates (derive one
source-defined subpower lower floor; RH) are route gates, not statements of this card.
