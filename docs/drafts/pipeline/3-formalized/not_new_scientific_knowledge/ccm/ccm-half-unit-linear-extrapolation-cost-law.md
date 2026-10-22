# Linear extrapolation across the CCM half-unit seam costs a square-root power

- **ID:** `ccm-half-unit-linear-extrapolation-cost-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / NO-GO WITH POSITIVE DUAL, `[BRIDGE]`
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Date:** 2026-08-13
- **Module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMHalfUnitExtrapolationCost.lean`
- **Parents:** the invariant half-unit weighted-domain seam, positive-shift Euler--Möbius
  contractivity, and the rectangular subpower lower RH gate

## Statement

Let `h>0`, let `omega_1,...,omega_r>=0`, and let `a_1,...,a_r` be complex coefficients.  If the
linear extrapolator reproduces the half-unit exponential atom exactly,

```text
sum_j a_j exp(-omega_j h)=exp(h/2),                       (1)
```

then

```text
sum_j |a_j| >= exp(h/2).                                  (2)
```

More generally, if the relative reproduction error is at most `eta<1`,

```text
|sum_j a_j exp(-omega_j h)-exp(h/2)|
  <= eta exp(h/2),                                        (3)
```

then

```text
sum_j |a_j| >= (1-eta)exp(h/2).                           (4)
```

At aperture `n=exp(h)`, every scalar linear continuation from safe nonnegative shifts through the
missing half-unit therefore has condition number at least `n^(1/2)`.  This remains true when the
number of shifts and their locations depend arbitrarily on `h`.  In particular, cofinal-order
Richardson, finite-difference, polynomial, rational-linear, or quadrature extrapolation cannot turn
separate positive-shift absolute bounds into the `n^o(1)` lower loss required by the rectangular
subpower RH gate.

## Proof

Since every `omega_j>=0` and `h>0`,

```text
|exp(-omega_j h)|<=1.                                    (5)
```

Under exact reproduction, the triangle inequality gives

```text
exp(h/2)
 =|sum_j a_j exp(-omega_j h)|
 <=sum_j |a_j| exp(-omega_j h)
 <=sum_j |a_j|,
```

which is `(2)`.  Under `(3)`, the reverse triangle inequality gives

```text
|sum_j a_j exp(-omega_j h)|
 >=exp(h/2)-eta exp(h/2)
 =(1-eta)exp(h/2).
```

Combining this with the last two inequalities above proves `(4)`. `QED`

## Why growing interpolation order does not help

For each fixed finite aperture the shifted Euler source is analytic in the shift, so it is tempting
to sample many safe positive shifts and let the interpolation order grow with `h`.  The obstruction
is not Taylor remainder.  The atom which the half-unit conjugation must create already forces the
operator norm lower bound `(4)`.  Additional nodes can redistribute the coefficient mass but cannot
reduce it.

Consequently an estimate obtained by bounding the sampled shifted values separately loses at least
the full square-root factor.  The rectangular endpoint tolerates `exp(o(h))`, but `(4)` costs
`exp(h/2)` before any source error is estimated.

## Positive dual

The no-go leaves a strict positive specification.  A successful half-unit transfer must evade at
least one premise of the scalar estimate:

```text
safe shifted channels
  -> retain their coupled prime--polar / floor--Mobius covariance
  -> perform a non-diagonal or nonlinear source cancellation
  -> scalarize only after the half-unit atom has cancelled
  -> leave an exp(o(h)) one-sided boundary loss.           (6)
```

Thus cofinal order is still allowed, but only inside a source-coupled covariance, determinant,
relative trace, or compressed graph.  It cannot be used as a scalar extrapolation of separately
bounded shifted values.  This is the quantitative positive counterpart of the fixed-order
transport wall and the critical Möbius mass-escape theorem.

## Boundary

The theorem does not exclude a source-specific identity in which large interpolation coefficients
cancel against correlated prime and archimedean channels before norms are taken.  It excludes only
linear scalar continuation controlled by the sum of separate absolute-value estimates.  That
distinction is exactly where the surviving RH mechanism must live.

## Lean status

**Superseded, 2026-08-03.**  The theorem is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCM/CCMHalfUnitExtrapolationCost.lean`.  The previous decision
declined it as a "generic norm estimate"; the estimate is in fact the entire content of the no-go,
and formalizing it settles the gates independently of how the source-coupled extrapolator is later
defined — the statements quantify over *every* finite node family.

- `norm_sum_shift_le_coefficient_mass` — the damped atoms have modulus at most one, so the modulus
  of any combination is dominated by the coefficient mass.  Nodes are an arbitrary `Finset ι` with
  arbitrary nonnegative shifts, which is gate 1: node count and placement are unconstrained and may
  depend arbitrarily on `h`.
- **`halfUnit_exact_cost`** — equations `(1)`--`(2)`: exact reproduction forces
  `∑ ‖a j‖ ≥ exp (h/2)`.
- **`halfUnit_approx_cost`** — equations `(3)`--`(4)`: relative error at most `eta` forces
  `∑ ‖a j‖ ≥ (1 - eta) exp (h/2)`.
- **`halfUnit_exact_cost_sqrt`** — the multiplicative aperture form: at `n = exp h > 1` the cost is
  at least `√n`, via `exp (log n / 2) = √n`.
- **`halfUnit_cost_attained`** — **sharpness**: a single node at shift zero reproduces the atom
  exactly with coefficient mass exactly `exp (h/2)`.  This is the non-vacuity certificate: the
  admissible class is inhabited and the bound is attained, so the no-go is a genuine equality
  threshold rather than an empty hypothesis.
- **`tendsto_halfUnit_cost_atTop`** and **`exists_aperture_halfUnit_cost_gt`** — the cost is
  unbounded in `h`: beyond any prescribed condition number there are apertures at which every exact
  scalar extrapolator exceeds it.  This is the quantitative form of "growing interpolation order
  does not help".

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Nothing of the card's proved content is left out.  What remains open is the positive dual `(6)` — a
source-coupled non-diagonal cancellation — which is by construction outside the scalar class the
theorem excludes.

Current audit: direct Lean compile passed; all seven principal theorem declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`; targeted Lake build passed; module has no `sorry`,
`admit`, `axiom`, `opaque`, or `unsafe`; `RHTower.lean` imports it in `HEAD`. Repository-wide lint
remains blocked only by another agent's concurrent untracked `FactorFramedTensorJacobian.lean`, with
no CCM half-unit finding.

## Gates

- [x] arbitrary node count and node placement included
- [x] exact and approximate reproduction costs proved
- [x] square-root aperture cost identified
- [x] positive non-diagonal source obligation extracted
- [x] Lean: exact and approximate costs `(2)`, `(4)` unconditional for arbitrary node families
- [x] Lean: square-root aperture form and unbounded condition number
- [x] Lean: sharpness witness, so the no-go is not vacuous
- [x] Stage 3 promotion audit complete
- [ ] construct the source-coupled cancellation which evades scalar extrapolation
- [ ] prove its remaining boundary loss is subpower
- [ ] RH
