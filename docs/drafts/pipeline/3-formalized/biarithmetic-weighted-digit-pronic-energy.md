# The exact pronic energy domain of signed digit rows

- **ID:** biarithmetic-weighted-digit-pronic-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../2-fully-proven/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** For arbitrary real base-five digit coefficients `x_l`, the ordinary readout has uniformly bounded pronic energy exactly when `sum_l x_l^2/5^l` converges.

## Uniform finite theorem

Write `E_x(N)=sum_(1<=n<N) W_x(n)^2/[n(n+1)]`, and put
`u_l=x_l/(sqrt(5))^l`, `q=1/sqrt(5)`. Complete digit blocks partition the
prefix at `N=5^(R+1)`. Their checked lower variance and upper digit estimates give

`(1/5) sum_(l<=R) u_l^2 <= E_x(5^(R+1))`,

`E_x(5^(R+1)) <= (64/5) sum_(M<=R) C_q(|u|)_M^2`.

The checked finite convolution theorem therefore yields the explicit upper bound

`(1-1/sqrt(5))^2 E_x(5^(R+1)) <= (64/5) sum_(l<=R) u_l^2`.

These bounds hold for every signed coefficient sequence, with constants independent
of the horizon and without a summability premise. Bounded energy bounds all partial
coefficient square sums; monotone summation gives convergence. Conversely convergence
bounds every complete prefix, and positivity bounds an arbitrary cutoff by the next
complete block, chosen with the exact natural logarithm.

This identifies the whole energy domain, not merely the geometric coefficient case.
The source-to-cofactor comparison and prime-tower payment statement are separate
theorems on the parent card. No external originality claim is made for the classical
digit-moment and geometric-convolution ingredients.

## Verification

Lean: `BiarithmeticGeometry/WeightedDigitPronicEnergy.lean`.
Main declarations: `fiveDigitPronicEnergyTo_complete`,
`fiveDigitPronicEnergyTo_complete_bounds`, and `bounded_fiveDigitPronicEnergy_iff`.

- [x] Dependency-closed finite inequalities and exact summability criterion.
- [x] Direct repository source check and umbrella import.
- [x] Three transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
