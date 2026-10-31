# The prime residual retains adjunction energy

- **ID:** critical-rigidity-relative-prime-residual
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** The literal full prime residual of a growing conductor packet is controlled by its coefficient mass and exact adjunction energy, with separate logarithmic costs.

## Statement

Let `H=1+log Q`, `M=Σ_(m≤Q)a_m²`, `L=Σ_(m≤Q)(log m+tameDifferent m)a_m²`, and `A=Σ_(p≤Q)log p/(p−1)`.
For the actual residual `R_a(N,n)=Σ_(m≤Q)a_m ramanujanPrimeResidual(m,N,n)`, there is an absolute constant `C>0` such that, for `Q,N≥2`,

`Σ_(n≤N) R_a(N,n)² / log N ≤ [C H M + 38 A H L] / log N`.

Consequently the second term is at most `532 H²L/log N`. This retains the arithmetic energy; the previous absolute estimate replaces `L` by `2HM`.

## Proof

The exact source identity decomposes the residual into the common scalar Mertens error times the packet, minus its complementary prime-dilation tail, all multiplied by `n^(-1/2)`.

The scalar residual theorem in `SuccessorShellArithmetic.Conductor.ScalarPrimePacketNorm` bounds its harmonic square by `C H M`. For the tail, active-prime Cauchy–Schwarz costs `A`. Interchanging the finite prime and row sums exposes the region `N/n<k`. The harmonic interval estimate bounds each actual dilation jump there by

`[18H+log k] ||Δ_k a||²`.

The exact prime square identity and first logarithmic moment then give `19 H L`. Thus the complete complementary tail has harmonic square at most `19 A H L`. Remove the finite prime cutoff using the proved generator sum, with the horizon fixed. The elementary square inequality for scalar error minus tail gives the claimed factor `38` and an absolute scalar constant.

All source terms are the actual von Mangoldt function, divisor jet, and prescribed Euler constant. No complete-Weil positivity, cancellation hypothesis, or independent residual estimate is assumed.

## Scope

This strengthens the existing growing-packet prime residual estimate. It does not bound the Gamma–pole–shell remainder or replace adjunction energy by completed conductor energy.

## Lean

`CriticalScaleArithmeticRigidity/RelativePrimeResidual.lean`.
