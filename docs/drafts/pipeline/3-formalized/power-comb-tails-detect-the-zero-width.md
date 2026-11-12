# Power comb tails detect the zero width

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** A82's power-tail extension; AGZ question 5.

## Statements

For `0<a<1/2`, let
`P_a(N)=N^(2a-1) combForm([1,N], n↦n^-a)`.
This is the literal power comb, normalized per degree point.
Write `w=zetaZeroWidth` and let `R` be the supremum of `0` together
with the positive subcritical parameters for which `P_a` converges.

1. **Exact width:** `R=1/2-w`, without an analytic or zero-free premise.
2. **Actual limit:** if `0<a` and `a+w<1/2`, then
   `P_a(N) → Σρ 1/((ρ-a)(1-ρ-a)) = 2ξ′/ξ(1-a)/(1-2a)`.
   The sum runs over all ξ zeros with multiplicity.
3. **RH criterion:** RH iff every positive subcritical power comb converges;
   equivalently, every such comb converges to the displayed zero pairing.
4. **Zero-side summability:** the pairing is absolutely summable for every
   real `a<1/2`, independently of RH.

Convergence at a positive subcritical parameter implies `a+w≤1/2`.
The supremum equality does not require boundary convergence.
The [boundary extension](convergent-power-combs-exclude-boundary-zeros.md)
now excludes zeros on `Re ρ=1-a` whenever the comb converges, proves
divergence at an attained positive width, and identifies every convergent
endpoint limit with the same zero pairing. Ordinary convergence at an
unattained endpoint remains open.

## Proof

The exact contact convolution is
`w_(2a) * (w_a(Λ-1))` plus a reference remainder of summatory order
`N^(1-2a)`. Weighted Möbius inversion preserves the strict growth threshold.
Consequently the normalized comb's exponent `σ≥0` is equivalent to
`XiZeroHalfPlaneBound (1/2-a+σ)`. Convergence gives exponent zero,
hence `a+w≤1/2`.

The corpus supplies `XiZeroHalfPlaneBound w`. Its prime-error abscissa
theorem gives weighted summatory bounds with exponent arbitrarily above
`1/2+w-a`. When `a+w<1/2`, choose `β<1-2a` above that threshold.
The finite polar term cancels exactly, leaving two Riemann sums with
integrable envelopes and finitely many jumps above every positive cutoff.
The remaining endpoint error vanishes. This proves actual convergence
throughout the strict range; its supremum is therefore exactly `1/2-w`.

For `θ=1-2a` and `s=1-a`, the limiting integrals satisfy

`θ I_prime=-ζ′/ζ(s)-ζ(s)`,
`θ I_reference=ζ(s)+θ/(a(1-a))`,
`archRow=ψ(s/2)-log π`.

The prime identity combines ordered Abel summation with the existing
energy-based Mellin continuation. Centered Euler power sums give the
reference finite part. The archimedean profile splits as
`2(t^-a-1)/(1-t²)+1/(1+t)`; termwise integration of its positive geometric
series gives a Gauss digamma difference. The ζ terms cancel, and the
logarithmic derivative of ξ gives the displayed limit.

Finally, ξ has no real zeros. Its symmetrized logarithmic-derivative
expansion therefore applies at `1-a` without RH. Partial fractions identify
the zero pairing and prove its summability. The exact width characterization
then gives both RH equivalences.

## Lean

Namespace `GaloisForLFunctions.AbsoluteGeometryOfSpecZ`:

- `PowerTailCombGrowth`: `powerCombTailGrowth_iff_zeroHalfPlane`.
- `PowerTailCombLimit`: `tendsto_powerCombTail_of_add_width_lt_half`.
- `PowerCombTailConvergenceCriterion`:
  `powerCombConvergenceRadius_eq_half_sub_zeroWidth`,
  `riemannHypothesis_iff_all_powerCombTails_converge`.
- `PowerTailZeroPairing`: `summable_powerTailZeroPairing`,
  `powerTailZeroPairing_eq_logDeriv`.
- `PowerTailCombZeroLimit`:
  `tendsto_powerCombTail_zeroPairing_of_add_width_lt_half`,
  `riemannHypothesis_iff_powerCombTails_tendsto_zeroPairings`.

All supporting modules checked; final leaf check passed. Umbrella imports
include the complete chain. No ordinary convergence at an unattained
endpoint or RH proof is claimed.
