# Power comb tails detect the zero width

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A82's remaining power-tail extension; AGZ question 5.

## Target

For `0<a<1/2`, let
`P_a(N)=combForm([1,N], n↦(N/n)^a)/N`.
Classify its growth by the rightmost zeta zeros. In particular, prove that
convergence of every such power tail is equivalent to RH, and identify the
limit in the convergent range by the Mellin pairing of the two powers.
The primary theorem must be unconditional; no zero-free or analytic input
may be assumed without proving the corresponding implication.

Stronger target: for actual width `w=zetaZeroWidth`, every `0<a` with
`a+w<1/2` converges to the same zero pairing. The corpus proves
`XiZeroHalfPlaneBound w`; the prime-error abscissa theorem then gives
cancellation exponent `1/2+w`. The weighted profile is integrable because
`2a+(1/2+w-a)<1`. RH is the specialization `w=0`.
The zero pairing itself is summable without RH, using ξ's real-axis
nonvanishing. These strengthened proofs are in progress.

Exact width target: adjoining `0` to the positive subcritical convergence
parameters, their supremum should be `1/2-w`. Convergence implies
subpolynomial growth and hence `a+w≤1/2`; the strict converse above fills
every smaller positive parameter. This identifies the supremum without
assuming or deciding convergence at the boundary.

## Connection

The existing Laguerre-tail theorem reaches all logarithmic moments, but
its Mellin integral is established only to the right of the boundary.
A positive power probes beyond that boundary. The exact contact increments
have Dirichlet transform involving
`ζ(s+2a)·(-ζ′/ζ)(s+a)`.
A zero `ρ` with `Re ρ>1-a` contributes at `s=ρ-a`. In this region
`Re(ρ+a)>1`, so the Euler product excludes cancellation by `ζ(ρ+a)`. The archimedean and polar terms must be controlled separately
at the same normalization.

## Required proof

1. Exact arithmetic contact convolution for the literal power comb — proved.
2. Weighted Möbius inversion and the exact prime-error growth criterion — proved.
3. Polar and archimedean remainder bounds, and the normalized comb's exact
   zero-half-plane criterion — proved.
4. Actual convergence whenever `0<a` and `a+w<1/2`, including singular
   weighted sums — proved in `tendsto_powerCombTail_of_add_width_lt_half`.
5. Exact convergence radius and identification of the Mellin limit with
   the zero pairing — verification pending.

## Existing sources

- `AbsoluteGeometryOfSpecZ/TheLaguerreTailsOfTheCombTendToTheLiCoefficients`:
  unsmoothed logarithmic tails already solved; not a new contribution.
- `AbsoluteGeometryOfSpecZ/TheRowOfTheFlatTailHasTheMellinTransformOfTheZeros`:
  exact Mellin row identity to the right of the boundary.
- `HodgeTheoryOfAFixedPart/TheNormalFormOfThePairingOfTheDegreePoints`:
  literal contacts, counterterm and pole degrees.

The finite contact reduction is formalized in
`AbsoluteGeometryOfSpecZ.combForm_powerTailWeight_eq`.
`partialSumPowerBound_centeredContact_iff_zeroHalfPlane` classifies the
centered contact exponent `1-2a+σ` by `Re ρ≤1-a+σ`.
Reference and archimedean bounds are formalized; the literal-comb growth
theorem `powerCombTailGrowth_iff_zeroHalfPlane` is formalized.
`riemannHypothesis_iff_all_powerCombTails_subpolynomial` gives the exact
RH criterion for subpolynomial growth of all positive subcritical tails.
Actual convergence in the strict width range is formalized. The exact
radius and zero-side identification remain to be checked.

## Arithmetic reduction

For unscaled coefficients `c_n=n^(-a)`, the contact sum is
`2 Σ_{n≤N} n^(-2a) Σ_{d|n} Λ(d)d^a`. Subtract
`2ζ(1+a) Σ_{n≤N} n^(-a)`. The difference from the full comb form
should be `O(N^(1-2a) log N)` for `0<a<1/2`: the pole-product tail
costs `O(N^(1-2a))`, while absolute jet and counterterm bounds cost one
logarithm. This reduces the lower analytic obstruction to the summatory
Dirichlet coefficient
`n^(-2a)Σ_{d|n}Λ(d)d^a - ζ(1+a)n^(-a)`.

The convolution decomposition is
`C_a-ζ(1+a)w_a = w_(2a)*(w_a(Λ-1)) + H_a`, where
`H_a=w_(2a)*w_a-ζ(1+a)w_a`. Integral comparison and the tail of the
`(1+a)`-series give summatory `H_a=O(N^(1-2a))`.
Weighted Möbius inversion preserves strict growth exponents
`θ≥1-2a`; thus the contact defect has the same growth class as
`w_a(Λ-1)`. This avoids a separate complex pole argument for growth.

## Convergence reduction

Write `E_a(X)=Σn≤X n^-a-X^(1-a)/(1-a)`,
`T_a(N)=Σn≤N n^(-1-a)`, and `g_a(n)=n^-a(Λ(n)-1)`.
The finite polar term cancels the leading reference convolution. The
normalized form becomes its archimedean part minus twice the meshes of
`t^-2a Σn≤1/t g_a(n)` and `t^-2a E_a(1/t)`, plus
`2N^(2a-1)T_a(N)E_a(N)`.
The last term vanishes because `E_a` and `T_a` are bounded.
Under RH, the first mesh has an envelope `t^-(2a+β)` for some
`1/2-a<β<1-2a`; the second has envelope `t^-2a/(1-a)`.
Both profiles have finitely many jumps above every positive cutoff.
These reductions and the resulting convergence criterion are written;
Lean verification remains unfinished.

## Mellin identification

For `θ=1-2a` and `s=1-a`, the proposed integral evaluations are
`θ I_prime=-ζ′/ζ(s)-ζ(s)`,
`θ I_reference=ζ(s)+θ/(a(1-a))`, and
`archRow=ψ(s/2)-log π`.
The first follows from RH prime-error bounds and the existing energy-based
continuation theorem; the second from centered Euler power sums.
The archimedean profile splits as
`2(t^-a-1)/(1-t²)+1/(1+t)`, whose geometric-series integrals give a
Gauss digamma difference. Together they yield
`lim P_a=2ξ′/ξ(1-a)/(1-2a)=Σρ 1/((ρ-a)(1-ρ-a))`.
Lean proofs of this identification and the resulting equivalence are
written in `PowerTailCombZeroLimit` and its dependencies; compilation pending.
