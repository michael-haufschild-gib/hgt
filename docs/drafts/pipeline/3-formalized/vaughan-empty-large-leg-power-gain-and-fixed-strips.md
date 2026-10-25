# A power gain for the centered empty large leg

- **ID:** vaughan-empty-large-leg-power-gain-and-fixed-strips
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** A fixed power gain for the centered both-large diagonal at square cutoffs is equivalent to a fixed zero-free strip, even though the literal both-large piece vanishes throughout that horizon.

## Exact statistic

At `U=V=N`, `T=N²`, the literal both-large piece is zero for every `n≤T`.
Its centered version is `-Z(ρ-A_N)² n`. Hence its diagonal energy is exactly

`G^c_33(N²;N,N)=Z²(ρ-A_N)^4 Σ_(1≤n≤N²) n/(n+1)`.

For `N≥1`, the final sum lies between `N²/2` and `N²`. Thus a bound

`G^c_33(N²;N,N) ≤ C (N²)^(1-2ε-δ)`, for some `δ>0`,

is equivalent up to constants to

`|ρ-A_N| ≤ C' N^(-ε-δ/2)`.

The already closed product-horizon little-o law does not provide this power rate.

## Converse to the tail estimate

Put `s=1+ε` and `F(N)=Σ_(d>N) μ(d)d^(-s)=ρ-A_N`.
The exact difference `μ(n)=n^s(F(n-1)-F(n))` gives

`M(N)=F(0)-N^s F(N)+Σ_(1≤n<N)((n+1)^s-n^s)F(n)`.

If `F(n)=O(n^(-ε-η))` with `0<η<1`, the last sum is bounded by a constant
times `Σ_(n<N)n^(-η)=O(N^(1-η))`; the boundary has the same bound.
Any larger `η` can first be weakened to a value in `(0,1)`.
The corpus equivalence `zetaZeroAbscissa_lt_one_iff_moebius_rate` then yields the strip.

Here the power increment bound requires no new analytic input. For `n≥1` and
`0<ε≤1`, concavity gives `(1+1/n)^ε≤1+ε/n`. Multiplication by
`(n+1)n^ε` and subtraction of `n^(1+ε)` gives

`0≤(n+1)^(1+ε)-n^(1+ε)≤(1+2ε)n^ε`.

The exact finite Abel identity is the specialization of `sum_mul_weight_eq` in
`HTGeometry/ShiftPartialSummation.lean` to the differences `F(n)-F(n+1)`.
The concavity inequality is `rpow_one_add_le_one_add_mul_self`; the required
power-sum bound is the already used `sum_rpow_neg_subcritical_le`.

Conversely, a strip gives `|M(N)|≤C N^β` for some `0≤β<1`. For `x≥N≥1`, this
implies `|M(x)|≤C N^(β-1)x`. Applying `abs_tsum_tail_rpow_le_of_linear` gives
`|F(N)|≤(2+1/ε)C N^(-ε-(1-β))`, hence the centered diagonal gains the fixed power
`δ=2(1-β)` in the horizon variable. Finite initial ranges can be absorbed into constants.

To recover a tail bound from the energy bound, use the lower bound `N²/2` for the
linear-sequence energy and `Z>0`. It yields
`(N^(ε+δ/2)|F(N)|)^4≤2C/Z²`; taking a fourth root supplies a uniform bound.
Weakening the resulting tail exponent to `η=min(δ/2,1/2)` gives the preceding converse.
This closes the proof of the exact equivalence for every fixed `0<ε≤1`.

## Significance and Lean status

Centering imports the infinite reciprocal density. At square cutoffs, the resulting
centered large-leg statistic can therefore encode the entire fixed-strip problem,
despite the corresponding literal finite sum being empty. This locates the exact
missing information in one explicit signed reciprocal-tail rate. It is an equivalence,
not a proof of that rate or a negative answer to Q-I.

The finite Abel identity, real-power increment bound, tail estimate, and strip/Mertens
equivalence have been checked in source. Search found related reciprocal-tail laws but
not this exact centered-empty-leg specialization; no external novelty claim is made.
The exact centered large-leg identity passed the complete scratch and standard-axiom
audit in `VaughanPacketsHaveAnExactResidualEnergyDensity.lean`; its producing check passed
and its final direct check passed. All seven finite Abel inversion, power increment,
explicit Mertens-to-tail rate, and tail-rate/strip equivalence targets passed their
producing check and transitive-axiom audits in
`VaughanReciprocalTailPowerGainsAreFixedStrips.lean`. Only standard axioms occur.
The module is wired; its final direct `lake --old env lean` check passed.

The finite energy identity and positive linear-energy comparison have no upper-half
restriction; only inverse-Abel inversion uses `ε≤1`. All four energy-rate declarations
in `TheEmptyVaughanLegDetectsAFixedStrip.lean` passed their scratch axiom audits and
final direct `lake --old env lean` check. Only standard axioms occur; the module is wired.
They prove the normalized quartic comparison, both rate transfers, and
`zetaZeroAbscissa_lt_one_iff_vaughan_square_energy_power`, expressed as decay
`O(N^(-δ))` of the energy divided by `(N²)^(1-2ε)`. This is exactly horizon saving
`δ/2`. The equivalence proves neither side and gives no new source estimate.
