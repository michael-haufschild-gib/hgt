# Complete odd positivity away from two polynomial moments

- **ID:** F1-MC
- **Stage:** 3-formalized
- **Type:** THEOREM; individually Lean-audited
- **Source:** [Joint first-fold payment](../1-in-progress/f1-joint-cubic-prime-payment.md)
- **Statement:** If a real odd C² test `F` is supported in `[-1/2,1/2]` and
  `∫xF(x)dx=∫x³F(x)dx=0`, then its complete Weil form satisfies `Q(F)≥∫F²/100`.

The conclusion pays the signed prime-2 term and the pole. The remaining first-stage problem is
the joint payment of the two low moments and their cross terms with this positive complement.

## Regional logarithmic spectrum

On `[-1,1]` put
`Tp(u)=∫(p(u)−p(v))/|u−v|dv` and
`J(G)=∫∫(G(u)−G(v))²/(2|u−v|)dudv`.
For a polynomial `p`, multiplication by position has the exact commutator

`T(up)(u)=uTp(u)+∫_{−1}ᵘp(v)dv−∫ᵤ¹p(v)dv`.

The Legendre primitive is `(Pₙ₊₂−Pₙ)/(2n+3)`. Bonnet's recurrence and this commutator,
starting from `TP₀=0` and `TP₁=2P₁`, give `TPₙ=2HₙPₙ`, where `Hₙ=Σ_{k=1}ⁿ1/k`.
Fubini gives `∫pTq=∫qTp` and `∫pTp=J(p)`; divided differences remove the diagonal
singularity. Orthogonality therefore yields `J(p)≥2Hₘ∫p²` whenever the polynomial
has zero moments below degree `m`.

For a continuous Lipschitz `G` orthogonal to degrees below `m`, choose a uniformly close
polynomial `p` and a finite Legendre span containing `p` and all degrees below `m`.
Let `ΠG` be the orthogonal projection onto this span. The eigenfunction identities and Fubini
give `J(G)=J(G−ΠG)+Σ2Hₙ‖ΠₙG‖²`. The first term is nonnegative, and the low projections vanish.
Pythagoras gives `‖G−ΠG‖²≤‖G−p‖²`, so
`J(G)≥2Hₘ(‖G‖²−‖G−p‖²)`. Uniform polynomial approximation proves the claimed gap.
All mixed energy terms are integrable because Lipschitz differences cancel the diagonal
singularity. For odd `G` with zero first and third moments, all moments below degree five
vanish. Hence `J(G)≥2H₅∫G²`, `H₅=137/60`.

## Gamma, prime and pole payment

Write `E=∫F²`, `C(t)=∫F(x)F(x+t)dx`, `D=E−C`, and `G(u)=F(u/2)`.
The exact regional/exterior split and scaling give

`∫₀¹D(t)/t dt ≥ (H₅+log2)E`,

because the exterior logarithmic potential on `[-1,1]` is
`log2−½log(1−u²)≥log2`.

Oddness and `|C|≤E` give `∫₀¹D=E`, `∫₀¹tD≤3E/4`, `∫₀¹t²D≤2E/3`.
Using `2ω(t)≥1/t+1/2−t/24−t²/16` and the unit exterior tail, exactly as in
[frozen cubic payment](../3-formalized/f1-rank-one-frozen-odd-payment.md), yields

`ΓE+J∞ ≥ [H₅−γ−logπ−5/96]E`.

Only prime `2` acts. Its shift exceeds half the support length, so its two supporting collars
are disjoint and `|C(log2)|≤E/2`. The prime cost is therefore at most `(log2/√2)E`.

The linear moment vanishes. On `|x|≤1/2`,
`|2sinh(x/2)−x|≤|x|³cosh(1/4)/24`, with `cosh(1/4)²≤16/15`.
Since `∫_{−1/2}^{1/2}x⁶=1/448`, Cauchy–Schwarz bounds half the squared sinh pairing by
`E/483840`. The cosh pairing vanishes by oddness. Thus

`Q(F)≥[137/60−γ−logπ−5/96−log2/√2−1/483840]E ≥ E/100`.

The last inequality follows from `γ<577216/1000000`,
`logπ≤log3+π/3−1`, the existing rational bounds for `log3` and `π`, and
`log2/√2<4902/10000`.

## Lean dependencies

- SP `LiouvilleOddWindowRefutationAndSelectiveFullPositivity`: Legendre recurrence,
  orthogonality and norms.
- LST `RegionalLogarithmicSpectrum`: `regionalLogOperator_legP`,
  `polynomial_eval_eq_legP_sum`, `regionalLogOperator_eq_integral` are kernel-checked,
  with standard axioms only.
- LST `RegionalLogarithmicGap`: `regionalLogEnergy_moment_gap` and
  `regionalLogEnergy_odd_two_moment_gap` prove the density extension and the exact `137/30`
  regional bound, with standard axioms only.
- LST `RegionalLogarithmicLagGap`: `regionalLogEnergy_eq_odd_principal` and
  `odd_two_moment_logarithmic_gap_unit` connect that spectrum to the full logarithmic lag count,
  with standard axioms only.
- LST `OddLogarithmicLagGap`: exact logarithmic pair/lag identities.
- AIP `SharedDerivativeEnergyAndGlobalAllocationSynthesis`: continuous odd high-lag bound
  `abs_autoCorrelation_le_half_of_le`; no extra smoothness premise is needed.
- WTZ `TheCubicMomentPaysTheFrozenOddComplement`: Gamma and hyperbolic remainder mechanisms.

## Lean conclusion

`WindowTowerOfSpecZ.TheFirstFoldIsPositiveAwayFromTwoOddMoments` proves
`stageForm_two_ge_of_odd_two_moments_zero` and `weilQuad_ge_of_odd_two_moments_zero`,
including support scaling and the exact identification of the complete form with stage two.
Both declarations have transitive axioms `[propext, Classical.choice, Quot.sound]` only.
All five changed proof modules passed individual `lake --old env lean` source checks;
finished modules are imported by their owning umbrellas. No positivity premise is assumed.

**Open:** the two low moments and their cross terms; this is not complete first-stage positivity.
