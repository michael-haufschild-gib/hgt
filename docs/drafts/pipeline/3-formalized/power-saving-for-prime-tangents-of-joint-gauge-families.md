# Power saving for prime tangents of joint gauge families

- **ID:** B130-tangent-power-gap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Pole-residue curvature of actual holomorphic gauge families.

## Target

Under the bounded holomorphic prime-phase and joint regularization
conditions of the residue-curvature theorem, let `u_p'(0)=i a_p`.
There is `0<δ<1/2` such that

`Σ_p a_p² p^(-(1-δ)) < ∞`.

This strengthens finite residue energy `Σ_p a_p²/p<∞`: joint analytic
regularity forces a power saving in the tangent energy.

## Paper proof

Cauchy's estimate bounds every `|a_p|` by a common constant `K`. For
`m≥1`, set `A(p,m)=m a_p²` and `λ(p,m)=m log p`. These are nonnegative.
Unique factorization makes `(p,m)↦p^m` injective, and

`m a_p² ≤ (K²/log 2) log(p^m)`.

Thus the positive Dirichlet series `S(s)=Σ_{p,m≥1} A(p,m)e^(-λ(p,m)s)`
converges absolutely on `Re s>1`, by convergence of
`Σ_n(log n)n^(-σ)` there. Summing the geometric derivative gives

`S(σ)=Σ_p a_p² p^σ/(p^σ-1)²` for real `σ>1`.

The actual zeta fibre fixes `U(0,1)=1`, so `log U` is jointly holomorphic
near `(0,1)`. Put `H(s)=-∂²_t log U(0,s)` and
`Q(s)=(H(s)+conj(H(conj s)))/2`. The paired function `Q` is holomorphic
near one. The Euler-phase curvature identity gives `Q(σ)=S(σ)` on the
real interval immediately right of one. The identity theorem on the
intersection of a disk with `Re s>1` gives complex agreement there.

Suppose no real `σ<1` makes `Σ_p a_p² p^(-σ)` finite. Restricting the
nonnegative prime-power series to `m=1` shows that `S` diverges at every
real `σ<1`. Its real abscissa is therefore one. The holomorphic local
continuation `Q` contradicts Landau's singularity theorem. Hence a prime
energy exponent below one exists. Monotonicity permits choosing that
exponent in `(1/2,1)`; writing it as `1-δ` proves the claim.

## Corpus audit and boundary

`RHTower.gdSeries_no_continuation_at_abscissa` supplies the local
positive-series obstruction. `EulerFisherCurvature.lean` supplies
prime-power injectivity and logarithmically weighted zeta summability. `QuadraticGaugeRigidity.lean` treats individual gauge
defects on a half-plane; `PoleResidueCurvature.lean` gives tangent energy
at one. Searches found these inputs, not the tangent power-gap statement.

A second search for prime-phase derivative summability below one found
amplitude estimates and phase-series results, not this family theorem.
No external novelty claim.

## Lean result

`formal/GaloisForLFunctions/ArithmeticWeightTheory/GaugeDeformations/TangentPowerSaving.lean`
proves `gauge_tangent_power_saving` under exactly the actual family
conditions above. `primeTangentSeries_real` identifies the positive
prime-power series; `prime_energy_below_one_of_continuation` applies the
local Landau obstruction. The final direct Lean audit passed. All three
capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

No family is constructed and no arithmetic Stepanov bound follows from
this theorem alone.

## Further question

[Admissible tangents as isozeric directions](../3-formalized/admissible-gauge-tangents-are-isozeric-directions.md)
gives their exact characterization: bounded admissible velocities are
absolutely prime summable below one and integrate to explicit isozeric
linear phase flows.
