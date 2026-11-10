# Logarithmic residue collapse at the Liouville boundary

- **ID:** B130-Liouville-boundary-residue-collapse
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Interior pole persistence and boundary path](../3-formalized/bounded-analytic-gauge-paths-preserve-interior-poles.md).

## Target

For the explicit phases `u_p(z)=exp(iπ z^p)`, let
`r(t)=jointGaugeRegularization u (t,1)`, `0<t<1`.

The exact complex limit is

`log(1/(1-t))² r(t) → ζ(2) exp(-2γ)` as `t→1⁻`.

Moreover `r(t)→0`, but `|r(t)|/(1-t)^α→∞` for every `α>0`.
Consequently no actual joint pole regularization can be holomorphic
near `(1,1)`, even after dropping the common boundedness assumption
on the complex prime coordinates. The endpoint fibre itself has a
simple holomorphic zero; the obstruction concerns the joint family.
Only real spectral agreement near one is needed; its neighborhood may
depend on the real parameter.

## Paper proof

[PROVED HERE, Lean-certified] Write `δ=1-t`, `N=floor(1/δ)`,
`A(t)=Σ_p t^p`, and let `H(t)` be the normally convergent Euler
logarithm, so `r(t)=exp(H(t))`. Prime density zero implies `δ A(t)→0`:
if `p_n` is the increasing prime enumeration, then for each integer `K>0`, eventually
`p_n≥Kn`. Hence `A(t)≤J+1/(1-t^K)` for a fixed `J`, and the upper limit
of `δ A(t)` is at most `1/K`. Let `K→∞`.

Put `L_N=Σ_{p≤N} log((p-1)/(p+1))`. The logarithm is Lipschitz with
constant two on the Euler disk of radius one half. For `p≤N`,
`|exp(iπt^p)+1|≤πpδ`; for `p>N`,
`|exp(iπt^p)-1|≤πt^p`. Therefore

`|H(t)-L_N| ≤ 2π δ π(N) + (2π/N) A(t)`.

For small `δ`, `1/2≤δN≤1`. The displayed error tends to zero by
`π(N)/N→0` and `δA(t)→0`. These estimates control the complex logarithm,
so they also determine the limiting argument of the residue.

The exact finite product is

`exp(L_N)=Π_{p≤N}(1-1/p)² · Π_{p≤N}(1-1/p²)^(-1)`.

The first product times `log(N)²` tends to `exp(-2γ)`; the second
tends to `ζ(2)`. Moreover `δN→1`, hence
`log N / log(1/δ)→1`. Multiplying by `exp(H(t)-L_N)→1` proves the
claimed complex limit.

The limit constant is nonzero. Since `log(1/δ)→∞`, the residue tends
to zero. For each `α>0`, `δ^α log(1/δ)²→0`, which gives
`|r(t)|/δ^α→∞`.

If an actual joint regularization were holomorphic near `(1,1)`,
Euler-side uniqueness would identify its restriction to `s=1` with
`r(t)` for real `t<1` sufficiently near one. Continuity fixes its
endpoint value as zero. Holomorphy then bounds its magnitude by
`C(1-t)`, contradicting the preceding divergence with `α=1`.
This rules out joint regularization even with only one-sided real
parameter agreement.

## Lean declarations

`ArithmeticWeightTheory/GaugeDeformations/PrimeAbelCutoff.lean`:

- `tendsto_normalized_primeAbelMass_zero`.

`ArithmeticWeightTheory/GaugeDeformations/LiouvilleCutoffAsymptotic.lean`:

- `norm_boundaryExponent_sub_cutoff_le`;
- `tendsto_liouvilleCutoffProduct_normalized`.

`ArithmeticWeightTheory/GaugeDeformations/LiouvilleResidueCollapse.lean`:

- `tendsto_boundaryExponent_sub_cutoff_zero`;
- `tendsto_liouvilleBoundaryResidue_normalized`;
- `tendsto_liouvilleBoundaryResidue_zero`;
- `tendsto_liouvilleBoundaryResidue_div_power`;
- `liouvilleBoundary_no_joint_endpoint_regularization`.

All eight capstones have transitive axiom audits containing only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are present.
All three modules passed final direct Lean checks without warnings.
The arithmetic inputs are the existing Mertens product limit,
prime-density-zero consequence of PNT, and prime-square Euler product.

## B130 boundary

This quantifies the singular parameter transition and excludes a
joint analytic boundary specialization without a boundedness premise.
It does not supply the arithmetic Stepanov estimate or a purity family.
No external novelty claim.

[Quadratic collapse and a nonpolynomial joint limit — formalized](../3-formalized/quadratic-residue-collapse-with-a-nonpolynomial-joint-limit.md).
