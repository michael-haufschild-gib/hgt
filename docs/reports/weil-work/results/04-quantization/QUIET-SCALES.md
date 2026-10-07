# J: no arbitrarily late sublinear residual scales

For the specified `hW : WeilPositiveFull lam`, write μ for its canonical measure,
κ for the integer atomic floor, ν=μ−κ, and R for λ(n)=Λ(n) for every n≥2 together
with RH. The exact conjecture is

`R ∨ ∀ α<1, ∀ K∈ℝ, ∀ᶠ T→+∞, K T^α < ν([-T,T])`.

Unlike G, this excludes arbitrarily late quiet scales, even with unrestricted
growth between them. It still does not exclude the second alternative. H
(source degeneration) remains open: the near-null/exposed-point results control
the deviation from Λ and cannot supply a near-null sequence for arbitrary λ.
The critical Gamma/pole boundary b≤a also leaves the constant density term free
when a=b=1. No source degeneration theorem is claimed.

## Attack before proof

Internal deep searches found G's global power receiver, finite-remainder
rigidity, and general conditional phase receivers. None of the inspected
statements allows arbitrarily late isolated quiet scales. Monotonicity alone
does not upgrade G: a cumulative function can have long plateaux separated by
large jumps, with unbounded power ratios and arbitrarily late small ratios.

[Booker, Definition 1.3 and Theorem 1.6](https://arxiv.org/pdf/1308.3067)
assumes discrete support and only finitely many noninteger multiplicities;
its o(T) criterion concerns the whole spectral datum. Neither the integer
floor nor ν has been proved to form a separate L-datum. That parent cannot
be applied to ν. Its ordinary converse also needs these unpaid premises.
No exact or stronger applicable theorem was located; this is not a complete
novelty certification. The localization estimates below are classical.

Verdict: **SURVIVES PRELIMINARY ATTACK**. Scientific novelty provisional.
Failure would reveal a source whose resonant arithmetic residues survive
despite arbitrarily long intervals of small cumulative phase variation.

## Closed paper proof

Assume the second alternative fails. Enlarging its exponent and constant,
there are 0<α<1, K>0 and T_j→∞ with ν([-T_j,T_j])≤K T_j^α.
Set U_j=T_j/2, discarding initial U_j<1. Let C(x)=ν((0,2x]); then C is monotone,
C≥0 and C(U_j)≤K 2^α U_j^α. Let C_U(x)=min(C(x),C(U)). On 1≤x≤U it equals C(x);
everywhere it is bounded above by C(U), and C_U(1)=C(1).

For each m≥1 use the already proved actual remainder
d_m(ε,t)=Φ(t)k(2t,ε+im)−a_mρ_m(ε+im,t). Its signed primitive obeys, for any
0<p≤1, 0<ε≤1 and b≤−1,

`|ε∫_{t≤b} d_m(ε,t)dt| ≤ A_{m,p} ε^(1−p) exp(b δ)`, δ=ε/|ε+im|.

All actual traces and remainders are measurable and integrable on the stated
sets. The bounded-phase layer-cake estimate gives

`|ε∫_{t≤−1} exp(iβ C_U(−t)) d_m(ε,t)dt|
 ≤ |A_{m,p}| ε^(1−p) [1+|β|(C(U)−C(1))]`.

For precision, apply the existing profile theorem with
φ(x)=1_{x≤C(U)}. Its integral over x>C(1) is C(U)−C(1). For x>C(U) the
superlevel set is empty, so no finite least upper bound b meets that theorem's
premise. For x≤C(U), exp(bδ)≤1. The required weighted integrability follows
from boundedness of C_U(−t)−C_U(1) on t≤−1. Thus no global growth of C is used.

The source's pointwise N=1 bound gives a constant D_m independent of ε∈(0,1]
such that, for t≤−1,

`|d_m(ε,t)| ≤ D_m(1+|t|) exp(−2δ|t|)`.

Since 1≤exp(δx) and δx≤exp(δx) for x≥0,
`(1+x) exp(−2δx) ≤ (1+δ⁻¹) exp(−δx)`.
Integrating over t≤−U gives
`∫ |d_m| ≤ D_m(1+δ⁻¹)δ⁻¹ exp(−δU)`.
The two phases agree on −U≤t≤−1 and differ in norm by at most 2 elsewhere.
As ε/(m+1)≤δ≤ε≤1, the uncapped integral therefore has norm at most

`|A_{m,p}| ε^(1−p) [1+|β|(C(U)−C(1))]
 + 4D_m(m+1)^2 ε⁻¹ exp(−εU/(m+1))`.

Choose α<q<1 and 0<p<1−α/q. Put ε_j=U_j^(−q)/r for any fixed r>0.
Eventually ε_j∈(0,1]. The first term tends to zero because
α−q(1−p)<0. The second tends to zero because it is a constant times
U_j^q exp(−U_j^(1−q)/(r(m+1))). Exponential decay beats every real power:
substitute v=U_j^(1−q), so U_j^q=v^(q/(1−q)). This proves vanishing of
every actual twisted remainder along ε_j, simultaneously as a statement
for each fixed m and each fixed r. Constants need not be uniform in m or r.

The source residue and compact near-piece limits remain valid along every
positive ε_j→0. The exact decomposition already proved in PowerRigidity
therefore gives `c a_m M(ε_j/m)→2β_G`, where |c|=1 and β_G≠0. Apply the same
statement to m=1 along ε_j/m to get `c M(ε_j/m)→2β_G`. Multiplication by a_m
and uniqueness of limits force a_m=1 for every m≥1. The existing actual
coefficient receiver gives R, a contradiction. Hence the eventual lower
bound holds for every α<1 and K. No RH, continuity across the edge, spectral
representation, phase settlement or growth condition has been assumed in
the final alternative.

## Formal status

J is compiled in `WeilWorkQuantizationQuietScales.lean` as
`quantization_rigidity_or_residual_eventual_power`. Its only substantive input
is hW. The stronger one-sided cumulative version is
`quantization_rigidity_or_cumulative_eventual_power`.

All three changed leaves passed final direct `lake --old env lean -o ...`
audits without warnings or diagnostics. The two new leaves are wired into the
umbrella; no umbrella build was run. All nineteen declarations passed the scratch axiom audit, using only
`propext`, `Classical.choice` and `Quot.sound`; complete output is saved in
`quiet-scales-lean-audit.txt`.

- `WeilWorkQuantizationLocalPhase.lean`: bounded phase variation, absolute
  exponential tail, capping error, generic localization and the actual-source
  localized bound.
- `WeilWorkQuantizationPowerRigidity.lean`: generalized existing main-twist
  comparison to arbitrary convergent filters and fixed rescalings; original
  public statements remain as wrappers, avoiding duplicate contour proofs.
- `WeilWorkQuantizationQuietScales.lean`: power-scale limits, remainder
  cancellation on quiet radii, frequent-scale rigidity and final alternatives.

No source growth upper bound was proved. H/H2 and full WP04 remain open.
