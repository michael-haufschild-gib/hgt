# Damped repair preserves the full L² convergence question

**Status:** formalized, two individual leaf builds and 19 public declaration
axiom audits passed. Only propext, Classical.choice and Quot.sound. Both leaves
wired into RHTower; authoritative lint passed with existing size warnings.
No full/umbrella build or numerical proof certificate.

**Frozen test [B], proved.** Put h(t)=1/t−1/(e^t−1),
R_N(t)=e^(−t)+Σ_(k≤N)μ(k)h(kt), and
D_(N,ε)(t)=e^(−t)+Σ_(k≤N)b_(k,ε)h(kt), where
b_(k,ε)=Σ_(d|k)μ(k/d)(−ε)^(d−1).
For every 0≤ε_N≤1/2 tending to zero,

||D_(N,ε_N)||_(L²(0,∞))→0 ⇔ ||R_N||_(L²(0,∞))→0.

The equivalence alone does not decide convergence. The separately formalized
[direct raw heat obstruction](chronological-raw-heat-obstruction.md) now excludes
both sides and every admissible vanishing damping schedule. The original
arbitrary bounded-array RH endpoint remains open.

## Dependency-closed paper proof

All finite residuals belong to L²: h is continuous on (0,∞) and
0≤h≤min(1,1/t), hence h²≤2/(1+t²). The exponential is square-integrable.
Positive dilation preserves integrability, and dilation by d≥1 contracts the
L² norm by the change of variables u=dt.

Exact finite divisor rearrangement, already formalized, gives

D_(N,ε)−R_N=Σ_(2≤d≤N)(−ε)^(d−1)
[R_floor(N/d)(dt)−e^(−dt)].

For N=0 both sides vanish. Every index floor(N/d) on the right is strictly
less than N. If all earlier raw norms are at most C≥0, Minkowski, dilation
contraction, ||e^(−t)||₂≤1, and the geometric tail give the positive estimate

||D_(N,ε)−R_N||₂≤2ε(1+C).

If raw norms tend to zero, they have one uniform bound C. The estimate and
ε_N→0 give damped convergence.

Conversely suppose damped norms tend to zero. Choose K so for N≥K their
norms are <1 and 2ε_N<1/4. Set C=2+Σ_(k<K)||R_k||₂. Strong induction proves
||R_N||₂≤C: below K this follows from the finite sum; afterwards the preceding
estimate and induction give ||R_N||₂≤1+(1+C)/4≤C. The perturbation estimate
now tends to zero uniformly in N, proving raw convergence. No arithmetic
cancellation estimate or RH hypothesis is used.

## Exact Lean map

Namespace `RHTower`, source directory `formal/GaloisForLFunctions/RHTower/`.

- `ChronologicalHeatL2`: membership of every actual finite residual in L²;
  `chronologicalL2Norm_eq_sqrt`; dilation contraction.
- `ChronologicalDampingRigidity.chronologicalDampedHeatError_perturbation`:
  the positive earlier-prefix estimate.
- `ChronologicalDampingRigidity.chronologicalVolterra_zero_convergence_iff`:
  the general scalar induction principle.
- `ChronologicalDampingRigidity.chronologicalDampedHeat_converges_iff_raw`:
  the actual full L² equivalence.

Module names before dots identify files; declarations themselves are directly
in namespace RHTower. One private finite-bound lemma is audited transitively.
No novelty claim is made for the general perturbation principle.

Audit artifacts: /tmp/chronological_damping_rigidity_axioms.txt,
/tmp/chronological_damping_rigidity_axiom_summary.json,
/tmp/chronological_damping_rigidity_lint.txt,
/tmp/chronological_damping_rigidity_index.txt.
