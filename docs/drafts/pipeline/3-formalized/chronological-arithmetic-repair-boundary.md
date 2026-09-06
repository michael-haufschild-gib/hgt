# Chronological arithmetic repair: bounds and truncation boundary

**Status:** four Lean leaves built individually; all 76 public declarations audited.
Only propext, Classical.choice and Quot.sound occur; no added axioms or placeholders.
One private combinatorial helper is covered transitively by the public theorem audit.
All four modules are wired into RHTower; no umbrella or full build was run.
The original lint audit reported two unrelated unwired HTGeometry modules,
DigammaMittagLeffler and PerronRationalKernels. Those imports have since been
resolved; the subsequent authoritative lint audit passes with size warnings.
**Scope:** unconditional bridges and exact obstructions for specific repair operations.
The original bounded-array L² approximation, and hence an RH proof, remain open.
[Active compact notes](../1-in-progress/chronological-bounded-repair-attack.md).

**Subsequent result:** two more leaves prove full L² convergence equivalence of
damped and raw residuals, for every vanishing schedule in [0,1/2]. The exact
perturbation bound and reverse boundedness induction are now formalized.
[Rigidity certificate](chronological-damping-convergence-rigidity.md).

## Proven statements and paper proofs

Write q=e^(−t), h(t)=1/t−1/(e^t−1), and g(t)=1/(e^t+1).

1. **[BRIDGE] Nonlinear recovery.** The literal dyadic response satisfies
   g=2h(2t)−h(t). Starting at P₀=0, set P_(m+1)=g(1+P_m).
   The fixed-point identity g(1+q)=q gives q−P_m=qg^m by induction.
   Since 0≤g≤1/2 for t≥0, ∫₀∞(q−P_m)²dt≤4^(−m)/2→0.
   Integrability and the actual full energy limit are proved in Lean.
   This uses products of responses, not only arithmetic dilations.

2. **Exact coefficient obstruction.** For a formal series F with zero constant
   coefficient, its Lambert inverse is a=μ*coeff(F), since ζ*μ=1 in the
   arithmetic-function convolution ring. For every r≥2,
   [q^(r+j)]g^r=(−1)^j binomial(r+j−1,r−1).
   At every prime p≥r its Lambert inverse therefore has absolute coefficient
   binomial(p−1,r−1). These coefficients are unbounded. Lean excludes bounded
   **real** Lambert representations, not merely integer representations.
   This is a formal-series obstruction; it does not exclude L² approximation.

3. **Positive residue: sharp prefix classification.** The actual m-step response is
   P_m=q−q^(m+1)/(1+q)^m. Its Lambert inverse A_(k,m) satisfies
   A_(k,m)=μ(k) for k≤m; A_(m+1,m)=μ(m+1)−1 for m≥1; and
   A_(m+2,m)=μ(m+2)+m for m≥2. For the last identity, the Taylor coefficient
   at m+2 is m, and all proper divisors of m+2 lie at most m.
   Consequently |A_(m+2,m)|≥m−1. A truncation bounded by B with m>B+1 must
   stop at N≤m+1; throughout that truncation it is exactly a Möbius prefix,
   with at most the terminal correction −1. This classifies what survives
   direct polynomial repair followed by truncation.

4. **[BRIDGE] Damped infinite-depth repair.** The fixed point
   F_ε=g(1+(1−ε)F_ε) is F_ε=q/(1+εq). Its formal Lambert inverse is
   b_(n,ε)=Σ_(d|n)μ(n/d)(−ε)^(d−1). For 0≤ε<1, absolute values and the
   injectivity of d↦d−1 on positive divisors give
   |b_(n,ε)|≤Σ_(j≥0)ε^j=1/(1−ε). Thus one fixed bound 2 works for every n
   and 0≤ε≤1/2. Separately q−F_ε=εq²/(1+εq), so its full squared L² error
   is at most ε²/4. This bound and its sequence limit are proved in Lean.

5. **The exact finite remainder.** Define R_N=q+Σ_(k≤N)μ(k)h(kt) and
   D_(N,ε)=q+Σ_(k≤N)b_(k,ε)h(kt). Finite divisor rearrangement gives
   D_(N,ε)(t)=q−Σ_(d≤N)(−ε)^(d−1)e^(−dt)
   +Σ_(d≤N)(−ε)^(d−1)R_floor(N/d)(dt).
   Lean proves this for the literal h, every N, ε and t. The rational-response
   estimate in item 4 does not bound the final sum. Its d=1 term is R_N.

## Source and verification map

All declarations are in namespace `RHTower` under
`formal/GaloisForLFunctions/RHTower/`:

| Leaf | Main audited statement |
|---|---|
| ChronologicalFermiRepair | chronologicalFermiRepairEnergy_tendsto |
| ChronologicalLambertRepair | chronologicalFermiPower_no_bounded_real_Lambert_representation |
| ChronologicalRepairCoefficientBoundary | chronologicalRepairArithmetic_bounded_prefix_classification |
| ChronologicalDampedRepair | chronologicalDampedArithmetic_uniform_bound; chronologicalDampedResponseEnergy_bound; chronologicalDampedHeatError_exact_remainder |

The ingredients are geometric series, divisor inversion, binomial coefficients,
and ordinary integral estimates. No priority claim is made. The scalar RH
criterion is classical; see the [literature assessment](../1-in-progress/chronological-rh-recovery-interface.md).
No computation supplied any proof, and no numerical experiment was needed.

Audit artifacts: /tmp/chronological_arithmetic_repair_axioms.txt,
/tmp/chronological_arithmetic_repair_axiom_summary.json,
/tmp/chronological_arithmetic_repair_manifest.json,
/tmp/chronological_arithmetic_repair_lint.txt.
