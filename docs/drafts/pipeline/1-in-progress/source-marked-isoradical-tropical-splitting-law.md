# Source-marked isoradical--tropical splitting law

- **ID:** `source-marked-isoradical-tropical-splitting-law`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; `[NOVELTY UNVERIFIED]`
- **Source:** operator-tail Gram geometry and source-marked Gibbs partitions
- **Statement:** A positive Gibbs deformation of a coefficient carrier preserves its support-stratified Gram radical at every temperature, while its normalized zero-temperature log partition converges to the tropical support radius of the marked source energy.

## Goal

Separate two geometries that are routinely conflated in positive HT carriers.  The coefficient
relations form a support-stratified differential matroid, whereas the source marking supplies an
independent asymptotic scale.  For positive base weights `a_p`, source energies `E_p`, and inverse
temperature `k`, set

\[
  w_k(p)=a_p e^{kE_p},\qquad
  Z(k)=\sum_p a_p e^{kE_p}.
\]

The target theorem has two simultaneous conclusions:

1. for every finite deletion and every coefficient vector, the weighted Gram energy has the same
   zero set for every `k` because every `w_k(p)` has the same positive support;
2. if `a` is positive and summable, `E_p\le R`, the values `E_p` approach `R` from below, and all
   Gibbs partitions converge, then

   \[
     \frac{\log Z(k)}{k}\longrightarrow R.
   \]

Thus the Gibbs family lies in a product chamber

\[
  \text{fixed coefficient radical}\ \times\ \text{tropical source radius}.
\]

This is a static constraint law, not a generative flow.

## RH audit

The Xi thermal corpus is a sharp application, not the subject of the theorem.  Its positive
finite-temperature Gram/KMS systems exist independently of RH and stay in one radical chamber.
The source-marked free-energy coordinate is the projective horizontal divisor radius; its
vanishing is equivalent to RH.  Therefore no RH route based only on positivity, temperature
variation, or finite KMS realizability can see the critical condition.  A viable route must prove
a source-derived asymptotic value relation, such as subexponential growth of the marked partition.

## Dual gate

- **Novelty:** The log-sum-exp/Laplace principle and invariance of a positive Gram radical under
  reweighting are classical separately.  The candidate new content is their exact product
  geometry for operator-tail coefficient carriers and its source-marked interpretation.
- **Significance:** If correct, it gives a positive classification law for all full-support Gibbs
  deformations of finite HT coefficient packets and cleanly locates which coordinate an arithmetic
  critical condition can inhabit.
- **Retirement condition:** Move to `not_new_scientific_knowledge` if the combined
  radical--tropical product theorem already appears in matroid, tropical, or thermodynamic Gram
  geometry under an equivalent formulation.

## Approach

1. Generalize the countable positive-partition argument in
   `XiThermalProjectiveFreeEnergyRadius.lean` to an arbitrary countable coordinate type.
2. Reuse the support-stratified radical theorem in
   `CofiniteTailGramPolarization.lean` for the Gibbs weights.
3. Package both conclusions in one theorem without an RH assumption or source-specific object.
4. Instantiate the abstract theorem on the Xi projective thermal system only as an application.
5. Run a focused literature audit for product decompositions of Gram-matroid strata and tropical
   zero-temperature support functions.

## Gates

- [x] 0 -> 1: well-posed, source-pure HT statement and proof plan
- [ ] 1 -> 2: complete paper proof with hypotheses minimized
- [ ] 2 -> 3: unconditional formal theorem, targeted build, lint, and axiom audit
- [ ] Novelty gate: independent literature audit of the combined geometry
- [ ] Significance gate: at least one non-zeta HT family gains a nontrivial classification

## Log

- 2026-07-14 -- Created after the operator-tail radical theorem was compared with the recent
  source--temperature/free-energy RH corpus.  Components are explicitly classified as classical;
  only the product geometry is a novelty candidate.
