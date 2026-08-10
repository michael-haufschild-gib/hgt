# Time-reversal likelihood cocycle, observer contraction, and open-history law

- **ID:** ULF-TRLC-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** higher pivot from object defects to measured histories
- **Statement:** A path law and reversal generate a signed likelihood cocycle with positive mean; every observer contracts its mean exactly by conditional relative entropy, and a recurrent finite observer can hide an escaping history with linearly growing production.
- **Status:** [PAPER-PROVED] [FIELD-LEVEL SINGLE PRODUCER] [MEASURED-GROUPOID/STOCHASTIC-THERMODYNAMIC PARENTS] [NOT RH] [LEAN CERTIFIED]

## 1. Coordinate-free path-law setup

Let \(\Omega\) be a standard Borel space, let \(\Theta:\Omega\to\Omega\) be a measurable
involution, and let (P) be a probability measure equivalent to its reversed law

\[
P^\Theta=\Theta_*P.
\]

Define the time-asymmetry variable

\[
\Sigma=\log\frac{dP}{dP^\Theta}.
\tag{1}
\]

No metric, connection, curvature, or preferred coordinates occur in this definition.

## 2. Likelihood-cocycle theorem

### Theorem 2.1

The following identities hold almost surely:

\[
\Sigma\circ\Theta=-\Sigma,
\tag{2}
\]

\[
\boxed{\mathbb E_P e^{-\Sigma}=1,}
\tag{3}
\]

and

\[
\boxed{\mathbb E_P\Sigma=D(P\Vert P^\Theta)\ge0.}
\tag{4}
\]

Equality in (4) holds exactly when (P=P^\Theta).

### Proof

Put (f=dP/dP^\Theta). Applying the involution twice gives

\[
f(\Theta\omega)=f(\omega)^{-1},
\]

which proves (2). Also (e^{-\Sigma}=dP^\Theta/dP), so integration proves (3).
Equation (4) is the definition and positivity of relative entropy, with equality exactly at equality
of the two probability laws. QED.

The important point is that production is not a pointwise nonnegative additive function. Reversal
changes its sign; positivity appears only after averaging against the constitutive path law. This
escapes the theorem that every nonnegative additive function on a groupoid is zero.

## 3. Exact observer contraction and sufficiency boundary

Let (q:\Omega\to Y) be a measurable observer into a standard Borel space. Assume it is compatible
with reversals:

\[
q\Theta=\theta q
\tag{5}
\]

for an involution \(\theta:Y\to Y\). Put (Q=q_*P), so (Q^\theta=q_*P^\Theta), and define

\[
\Sigma_q=\log\frac{dQ}{dQ^\theta}.
\tag{6}
\]

### Theorem 3.1

One has the exact conditional formula

\[
\boxed{
e^{-\Sigma_q(q\omega)}
=\mathbb E_P\!\left[e^{-\Sigma}\mid q\right](\omega),}
\tag{7}
\]

and the data-processing inequality

\[
\boxed{
D(Q\Vert Q^\theta)\le D(P\Vert P^\Theta).}
\tag{8}
\]

If (P_y) and (P_y^\Theta) are regular conditional laws over the common observer map, then

\[
\boxed{
D(P\Vert P^\Theta)-D(Q\Vert Q^\theta)
=\int_Y D(P_y\Vert P_y^\Theta)\,dQ(y).}
\tag{9}
\]

Hence equality in (8) holds exactly when the likelihood ratio (dP/dP^\Theta) is (q)-measurable,
equivalently when (q) is sufficient for discriminating forward from reversed history.

### Proof

For every bounded measurable (g),

\[
\int g(q\omega)e^{-\Sigma(\omega)}\,dP(\omega)
=\int g(q\omega)\,dP^\Theta(\omega)
=\int g(y)\,dQ^\theta(y).
\]

This is precisely the conditional-expectation characterization of (7). Inequality (8) is relative
entropy data processing. Standard disintegration and the chain rule for relative entropy give (9),
and the equality criterion follows. QED.

The right side of (9) is a route-independent, coordinate-free measure of **hidden law history**.
It vanishes only for a sufficient observer, not merely for an observer whose output happens to
recur or close.

## 4. Closed recurrent observer with escaping produced history

Fix (p\in(1/2,1)), put (r=1-p), and let \(\xi_j\in\{+1,-1\}\) be independent with

\[
P(\xi_j=+1)=p,
\qquad
P(\xi_j=-1)=r.
\]

Let

\[
X_n=\sum_{j=1}^n\xi_j
\]

and observe only

\[
Y_n=X_n\pmod m
\qquad(m\ge2).
\]

Reverse an (n)-step path by reversing its order and flipping every increment. Its likelihood
production is

\[
\Sigma_n=X_n\log\frac p r.
\tag{10}
\]

### Theorem 4.1

The finite-state observer (Y_n) is recurrent and visits (0) infinitely often almost surely. If
\(\tau_j\to\infty\) are successive return times to (0), then almost surely

\[
Y_{\tau_j}=0,
\qquad
X_{\tau_j}\longrightarrow+\infty,
\tag{11}
\]

and

\[
\frac{\Sigma_{\tau_j}}{\tau_j}
\longrightarrow
(2p-1)\log\frac p r>0.
\tag{12}
\]

### Proof

(Y_n) is an irreducible finite Markov chain, hence every state is recurrent. The strong law gives

\[
\frac{X_n}{n}\to p-r=2p-1>0
\]

almost surely. Applying this along the unbounded return-time subsequence proves (11); multiplying by
\(\log(p/r)\) proves (12). QED.

Thus a closed recurrent observer history can conceal an open lifted history and strictly positive
asymptotic production. No covering-space metaphor is needed: all three statements are exact
probabilistic laws of one source measure.

## 5. Candidate field primitive

The theorem promotes a different ontology from objects-with-defects:

\[
\boxed{
\text{constitutive path law}
+\text{reversal}
+\text{observer statistics}.}
\]

Its shadows are forced, not independently named:

- time orientation: the involution \(\Theta\);
- signed local history: the likelihood cocycle \(\Sigma\);
- positivity: its mean relative entropy;
- observer no-go: strict data-processing loss;
- recurrence/open lift: Theorem 4.1;
- experimental completeness: the equality/sufficiency criterion in Theorem 3.1.

For a measured path groupoid whose law is multiplicative under concatenation, the likelihood ratio
is a multiplicative modular cocycle and \(\Sigma\) is additive. A (U(1))-valued path cocycle may be
combined with it into a \(\mathbb C^\times\)-valued polar history weight. This is the live higher
conjecture; it is not required for the theorems above.

## 6. Hostile scope

- Relative entropy, fluctuation identities, sufficiency, and data processing are established.
- Measured groupoids and modular cocycles are established.
- A generic path law can be chosen arbitrarily; source genesis remains open.
- Not every mathematical proof system has a natural probability measure or reversal.
- Differential hypertranscendence is not equivalent to positive entropy production.
- Complex phase is additional cocycle data unless one producer derives it.
- These results establish a strong field calibration, not a universal field or an RH theorem.

## Log

- 2026-08-09 — path-law/reversal single-producer theorem proved; positive cost reinterpreted as mean signed production.

## Lean certification status (2026-08-10) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle`
(wired into `HTGeometry.UniversalLawField`).

**§2, Theorem 2.1.**  `revLaw P Θ = Θ_*P` and `timeAsymmetry P Θ = llr P (revLaw P Θ)` are (1).
`comap_of_involution` shows a measurable involution generates the whole σ-algebra by comap, so
`toReal_rnDeriv_map` at `g = Θ` collapses to the identity conditional expectation; combined with
`neg_llr` this gives `timeAsymmetry_comp_involution`, equation (2).
`integral_exp_neg_timeAsymmetry` is (3), and `integral_timeAsymmetry_eq_klDiv`,
`integral_timeAsymmetry_nonneg`, `integral_timeAsymmetry_eq_zero_iff` are (4) with its equality
criterion `P = P^Θ`.

**§3, Theorem 3.1.**  `revLaw_map` is compatibility (5) transported along the observer, and
`exp_neg_timeAsymmetry_observer` is equation (7), obtained directly from mathlib's
`toReal_rnDeriv_map`.

Two lemmas mathlib does not have were built for (8) and (9):

- `absolutelyContinuous_map_iff_of_measurableEmbedding` and `klDiv_map_measurableEmbedding` —
  `klDiv` is invariant under a measurable embedding;
- `measurableEmbedding_graph` — the graph map `ω ↦ (q ω, ω)` of a measurable observer is a
  measurable embedding.

With `jointLaw`, `jointLaw_fst`, `klDiv_jointLaw` and mathlib's disintegration
(`Measure.disintegrate`) and chain rule (`klDiv_compProd_eq_add`), `klDiv_eq_map_add_cond` splits
the production exactly into the observed part plus a nonnegative conditional part; `klDiv_map_le`
is **equation (8), the data-processing inequality**, and `klDiv_map_eq_iff` is the sufficiency
criterion — the observer loses nothing exactly when the two disintegrations agree over the
observation.

For equation (9) in its stated integral form, the conditional divergence had to be identified with
an integral, which mathlib also lacks: `rnDeriv_compProd_right` proves
`(μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) = κ.rnDeriv η` a.e. and `klDiv_compProd_right` deduces
`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ y, klDiv (κ y) (η y) ∂μ`.  `klDiv_eq_map_add_integral` is then (9):

    D(P‖Q) = D(q_*P‖q_*Q) + ∫_Y D(P_y‖Q_y) d(q_*P)(y),

with `P_y = (jointLaw P q).condKernel y` the regular conditional law.

**§4, Theorem 4.1.**  The deterministic core: `exists_hit_of_tendsto` (a `±1` path that diverges
hits every level above its start), `le_of_hit`, `returns_unbounded` (the mod-`m` observer returns to
zero at arbitrarily late times while the path escapes), `tendsto_atTop_of_rate`,
`closed_observer_open_history`.  Production: `walkProduction` is (10),
`tendsto_walkProduction_rate` is (12) and `walkProduction_rate_pos` its strict positivity.
Increments: `walk`, `walk_step`, and `integral_increment` derives the mean `2p − 1` from the `±1`
law.  `ae_closed_observer_open_history` is Theorem 4.1 in full probabilistic form, obtained from
`ProbabilityTheory.strong_law_ae`.

Note that recurrence is obtained **without** any Markov-chain theory: a `±1` path with positive
drift hits every large integer, and each level is reached only after at least that many steps.

`#print axioms` on `timeAsymmetry_comp_involution`, `integral_exp_neg_timeAsymmetry`,
`integral_timeAsymmetry_eq_klDiv`, `integral_timeAsymmetry_eq_zero_iff`,
`exp_neg_timeAsymmetry_observer`, `klDiv_map_measurableEmbedding`, `measurableEmbedding_graph`,
`klDiv_eq_map_add_cond`, `klDiv_map_le`, `klDiv_map_eq_iff`, `rnDeriv_compProd_right`,
`klDiv_compProd_right`, `klDiv_eq_map_add_integral`, `returns_unbounded`,
`closed_observer_open_history`, `tendsto_walkProduction_rate`, `integral_increment`, and
`ae_closed_observer_open_history` reports only `propext`, `Classical.choice`, and `Quot.sound`.
