# Rough Subleading Polynomial Magnitudes Destroy Every Prouhet Escape

- **ID:** `rough-subleading-polynomial-taylor-magnitude-hypertranscendence`
- **Stage:** 3-formalized / needs scientific-novelty audit
- **Type:** THEOREM CANDIDATE / GENERAL HT LAW / ALMOST-SURE MAGNITUDE RIGIDITY
- **Scientific status:** `[PROVED HERE] [LEAN FORMALIZED] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** A bounded-density rough perturbation strictly below the curvature scale of `n^beta` almost surely destroys every logarithmic fixed-shift resonance, forcing hypertranscendence for every coefficient phase.

## Goal

Attack the genuine Prouhet boundary left by the polynomial ADE-degree floor. Smooth polynomial magnitudes permit high finite differences to decay to logarithmic size. The proposed law says that this escape is unstable: an asymptotically invisible rough layer restores all-order shift separation without changing the leading value, slope, or curvature scale.

## Theorem `[PROVED HERE]`

Fix real numbers

`beta>3`, `1<alpha<beta-2`.                                                 `(A)`

Let `(U_n)_(n>=1)` be independent random variables, each uniform on `[1,2]`, and put

`b_n=n^beta+n^alpha U_n`.                                                   `(1)`

Then, with probability one, every eventually full-support entire series

`f_theta(z)=sum_(n>=0) exp(-b_n)exp(i theta_n)z^n`                          `(2)`

is HT over `C(z)`, simultaneously for every phase sequence `(theta_n)`.

The perturbation is below the discrete-curvature scale:

`n^alpha=o(n^(beta-2))`.                                                    `(3)`

Consequently, almost surely,

`b_n~n^beta`, `Delta b_n~beta n^(beta-1)`,

and

`Delta^2b_n~beta(beta-1)n^(beta-2)`,                                      `(4)`

yet the HT conclusion is stronger than the current conclusion for the unperturbed profile `b_n=n^beta`, where only an ADE-degree floor is proved.

## Universal small-ball target

The central probabilistic claim is stronger than curvature separation. Almost surely, for every nonzero finitely supported integer family `(d_r)`,

`|sum_r d_r b_(n+r)|/log n -> infinity`.                                  `(LSS*)`

The target in the small-ball estimate includes the deterministic polynomial defect `sum_r d_r(n+r)^beta`; no moment cancellation assumption is needed.

## Universal small-ball lemma `[PROVED HERE]`

With probability one, `(LSS*)` holds simultaneously for every nonzero finitely supported integer family `(d_r)`.

### Proof

Fix one family and choose an offset `r_0` with `d_(r_0)!=0`. For all sufficiently large `n`, condition on every random variable in

`X_n:=sum_r d_r b_(n+r)`

except `U_(n+r_0)`. The remaining random term is

`d_(r_0)(n+r_0)^alpha U_(n+r_0)`,

uniform on an interval of length `|d_(r_0)|(n+r_0)^alpha`. The deterministic polynomial defect and all conditioned random terms merely translate this interval. Hence, for every integer `M>=1`,

`P(|X_n|<=M log n)`

` <= 2M log n/(|d_(r_0)|(n+r_0)^alpha)`                                   `(5)`

for all large `n`. Since `alpha>1`, the sum over `n` of the right side converges. The first Borel--Cantelli lemma shows that, almost surely, `|X_n|<=M log n` occurs only finitely often.

There are countably many integer stencils and countably many `M`. Intersecting their probability-one events, almost surely every fixed nonzero stencil eventually satisfies `|X_n|>M log n` for every prescribed `M`. This is exactly `(LSS*)`. No independence between the events at different `n` is used. `square`

## Deterministic polynomial-confinement lemma `[PROVED HERE]`

Fix a realization with every `U_n in [1,2]`. Let `D>=1`, let `c` range over a fixed finite set of source-sum shifts, and suppose that one active degree-`D` class contains a fixed-offset witness. For all sufficiently large `N`, every atom within `O(log N)` of the global minimum has degree `D`, belongs to the least active degree-`D` shift, and has indices

`k_i=floor(N/D)+O(1)`.                                                     `(6)`

### Proof

Uniformly over all realizations,

`b_n=n^beta+O(n^alpha)`,

`Delta b_n=beta n^(beta-1)(1+o(1))`,

`Delta^2b_n=beta(beta-1)n^(beta-2)(1+o(1))`,                              `(7)`

because every first or second finite difference of `n^alpha U_n` is `O(n^alpha)` and `alpha<beta-2`. In particular `b` is eventually increasing and strictly convex.

### 1. Degree separation

At degree `d`, convexity of the main term gives

`sum_(i=1)^d k_i^beta >= d((N+O(1))/d)^beta`

up to the harmless integer balancing error `O(N^(beta-2))`. The rough terms are nonnegative. A degree-`D` fixed-offset witness has valuation

`D(N/D)^beta+O(N^(beta-1))+O(N^alpha)`.

Since `d^(1-beta)>D^(1-beta)` for every `d<D`, every lower-degree atom exceeds the witness by a positive constant times `N^beta`. Degree-zero terms disappear at large coefficient indices.

### 2. Source-sum separation

Let `c_*` be the least active top-degree shift. Raising the source sum by one raises the exactly balanced main-term minimum by

`beta(N/D)^(beta-1)(1+o(1))`.                                             `(8)`

The fixed-offset witness in `c_*` exceeds its main-term balanced minimum by `O(N^(beta-2))` and has rough contribution `O(N^alpha)`. Both are `o(N^(beta-1))`. Since every competitor's rough contribution is nonnegative, no larger shift can lie within logarithmic distance of the minimum.

### 3. Offset confinement

Put `q=floor(N/D)` and write a degree-`D`, shift-`c_*` tuple as `k_i=q+x_i`, with `sum_i x_i=O_D(1)`. The fixed witness has bounded offsets.

For `D=1`, the source sum fixes the sole index, so confinement is immediate. Assume `D>=2`.

If `R=max_i|x_i|` is comparable to `q`, compactness and strict convexity of `t^beta` on the normalized simplex give

`sum_i k_i^beta-Dq^beta-beta q^(beta-1)sum_i x_i >= c_D q^beta`            `(9)`

along that case, after reducing the constant if necessary. This also covers a source index that stays bounded: the fixed-sum constraint forces another normalized index away from `1`.

If `R=o(q)`, Taylor expansion, with the common first moment removed, gives

`sum_i k_i^beta-Dq^beta-beta q^(beta-1)sum_i x_i`

` >= c_D q^(beta-2)sum_i(x_i-bar x)^2`                                    `(10)`

for all large `q`, where `bar x=D^(-1)sum_i x_i=O_D(1)`. Thus an offset of size `R` costs at least `c'_D q^(beta-2)R^2-O_D(q^(beta-2))` in the main term.

The rough contribution of the competing tuple is nonnegative, while the complete rough contribution of the fixed witness is only `O_D(q^alpha)=o(q^(beta-2))`. The witness's main-term imbalance is `O_D(q^(beta-2))`. Choose a fixed `R_0` large enough in (10). Every tuple with `R>R_0` then exceeds the witness by a positive constant times `q^(beta-2)=omega(log N)`; equation (9) is still stronger. This proves (6). `square`

## Proof of the theorem

Work on the probability-one event supplied by the small-ball lemma and fix an arbitrary coefficient-phase sequence. Equation (7) gives `b_n/n->infinity`, so (2) is entire.

Suppose it is DA. Mahler normalization gives a nonzero integer ADE of maximal dependent-variable degree `D`. Generic coefficient extraction, grouping, and balanced survival produce a nonzero coefficient identity at every sufficiently large `N`, with polynomially many nonzero integer weights and a fixed-offset top-degree witness.

The Archimedean tropical bend law forces two distinct grouped atoms whose valuations differ by `O_P(log N)`. The deterministic confinement lemma places both atoms in the same degree-`D`, least-source-sum, fixed-offset class. Their valuation difference is

`sum_r d_r b_(q+r)`                                                        `(11)`

for one nonzero finitely supported integer family `(d_r)`. Only finitely many bounded pairs occur on each residue class of `N modulo D`; after restricting to an infinite subsequence, the family `(d_r)` is fixed.

Condition `(LSS*)` makes the absolute value of (11) `omega(log q)=omega(log N)`, contradicting the bend law. Thus no ADE exists. Since the magnitude event was chosen before the phases and `(LSS*)` is phase-free, the conclusion holds simultaneously for every phase sequence. `square`

## Boundary attacks

1. **Bounded source indices are covered.** They force a compensating macroscopic index, and normalized strict convexity yields the `q^beta` gap (9).
2. **Roughness cannot subsidize imbalance.** Every rough summand is positive. In comparison with the witness, the worst possible subsidy is therefore only the witness's `O(q^alpha)` rough mass, already below one unit of main curvature.
3. **The conclusion is divergence, not nonvanishing.** Borel--Cantelli is applied for every integer multiple `M log n`; the countable intersection yields ratio tending to infinity.
4. **The perturbation is genuinely sub-curvature.** It does not alter the asymptotics of `b`, `Delta b`, or `Delta^2b`; it acts only on the arbitrarily deep fixed-shift relations that smooth asymptotics forget.

## Significance

The result identifies an instability law:

> Polynomial Prouhet resonances are not stable under sub-curvature roughness. Differential algebraicity would require structured, recurrent lower-scale cancellation; bounded-density microstructure almost surely destroys it.

This is a magnitude theorem, not a random-phase theorem. The same almost-sure magnitude profile forces HT for every adversarial choice of coefficient phases.

## Parent and novelty status

- **Generic and random power series:** located Baire-category and random-entire-function papers study boundary behavior, value distribution, zeros, or randomization of the full complex coefficients. They do not supply the quantifier order proved here: first choose almost every positive magnitude profile, then obtain HT simultaneously for every adversarial phase sequence.
- **Algebraically independent coefficients:** Gokhman's differential-transcendence theorem assumes algebraic independence of the coefficients. The present coefficients may all lie in highly dependent fields after phases are chosen; the obstruction is quantitative convolution isolation, not coefficient-field transcendence.
- **Perturbations of known HT functions:** Bank-type and Huang--Ng perturbation theorems start from a specified HT meromorphic function and constrain additive or multiplicative perturbations. Here no base HT function is used.
- **Lipshitz--Rubel gap theory:** the support is all of `N`, so support-spectrum gaps are absent.
- **Probabilistic parent:** the conditional bounded-density estimate and Borel--Cantelli lemma are classical. The candidate scientific content is their combination with Mahler normalization, balanced convolution confinement, and the phase-uniform Archimedean bend obstruction.
- **Preliminary verdict:** exact, equivalent, stronger, generic-series, random-entire, and proof-mechanism searches located no theorem implying this phase-uniform almost-sure magnitude law. Novelty remains unverified pending full specialist bibliography review and independent proof checking.

## Exact RH-route scope

The law further enlarges the class of phase fibers on which HT status is constant while divisors remain phase-sensitive. It excludes only RH implementations factoring through the forced HT bit, the leading polynomial magnitude asymptotic, or its first two discrete derivatives. Complete spectral, positivity, norm, Euler, and divisor criteria retain additional data and are not categorically excluded.

## Lean status

Unconditionally formalized in
`formal/GaloisForLFunctions/HTGeometry/RoughSubleadingPolynomialMagnitudeHypertranscendence.lean`.
The module proves the product-measure affine small-ball estimate, summable Borel--Cantelli
shift separation, deterministic polynomial confinement and ADE-resonance reduction,
finite-prefix invariance, phase-uniform hypertranscendence for every entire series with
the stated eventual magnitudes, the explicit entire phase family, and the profile,
first-difference, and second-difference asymptotic corollaries. The principal theorem
surfaces are
`ae_phaseUniform_hypertranscendental_roughPolynomialMagnitude`,
`ae_forall_phase_hypertranscendental_roughPolynomialPhaseFunction`,
`tendsto_roughPolynomialProfile_div_purePower`,
`tendsto_roughPolynomialFirstDifference_ratio`, and
`tendsto_roughPolynomialSecondDifference_ratio`.

## Gates

- [x] Exact candidate theorem and scale separation stated.
- [x] Complete unconditional paper proof.
- [ ] Parent-theory and literature novelty gates.
- [x] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Opened the sub-curvature roughness attack on the polynomial Prouhet boundary.
- 2026-07-11 — Proved the universal small-ball law, uniform polynomial confinement, and the almost-sure phase-uniform HT theorem; promoted to paper-proven with novelty unverified.
- 2026-07-16 — Formalized the complete unconditional theorem, its product-measure/Borel--Cantelli source, deterministic ADE-confinement bridge, explicit phase family, and all stated leading/slope/curvature asymptotics in `RoughSubleadingPolynomialMagnitudeHypertranscendence.lean`; exact-module build, direct file verification, and standard-axiom audit passed; promoted to stage 3.
