# Permutation-averaged first-failure, symmetric convolution tomography, and compact properness law

- **ID:** ULF-OFCM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** positive survivor of ULF-OFCM-1; ULF-CDM-2 defect conservation; compact Hausdorff moment source
- **Statement:** Uniformly permutation-averaged first-failure data over the complete moment tower reconstruct the unordered multiset of compact source laws, and the reconstruction map is a proper topological embedding.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [FOUR-ORGAN FUSION] [BRIDGE] [NOVELTY UNVERIFIED] [LEAN-PROVED]

## 1. Mechanism, not route

Ordered first-failure coordinates are ordinary hazard coordinates. The mechanism retained here is
different: erase the schedule deliberately, retain every failure position over the full response
tower, and ask whether the symmetrized formation still determines its sources.

The answer is yes. The proof is not a relabeling of finite hazard inversion. It passes through four
structurally different organs:

1. **formation/history:** a conserved first-failure ledger;
2. **symmetric algebra:** elementary coefficient reconstruction;
3. **analytic source testing:** Hausdorff moment determinacy;
4. **convolution/topology:** factorization in a zero-divisor-free measure algebra and compact properness.

The theorem is finite in source multiplicity but global in each source law.

## 2. Setup

Fix `k >= 1`. Let `P([0,1])` be the space of Borel probability measures on `[0,1]`
with its weak topology. For

\[
 \boldsymbol\mu=(\mu_1,\ldots,\mu_k)\in\mathcal P([0,1])^k
\]

define moment survivals

\[
 a_i(n)=\int_0^1 y^n\,d\mu_i(y),
 \qquad
 s_i(n)=a_i(n)^2,
 \qquad n\ge 1.
 \tag{PFF.1}
\]

For a permutation `sigma in S_k`, the unnormalized probability that the first failure occurs at
position `r` is

\[
 F_{\sigma,r}(n)
 =\left(\prod_{j<r}s_{\sigma(j)}(n)\right)
  \left(1-s_{\sigma(r)}(n)\right).
 \tag{PFF.2}
\]

Average away the schedule:

\[
 W_r(n)=\frac1{k!}\sum_{\sigma\in S_k}F_{\sigma,r}(n),
 \qquad 1\le r\le k.
 \tag{PFF.3}
\]

The observer is

\[
 \mathfrak W_k:\operatorname{Sym}^k\mathcal P([0,1])
 \longrightarrow [0,1]^{\mathbb N_{\ge1}\times\{1,\ldots,k\}},
 \qquad
 \{\mu_i\}\longmapsto (W_r(n))_{n,r}.
 \tag{PFF.4}
\]

It is well-defined because permutation averaging makes `(PFF.3)` invariant under relabeling the
sources.

## 3. Finite formation conservation and inversion

Write `e_r(s)` for the `r`th elementary symmetric polynomial in `s_1,...,s_k`, with
`e_0=1`.

### Theorem 3.1 -- symmetric first-failure identity

For every `s in [0,1]^k` and `1 <= r <= k`,

\[
 \boxed{
 W_r(s)=
 \frac{(k-r+1)e_{r-1}(s)-r e_r(s)}
      {k\binom{k-1}{r-1}}.}
 \tag{PFF.5}
\]

Consequently the full failure ledger conserves total failed mass:

\[
 \boxed{\sum_{r=1}^k W_r(s)=1-e_k(s).}
 \tag{PFF.6}
\]

The coordinates `W_1,...,W_k` recover all elementary coefficients recursively:

\[
 \boxed{
 e_r(s)=\frac{(k-r+1)e_{r-1}(s)
 -k\binom{k-1}{r-1}W_r(s)}{r}.}
 \tag{PFF.7}
\]

#### Proof

Fix a prefix set `A` of size `r-1` and a next index `i` outside `A`. Exactly
`(r-1)!(k-r)!` permutations have `A` as the unordered first `r-1` indices and `i` in
position `r`. Hence

\[
 W_r=\frac{(r-1)!(k-r)!}{k!}
 \sum_{|A|=r-1}\sum_{i\notin A}s_A(1-s_i),
 \tag{PFF.8}
\]

where `s_A=prod_{j in A}s_j`. The first part of the double sum is
`(k-r+1)e_{r-1}`. In the second part, each monomial `s_B` with `|B|=r` occurs once for
each of its `r` possible distinguished indices, hence contributes `r e_r`. Finally

\[
 \frac{k!}{(r-1)!(k-r)!}=k\binom{k-1}{r-1},
\]

which proves `(PFF.5)`. Equation `(PFF.7)` is algebraic rearrangement. Equation `(PFF.6)`
also follows directly: every ordered execution either survives all stages, with probability
`e_k`, or has a unique first failure. This includes all boundary cases `s_i=0` or `1`. QED.

## 4. Coefficient measures

Let `boxtimes` denote multiplicative convolution on `[0,1]`: it is the pushforward of a product
measure under `(x,y) |-> xy`. Put

\[
 \rho_i=\mu_i\boxtimes\mu_i.
 \tag{PFF.9}
\]

Then

\[
 \int x^n\,d\rho_i(x)=a_i(n)^2=s_i(n).
 \tag{PFF.10}
\]

For `0 <= r <= k`, define the elementary coefficient measure

\[
 E_r=\sum_{\substack{A\subseteq\{1,\ldots,k\}\\|A|=r}}
       \mathop{\boxtimes}_{i\in A}\rho_i,
 \qquad E_0=\delta_1.
 \tag{PFF.11}
\]

It has total mass `binom(k,r)` and moments

\[
 \int x^n\,dE_r(x)=e_r(s_1(n),\ldots,s_k(n)).
 \tag{PFF.12}
\]

By Theorem 3.1 the observed `W` recovers the right side for every `n >= 1`; total mass supplies
the zeroth moment. Hausdorff moment determinacy therefore recovers every coefficient measure
`E_r`.

This step is stronger than recovering the scalar unordered tuple `{s_i(n)}` separately at each
`n`: the `E_r` retain the compatibility of all moments as measures.

## 5. The absorbing-zero repair

The point `0` is absorbing for multiplicative convolution. Factoring directly in all signed
measures on `[0,1]` is therefore the wrong algebra. Remove the absorbing face before factorization.

Let

\[
 \alpha_i=\rho_i\!\restriction_{(0,1]}.
 \tag{PFF.13}
\]

Since a finite product is positive exactly when every factor is positive,

\[
 E_r\!\restriction_{(0,1]}
 =\sum_{|A|=r}\mathop{\boxtimes}_{i\in A}\alpha_i.
 \tag{PFF.14}
\]

Thus the recovered restrictions are the coefficients of the formation polynomial

\[
 \boxed{
 \mathcal F_{\boldsymbol\mu}(T)
 =\prod_{i=1}^k(T+\alpha_i)}
 \tag{PFF.15}
\]

in the convolution algebra of finite signed measures on `(0,1]`.

### Lemma 5.1 -- positive multiplicative measure algebra is a domain

The commutative algebra

\[
 \mathcal M((0,1]),+ ,\boxtimes
\]

of finite complex signed measures has no zero divisors.

#### Proof

Push a measure forward by `x |-> -log x`. This identifies multiplicative convolution on
`(0,1]` with additive convolution of finite signed measures on `[0,infinity)`. For such a measure
`eta`, define

\[
 \mathcal L\eta(z)=\int_0^\infty e^{-zt}\,d\eta(t),
 \qquad \operatorname{Re}z>0.
 \tag{PFF.16}
\]

This is holomorphic and

\[
 \mathcal L(\eta*\xi)=\mathcal L\eta\,\mathcal L\xi.
 \tag{PFF.17}
\]

If `eta*xi=0`, the product of the two holomorphic transforms vanishes on the connected right
half-plane. The ring of holomorphic functions on a connected domain is an integral domain, so one
transform vanishes identically.

The Laplace transform is injective here. Indeed, if `L eta(z)=0` for all real `z>0`, push `eta`
forward by `t |-> exp(-t)` and extend the resulting signed measure by zero at `0`. Its positive
integer moments vanish, and dominated convergence as `z` decreases to zero also gives vanishing
total mass. Polynomials are dense in `C([0,1])`; hence the signed measure, and therefore `eta`, is
zero. Thus one convolution factor is zero. QED.

### Lemma 5.2 -- monic linear factor uniqueness over a domain

Let `D` be a commutative integral domain. If

\[
 \prod_{i=1}^k(T+a_i)=\prod_{i=1}^k(T+b_i)
 \quad\text{in }D[T],
 \tag{PFF.18}
\]

then the multisets `{a_1,...,a_k}` and `{b_1,...,b_k}` are equal.

#### Proof

Evaluate at `T=-a_1`. The product `prod_j(b_j-a_1)` is zero, so the domain property gives
`b_j=a_1` for some `j`. Reorder, cancel the common monic factor `T+a_1`, and induct on `k`.
QED.

By Lemmas 5.1 and 5.2, the recovered polynomial `(PFF.15)` uniquely determines the multiset
`{alpha_i}`.

## 6. Restoring the source laws

Each `rho_i` is a probability measure. Its missing zero atom is determined by the positive mass:

\[
 \rho_i=\alpha_i+
 \left(1-\alpha_i((0,1])\right)\delta_0.
 \tag{PFF.19}
\]

It remains to undo the convolution square. This square root is unique in the present positive
compact source class.

### Lemma 6.1 -- unique positive convolution square root

If probability measures `mu,nu` on `[0,1]` satisfy

\[
 \mu\boxtimes\mu=\nu\boxtimes\nu,
 \tag{PFF.20}
\]

then `mu=nu`.

#### Proof

For every `n >= 0`,

\[
 \left(\int x^n\,d\mu\right)^2
 =\left(\int x^n\,d\nu\right)^2.
\]

Both moments are nonnegative, so their nonnegative square roots agree. Hausdorff moment
determinacy on `[0,1]` gives `mu=nu`. QED.

Applying Lemma 6.1 to every recovered `rho_i` recovers the unordered multiset `{mu_i}`.

## 7. Reconstruction theorem

### Theorem 7.1 -- permutation-averaged source tomography

For every finite `k >= 1`, the observer

\[
 \mathfrak W_k:\operatorname{Sym}^k\mathcal P([0,1])
 \longrightarrow [0,1]^{\mathbb N_{\ge1}\times\{1,\ldots,k\}}
\]

is injective.

Equivalently, if two `k`-tuples of compact source probability laws have identical uniformly
permutation-averaged first-failure coordinates at every positive integer response moment and every
failure position, then the tuples differ only by permutation.

#### Proof

Theorem 3.1 reconstructs all elementary moment sequences. Equations `(PFF.11)--(PFF.12)` and
Hausdorff determinacy reconstruct the coefficient measures. Restriction to `(0,1]`, Lemma 5.1,
and Lemma 5.2 reconstruct the positive parts of all convolution squares. Equation `(PFF.19)`
restores their zero atoms. Lemma 6.1 reconstructs the original probability laws. QED.

## 8. Fourth-organ prediction: global properness and stability

The theorem forces a topological consequence not used in its algebraic proof.

### Theorem 8.1 -- compact properness

The observer `mathfrak W_k` is a homeomorphism from
`Sym^k P([0,1])` onto a compact closed subset of the countable response cube. In particular it is
proper.

Consequently, if a sequence of averaged response arrays converges coordinatewise, then the
corresponding unordered source multisets converge weakly to the unique source multiset producing
the limiting array.

#### Proof

The probability space `P([0,1])` is compact metrizable in the weak topology. Its finite symmetric
product is compact Hausdorff. Every coordinate of `mathfrak W_k` is a polynomial in finitely many
continuous moment functionals, so `mathfrak W_k` is continuous. Theorem 7.1 makes it injective.
A continuous injection from a compact space into a Hausdorff space is a homeomorphism onto its
compact, hence closed, image. Properness and the sequential statement follow. QED.

For any compatible metrics, compactness also makes the inverse uniformly continuous. Thus there is
no hidden ill-posed sequence inside the fixed-multiplicity compact chart: response convergence
forces source convergence.

## 9. Exact fusion/conservation ledger

The construction supplies the requested field-level grammar:

\[
\begin{array}{c|c|c}
\text{organ}&\text{generated object}&\text{exact law}\\
\hline
\text{formation history}&W_r&\sum_rW_r=1-e_k\\
\text{symmetric algebra}&e_r&\text{triangular reconstruction }(PFF.7)\\
\text{analytic source}&E_r&\text{Hausdorff moment reconstruction}\\
\text{convolution law}&\prod_i(T+\alpha_i)&\text{domain factorization}\\
\text{topological admission}&\operatorname{Sym}^k\mathcal P([0,1])&\text{proper inverse}
\end{array}
\tag{PFF.21}
\]

This is one mechanism with conserved formation coefficients, not several route analogies.

## 10. Sharp boundaries and countermodels

1. **One response coordinate is insufficient.** At fixed `n`, `W_r(n)` recovers only the scalar
   multiset `{s_i(n)}`. Cross-moment compatibility is what reconstructs laws.
2. **The absorbing zero must be separated.** Factoring directly in measures on `[0,1]` ignores the
   zero-divisor pathology produced by the absorbing point. Restriction `(PFF.13)` and restoration
   `(PFF.19)` are load-bearing.
3. **Positivity is load-bearing only at the square-root step.** General signed convolution squares
   can have sign ambiguity. Probability moments select the nonnegative root.
4. **Compact support is load-bearing for unconditional moment determinacy and properness.** On an
   unbounded source space, moments need not determine a measure and the source moduli need not be
   compact.
5. **Fixed finite multiplicity is load-bearing.** No cofinal or countably infinite factorization
   theorem follows from this card; an infinite formation determinant needs new summability or
   renormalization data.
6. **The theorem does not restore schedule.** It reconstructs the unordered source multiset. This
   is exactly the information invariant under the deliberate permutation quotient.
7. **No RH selection follows.** A literal arithmetic comparison must still prove that the complete
   pre-zero source formation lands in this compact proper chart and that physical nullity acts on
   the reconstructed formation polynomial.

## 11. Parent and priority audit

Occupied ingredients:

- Samaniego and Jones (1981) recover heterogeneous Bernoulli parameters using elementary symmetric
  functions in a reliability model.
- Marichal--Mathonet--Waldhauser,
  [arXiv:1010.0162](https://arxiv.org/abs/1010.0162), develop permutation/signature-based
  reliability representations.
- Buchstaber--Rees,
  [*The Gelfand map and symmetric products*](https://arxiv.org/abs/math/0109122), provide a broad
  algebraic parent for symmetric-product reconstruction.
- Garncarek,
  [arXiv:1110.3692](https://arxiv.org/abs/1110.3692), is a nearby zero-divisor/Titchmarsh parent
  for compactly supported convolution algebras. Lemma 5.1 is proved independently for the exact
  finite-measure half-line algebra needed here.
- Hausdorff moment determinacy, Laplace uniqueness, and compact-to-Hausdorff embedding are classical.

Searches through current 2025--2026 reliability, moment, and convolution literature found no exact
combination of permutation-averaged first-failure histories, measure-valued coefficient recovery,
absorbing-zero repair, unique positive convolution square roots, and compact properness. This is
not a priority proof. The honest label is `[BRIDGE] [NOVELTY UNVERIFIED]`.

## 12. Cofinal successor

The finite theorem identifies the correct higher object:

> formation is encoded by a characteristic polynomial whose coefficients are generated histories
> and whose evaluation tower is determinate.

The immediate cofinal problem was not another route endpoint. It was to classify limits of formation
polynomials when factor number diverges. That problem is now solved at paper level by ULF-FCM-1,
`poisson-dust-formation-compactification-cumulant-separation-and-equivariant-neutrality-law.md`.
Its exact answer is not merely a countable packet: vanishing factors can converge to a
convolution-exponential dust generator. The next arithmetic gate is to realize the all-prime source
in that compactification and prove that physical displacement is a positive two-sided additive dust
family with faithful calibration.

## Gates

- [x] 0 -> 1: exact source-generated statement and attack plan
- [x] 1 -> 2: dependency-closed paper proof, countermodels, parent audit, fourth-organ prediction
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.PermutationAveragedFirstFailure`, `GaloisForLFunctions.HTGeometry.ComplexMeasurePairing`, `GaloisForLFunctions.HTGeometry.MultiplicativeConvolutionDomain`, `GaloisForLFunctions.HTGeometry.PositiveIntervalConvolutionDomain`, `GaloisForLFunctions.HTGeometry.FirstFailureSourceTomography`, `GaloisForLFunctions.HTGeometry.FirstFailureCompactProperness`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 -> 4: publication audit and source-specific realization


## Lean certificate

Modules `GaloisForLFunctions.HTGeometry.PermutationAveragedFirstFailure` (Theorem 3.1),
`GaloisForLFunctions.HTGeometry.ComplexMeasurePairing` (pairing of finite complex measures with
bounded functions through their Jordan parts, independent of the splitting),
`GaloisForLFunctions.HTGeometry.MultiplicativeConvolutionDomain` (the multiplicative convolution
ring of finite complex measures on `[0,1]`), `GaloisForLFunctions.HTGeometry.PositiveIntervalConvolutionDomain`
(Lemmas 5.1–5.2), `GaloisForLFunctions.HTGeometry.FirstFailureSourceTomography` (§§2, 4–7, §10.2)
and `GaloisForLFunctions.HTGeometry.FirstFailureCompactProperness` (Theorem 8.1).  Sources are
`ProbabilityMeasure` on `unitInterval` with the topology of weak convergence; positions are
`0`-indexed (`r : Fin k` is the card's position `r + 1`) and response moments are indexed by
`n + 1`, `n : ℕ`.  `M((0,1])` is the subring `positiveSupport` of the convolution ring
`ConvMeasure` (finite complex measures on `[0,1]`, ring structure transported through the
injective multiplicative moment map) consisting of the measures without atom at `0`.  Names
with prefix `FirstFailure.` and `MeasureConvolution.` live in those namespaces under
GaloisForLFunctions.HTGeometry.

| Claim | Lean declaration |
|-|-|
| (PFF.1) `a_i(n) = ∫ yⁿ dμ_i`, `s_i(n) = a_i(n)²` | `FirstFailure.sourceMoment`, `FirstFailure.survival`, `FirstFailure.survivals`, `FirstFailure.survival_zero` |
| (PFF.2)–(PFF.4) first-failure weights, schedule average, the observer; invariance under relabelling the sources | `FirstFailure.firstFailure`, `FirstFailure.averagedFirstFailure`, `FirstFailure.observer`, `FirstFailure.observer_apply`, `FirstFailure.esymm_comp_perm`, `FirstFailure.averagedFirstFailure_comp_perm`, `FirstFailure.observer_comp_perm` |
| prefix averages: `∑_σ ∏_{j<m} s_{σ(j)} = m!(k-m)! e_m`, exactly `m!(k-m)!` permutations carry the prefix onto a given `m`-set | `FirstFailure.esymm`, `FirstFailure.prefixSet`, `FirstFailure.card_perm_map_prefixSet`, `FirstFailure.sum_prod_prefixSet` |
| Theorem 3.1, (PFF.5) `W_r = ((k-r+1)e_{r-1} - r e_r)/(k C(k-1,r-1))` | `FirstFailure.firstFailure_eq`, `FirstFailure.sum_firstFailure`, `FirstFailure.averagedFirstFailure_eq_div_choose`, `FirstFailure.averagedFirstFailure_eq` |
| (PFF.6) `∑_r W_r = 1 - e_k` | `FirstFailure.sum_averagedFirstFailure`, `FirstFailure.esymm_zero`, `FirstFailure.esymm_card` |
| (PFF.7) recursive recovery of `e_r`; equal ledgers give equal elementary coefficients | `FirstFailure.esymm_succ_eq`, `FirstFailure.esymm_eq_of_averagedFirstFailure_eq` |
| (PFF.8) `W_r = ((r-1)!(k-r)!/k!) ∑_{|A|=r-1} ∑_{i∉A} s_A(1-s_i)`, each `r`-set counted `r` times | `FirstFailure.sum_sum_compl_prod_mul`, `FirstFailure.averagedFirstFailure_eq_prefix_sum` |
| (PFF.9)–(PFF.10) `ρ_i = μ_i ⊠ μ_i` (push-forward of the product under `(x,y) ↦ xy`), `∫ xⁿ dρ_i = s_i(n)` | `FirstFailure.selfConv`, `FirstFailure.integral_pow_mconv`, `FirstFailure.integral_pow_selfConv` |
| (PFF.11)–(PFF.12) `E_r = ∑_{|A|=r} ⊠_{i∈A} ρ_i`, `E_0 = δ_1`, mass `C(k,r)`, moments `e_r(s(n))` | `FirstFailure.prodConv`, `FirstFailure.integral_pow_prodConv`, `FirstFailure.coeffMeasure`, `FirstFailure.coeffMeasure_zero`, `FirstFailure.coeffMeasure_univ`, `FirstFailure.integral_pow_coeffMeasure`, `FirstFailure.sourceCoeffMeasure`, `FirstFailure.integral_pow_sourceCoeffMeasure` |
| the observer recovers every `E_r` (Hausdorff determinacy) | `MeasureConvolution.measure_eq_of_moments_eq`, `FirstFailure.sourceCoeffMeasure_eq_of_observer_eq` |
| (PFF.13)–(PFF.14) `α_i = ρ_i|_{(0,1]}`, `E_r|_{(0,1]} = ∑_{|A|=r} ⊠ α_i` (a product is positive iff every factor is) | `FirstFailure.posPart`, `FirstFailure.prod_ne_zero_iff`, `FirstFailure.posPart_prodConv`, `FirstFailure.posPart_finset_sum`, `FirstFailure.posPart_coeffMeasure` |
| (PFF.15) the formation polynomial `∏(T + α_i)` over `M((0,1])` has the restricted `E_r` as coefficients | `FirstFailure.toPositive`, `FirstFailure.alphaElem`, `FirstFailure.formationPoly`, `FirstFailure.prod_ofMeasure`, `FirstFailure.ofMeasure_finset_sum`, `FirstFailure.esymm_alphaElem` |
| finite complex measures, their Jordan parts and the splitting-independent pairing; `ℂ`-linearity | `MeasureConvolution.ofMeasure`, `MeasureConvolution.jordanPart`, `MeasureConvolution.pair`, `MeasureConvolution.pair_eq_of_split`, `MeasureConvolution.pair_add`, `MeasureConvolution.pair_smul`, `MeasureConvolution.pair_sum_smul_ofMeasure` |
| multiplicative convolution of finite complex measures; the convolution ring (moment map injective and multiplicative) | `MeasureConvolution.conv`, `MeasureConvolution.integral_mconv`, `MeasureConvolution.pair_conv`, `MeasureConvolution.momentSeq`, `MeasureConvolution.momentSeq_injective`, `MeasureConvolution.momentSeq_mul`, `MeasureConvolution.ConvMeasure` |
| Lemma 5.1 the algebra `M((0,1])` of finite complex measures under `⊠` has no zero divisors: the Mellin transform is multiplicative and holomorphic on `Re z > 0`; holomorphic functions on the connected half-plane form a domain; moments of order `≥ 1` determine a measure on `(0,1]` | `MeasureConvolution.positiveSupport`, `MeasureConvolution.conv_singleton_zero`, `MeasureConvolution.mellin`, `MeasureConvolution.mellin_conv`, `MeasureConvolution.differentiableOn_integral_mellinTest`, `MeasureConvolution.analyticOnNhd_mellin`, `MeasureConvolution.eqOn_zero_or_eqOn_zero_of_mul`, `MeasureConvolution.measure_eq_of_moments_succ_eq`, `MeasureConvolution.eq_zero_of_momentSeq_succ` |
| Lemma 5.2 over a domain, `∏(T+a_i) = ∏(T+b_i)` forces `{a_i} = {b_i}` | `MeasureConvolution.multiset_eq_of_prod_X_add_C_eq` |
| (PFF.19) `ρ_i = α_i + (1 - α_i((0,1]))δ_0` | `FirstFailure.eq_posPart_add_atom` |
| Lemma 6.1 `μ ⊠ μ = ν ⊠ ν ⇒ μ = ν` | `FirstFailure.selfConv_injective` |
| Theorem 7.1 the observer is injective on `Sym^k P([0,1])`; equivalently equal observations differ by a permutation | `FirstFailure.observer_injective`, `FirstFailure.exists_perm_of_multiset_eq`, `FirstFailure.exists_perm_of_observer_eq` |
| Theorem 8.1 `Sym^k P([0,1])` compact; the observer continuous, a closed embedding, a homeomorphism onto its compact closed image, proper; coordinatewise convergence of responses forces weak convergence of multisets to the unique source | `FirstFailure.symSetoid`, `FirstFailure.SymSource`, `FirstFailure.continuous_sourceMoment`, `FirstFailure.continuous_observer`, `FirstFailure.symObserver`, `FirstFailure.symObserver_injective`, `FirstFailure.isClosedEmbedding_symObserver`, `FirstFailure.symObserver_compact_properness`, `FirstFailure.tendsto_of_symObserver_tendsto` |
| §10.2 on `[0,1]` the absorbing atom is a zero divisor: `δ_0 ⊠ (δ_1 - δ_{1/2}) = 0` | `FirstFailure.absorbing_zero_divisor` |

The mechanism discussion (§1), the remark after Theorem 8.1 on uniform continuity for compatible
metrics, the ledger (PFF.21), the remaining sharp-boundary remarks of §10, the parent and
priority audit (§11) and the cofinal successor (§12) are commentary.

## Log

- 2026-08-14 -- extracted as positive survivor after ordered hazard/swap-current mechanism failed significance audit.
- 2026-08-14 -- finite reconstruction, conservation, absorbing-zero factorization, and compact properness proofs closed.
- 2026-10-06 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
