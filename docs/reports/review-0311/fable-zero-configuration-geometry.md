# Zero Configuration Geometry — brief for an RH field built on the Gram engine

Constraint: no Weil or other positivity, no spectral realization, no counting, no Hodge index as the
decisive mechanism. Tags: `[L]` Lean statement read in source; `[D]` derived here; `[C]` proposal.
Companions: `fable.md`, `astra-research-programmes.md`, the READMEs of `IncommensurableGaborPinching`
(IGP), `TransThresholdPairCorrelation` (TTPC), `SquareRootThreshold` (SRT), and the `Zeta23` package.

---

## 1. The engine and what it establishes

**The matrix explicit formula.** At height `T` take `L = λ log(T/2π)`, the grid `τ_k = T + 2πk/L`, a
taper `φ` on `[−L/2, L/2]` and the modulated tests `f_k = φ e^{−iτ_k u}`. The Gram `G_{kl} = W(f_k, f_l)`
has two expressions `[L: Zeta23 Gz, Gentry, Gz_eq_Gp]`:

- zero side `Σ_ρ m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l)`, `γ_ρ = (ρ − ½)/i = γ − i(β − ½)`;
- prime side `∫ φ̂(τ − τ_k) φ̂(τ − τ_l) ν_X(τ) dτ`, `ν_X = μ + Π_X + P_X`: the archimedean density
  (`Γ′/Γ`), the pole, and the primes `n ≤ X = T^λ`.

**The zero configuration as a geometric object.** Each on-line zero is a point `w(γ) = (φ̂(γ − τ_k))_k`
of the real evaluation curve and contributes `w wᵀ`; an off-line pair `{ρ, 1 − ρ̄}` contributes the
indefinite block `2 Re(w wᵀ)` `[L: prop_block_ii_decomp, prop_block_ii_P_posSemidef]`. Since
`φ̂(z) = ∫ φ(u) e^{izu} du` (`paperFT`), the point `γ − iδ` is the real point `γ` seen through the
tilted window `φ(u) e^{δu}`: **depth is tilt** `[D]`. A tilted point has `|w|` up to `e^{δL/2} = T^{λδ/2}`.

**What the engine produces.** Proportions: `2/3` on the line, `0.6725` simple and on the line
(Theorem D), `+10⁻⁸` (IGP) `[L]`; beyond `λ = 1` certificates retain a signed coalescent prime surplus
`[L: zetaCosine_surplus_certificate]`. And, beneath the counts, **configuration geometry**: the overlap of
two zero vectors is the window kernel at their gap; the cosine-window kernel has no additive triple of
zeros (`mtKernel_additive_zero_triple_iff`) `[L]`, so no three close simple critical zeros are mutually
orthogonal. This is information about positions, read from primes, that no density or measure carries.

## 2. Why the counting layer cannot prove RH

- IGP and TTPC are proportion programmes; their READMEs say so.
- Density-one and fixed-aperture control leave finite or shallow exceptions (frontier scope guard).
- Finite moment data cap the certificates: cubic-model moments give `≤ 2/3`, sine-kernel moments through
  order four give the sharp model `16/21` `[L: killed-route ledger, abstract Gram sharpness]`.
- The engine's exact endpoint is Hermite's root-counting theorem for `ξ` in a windowed basis: negative
  inertia = number of off-line pairs, i.e. a count or, equivalently, `Â ⪰ 0`.

So the engine is kept as an **instrument**: an arithmetic camera that images the zero configuration.
The field asks what the images force, by rigidity rather than by sign or cardinality.

## 3. The questions, and why the tools do not exist

**Q0 (central).** Which geometric property of the imaged configuration, computable from arithmetic Grams,
forces every point onto the real curve — with the conclusion an identity, a rigidity theorem or a
deformation theorem, never a sign or a count?

**Q1 — Identifiability.** The full Weil form determines the configuration (`eq_of_weil_eq`) `[L]`;
separated on-line sets are resolved exactly when the aperture exceeds `π/(2g)`
(`eq_of_weil_eq_of_separated`) `[L]`; below threshold an off-line lattice has an on-line shadow with the
same form (`weil_nonneg_iff_onLineShadow_of_lagFormula`) `[L]`. Faithfulness is non-quantitative. Missing:
a stable inverse theory for tilted points on Gabor evaluation curves under arithmetic error — at which
bandwidth and precision do arithmetic images determine the depth of a point at height `T`? Prony and
Kruskal identifiability exist for algebraic curves with exact data, not for transcendental windowed
curves with prime-side noise.

**Q2 — Tilt rigidity.** A tilted point produces a block of size `T^{λδ}` while the prime side is a
real-line integral against `ν_X`. An isolated tilted point is incompatible with the image; only clusters
of tilted points whose blocks cancel can hide. Missing: the classification of cancelling clusters (their
exact algebraic and Diophantine conditions) and a proof that the arithmetic channels forbid them.

**Q3 — Sub-spacing arithmetic geometry.** Resolving the configuration below the mean spacing
`2π/log T` needs `λ > 1`. The prime side then carries coalescent pairs, odd primes at even shifts with
`0 < |log(n/m)| ≤ T^{−1+η}` (`primeCoalSum_eq_oddEvenShiftPrimeCoalSum`) `[L]`, split into a parity-locked
Hardy–Littlewood model and a discrepancy `[L]`. Unsigned sieves and one-sided positivity provably cannot
supply it (`calibration_five_models_four_thirds`; positivity-three-quarters ledger row) `[L]`. Missing:
parity-sensitive geometry of primes in short multiplicative windows as exact signed input — beyond every
sieve and every on-average prime-pair theorem.

**Q4 — Deformation without collision.** RH holds iff no zero of `H_t` is multiple for any `t > 0`
(`riemannHypothesis_iff_forall_zeros_simple`) `[L]`; `Λ = sup_X Λ_X` with
`Λ_X ≤ (2/3 + ε)/log((X − 1)/2π)` for large `X` (`eventually_localNewmanConstant_le_twoThirds`) `[L]`;
symmetrized exponentials of truncated Euler logarithms have every strip zero above height
`2π exp(2ψ(N) + 1)` on the line (`eulerCarrier_re_eq_half`) `[L]`. Under the functional equation a simple
real point stays real along a deformation until it collides `[D]`. Missing: a repulsion law for imaged
configurations along a deformation ending at `ζ` — a pointwise lower bound, uniform in the deformation
parameter, on how close two evaluation vectors can come, derived from the arithmetic image.

**Q5 — Kernel design.** IGP turns the additive rigidity of real kernel zeros into geometry of real
configurations. Missing: windows whose complexified kernels make tilted points inconsistent with their
real neighbours — an extremal theory of evaluation curves with prescribed additive structure of kernel
zero sets, real and complex.

**Q6 — Selectivity (a constraint on every answer).** The positive twins `ζ(s)(1 + A p^{−s} + p^{1−2s})`
have zeros at any prescribed `Re s ∈ (½, 1)` and are excluded only by the strict Euler bound
(`exists_positive_multiplicative_twin`) `[L]`; their extra zeros form vertical progressions of spacing
`2π/log p`, a lattice-like column — the shape SRT shows hides best `[D]`. Every answer must also fail for
sparse prime flips, Davenport–Heilbronn data (no prime channel), Epstein data and the golden datum.

## 4. Point of view

The explicit formula is a camera, not a sum rule. At each height, bandwidth and window it produces an
exact image — a Gram matrix — of the zero configuration embedded in a curve of evaluation vectors, and
the primes compute that image. RH is a statement about where the imaged points lie: on the real curve,
or tilted off it. The field reads positions, alignments and motions of the configuration from arithmetic
images and proves reality by rigidity: the arithmetic image has a structure that no configuration with a
tilted point can produce.

## 5. Objects

| Object | Meaning |
|---|---|
| Camera | window `φ`, bandwidth `λ`, height `T`, grid `τ_k`; resolution `2π/L` |
| Evaluation curve, real curve | `z ↦ w(z) = (φ̂(z − τ_k))_k` on `ℂ`; its restriction to `ℝ` |
| Imaged configuration | the multiset `{w(γ_ρ)}` with multiplicities and reflection symmetry |
| Arithmetic image | prime-side Gram, split into channels: archimedean, pole, diagonal primes, coalescent pairs, sum frequencies |
| Tilt | `φ ↦ φ e^{δu}`; a point of depth `δ` is a real point of the `δ`-tilted camera |
| Hyperbolic block | `2 Re(w wᵀ)` of a tilted pair |
| Cancelling cluster | tilted points whose blocks cancel to arithmetic size |
| Shadow | a real configuration with the same image (mimicry) |
| Kernel | `K_φ(Δ)`, the normalized overlap at gap `Δ`; its real and complex zero sets and their sumsets |
| Deformation family | heat time `t` (`H_t`), Euler depth `N`, tilt, bandwidth |
| Collision locus, Lehmer configuration | parameters where two points coincide; near-coincidences |

## 6. Language

- **Real / tilted point**; **depth = tilt**.
- **Image**, **camera**, **resolution**; a **faithful camera** determines the configuration.
- **Mimicry**: two configurations with one image; **identifiability threshold**: least bandwidth at
  which a tilted point has no real mimic.
- **Channel**: diagonal (`λ ≤ 1`), coalescent (sub-spacing prime pairs), sum-frequency.
- **Cancelling cluster**; **collision**, **near-collision**, **repulsion law**.
- **Incommensurable kernel**: kernel zeros with no additive relations of a given order.

## 7. Foundational principles

1. **No sign, no count, no spectrum, no Hodge index.** Conclusions are positions (identifiability),
   relations (rigidity) or continuations (deformation).
2. **Configuration before measure.** Densities and moments are shadows of the configuration; finite
   moment data are provably insufficient `[L]`.
3. **Depth is tilt.** The prime side never sees depth directly; depth appears only as the size and shape
   of a tilted block in an image.
4. **Every camera has a resolution and a mimicry class.** A theorem names its camera and what that
   camera cannot distinguish.
5. **Arithmetic enters with its signs.** Coalescent prime geometry is signed; majorants and one-sided
   bounds fail `[L]`.
6. **Symmetry makes reality topological.** Real points stay real under a symmetric deformation until two
   collide `[D]`.
7. **Pointwise in height.** No density-one or averaged conclusion: every height, every point.
8. **Selection.** Archimedean, pole and prime channels are used together, with the strict Euler bound.

## 8. Criteria the field must fulfil

1. Reproduce the anchors: matrix explicit formula, faithfulness, the separated resolution threshold,
   mimicry below threshold, IGP rigidity, the collision criterion, Euler-carrier domination `[L]`.
2. Reach its conclusions without counts, signs, spectra or Hodge index.
3. Separate `ζ` from the twins, sparse flips, Davenport–Heilbronn, Epstein and golden data.
4. Use the functional equation and the Euler product with the strict Euler bound.
5. Hold pointwise in height and effectively in the resolution scale.
6. Produce intermediate theorems that are not proportions: identifiability thresholds, cluster
   classifications, repulsion laws in model families.

## 9. Research topics and first theorems `[C]`

1. **Tilted identifiability.** For cosine and spline cameras, the least `λ(δ, T)` at which a tilted point
   has no real mimic of Riemann–von Mangoldt density. Calibration: lattices hide to `L/2`; an isolated
   pair on `ζ`'s background is seen at aperture `≍ (1/2δ) log log T` (SRT README).
2. **Cancelling clusters.** Exact algebraic conditions under which tilted blocks cancel to `O(L)`; their
   Diophantine content; whether diagonal-prime images (`λ ≤ 1`) admit any.
3. **Signed coalescent geometry.** The parity-locked model and its discrepancy (TTPC) read as the
   configuration's geometry below the mean spacing.
4. **Repulsion laws.** Pointwise lower bounds on the distance between consecutive evaluation vectors along
   heat time and Euler depth; Lehmer configurations; the decay `Λ_X → 0` as a statement about cameras at
   large height.
5. **Window design.** Extend `mtKernel_additive_zero_triple_iff` to complex arguments; windows whose
   complexified kernels exclude cancelling clusters.
6. **Calibration suite.** Twins' vertical progressions, sparse flips, Davenport–Heilbronn, Epstein,
   golden datum: each first theorem must separate them.
7. **Function-field model.** For a curve over `𝔽_q` the configuration is finite and the image exact; the
   identifiability, cluster and deformation questions are finite-dimensional there and must be answered
   first.

## 10. Status

No rigidity, identifiability or repulsion theorem of this kind exists, in the corpus or in mathematics.
The corpus walls (Σ = Π = Γ) predict that any rigidity conclusion will require the same arithmetic input
as the estimate routes: signed prime geometry below the mean spacing (Q3). The field's contribution is to
state that input as geometry of a configuration — positions, tilts, collisions — rather than as a
cancellation bound, a sign or a count.

## Anchors

| Fact | Lean |
|---|---|
| Matrix explicit formula; zero- and prime-side Gram | Zeta23 `Gz`, `Gentry`, `Gp`, `Gz_eq_Gp` |
| On-line part PSD, block structure | Zeta23 `prop_block_ii_decomp`, `prop_block_ii_P_posSemidef`, `prop_block_i_rank` |
| Proportions | Zeta23 `ThmD.thmD₀_simple_mult`; IGP `simple_critical_proportion_ge_67250071` |
| Kernel additive rigidity | IGP `mtKernel_additive_zero_triple_iff` |
| Signed surplus beyond `λ = 1`; coalescent band; calibration | TTPC `zetaCosine_surplus_certificate`, `primeCoalSum_eq_oddEvenShiftPrimeCoalSum`, `calibration_five_models_four_thirds` |
| Faithfulness; separated resolution; mimicry | SRT `eq_of_weil_eq`, `eq_of_weil_eq_of_separated`, `weil_nonneg_iff_onLineShadow_of_lagFormula` |
| Collision criterion; local Newman constant | RHTower `riemannHypothesis_iff_forall_zeros_simple`, `newmanConstant_eq_iSup_localNewmanConstant`, `eventually_localNewmanConstant_le_twoThirds` |
| Euler-carrier domination | RHTower `eulerCarrier_re_eq_half` |
| Twins | SelbergClass `exists_positive_multiplicative_twin` |
