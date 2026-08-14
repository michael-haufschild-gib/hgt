# new_scientific_knowledge/other stage-3 sweep — ledger

Goal (session stop hook): every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/`
fully formalized unconditionally in Lean and moved to stage 3. 65 at start; **24 promoted 2026-08-13; 41 remain**.
(#24 = `weighted-euler-tangent-global-graph-decoupling`, promoted 2026-08-13 late: its (3)/(18)/(19)
are `RHTower.topologicalClosure_primeQuadrantGraph_eq_top'`,
`RHTower.closure_primeQuadrantGraph_eq_univ`,
`RHTower.closure_affine_primeQuadrantGraph_eq_univ` in
`RHTower/WeightedEulerJointClosure.lean`, all axiom-clean.  20 new modules; see memory
`route-weighted-euler/joint-closure-plan-2026-08-13`.)

Promotion procedure that worked (Phase A + tranche 2): batched `lake build <mods>` foreground →
`#print axioms` scratch on capstones (⊆ propext/Classical.choice/Quot.sound) → sed Stage line →
`git mv` to 3-formalized/new_scientific_knowledge/other/ → rename clashing cert `<name>-formalized.md`
→ fix Paper-proof/relative links (`grep -rn '2-fully-proven/new_scientific_knowledge/other/'` must
come back clean). Namespaces vary (GaloisForLFunctions / GaloisForLFunctions.HTGeometry / RHTower /
RHTower.Sieve / GaloisForLFunctions.UniformBoundaryWedge); check `grep '^namespace'` first.

## DONE (23): Phase A 12 = bounded-relation-log-magnitude-ht, charged-scalar-core, double-sine-defect-coset,
gaussian-torsion-language, torsion-universal-phase, complete-scalar-persistent, coordinate-intrinsic-fusion,
route-c2-zero-safe, scalar-differential-inversive, von-mangoldt-toeplitz, nonreal-factorial-slope,
double-sine-translation-annihilator. Tranche2 11 = barnes-differential-source-face, split-source-boundary,
primitive-fibre-modular, von-mangoldt-bivariate, wold-sieve-normal-cone, ramsey-weyl, shift-one-seam-power64,
theta-cusp-calibrated, boundary-wedge-uniform-ht (stale para fixed, boundaryWedge_geometry is in ns
GaloisForLFunctions.UniformBoundaryWedge), projective-prime-weyl-leakage, prime-tail-reflection-folded.

## ACTIVE CARD: universal-first-order-entire-cascade-unit-cost
653KB work-log card. Frontier (from log parts 3–12, all 2026-08-09):
- Item 1 (place above infinity): DONE — AlgebraicCascadePlace.exists_heightOneSpectrum_over_topInt.
- Item 2' (ord_Q(minpoly'(α)) = e−1, the tame different at the place): parts 5–12 built
  SeparableFactorDerivativeOrder (not_pow_dvd_derivative), IdealQuotientTransport
  (mem_pow_iff_dvd_of_quotEquiv, not_mem_pow_of_deriv), DedekindOrderMonogenic
  (exists_adjoin_eq_top_of_dedekind_finite), QuotientPowerMonogenic, ProductMonogenic,
  DedekindLocalUniformizer. **REMAINING: the instantiation** — produce `h, g, e` for a given prime Q
  from mathlib `KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` +
  `emultiplicity_factors_map_eq_emultiplicity`, i.e. close `ord_Q(𝔡) = e−1`, then the derivation
  bound `w(∂_{X_m} f) ≥ w(f) + e`.
- Item 3: restate the peel over the extended datum + Reduction I analytic place-selection
  (Wiman–Valiron layer: MaximumTermCentralIndex, MaximumTermLogarithmicDerivative,
  CircleMaximumCriticality, DiscreteJensenExp, MeanIndexComparison, BorelGrowthLemma exist).
- REUSE: corpus already owns `DifferentExponentTame.differentIdeal_eq_span_pow` (tame different for
  finite DVR extensions, trivial residue ext) + `RingOrdRamification.lean` (Ring.ord bridge) from the
  stable-coframe campaign (memories research/tame_different_exponent_assembled_2026_08_06,
  research/ring_ord_ramification_bridge_2026_08_06). Check whether item 2' closes by DVR-localising
  at Q and applying differentIdeal_eq_span_pow instead of the Kummer–Dedekind route.
- Open gate box line ~465: observability (helim) on a general cascade (Reduction III w/ algebraic law).

## Open-gate census 2026-08-13 (remaining 41, by count of unchecked `- [ ]` boxes)
0: power-canonical-product (only eq. (1), the Barnes tail of `W_s`, is unformalized),
   prime-tail-hedenmalm (Young `L¹⋆L²→L²` built as `HTGeometry/YoungConvolutionL2.lean`; the
   half-line convolution operator, trace intertwining and `L²` wall of Theorem 1 are still
   paper-level, so NOT ready — its "revised open core" is RH-equivalent and is flagged open on the
   card itself, which is fine, but Theorem 1 must still be formalized).
1: gauss-component-quasi-inner, prime-euler-unit-tangent, prime-modulated-weyl.
2: abelian-multiplication-tail-manin, additive-heat-aperture-shifted-zeta-echo,
   additive-heat-aperture-zeta-zero-echo, all-depth-compatible-pair-face,
   almost-periodic ×2, archimedean-relative-prime-cocycle, …

## Attack order for the remaining 42
Bounded gaps (do first): universal-first-order-entire-cascade (ACTIVE), weighted-euler-tangent
(construct 2nd factor: Fréchet O(Q₊)_R as LCS + instantiate pair-criterion; LpSingleAnnihilator etc.
exist), power-canonical-product (Barnes-tail identification of the formalized transform theory),
additive-heat-aperture-shifted-zeta-echo-ladder (Jonquière expansion + Gaussian asymptotic),
gauss-component-quasi-inner (open core (T) m≥2, full proof plan written at card tail: band split
J=⌊n/4⌋, finite Parseval; m=1 closed), all-order-multiple-sine (lower face layers (10)–(11)
descent bookkeeping; 1 open box line 1078), prime-euler-unit-tangent (two-carrier separation Runge:
compact set w/ connected complement; corpus has half-plane Runge oneGeneratorRungeDense_holoAlgebra,
pole-pushing tendstoUniformlyOn_cauchyKernel_poly), noncompact-period-quotient (Siegel bound compact
complex tori, d≥2), prime-modulated-weyl (needs: smooth jet interpolation, superlinear aperiodicity
lemma, and an unconditional infinite-critical-zeros input — try Hardy's theorem instead of Conrey),
floquet-orbifold-tail (needs parent classification below for Tail(R_i)=C).
Deep/new-theory: rational-coarse-graining-orbifold-tail (Casale classification + Zariski-dense
translation-deck (8) + jet transport), orbifold-tail-holographic (assemble w/ tail interface),
all-depth-pair-face + irrational-triptic (elliptic principal parts + triptic DA-completeness; card
warns formalizing shell alone is 'theatre'), abelian-multiplication-tail-manin + embedded-manin +
isogeny-tail-maurer-cartan + jet-horizon (diff algebraic groups/Kolchin/Manin/DCF layer),
differential-variational-building (Ore localization + buildings), eigenplurivolume (pluricanonical),
toric-log-calabi-yau (toric + stable-field equality), bessel-order (Dreyfus DA-to-periodic-exponential
special case), critical-half-density (atomic measure + distributional jump), almost-periodic ×2,
archimedean-relative-prime-cocycle, active-quasi-abelian (full surface), torusless-quasi-abelian
(Poincaré estimates), prescribed-gap-process, fixed-divisor-full-complex, symmetry-caged-fixed-divisor,
prime-completion-annihilates, prime-occupation-polarized, prime-valuation-dyadic-fermion,
prime-wold-accelerated, prime-tail-hedenmalm, additive-heat-aperture-zeta-zero-echo (polylog boundary
asymptotics; card says formalize after audits — goal overrides), scalar-ht-horizon (exact meet + H³),
nonlinear-rational-observation (depth-one inversion + arbitrary-depth branch separation assembly),
differential-variational, jet-horizon, universal cards remaining in tranche 4.

## Session log
- 2026-08-13: ledger; Phase A 12 promoted; tranche2 11 promoted; links clean; started
  universal-first-order-entire-cascade item 2' instantiation.
