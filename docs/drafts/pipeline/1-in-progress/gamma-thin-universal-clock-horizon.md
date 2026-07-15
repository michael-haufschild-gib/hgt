# The dimension-zero universal-clock horizon of Gamma

- **ID:** `gamma-thin-universal-clock-horizon`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Scientific status:** `[UNCONDITIONAL ANALYTIC TOPOLOGY, IRREVERSIBLE CLOCK, AND ALL-FINITE-DEPTH B-JET UNIVERSALITY PROVED IN LEAN] [MOVING-BASE D-JET BRIDGE OPEN] [NOVELTY PLAUSIBLE, NOT PRIORITY-CERTIFIED]`
- **Statement:** There is a nonstationary inverse-Gamma horizon homeomorphic to Baire space and of
  Hausdorff dimension zero, while every finite depth and every finite normalized inverse-jet
  resolution remains Zariski universal.

## Theorem

There are increasing pole thresholds `N_1,N_2,...` and a coding map

\[
 \pi:\prod_{k\ge1}\{n\in\mathbb N:n\ge N_k\}\longrightarrow\mathbb C
\]

with the following properties.

1. `pi` is a homeomorphism onto its image `H`, so `H` is homeomorphic to Baire space.
2. If `omega=(n_1,n_2,...)`, then

   \[
     \Gamma^j(\pi(\omega))=\pi_j(n_{j+1},n_{j+2},...),
   \]

   where `pi_j` is the same inverse construction with the shifted threshold sequence.  Each
   orbit point lies on the inverse sheet based at `-n_{j+1}`.
3. `dim_H H=0`.
4. For every finite depth `d` and jet order `m`, the normalized clock-decoration projection

   \[
    \omega\longmapsto
    (D_{n_1}\bmod T^{m+2},...,D_{n_d}\bmod T^{m+2})
   \]

   has Zariski-dense image in `G_m^d`.  The same remains true after fixing any finite prefix and
   reading a later finite block.  Here `D_n` is the intrinsic normalized jet of the actual
   reciprocal transition, defined below.

The theorem is static: the threshold sequence is an admissibility constraint on complete
histories.  Gamma sends one constrained horizon to the horizon with shifted thresholds; no
founding flow is asserted.

## Proof

Let `s_n=(-1)^(n+1)/n!`.  The locally uniform factorial microscope for reciprocal Gamma gives

\[
 A_n(X):=-\Gamma(-n+s_nX)^{-1}\longrightarrow X
\]

on every compact subset of `C`.  Choose `0<rho<R<1/3`.  Rouche's theorem gives, for every large
`n`, a unique simple inverse `B_n:D_rho -> D_R`, with `A_n o B_n=id` and `B_n -> id` locally
uniformly with derivatives.

On an exterior collar `Omega_C={|y|>C}`, set

\[
 I_n(y)=-n+s_nB_n(-1/y).
\]

After increasing `C` and the pole threshold, `Gamma o I_n=id`, the images lie in pairwise
disjoint disks contained in `Omega_C`, and

\[
 |I_n(y)-I_n(y')|\le r_n|y-y'|,
 \qquad r_n\le \frac K{n!}
\]

for a common `K`, with every `r_n<1`.  Infinite inverse compositions therefore converge,
independently of the terminal point.  Disjoint first-level disks recover the first symbol;
applying Gamma recovers successive symbols.  Common-prefix contraction proves continuity of the
coding, and the separated disks prove continuity of its inverse.

Choose `N_k` recursively so that

\[
  \sum_{n\ge N_k} r_n^{1/k}\le 2^{-k}.
\]

This is possible because `r_n<=K/n!`.  A depth-`d` cylinder has diameter at most
`D prod_{k<=d} r_{n_k}`.  For any `s>0` and all sufficiently large `k`, `s>=1/k`, hence

\[
 \sum_{n\ge N_k}r_n^s\le2^{-k}.
\]

The sum of the `s`th powers of the depth-`d` cylinder diameters tends to zero.  Thus every
positive-dimensional Hausdorff measure of `H` vanishes and `dim_H H=0`.

Finally, the complete coefficient germs of `B_n` are algebraically independent.  Every pole tail
is therefore Zariski dense in every finite jet group.  Products of dense tails are dense, so the
independently constrained labels at the first `d` depths give density in `G_m^d`.  Fixing a prefix
only shifts the thresholds used by the same argument.

The decoration is intrinsic to the actual moving-base transition.  In reciprocal coordinates,

\[
 C_n(T)=-I_n(-1/T)^{-1}=\frac1{n-s_nB_n(T)}.
\]

For `n>=1`, normalize its source and target scales by

\[
 D_n(T)=\frac{n^2}{s_n}\left(C_n(T)-\frac1n\right)
       =\frac{B_n(T)}{1-(s_n/n)B_n(T)}.
\]

Thus `D_n(T)=T+O(T^2)` is the actual edge clock in the jet-groupoid fiber at infinity.  The
inverse formula

\[
 B_n(T)=\frac{D_n(T)}{1+(s_n/n)D_n(T)}
\]

shows that the passage between formal clocks is a Möbius coefficient automorphism once the shell
parameter `s_n/n` is retained.  The factorial--harmonic proof is stronger than its current Lean
statement: it gives algebraic independence of the branch coefficients over `C(n)`, because the
generalized harmonic jets are independent over `C(n)` and the reciprocal factorial is
transcendental over that harmonic field.  Hence the `D_n` coefficients are likewise independent
over `C(n)`, and their finite product tails are Zariski dense.  Formalizing this relative-base
upgrade is the remaining algebraic proof obligation.

## What is new and what is not

- A rapidly contracting nonstationary iterated-function system can have a dimension-zero Baire
  limit set; this general mechanism is not claimed as new.
- Product density of algebraically independent coordinate sequences is standard algebraic
  geometry.
- The candidate new statement is their exact coexistence for the Euler Gamma source: an actual
  inverse-orbit horizon of geometric dimension zero carries the complete algebraically universal
  normalized jet of its own moving-base transition at every finite depth.

The significance gate is not cleared by topology alone.  It is cleared only if the normalized
clock decoration is shown to be intrinsic to the moving-base Gamma jet groupoid, or if the horizon
closes the differential-independence proof for the positive Gamma iterates.

## Unconditional Lean theorem package

The actual Euler-Gamma construction is now formalized without analytic, IFS, representative, or
dimension hypotheses.

1. `GammaCommonInverseCollar.lean` constructs one common target disk and unconditional analytic
   inverse branches of the actual normalized Gamma pole microscopes.
2. `GammaExteriorInverseBranches.lean` constructs the actual exterior sheets, proves
   `Gamma o I_n = id`, pairwise pole-disk separation, exterior preservation, and factorial
   contraction.
3. `GammaBaireInverseCoding.lean` proves convergence for every literal Baire word, injectivity,
   continuity of the code and decoder, the homeomorphism onto the coded horizon, and exact Gamma
   tail reading.
4. `GammaDimensionZeroHorizon.lean` proves the reciprocal-compression diameter bound, summable
   countable cylinder covers for every positive exponent, vanishing Hausdorff measures, and
   `dimH gammaConstrainedHorizon = 0`.
5. `GammaIrreversibleClockHorizon.lean` proves forward invariance and the exact clock law

   `tau(omega)(k) = omega(k+1)+1`,

   together with strict age layers, an empty infinite-age core, and absence of periodic Gamma
   histories on the horizon.
6. `GammaUniversalClockHorizon.lean` removes the prior representative hypothesis by selecting
   representatives of the inverse-branch coefficient germs internally.  At every finite clock
   depth and finite jet resolution, every nonzero mixed polynomial is detected by a legal pole
   word, and every such word extends to an actual point of the analytic horizon.

The integrated terminal declaration
`gamma_dimensionZero_algebraicallyUniversal_irreversibleClockHorizon` is unconditional.  The
algebraic decoration currently uses the tangent-to-identity normalized branch jets `B_n`.  It does
not yet identify them with the intrinsic moving-base clocks `D_n`; that distinction remains the
load-bearing significance gate.

## Physical interpretation

`H` is a precise zero-area/infinite-information horizon.  Its Euclidean geometry is invisible to
every positive Hausdorff dimension, yet no finite algebraic clock observable exhausts the
normalized jets of its actual transitions.  A point of `H` reconstructs its entire pole itinerary
by repeated application of Gamma, while the itinerary reconstructs the point by the inverse
constraint.  This is a literal boundary reconstruction theorem, not a claim about quantum
amplitudes or black-hole dynamics.

## RH impact

The Gamma factor is the archimedean source in the completed zeta function.  This theorem shows
that a Hausdorff-dimension-zero exceptional set can still carry unbounded algebraic jet capacity.
Consequently an RH strategy cannot discard an archimedean boundary merely because it is thin in
Euclidean dimension; it must control the normalized source clocks or prove that its chosen
functional ignores them.  No zero localization or positivity statement follows.

## Lean plan

1. `[DONE]` `GammaInversePoleBranchProductDensity.lean` proves that Cartesian products of
   polynomial-detecting families detect every mixed polynomial on a sum of variable blocks.
2. `[DONE AT DEPTH TWO]` The same module proves that, beyond arbitrary independent lower bounds
   on two Gamma pole labels, every nonzero mixed polynomial in two normalized finite inverse-jet
   frames survives.  The generic sum theorem is the induction step for arbitrary finite depth.
3. `[LOGARITHMIC SOURCE DONE]` `GammaPoleRelativeLogFreeness.lean` proves that the complete exact
   Gamma pole logarithmic-jet family is algebraically independent over the full rational
   pole-position field `C(n)`.  The exact target build and direct file elaboration pass.
4. `[OPEN]` Transport this relative freeness through the Bell, unit-inverse, compositional-inverse, and
   intrinsic Möbius coefficient automorphisms to obtain `B_n <-> D_n` over `C(n)`.
5. `[DONE FOR ACTUAL GAMMA]` The common collar, exterior sheets, Baire coding, and exact clock are
   formalized directly rather than behind a reusable conditional IFS interface.
6. `[DONE]` The dimension-zero cylinder argument is formalized and instantiated with the actual
   factorial contraction and reciprocal-compression bound.
7. `[DONE FOR B_n]` Arbitrary finite-depth Zariski detection is formalized with an unconditional
   internally selected coefficient representative and legal-word extension into the analytic
   horizon.

The exact target build and direct file elaboration pass.  Its imported dependency closure was
already cached; no full or concurrent build was run.

## Attacks

1. **Generic-IFS attack.**  Dimension zero alone is standard and not significant.  The only
   source-specific content is simultaneous actual Gamma coding and universal normalized clocks.
2. **Wrong-clock attack.**  Actual reciprocal transitions are
   `C_n(T)=1/(n-s_nB_n(T))`.  The theorem uses their intrinsic normalization
   `D_n=(n^2/s_n)(C_n-1/n)`, not false prefix composition of the `B_n`.
3. **Metric-dependence attack.**  Hausdorff dimension uses the ambient Euclidean metric and is not
   a topological invariant.  The theorem deliberately contrasts this metric thinness with Baire
   topology and algebraic capacity.
4. **RH upcast attack.**  Thinness plus infinite capacity is a constraint on proof architectures,
   not an RH criterion.

## Gates

- [x] 0 -> 1 in-progress: exact theorem, proof, no-go correction, physical meaning, and RH audit
- [ ] 1 -> 2 fully-proven: moving-base intrinsicity or differential-independence consumer closed;
  otherwise classify as a strong source-specific theorem below the significance threshold
- [ ] 2 -> 3 formalized: product density, inverse coding, and zero-dimension threshold theorem in
  Lean with serialized exact-module verification
- [ ] 3 -> 4 publication-ready: primary audit in transcendental meromorphic dynamics, countable
  nonautonomous IFS, Gamma inversion, and Faà di Bruno jet groupoids
