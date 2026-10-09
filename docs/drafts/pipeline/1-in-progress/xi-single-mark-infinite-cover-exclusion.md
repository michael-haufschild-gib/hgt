# Actual Xi: exclusion of a nontrivial infinite covering factor

- **ID:** XI-INFINITE-COVER-20261008
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `RHTower/XiMarkedMonodromyMap.lean`, `XiMarkedFiniteMonodromy.lean`, `XiMarkedNormalClosure.lean`, `XiPolynomialLeftFactors.lean`.
- **Statement:** The map induced by actual Xi from `C \ xi⁻¹({0,-1})` to `C \ {0,-1}` is surjective on the based fundamental group.

## Goal and scope

Set A={0} in the existing actual source map. The exact target is surjectivity, not finite-image surjectivity or normal generation. Finite-image equality and normal generation already hold. This conjecture addresses the unresolved infinite, nonnormal case. No RH claim follows from surjectivity alone; it would classify a geometric limitation of this source encoding. The full multi-mark image remains a separate stronger target.

User constraints: corpus only; no web, numerical experiments, positivity, spectral, energy or Fourier route. Do not abandon this conjecture because its proof requires missing mathematics.

## What the failed inference teaches

`HTGeometry/InfinitePacketObstruction.lean` constructs a proper subgroup of a rank-two free group satisfying the finite packet mechanism, containing a primitive meridian, with surjective winding, full normal closure and every finite group image full. Its cosets are one distinguished sheet plus an integer line. Thus a proof must use additional analytic geometry of Xi.

## New proof attack: complete the hypothetical cover

Assume the actual image H is proper. Take the connected covering of the twice-punctured plane classified by H. The actual Xi map lifts. Complete finite peripheral cycles by their ramification points. The lift from the plane should extend across all deleted source points, producing a factorization Xi=F∘g through a completed Riemann surface E.

The following are proof obligations, not established conclusions:

1. **[OPEN CORE: completion]** Construct E as a Hausdorff Riemann surface, extend both maps, and prove F has no critical or asymptotic values outside {0,-1}. Infinite peripheral cycles remain ends; do not fill them by fiat.
2. **[OPEN CORE: uniformization]** The entire nonconstant lift should force E to be conformally C or C*. Compact cases cannot support nonconstant holomorphic F:E→C. Hyperbolic cases should be excluded by lifting g to the disk and Liouville.
3. **[OPEN CORE: composition]** For E=C, if F is transcendental with finitely many singular values, a transcendental entire g should make F∘g have infinite order. Need a dependency-closed proof; the corpus's Clunie characteristic ratio theorem alone does NOT establish this. If g is polynomial, Xi would have only finitely many critical values.
4. **[OPEN CORE: punctured-plane case]** Treat F:C*→C and g=exp(h). Do not pretend entire composition results apply across essential singularities at 0. Analyze both ends.
5. Polynomial outer F is excluded by `xi_polynomial_left_factor_natDegree_eq_one` with tilt zero. This existing theorem must be reused.
6. Prove from actual Xi that nonzero critical values accumulate at zero. Candidate proof: arbitrarily high real zeros of XiC, nontrivial real extrema between consecutive zeros, and XiC(t)→0. Use gamma/Stirling decay, not Fourier machinery. A nonzero accumulation sequence excludes a finite critical-value set.

## Attack before formalization

Potential failure: completed cover could fail the asserted global surface properties; its projection could acquire additional asymptotic values; or finite-order composition could admit a zero-order transcendental outer factor. Every one must be settled explicitly. No structural hypothesis may be packaged as an input to a purported unconditional Xi theorem.

The abstract countermodel is compatible with a fixed primitive meridian and infinite ends. The new attack aims to exclude its entire-function realization for Xi; it does not infer exclusion from finite data.

## Actual critical-value lemma: complete paper proof

**Claim.** For every T and epsilon>0 there exists t>T with XiC'(t)=0 and 0<|XiC(t)|<epsilon. In particular, Xi has infinitely many critical values, with nonzero critical values accumulating at zero. This claim has no RH assumption.

**Decay without Fourier.** Put s=1/2+it, t>=2. The exact gamma-zeta factorization gives
|XiC(t)|=|s(s-1)/2| pi^(-1/4) |Gamma(1/4+it/2)| |zeta(s)|.
Triangle bounds give |s(s-1)/2|<=2t^2. The corpus's elementary positive-half-strip zeta bound gives |zeta(s)|<=2+4t<=5t. Thus
|XiC(t)|<=80 pi^(-1/4) |(t/2)^3 Gamma(1/4+it/2)|.
The last quantity tends to zero by `Gamma_vertical_tendsto_zero_mul_pow` at sigma=1/4, n=3, composed with t/2. Its proof uses the Euler integral bound and the gamma recurrence, with no Fourier step: |Gamma(sigma+iu)|<=Gamma(sigma+k)/u^k for every integer k.

Choose U>T so every t>=U has |XiC(t)|<epsilon. `exists_high_simple_critical_xi` supplies a real XiC zero a>max(U,0), then another b>a. On [a,b] the nonzero entire function XiC has finitely many zeros. Take p to be the largest real zero in [a,b), and q=b. Then p>=a, p<q, and XiC has no real zero in (p,q). XiC is real on the real axis. Rolle's theorem supplies c in (p,q) with XiC'(c)=0. XiC(c) is nonzero by the gap, while c>U gives its norm below epsilon. This proves the claim.

For infinitude, if the nonzero critical values formed a finite set, their positive norms would have a positive minimum; choose epsilon smaller than it. Multiplication by i in the coordinate change s=1/2+it preserves the equation that the derivative vanishes, so the same critical values belong to Xi.

**Formal status:** completed in `RHTower/XiCriticalValueAccumulation.lean`. The strengthened zero-gap theorem now exports a<=p, with its prior API preserved. The accumulation, infinitude and polynomial-inner exclusion are Lean-checked. See the formalized child card for validation. This completes only this source lemma, not the covering conjecture.

## Corpus evidence

- `XiEntireRational.lean`: actual rational entire lifts have constant denominator and linear numerator, all real tilts.
- `ClunieCompositionGrowth.lean`: characteristic of transcendental composition dominates arbitrary multiples of inner characteristic along a sequence; weaker than finite-order obstruction above.
- `PolyaCompositionGrowth.lean`: quantitative minimum-modulus transfer, not the requested finite-order/Speiser classification.
- `/tmp/hgt-xi-entire-cover-factorization.json`: partial search, no applicable complete exclusion theorem found. Absence not certified.
- External novelty unverified under no-web instruction. No claim of absence from training data.

## Log

- 2026-10-08: exact conjecture retained after finite-packet inference failed. Derived covering-completion attack; listed its hard mathematical obligations rather than assuming them. Actual-source critical-value step under investigation.

## Refined attack: pass to the universal cover before classifying E

The punctured-plane obligation need not be isolated. Once the completed surface E exists, take its universal cover U. The entire lift g:C→E lifts to h:C→U because C is simply connected. Uniformization and Liouville should exclude U=disc; compact U cannot support the nonconstant projection U→C. Thus U=C and Xi=F̃∘h for an entire F̃. Restriction of F̃ over C\{0,-1} must be proved a covering. This is the precise way to retain the two-singular-value property after the universal-cover step; do not merely assert stability of asymptotic values under composition.

This unifies E=C and E=C*. In the latter coordinates F̃(w)=F(exp(w)), but no extension of F through zero is used. It also avoids prematurely asserting that E itself has only two conformal types.

The resulting general candidate theorem is stronger: an entire finite-order f with infinitely many critical values and no polynomial left factor of degree>1 should induce a surjection on π₁ after deleting the inverse image of any finite target set B. Proof still requires covering completion, uniformization, positive lower growth for transcendental finite-singular-value entire functions, and finite-order composition rigidity. These are active mathematical obligations, not hypotheses smuggled into an unconditional theorem. For Xi, polynomial-left-factor exclusion already exists, and the infinite-critical-value source lemma is being formalized.

## Constructive growth attack (paper derivation, dependencies still open)

A sharper route to the finite-order composition obligation has two geometric steps.

1. **Circle coverage from two omitted values.** Normalize g(0)=0. Suppose g(D_r) fails to contain either full circle |w|=R or |w|=2R. Choose omitted a,b on those circles. The normalized map (g-a)/(b-a) omits 0,1, and its value at 0 lies in a fixed compact subset of C\{0,1}: its modulus lies between 1/3 and 1 and its distance to 1 between 2/3 and 2. A *uniformly anchored* Schottky estimate on D_{r/2} would imply M_g(r/2)≤C R with absolute C. Contraposition gives a fully covered circle at radius R or 2R whenever M_g(r/2)>C R. Hence M_{F∘g}(r)≥M_F(R). Existing `SchottkyDiskGrowth.exists_exp_bound_of_omitting_disk` has a map-dependent constant; extracting uniformity over that compact anchor set is an explicit missing step, not already provided by its statement. Local sections of the modular covering and compactness should supply it.

2. **Positive lower growth from one logarithmic tract.** If transcendental entire F has no singular values outside a disk, prove some exterior component is a logarithmic tract. Its inverse logarithm φ:H→C is univalent. A disk-to-half-plane map plus the Koebe upper growth bound gives |φ(x)|≤C x² along the positive real axis. Since |F(φ(x))|=exp(x), this forces log M_F(R)≥c sqrt(R) for all sufficiently large R. Combining with step 1 and a finite-order bound for F∘g gives a polynomial bound on M_g, hence g is polynomial by Cauchy estimates.

Crucial unresolved details: construction/classification of the exterior tract (a finite covering end would force polynomial F); anchored uniformity; availability/formalization of Koebe growth; normalization constants; and conversion of polynomial norm bounds to polynomiality. This is a proof attack, not a claimed theorem. It avoids relying on the corpus's weaker Clunie characteristic-ratio result.

### Corpus correction: circle coverage already formalized

Further source inspection found `HTGeometry/PolyaCompositionMaximum.lean`, not the earlier `RHTower/PolyaCompositionGrowth.lean`. Its `exists_polya_constant` is the exact absolute-constant composition maximum inequality required above, proved through `BohrCoveringCircle.exists_covered_circle`. Thus the proposed uniform-Schottky subproblem is already solved in the corpus and must not be re-created or called new. `CompositionGrowthHeight.growthHeightAtLeast_comp_add` consumes it, but the arbitrary transcendental-inner/polynomial conclusion still needs its precise argument. No general Koebe growth bound was found by source search in mathlib Analysis/Complex, HTGeometry or Bottcher; this is a scoped negative search, not an absence certificate.

## Composition rigidity: completed paper reduction to polynomial growth

Assume entire F has positive lower order in the exact corpus sense: for some δ>0, every sufficiently large R admits |w|≤R with |F(w)|≥exp(R^δ). Suppose F∘g has finite order. Normalize h=g−g(0), G(w)=F(w+g(0)); translating the argument preserves positive lower order after decreasing δ if necessary (the disk of radius R around g(0) contains the disk of radius R−|g(0)| around zero).

Let c>0 be the verified Pólya constant. There are C,d>0 with M_{G∘h}(r)≤exp(C(1+r)^d). For any sufficiently large r and H=M_h(r/2), Pólya gives M_G(cH)≤M_{G∘h}(r). If cH is above the lower-growth threshold, then (cH)^δ≤C(1+r)^d, so H≤c⁻¹ C^(1/δ)(1+r)^(d/δ). If cH is below the threshold, H is bounded by that fixed threshold divided by c. Choose an integer n≥d/δ. The resulting polynomial bound for h outside a disk extends globally by compactness. `PolynomialAntiderivative.exists_polynomial_of_polynomial_growth` now gives a polynomial h, hence polynomial g.

All ingredients of this conditional lemma have corpus counterparts (Pólya maximum inequality; polynomial-growth recognition; elementary powers/translation/compactness). Formal statement and proof pending. It does NOT establish the still-missing positive-lower-order property of the hypothetical transcendental cover projection.

The actual polynomial-inner branch has been removed separately by the new Xi critical-value accumulation theorem: finite critical values of F plus polynomial g imply finite critical values of F∘g. See the formalized child card `../3-formalized/xi-nonzero-critical-value-accumulation.md`.

## Geometric test of the abstract obstruction (new conjecture, not a route switch)

Candidate explicit realization: L(z)=(z−1)exp(z). Formal differentiation should give L'(z)=z exp(z), so it has exactly one critical point (0), critical value −1, and one simple zero (1). Along the negative real ray L tends to zero. These facts suggest its inverse-sheet monodromy around 0 and −1 realizes the already formalized action on Option Z: a fixed sheet plus a translating integer line for 0, and a transposition linking the fixed sheet to that line for −1.

**Unproved:** that zero is its only finite asymptotic value; covering over C\{0,−1}; the exact sheet labeling and generator action. Do not identify this entire map with the abstract countermodel without those proofs. If established, it would show the obstruction can occur for finite-order entire maps and explain why the actual Xi infinite-critical-value theorem supplies genuinely additional source information. This test remains subordinate to the same exact Xi monodromy conjecture.

## Cover completion: local construction worked out on paper

Let B be finite and H the image subgroup of f:C\f⁻¹(B)→C\B. For each b∈B choose a disk avoiding the other marks. The components of its lifted punctured disk correspond to cycles of the peripheral permutation on sheets. A finite cycle of length e is the e-fold punctured-disk cover; cap it with one point using the chart in which projection is b+ζ^e. Do not cap infinite cycles.

The proposed atlas is Hausdorff: charts attached over different marked disks are disjoint; charts for different cycles over one disk are disjoint; points already in the uncompleted cover separate by their old charts, which lie over the unmarked base. Countability of the sheet set gives a countable atlas. These statements still need a formal construction of the topology and chart transitions.

At a deleted source point a, write f(z)−b=(z−a)^m u(z), with u(a)≠0. The lift of a source meridian is closed, so the peripheral cycle containing its sheet has finite length e dividing m. In its cap chart the lifted map is (z−a)^(m/e) times a holomorphic e-th root of u, up to a fixed e-th root of unity. Hence it extends across a. No infinite-cycle end receives a source puncture by fiat.

After a universal cover U→E is available, projection U→C remains a covering over C\B: take a simply connected target disk disjoint from B. The first cover splits into disks over it, and the universal cover splits over each such disk. Thus the composite is trivial over that disk. If uniformization gives U=C, its entire projection has no critical values outside B and no finite asymptotic values there. For the latter, a curve tending to infinity whose image tends to w∉B eventually lies in a single lifted disk; the inverse branch makes the curve converge to a finite point, a contradiction.

**Still unproved/formally absent here:** the global covering/classification construction, the analytic capped atlas, and the uniformization step. This paragraph supplies the missing local extension and outside-B asymptotic reasoning; it is not a claim that the complete global construction is done.

## Stronger positive survivor suggested by the same proof

The proposed covering argument would first prove a general finite-index theorem: if an entire finite-order f has infinitely many critical values, then its induced image after deleting any finite target set B has finite index. Indeed the transcendental completed-cover projection is excluded by positive lower order plus the polynomial-inner result, forcing a polynomial projection; a polynomial has finite covering degree away from its critical values. Polynomial-left-factor primitivity would then upgrade finite index to index one.

This is a new *conjectural* strengthening of the same mechanism, not a proven classification. It exposes the positive statement behind exclusion of the infinite-index case. The analytic completion/uniformization and tract-growth obligations remain unchanged. The explicit L(z)=(z−1)exp(z) candidate tests sharpness of the infinite-critical-values hypothesis.

## Stronger completion deduction: E itself is simply connected

The universal-cover step can be removed if E is constructed as above from the *actual image* subgroup H. Let X=C\f⁻¹(B) and let g°:X→E° be the lifted map. Because p_* is injective with image exactly H=f_*(π₁X), the map g°_* is surjective onto π₁(E°).

The inclusion j:E°→E induces a surjection on π₁: the added points form a closed discrete set, and a compact loop meets only finitely many of them; replace its small disk pieces by detours around those finitely many points. After the extension g:C→E is established, the composite j∘g° factors through the simply connected plane. Thus j_*∘g°_*=0. Both maps are surjective, so π₁(E)=0.

This is stronger than merely passing to a universal cover. It rules out E=C* and any nontrivial fundamental group directly, and the remaining uniformization obligation is only for the simply connected noncompact E. Disk uniformization would contradict Liouville applied to g; plane uniformization would provide the desired entire factorization. The cover construction, loop-detour lemma and analytic uniformization still need formal proofs; the group-surjectivity deduction itself is complete on paper. This is a refinement of the same conjecture, not an abandonment of its missing geometry.

## Corpus-driven replacement for the missing Koebe bound

The exact quadratic Koebe growth theorem is unnecessary. A weaker polynomial bound for a univalent inverse logarithm suffices, and can be attacked directly from the proved `BohrCoveringCircle.exists_covered_circle`.

Fix its constant c>0 at rho=1/2. If an injective holomorphic disk map h omits a, then
|h(z)−h(0)| ≤ |h(0)−a|/c for |z|≤1/2.
Otherwise normalize by H=|h(z)−h(0)|. Bohr supplies a covered circle centered at h(0), of radius at least cH>|h(0)−a|. An injective holomorphic disk image is simply connected, so a covered circle cannot enclose an omitted point: pull the circle back by the continuous inverse, contract it in the disk, and use invariance of winding around a. This is the exact topological lemma to formalize; the proof does not invoke a recalled Koebe theorem.

Apply this to a univalent inverse logarithm phi:H→C whose image omits a fixed a. The disk centered at x>0 with radius x lies in H. At its real point 3x/2 the estimate gives
|phi(3x/2)−a| ≤ B |phi(x)−a|, where B=1+1/c>1.
Hence |phi((3/2)^n)|≤|a|+B^n |phi(1)−a|. Choose an integer N with B≤(3/2)^N. The chart has polynomial growth along these geometrically spaced real points. If F(phi(x))=R exp(x) with R≥1, its values there grow exponentially in x. Comparing adjacent radii, then decreasing the exponent to absorb constants, gives `PositiveLowerOrder F` on every sufficiently large disk.

**Status:** paper attack with elementary winding and geometric-sequence details exposed; no formal theorem claimed yet. Remaining tasks are the precise disk-image winding lemma, transfer to the ray recurrence, the all-radii lower bound, and construction of a logarithmic tract from a transcendental projection covering the exterior disk. The exact composition and actual Xi finite-critical-value exclusion needed afterward are now Lean-checked.

### Stronger simplification from actual root/Schottky code

Reading mathlib's partial Riemann-mapping square-root construction exposed a shorter proof of the required local growth bound. Choose s²=f−a and normalize psi=−s/s(c). If c is the unique preimage of f(c), psi omits 0 and 1 and psi(c)=−1. The existing compact-base Schottky theorem with the singleton base {−1} bounds psi uniformly on the half disk, and squaring gives |f(z)−a|≤B|f(c)−a|. Thus full injectivity is stronger than needed, and the circle-filling/winding lemma can be bypassed by a dependency-closed analytic proof. Card: `../3-formalized/one-fiber-omitted-value-disk-growth.md`; scratch formalization in progress. This directly addresses the same missing tract-growth step.

## Exterior-cover obligation, sharpened to peripheral orbits

For an entire projection F covering the exterior of a disk, an infinite orbit of one sheet under the exterior circle should supply the needed injective inverse logarithmic chart: lift the exponential half-plane cover through F; equality of two lifted values would differ by an integer deck translation, contradicting the infinite peripheral orbit.

The complementary statement to prove is: a finite peripheral orbit of length e forces F polynomial. Minimality of e gives an injective holomorphic parametrization psi of that lifted exterior component by an exterior disk, with F(psi(t))=t^e after scaling. At infinity psi cannot have an essential singularity: its dense tail image would meet an open local image of a finite point, violating injectivity. A removable limit is impossible because F(psi(t)) tends to infinity. Thus psi has a pole at infinity; its image contains a neighborhood of infinity and the identity forces polynomial growth of F, hence F is polynomial.

These arguments still require formal analytic continuation/cover classification and isolated-singularity details. They identify precise finite-orbit and infinite-orbit theorems to construct, rather than treating a logarithmic tract as a new input to the final Xi monodromy statement.

## Current frontier after the checked growth results (2026-10-09)

Completed in Lean: infinite nonzero critical values of actual Xi; polynomial-inner finite-critical-value exclusion; positive-lower-order composition rigidity; one-center-fiber disk distortion; geometric inverse-chart growth; and the actual Xi nonexistence theorem for finite-critical-value outer factors carrying such a chart. All audited declarations use only standard axioms.

Still active: construction and analytic capping of the exact image cover, proof of its simple connectedness, intrinsic plane/disc uniformization, and production of the logarithmic chart from an infinite exterior peripheral orbit (with polynomiality in the finite-orbit case). No missing item has been promoted to an assumption in a purported Xi-monodromy or RH theorem. Exact monodromy surjectivity and RH remain unproved.

## Capping loop-surjectivity now checked (2026-10-09)

`HTGeometry/OpenCapFundamentalGroup.lean` proves the single-cap inclusion is surjective, computes its exact normal-closure kernel, handles any basepoint in the body, and proves every loop class in a directed open union comes from one member.

`HTGeometry/OpenCapFamily.lean` builds the relative attachment and finite-stage induction, then proves the arbitrary-family theorem. Pairwise disjointness is unnecessary: distinct cap intersections need only lie in the original open body. Its puncture-deletion corollary states that if a closed set A has, at each a, an open simply connected neighborhood meeting A exactly in {a} and with path-connected punctured part, then inclusion X\A→X is surjective on π₁, assuming X\A path connected. This removes the formerly missing loop-detour lemma once the actual cap charts are built.

Both production leaf builds and all eight declaration axiom audits pass (standard axioms only). The global construction and analytic uniformization are still open. Full details and verification logs are on `../3-formalized/open-cap-fundamental-group-surjection.md`. Final direct source checks of both modules also pass with empty logs.

## Local ramification extension now checked (2026-10-09)

`HTGeometry/PuncturedPowerRoot.lean` proves that a holomorphic punctured lift s with s^n=f, f analytic and f(a)=0, extends analytically by setting s(a)=0. It proves the exact analytic-order identity and classifies existence at a finite-order zero: a punctured holomorphic n-th root exists if and only if n divides the zero order. Thus extension of a lift in the chart b+ζ^n is derived without assuming divisibility beforehand; divisibility follows from the lift.

Production leaf build, six-declaration standard-axiom audit, and final actual-source check all pass. Card `../3-formalized/punctured-power-root-extension.md`. Construction of the exact image cover is now pursued explicitly in `../3-formalized/universal-cover-subgroup-factorization.md`; its first ingredient constructs sheet-moving deck homeomorphisms using unique lifts from the simply connected cover. This remains the same actual Xi image-cover conjecture, not a replacement target.

## Exact actual Xi image cover now constructed (2026-10-09)

`HTGeometry/SubgroupCover.lean` constructs subgroup orbit covers and proves their exact induced fundamental-group images. `ImageCoverLift.lean` proves the lift to the exact image cover induces a surjection on fundamental groups. `RHTower/XiMarkedImageCover.lean` applies this to actual Xi and every actual finite-mark coordinate using the transported corpus modular-lambda universal cover. The untwisted theorem `xi_exact_image_cover_factorization` has no mathematical hypotheses.

All four new modules passed their production leaf builds, all 28 declaration axiom audits (standard axioms only), and final actual-source checks. The topological construction card moved to `../3-formalized/universal-cover-subgroup-factorization.md`. Global lint has seven unrelated unreachable-module errors; no own-module or forbidden-declaration errors. This discharges the abstract cover-existence and loop-surjective source-lift obligations, not the original target-surjectivity conjecture.

The next active construction is `../3-formalized/xi-image-cover-analytic-capping.md`: classify peripheral components, attach finite power-chart caps, extend the actual source lift, and use the checked cap theorem to deduce simple connectedness. Intrinsic uniformization and exterior-orbit classification remain open. The same exact Xi monodromy conjecture remains the target; no RH implication is asserted from it alone.

## Peripheral classification and local source capping checked (2026-10-09)

`PuncturedDiskCover.lean` and `PuncturedDiskCoverClassification.lean` classify every connected, locally path-connected covering of the punctured unit disk as a positive power cover or the exponential half-plane cover. `AnalyticZeroCoverCap.lean` proves that a continuous punctured lift of an analytic zero excludes the exponential alternative and extends analytically in the finite power chart, with exact multiplicity identity. No finite-sheet premise or prior analytic atlas on the cover is assumed in this local theorem.

All three leaf builds, forty-nine standard-only axiom audits and three final actual-source checks pass. This discharges the local classification/extension mechanism. Component restriction, the global cap atlas, global extension, intrinsic uniformization and exterior analytic classification remain active obligations; the exact Xi monodromy and RH statements remain unproved.

## Explicit cap topology and component bridge checked (2026-10-09)

`CoveringComponentRestriction.lean` now proves that peripheral source components inherit covering maps. `PeripheralCoverComponent.lean` applies the power/exponential classification and analytic zero extension to those components. `SubgroupCoverTopology.lean` derives Hausdorffness, second countability and countable component indexing from the actual subgroup-cover construction.

`DisjointPointCaps.lean` explicitly constructs the completion topology, open old/cap embeddings, Hausdorffness through projection separation and second countability for countably many caps. `DisjointPointCapsFundamentalGroup.lean` identifies the overlaps and proves old-body loop surjectivity and path connectedness. All five additional leaf builds, forty-two public-declaration axiom audits and final actual-source checks pass. Cards: `../3-formalized/peripheral-component-bridge.md` and `../3-formalized/disjoint-point-cap-completion.md`.

The actual Xi peripheral index/charts and global extended lift still need assembly. The generic construction has not been presented as an already completed actual Xi surface. Exact monodromy surjectivity and RH remain unproved; the same route continues.

## Actual topological completion and simple connectedness verified (2026-10-09)

The actual peripheral index, disjoint target charts, chosen power charts and cap family are now assembled in `XiPeripheralTargetCharts.lean`, `XiPeripheralComponents.lean` and `XiPeripheralCaps.lean`, with `PuncturedDiskCapModel.lean`. The completed projection is continuous and remains a covering precisely on its old unmarked part; its space is Hausdorff, second countable and path connected. `PuncturedSourceDisk.lean`, `PuncturedLocalGluing.lean` and `XiIsolatedMarkedPunctures.lean` supply the source neighborhoods and local-to-global gluing. These seven modules and all seventy-one public declarations pass production builds, standard-only axiom audits and final source checks.

`XiContinuousCappedLift.lean` now extends the actual lift over every deleted source point, preserving Xi. `CappedSimplyConnectedFactorization.lean` proves the commuting-diagram loop argument, and `XiSimplyConnectedCappedFactorization.lean` applies it unconditionally to actual Xi. These three additional modules and all seven public declarations pass the same checks. Card: `../3-formalized/xi-simply-connected-capped-factorization.md`.

Thus actual Xi now has a continuous factorization through a simply connected completed image cover. The remaining construction is its analytic atlas and analyticity of both maps. A zero-allowing continuous-root theorem and a generic positive-power atlas theorem have passed scratch Lean checks; their actual Xi application is being checked. Intrinsic uniformization and exterior analytic classification remain open. The original monodromy conjecture and RH remain unproved.

## Actual analytic completion verified (2026-10-09)

`ContinuousAnalyticRoot.lean` removes the nonvanishing restriction from continuous-root analyticity. `ComplexPowerAtlas.lean` constructs a complex analytic manifold from covering power coordinates, proves the projection analytic, and upgrades every continuous lift with analytic projection. `XiCappedAnalyticAtlas.lean` constructs those coordinates on the actual completed cover, proves noncompactness, and combines all previous results into `xi_analytic_simplyConnected_capped_factorization`, with no mathematical hypotheses.

All three leaf builds, twenty-one standard-only public-declaration axiom audits and three final actual-source checks pass. The completion card is now `../3-formalized/xi-image-cover-analytic-capping.md`. The next active obligation is `xi-capped-surface-uniformization.md`: construct a global analytic coordinate, then use the existing geometric growth and composition results. A bounded injective analytic coordinate is already excluded by a checked scratch argument using the actual entire lift and Liouville. Global uniformization, the exterior analytic classification, exact monodromy surjectivity and RH remain unproved.

The subsequent planar-image rigidity result is now fully verified: `XiCappedNoBoundedEmbedding.lean` excludes bounded injective analytic maps and proves that every analytic open embedding of the selected actual surface into C is onto, using `ParabolicOpenEmbedding.lean`. Both builds, all four standard-only axiom audits and both final source checks pass. Card: `../3-formalized/xi-capped-planar-image-rigidity.md`. Existence of a global embedding remains the precise next conjecture. All new modules are indexed; global lint has eight unrelated unreachable-module errors and no errors in this work. Audit details are on the completed capping card.
