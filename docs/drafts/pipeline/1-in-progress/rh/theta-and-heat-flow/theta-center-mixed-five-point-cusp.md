# Theta center-mixed five-point cusp

- **ID:** TCD-C12-FIVE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** rh-current-frontier-map.md · route TCD
- **Statement:** For every critical aperture `0 < a < 1/2`, the equispaced five-node Gram matrix of the theta center-mixed density is positive definite on a punctured neighborhood of the coalesced node.
- **Status:** `[GLOBAL NATIVE D1 LEAN-PROVED] [ACTUAL RANK-THREE MIXTURE LEAN-PROVED] [ACTUAL ARBITRARY FIVE-POINT CLUSTERS LEAN-PROVED] [GENERAL-PACKET/COFINAL CONTINUATION OPEN]`

## Goal

**Current dependency state.** D1, D2, and D3 are Lean-proved. See the dependency-closed cards
`../../../3-formalized/clg-ttf-global-native-d1.md`,
`../../../3-formalized/clg-ttf-rank-three-center-mixture.md`, and
`../../../3-formalized/clg-ttf-five-point-cusp.md`. The actual five-node matrix is positive
definite for every distinct configuration below one aperture-dependent diameter bound, independently
of ordering and spacing ratios. See `../../../3-formalized/clg-ttf-arbitrary-five-point-clusters.md`.
Mixed divided differences and the existing C8 theorem give uniform control of every cluster shape. General-packet
extension, theta-specific all-packet incidence, and cofinal no-escape remain. The source investigations
below retain their scoped statements; their former D1/D2/D3 gaps are discharged by these capstones.

The finite rank-five target is complete. This notebook retains the source investigations supporting that theorem; active continuation is the general-packet/cofinal programme. The cusp uses the literal theta source and center-mixture representation with every sign input discharged.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: finite cusp has a dependency-closed proof in the linked formalized card
- [x] 2 → 3 formalized: finite cusp passes direct `lake env lean`, with new-capstone axiom audit PASS; no cascading or umbrella rebuild
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus-driven decomposition

For an even kernel sampled at `0,h,2h,3h,4h`, reversal symmetry splits the five-by-five Toeplitz Gram form into an odd block of dimension two and an even block of dimension three.

- The odd block's first nonzero coalesced coefficient is governed by the already proved strict second--sixth signed reflected Hankel determinant.
- The even block's first nonzero coefficient is governed by the signed three-by-three reflected jet matrix
  ```text
  [[ J0, -J2,  J4],
   [-J2,  J4, -J6],
   [ J4, -J6,  J8]].
  ```
- Corpus search found `integral_twoByTwo_det_pos` but no corresponding strict three-by-three integral-mixing theorem. It found all-order matrix spectral machinery only under stronger spectral-representation or separation hypotheses not yet established for this center mixture.

## Conjecture loop

### D1 — global source eighth-Hankel curvature

For every real source coordinate, the signed three-by-three reflected jet matrix above is positive definite. In normalized complete-log coordinates
`A = -ℓ₂`, `B = -ℓ₄`, `C = -ℓ₆`, `D = -ℓ₈`, its determinant is an explicit polynomial. The existing sixth-curvature proof supplies the leading two principal minors; new burden is the determinant involving `D`.

Attack: extend corpus likelihood-score and Bell-transfer infrastructure from order six to order eight, prove symbolic score identities, derive analytic rational tail bounds, and clear the resulting polynomial chamber in Lean. No numerical interval certification.

**Seam result `[PROVED HERE]`.** The self-dual modular ODE closes two further jet steps. For modular mass `M`, scale `R`, and `X=R²`, the signed rank-three determinant is exactly `M⁶ P₁₂(X)`. After `X=191/10+y`, every coefficient of `P₁₂(191/10+y)` is strictly positive. Since the actual source satisfies `X>191/10` and `M>0`, the complete theta source has strict signed rank-three reflected eighth-jet curvature at `x=0`. This is an exact rational polynomial proof, not interval arithmetic. Global continuation remains D1.

**Open center chamber `[PROVED HERE]`.** The native rank-three determinant is continuous because every complete-source iterated derivative is continuously differentiable. Seam strictness therefore persists on some symmetric interval `|x|<δ`, with `δ>0`. Thus D1 is now closed on a nontrivial open source chamber; remaining burden is continuation away from that chamber.

**Order-eight likelihood ladder `[PROVED HERE]`.** Exact seventh/eighth cumulants and source-coordinate jets are formalized. More than `2/3` of normalized eighth spectral moment survives in eighth cumulant. Complete-source raw rank-three curvature is exactly `4 Φ(x)^6` times normalized D1 polynomial on `x>0`; all Bell terms through order eight and actual log jets are now closed.

**Low-score obstruction and positive survivor `[PROVED HERE]`.** Literal eighth source score
`P₈(z)=z⁸-28z⁷+266z⁶-1050z⁵+1701z⁴-966z³+127z²-z`
is negative at proved support margin `z=47/5`, so pointwise score positivity is false and cannot prove D1. Fixed spectral carrier exposes stronger fact: dominant `n=2` component is Dirac mass at gap three plus a Lebesgue ray. Exact incomplete-Laplace integration makes their combined eighth score strictly positive for every physical `A≥157/50`. After clearing `(A-3/2)^9`, certificate is positive-coefficient polynomial in `A-157/50`. Every `n≥3` component lies in `z≥24` positive Taylor chamber. Consequently complete ordinary eighth likelihood jet is strictly positive and satisfies sharp proved lower bound
```text
(128/15) A^8 m₈ < ordinary₈.
```
Equivalently, integrated score retains more than `1/30` of leading unnormalized eighth moment. Trial constant `1/10` fails at seam; direct positive-coefficient certificate also fails at `1/25`, while `1/30` succeeds simultaneously for dominant and stable atom-rays.

**Dominant grade-two absorption `[PROVED HERE]`.** Fixed binary fusion constant is wrong order-eight invariant: exact dominant pair/single core ratio is not controlled by seam-sharp constant as `A` moves. Convolving two gap-three rays introduces transform
```text
T₂(r,z)=P₈(z)+2rP₈'(z)+3r²P₈''(z)+...+9r⁸P₈⁽⁸⁾(z).
```
Its literal weighted-ray integral is proved. Complete `(3,3)` core—Dirac--Dirac, both mixed sectors, and ray--ray—is strictly below degree-twenty Taylor polynomial for `exp(3A)` times compensated one-particle core. Multiplication by exact `exp(-3A)` particle activity gives
```text
(3/2) dominantPairMass₈(A) < dominantSingleMass₈(A),  A ≥ 157/50.
```
After shifting `A=157/50+s`, cleared fusion difference has positive coefficients. The `3/2` reserve is essential: coefficientwise proof fails at factor `7/4` and gives an exact one-third one-particle budget for the remaining pair chambers.

**Full grade-two absorption `[PROVED HERE]`.** Every pair outside `(2,2)` has total gap at least eleven and scaled support above `34`. On that chamber, exact symbolic envelopes are
```text
P₈(z) ≤ z⁸,   T₁(r,z) ≤ 2z⁸,   T₂(r,z) ≤ 4z⁸,   0≤r≤2.
```
Normalized ray coefficient is at most corresponding point coefficient, giving factor-nine bound for every atom pair. New Gaussian sums close infinite arithmetic chambers:
```text
Σ_{n≥3} n⁴(n²-1)⁸e^{-π(n²-1)} ≤ 25/99,
Σ_{n≥3} n⁴e^{-π((n²-1)-3)} ≤ 1/999.
```
Hence each ordered dominant--stable tail costs at most `(5200/11)A⁸e^{-3A}`, stable--stable square costs at most `A⁸e^{-3A}`, and all non-dominant pairs cost at most `(10411/11)A⁸e^{-3A}`. Dominant single mass exceeds `(17496/5)A⁸e^{-3A}`; non-dominant total fits strictly inside its one-third reserve. Therefore complete ordered grade-two sector—dominant, both mixed orientations, and stable square—is strictly smaller than dominant one-particle mass. Remaining logarithmic/D1 burden starts at higher even Fock grades.

**Higher-even Fock budget absorption `[PROVED HERE]`.** Sharpened exact exponential certificates give
```text
Σ_{n≥3} n⁴(n²-1)⁸e^{-π(n²-1)} ≤ 100/1999,
Σ_{n≥3} n⁴e^{-π((n²-1)-3)} ≤ 20/999999.
```
The coupled dominant monomial ray costs at most sixteen point monomials; every stable ray costs at most three. Consequently complete one-particle eighth monomial mass is at most `1300000 A⁸e^{-3A}`. For theta activity `r`, corpus theorem `399r<1` and order-eight convex fusion give the exact infinite logarithmic scalar
```text
Σ_{q=4,6,8,...} q⁷ r^(q-1) < 1/3000.
```
All higher even grades therefore cost at most `(1300/3)A⁸e^{-3A}`. Combined with sharpened non-dominant pair cost `(376399/1999)A⁸e^{-3A}` and dominant `3/2` reserve, source-defined eighth Fock odd weight is strictly positive for every `x≥0`. Remaining burden is no longer an estimate: prove exact identity connecting this completed Fock budget to literal eighth logarithmic jet entering D1.

**Ordinary source landing `[PROVED HERE]`.** Complete ordered pair sector and higher-even loss are nonnegative. Splitting the summable one-particle score tower at dominant atom shows Fock reserve is strictly below dominant mass, hence below full unnormalized ordinary score. Exact partition normalization and `399r<1` give `1<256/(1+r)`, so reserve lands strictly inside literal normalized ordinary eighth source jet. Thus remaining log-J8 connector has one precise missing identity: ordered convolution/Fock grades must be matched to negative even Bell grades of `d⁸ log(1+r(x))`; no positivity, summability, source-scaling, or normalization estimate remains.

**Exact Bell decomposition and higher-even absorption `[PROVED HERE]`.** Literal log-J8 has the exact finite identity
```text
J8_log = b8 - B₈,₂ + 2B₈,₃ - 6B₈,₄ + 24B₈,₅ - 120B₈,₆
         + 720B₈,₇ - 5040B₈,₈.
```
Ordinary source jets `b1,...,b6` are strictly positive, so odd grades `B₈,₃,B₈,₅,B₈,₇` are favorable. New four-, six-, and eight-factor likelihood moment laws cost exactly `p³,p⁵,p⁷`. Their coefficient sums fit the corresponding `4⁷r³,6⁷r⁵,8⁷r⁷` Fock terms. Consequently
```text
6B₈,₄ + 120B₈,₆ + 5040B₈,₈ ≤ (256/P) · higherEvenFockLoss.
```
The exact logarithmic connector is therefore reduced to one theorem: normalized Bell grade two must land inside `(256/P)` times complete ordered pair score mass.

### D2 — strict three-by-three mixture law

**Closed.** `HedenmalmCenterMixedEighthHankelClosure` integrates the globally strict source form through an exact cofactor-vector identity and identifies every entry with a literal center derivative through order eight.

### D3 — five-point parity cusp

**Closed.** `ThetaCuspCenterMixedFivePointCusp` proves the literal matrix positive definite throughout a punctured neighborhood. `FivePointFiniteDifferenceCusp` gives the exact parity-adapted congruence and normalized-entry convergence. Only C8 regularity is required; determinant differentiation through order twelve is unnecessary.

### Pivot criteria

If D1 is false, prove the exact sign obstruction and audit D2 directly: pointwise failure need not imply failure after positive mixing. If the center determinant is also false, extract the sharp aperture/radial boundary or maximal rank-four survivor before retiring this branch. Missing order-eight or order-twelve infrastructure is not a pivot criterion.

## Novelty collision audit

Closest August 2026 item is Planat--Solé's second-level concavity theorem for the classical Xi kernel. Its inequality uses derivatives through order eight and may be algebraically related to one principal-minor expression. Before any novelty claim, compare its exact transformed kernel and determinant polynomial with D1 and with the center-mixture theorem. D1--D3 now have the corpus proofs named above; no external novelty claim is made here.

Exact comparison now separates the statements. Planat--Solé prove negativity of the successive-derivative Hankel determinant `det(s^(i+j))_(0≤i,j≤2)` for `s(t)=Φ(√t)` in radial-square coordinate, equivalently strict log-concavity of `s'²-ss''`. D1 is positivity of the signed even reflected-product jet determinant of `u↦Φ(x+u)Φ(x-u)` in logarithmic source coordinate, for every center `x`. Derivative order overlaps, but kernel, coordinate, determinant, and sign differ. The seam theorem above is therefore not obtained from their result.

## Lean artifacts

- `HilbertMetric/ReflectionEighthJet.lean`: exact eighth reflected product jet and even-log determinant polynomial.
- `HTGeometry/PolynomialODEJetRankThreeClosure.lean`: exact ten-jet self-dual ODE elimination.
- `RHTower/PrimeArchThetaModularDifferentialClosure.lean`: actual theta-source modular connector.
- `RHTower/PrimeArchThetaBornWittenEighthJet.lean`: actual Born--Witten seventh/eighth jets and atomwise D1 positivity.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodSeventhEighthCumulant.lean`: exact cumulants and quantitative `κ₈>(2/3)m₈`.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodSeventhEighthSourceJets.lean`: actual source jets and exact pointwise low-score obstruction.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthScoreRayTransform.lean`: exact one- and two-ray incomplete-Laplace transforms, dominant Dirac--ray compensation, and `1/30` core certificate.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthOrdinaryPositivity.lean`: strict full ordinary eighth-jet positivity and sharpened `(128/15)A⁸m₈` normalized-moment lower bound.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthDominantPairCompensation.lean`: degree-twenty exponential fusion and strict dominant grade-two absorption.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthStablePairCompensation.lean`: exact atom-pair core, factor-nine transform envelope, Gaussian stable-tail budgets, and complete ordered grade-two absorption.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthFockSector.lean`: sharp stable Gaussian bounds, full one-particle monomial budget, `q⁷` higher-even summability, and strict completed even-Fock reserve.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthFockTraceConnector.lean`: positivity of completed losses and strict coefficient-faithful landing inside literal ordinary eighth source jet.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthBellGrades.lean`: exact literal log-J8 Bell decomposition, positivity of all favorable odd grades, and reduction to four even losses.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthBellHigherEvenAbsorption.lean`: iterated normalized-moment product laws, exact monomial trace, and absorption of Bell grades four, six, and eight into higher-even Fock loss.
- `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthLogJets.lean`: actual complete-source seventh/eighth log jets and normalized D1 polynomial.
- `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthBellTransfer.lean`: exact raw-to-log D1 connector through Bell order eight.
- `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthHankelSeam.lean`: strict source seam theorem and nontrivial open D1 chamber.

## No-go closure

- **Exact killing theorem/mechanism:** open
- **Strongest positive survivor:** exact atom-ray compensation, strict ordinary eighth likelihood jet with `1/30` leading-moment survival, strict absorption of complete infinite even-Fock budget, exact literal Bell decomposition, and complete absorption of negative Bell grades four, six, and eight; D1 holds on a nontrivial open center chamber.
- **New insight:** rank five separates exactly into previously closed odd rank-two curvature and new even rank-three eighth-jet determinant. Pointwise eighth-score sign and fixed-constant binary fusion are wrong invariants. Exact ray convolution and gap-separated Gaussian activity close all two-particle chambers; logarithmic `1/q` cancellation reduces every higher even grade to `Σq⁷r^(q-1)<1/3000`. Iterated moment multiplication identifies Bell grades `4,6,8` with finite subterms of that scalar. Remaining obstruction is only exact ordered-pair trace identification for Bell grade two, not higher sectors, tail size, normalization, or source scaling.
- **Status:** active paper/Lean conjecture loop

## Log

- 2026-08-27 — created directly in 1-in-progress after corpus audit; D1 selected as hardest source-pure open core.
- 2026-08-27 — exact reflected eighth-jet determinant identity and strict rank-three modular-seam theorem proved in Lean; global D1 continuation remains active.
- 2026-08-27 — completed seventh/eighth cumulant and source-jet ladders, Bell transfer, raw/native D1 connector, and open center chamber in Lean.
- 2026-08-27 — disproved pointwise eighth-score route at `47/5`; proved exact `n=2` Dirac--ray compensation, stable-tower positivity, full ordinary eighth-jet positivity, and quantitative `1/100` eighth-moment survival. Global logarithmic grade-two compensation remains open.
- 2026-08-27 — sharpened one-particle survival from `1/100` to `1/30`; proved exact two-ray transform and degree-twenty exponential-Taylor absorption of dominant `(3,3)` two-particle sector. Fixed fusion constants failed and were replaced by activity-coupled fusion.
- 2026-08-27 — strengthened dominant absorption to a `3/2` reserve; proved factor-nine non-dominant pair envelope, exact `25/99` and `1/999` Gaussian budgets, and strict absorption of complete infinite ordered grade-two sector. Higher even Fock grades remain.
- 2026-08-27 — sharpened Gaussian budgets to `100/1999` and `20/999999`; proved dominant/stable monomial-ray factors `16`/`3`, full one-particle budget, `Σq⁷r^(q-1)<1/3000`, and strict absorption of complete even-Fock budget. Exact connector to literal logarithmic J8 remains.
- 2026-08-27 — proved complete loss nonnegativity and strict Fock-reserve landing into literal normalized ordinary eighth source jet. Remaining connector is exact ordered-convolution to negative-even Bell-grade identification.
- 2026-08-27 — proved exact literal order-eight Bell-grade decomposition, positivity of favorable odd grades, four/six/eight-factor normalized-moment laws, exact full monomial trace, and absorption of Bell grades four, six, and eight into completed higher-even Fock loss. Exact log-J8 positivity is reduced to grade-two ordered pair trace.

**Exact pair trace and literal log-J8 positivity `[PROVED HERE]`.** Product exponential tilting is exactly the product Gibbs density. Absolute integrability permits expansion of the spectral product into the ordered atom-pair sum. For every atom pair, finite shifted incomplete-Laplace moment algebra identifies the explicit point/ray score mass with its literal product-measure integral; this includes the ray--ray sector without a new convolution axiom. Countable Fubini and the exact four-sector split then give
```text
algebraicPairTrace₈ = pairSectorMass₈.
```
Consequently Bell grade two is at most `(128/P²)·pairSectorMass₈`. Since `P=1+r≥1`, this is at most `(256/P)·pairSectorMass₈`, matching the higher-even coefficient. The ordinary leading trace contains `(256/P)` times dominant one-particle mass, so the strict positive Fock reserve survives after every negative even Bell grade. Favorable odd grades yield the literal theorem
```text
0 < d⁸/dx⁸ log(thetaCuspLikelihoodPartition(thetaCuspLikelihoodCoordinate x)),
    for every x ≥ 0.
```
All connector and positivity theorems pass direct Lean, targeted module builds, and axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`. This closes the global order-eight logarithmic likelihood burden; next D1 burden is transfer of this signed eighth likelihood input through the full reflection determinant polynomial.

**New Lean artifacts.**

- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthPairTraceIntegral.lean`: exact algebraic-pair/product-integral identity.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthAtomPairTrace.lean`: exact point/ray atom-pair integral formula, including symbolic ray--ray shifted moments.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthPairSectorTrace.lean`: product tilting, absolutely convergent atom expansion, four-sector reassembly, and `algebraicPairTrace₈ = pairSectorMass₈`.
- `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthLogPositivity.lean`: coefficient-matched even-loss absorption and strict literal logarithmic J8 positivity on `x≥0`.

- 2026-08-27 — proved exact tilted-product trace, exact atom-pair trace including ray--ray sector, absolutely convergent four-sector pair reassembly, and strict literal logarithmic eighth likelihood jet positivity for all physical sources. Global D1 transfer remains active.

**Quantitative D1 transfer and chamber split `[PROVED HERE]`.** The exact determinant gain of the
literal likelihood eighth jet is
```text
(4A²-B) J8,
```
and `B<2A²`, so the proved logarithmic floor gives the strict native gain
```text
128000 A² A_scale⁸ exp(-3 A_scale).
```
The complete second/fourth likelihood perturbation preserves a strict no-sixth baseline globally.
Actual D1 is exactly that baseline plus eighth gain minus the positive sixth displacement. Above
first-atom weight five, the uniform worst sixth loss still leaves a positive polynomial; the
elementary source bound places every `x≥11/20` in this chamber. Thus D1 is now unconditional on the
complete large-source half-line. Remaining scalar burden is compact `0≤x<11/20`.

**Sharp compact reserve `[PROVED HERE]`.** Independent linear jet bounds erase crucial fourth-jet
correlations. Expanding the exact D1 polynomial while applying curvature monotonicity only to its
Born baseline gives a stronger lower reserve: it retains the favorable cubic and quadratic fourth
terms, the favorable fourth--eighth coupling, and the exact linear-plus-quadratic sixth loss. The
native D1 dominates this explicit reserve for every `x≥0`; positivity of this one scalar is now a
sufficient compact endpoint.

**Atom-pair PSD obstruction and diagonal-absorption survivor `[PROVED HERE]`.** Decomposing the
reflected product into individually positive-semidefinite symmetrized atom pairs is impossible.
In readout coordinates, normalized first--second cross signed curvature is
```text
2(C(q)+C(r)-(S(q)-S(r))²),
S(q)=3/2+3/q-2q,  C(q)=(2q+3)(2+3/q²),  r=4q+9/2.
```
Throughout `41/25≤q≤23/14` it lies strictly between `-1058` and `-656`; the physical modular seam is
inside this interval. Hence pair-channel PSD fails already at its signed second entry. Positive
survivor is quantitative: for every nonnegative mixing weight `ρ≤1/100`, first diagonal alone
absorbs the defect and the mixed signed second entry is strictly positive. Corpus activity bound
`399r<1` implies actual second-to-first atom likelihood at seam lies in this chamber, so physical
first-plus-second mixture is strictly positive despite its indefinite cross channel. Any rank-three
proof must use diagonal domination or nonlinear Schur absorption, not termwise pair PSD.

**New Lean artifacts.**

- `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthLikelihoodGain.lean`: exact `(4A²-B)J8` gain and quantitative native lower gain.
- `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthLowerJetBaseline.lean`: globally positive no-sixth baseline and exact coupled sixth/eighth burden.
- `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthCompactReserve.lean`: sharp nonlinear compact lower reserve.
- `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthLargeWeight.lean`: strict native D1 for `x≥11/20`.
- `RHTower/ThetaCusp/ThetaCuspFirstSecondAtomCrossHankelObstruction.lean`: exact cross-indefiniteness interval and physical diagonal-absorption survivor.

- 2026-08-27 — proved quantitative eighth likelihood gain, strict global lower-jet baseline, exact sixth/eighth coupling, sharp nonlinear compact reserve, and unconditional D1 for `x≥11/20`. Compact interval remains.
- 2026-08-27 — disproved atom-pair PSD at first--second signed curvature with uniform defect `656<-cross<1058`; proved `ρ≤1/100` diagonal absorption and instantiated it for actual seam likelihood weight. Rank-three compact work continues through nonlinear absorption.

**Refined worst-sixth chamber `[PROVED HERE]`.** The earlier weight-five boundary was not sharp.
After clearing the exact rational profiles, each of the three independent certificates needed by
the large-weight transport—worst-loss baseline, curvature bracket, and bracket derivative—has a
positive-coefficient expansion already from
```text
q = thetaCuspBornWittenWeight 1 x ≥ 19/4.
```
Therefore the full Born-top baseline and native rank-three curvature are strict throughout that
weight chamber. An eighth-order Taylor lower bound gives the exact source landing
```text
x ≥ 69/200  ⇒  π exp(2x) > 25/4  ⇒  q > 19/4,
```
so native D1 is unconditional on `x≥69/200`. This replaces the prior `x≥11/20` endpoint and shrinks
the remaining finite source chamber to `0≤x<69/200` (a reduction of `41%` in interval length).
The proof is symbolic: rational profile clearing, positive-coefficient expansions, and the finite
Taylor lower bound; it uses no interval oracle or computed certificate.

**Conjecture-loop audit.** A global positive representing measure for all even likelihood log jets
is impossible because the corpus already proves the likelihood law is not Thorin/GGC infinitely
divisible. Termwise symmetrized atom-pair PSD is also false by the proved first--second cross
obstruction. The surviving next attack is nonlinear compact absorption on `0≤x<69/200`, coupling
the exact sixth loss to eighth Fock grades and retained fourth-jet terms. The August 2026
Planat--Solé second-level concavity result concerns a different order-two transform and reports
higher Turán orders open; it does not supply this rank-three D1 sign.

**New Lean artifact.** `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthRefinedLargeWeight.lean` proves the
three refined profile certificates, Born-top and native D1 positivity at weight `19/4`, the exact
Taylor landing, and native D1 positivity for every `x≥69/200`. Direct Lean, exact module build, and
axiom audit pass; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-27 — sharpened S6F large-source boundary from `x≥11/20` to `x≥69/200`; remaining compact D1 chamber is `0≤x<69/200`.

**Sharp physical first--second reserve `[PROVED HERE]`.** Direct reduction of the second-to-first
theta likelihood weight at the modular seam gives the exact identity
```text
ρ₂ = ((32π-12)/(2π-3)) exp(-3π).
```
The corpus enclosure `exp(-3π)<1/12000`, together with its certified lower bound on `π`, proves the
strict chamber estimate `445ρ₂<1`. Combining this with the uniform cross budget
`-1058<cross(q,4q+9/2)` yields a stronger diagonal-absorption law: throughout
`41/25≤q≤23/14`, every `ρ≥0` with `445ρ≤1` leaves mixed signed-second reserve strictly greater than
`21`. In particular the physical first-plus-second mixture at the modular seam has reserve `>21`.
This quantitative margin is available for the remaining rank-three Schur/determinant closure.

**Conjecture-loop boundary.** Exact rational endpoint reductions for the full first--second
rank-three determinant remained positive at both seam interval endpoints with `ρ=1/100`, but the
attempted global two-variable positive-coefficient certificates produced mixed-sign coefficients;
this is a failed certificate, not a counterexample. A separate scalar erasure of all favorable
fourth/eighth correlations at `q=41/25` fails with a worst-sixth budget `10000` and succeeds with
budget `5000`. Thus any compact proof based only on an independent sixth upper bound must cross
that narrow threshold; current global sixth estimates do not. Surviving route is correlated
full-determinant or nonlinear Schur absorption, retaining fourth/eighth structure.

**New Lean artifact.** `RHTower/ThetaCusp/ThetaCuspFirstSecondAtomSharpSeamWeight.lean` proves the exact seam
ratio, `445ρ₂<1`, uniform reserve `>21`, and its unconditional physical specialization.

- 2026-08-28 — sharpened actual second-atom seam weight to `ρ₂<1/445` and proved physical
  first--second mixed signed-second reserve `>21`; full compact rank-three determinant remains open.

**Shared sixth--eighth spectral law and lower-jet reserve `[PROVED HERE]`.** The fixed
higher-theta spectral measure has support at `t≥3`. Its ordinary sixth score is bounded by the
leading sixth monomial, while the fully resummed logarithmic eighth jet retains `32/325` of its
normalized leading eighth monomial. The support recurrence `M₈≥9M₆`, combined with the sharp
log-sixth/ordinary-sixth comparison, gives the strict global law
```text
(9/676) A_scale² J₆ < J₈,   x≥0.
```
The sharp compact eighth coefficient is positive on the entire physical half-line. Multiplying
the spectral law by this coefficient eliminates the independent `J₈` variable from the compact
reserve: the resulting sixth-spectral reserve is a strict lower bound for the prior compact
reserve and depends only on `J₄` and `J₆`. Positivity of this reduced reserve therefore implies
native D1 positivity.

**Spectrally refined native chamber `[PROVED HERE]`.** Applying the same coupling before the
conservative compact curvature estimate is stronger. In the native worst-curvature polynomial,
retain the guaranteed eighth gain while inserting the uniform sixth budget `63232`. Exact profile
clearing at
```text
q = thetaCuspBornWittenWeight 1 x = 47/10
```
proves positivity of the compensated baseline, the worst-sixth curvature bracket, and its
derivative bracket. On the only new strip `47/10≤q<19/4`, the effective sixth-loss coefficient is
strictly positive, so the identity
```text
actual − worst = K₈·(J₈ − (9/676)A_scale²J₆)
               + (63232−J₆)·(L_eff+63232+J₆)
```
is a sum of two strict positive terms. Curvature and fourth-jet transport then give native D1
positivity for every `q≥47/10`. An order-eight rational Taylor lower bound proves
```text
31/5 < π exp(17/25),
```
hence every `x≥17/50` lies in the new chamber. Remaining scalar interval is now
`0≤x<17/50`.

**Conjecture-loop audit.** The first trial asserted that the compact reserve's conservative
`A₀³` sixth coefficient would already permit the same `q=47/10` threshold. Its cleared polynomial
has negative constant term there, so that conjecture is false. The surviving correction keeps
sixth/eighth coupling in the native polynomial, where the coefficient is the physical
worst-curvature `W³`; all three required profile certificates then become positive at `47/10`.
A stronger `q=9/2` native uniform-loss conjecture was also rejected by a negative cleared constant,
so no unsupported endpoint extrapolation was retained.

**New Lean artifacts.** `RHTower/ThetaCusp/ThetaCuspLikelihoodSixthEighthSpectralCoupling.lean` proves the
ordinary sixth leading-moment bound, retained eighth Fock fraction, and global strict jet coupling.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthSixthSpectralReserve.lean` proves positivity of the compact
eighth coefficient and the lower-jet reserve reduction.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthSpectralRefinedWeight.lean` proves the `47/10` native chamber,
exact Taylor landing, and native D1 positivity for `x≥17/50`. Direct Lean, exact module builds, and
axiom audits pass; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — proved global strict sixth--eighth likelihood coupling and eliminated independent
  eighth-jet estimation from the compact reserve.
- 2026-08-28 — used native spectral compensation to sharpen S6F large-source boundary from
  `x≥69/200` to `x≥17/50`; remaining compact D1 chamber is `0≤x<17/50`.

**Scale-local sixth collapse and `q=9/2` chamber `[PROVED HERE]`.** The negative `q=9/2`
constant for the *uniform* loss budget does not obstruct a source-faithful bound. Once source scale
`A≥6`, write the dominant score coordinate as `3A-9=9+s`, `s≥0`. Positive-coefficient Taylor
envelopes at this new center, together with `A/(A-3/2)≤4/3`, give
```text
dominant sixth-score mass < 44,
complete sixth-score integral < 55,
J₆ < 3700.
```
This is a factor greater than `17` improvement over uniform `J₆<63232`. After inserting `3700`,
the cleared rank-three baseline, curvature bracket, and derivative bracket all have positive
coefficients from `q≥9/2`. Exact sixth, curvature, and fourth-jet transport plus positive eighth
gain therefore prove native D1 throughout that chamber. The finite Taylor certificate
```text
6 < π exp(13/20)
```
places every `x≥13/40` there. Remaining scalar interval is now `0≤x<13/40`, a further reduction
from `17/50`.

**New Lean artifacts.** `RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleSixBound.lean` proves the recentered
point/ray envelopes and scale-local `J₆<3700`. `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleSix.lean`
proves the `q≥9/2` rank-three chamber and native D1 positivity for every `x≥13/40`. Direct Lean,
targeted module builds, and axiom audits pass; axioms are only `propext`, `Classical.choice`, and
`Quot.sound`.

- 2026-08-28 — recentered the exact dominant sixth score at scale six, improved local `J₆` budget
  from `63232` to `3700`, and sharpened S6F large-source boundary to `x≥13/40`; remaining compact
  D1 chamber is `0≤x<13/40`.

**Second scale-local chamber at `A≥11/2` `[PROVED HERE]`.** Propagating the scale-six
positive-coefficient score envelopes to shifted center `15/2`, and proving the exact ray
comparison
```text
Ray(11/8,y) ≤ (6/5) Ray(4/3,y),
```
controls the lower chamber `A≥11/2`. The exponential enclosure
`exp(-33/2)<1/8000000` gives
```text
dominant sixth-score mass < 426,
complete sixth-score integral < 437,
J₆ < 30000.
```
After inserting this source-local budget, exact coefficient clearing proves the reflected
rank-three baseline, curvature bracket, and derivative bracket positive from `q≥4`. The same
curvature/fourth/sixth transport and favorable eighth likelihood channel yield native D1
positivity there. An order-eight finite Taylor certificate proves
```text
11/2 < π exp(9/16),
```
so every source `x≥9/32` lies in the chamber. Remaining scalar interval is now
`0≤x<9/32`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleElevenHalvesBound.lean` proves the shifted point/ray
envelopes and scale-local `J₆<30000`.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleElevenHalves.lean` proves the `q≥4` profile chamber
and native D1 positivity for every `x≥9/32`. Direct Lean, targeted module builds, and axiom
audits pass; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — extended source-faithful sixth-score decay below scale six and sharpened S6F
  large-source boundary to `x≥9/32`; remaining compact D1 chamber is `0≤x<9/32`.

**Center-specific scale-five collapse and `q=7/2` chamber `[PROVED HERE]`.** Propagating the
prior coarse envelope is far from sharp at `A=5`. Re-expanding the literal positive sixth-score
polynomial at its exact shifted center `6`, with physical ray ratio `A/B≤10/7`, instead proves
```text
ScoreShift(6+s) ≤ 3000000 exp(s),
Ray(10/7,6+s) ≤ 8000000 exp(s).
```
The rational enclosure `exp(-15)<1/3000000` then gives
```text
dominant sixth-score mass < 30,
complete sixth-score integral < 41,
J₆ < 2800.
```
Thus moving one half-unit lower in source scale improves, rather than worsens, the certified
sixth loss: direct recentering removes the inherited envelope slack. Inserting `2800` makes all
three cleared profile certificates strictly positive from `q≥7/2`. Exact jet transport and the
positive eighth likelihood gain prove native D1 in that chamber. The finite Taylor certificate
```text
5 < π exp(15/32)
```
places every `x≥15/64` there. Remaining scalar interval is now `0≤x<15/64`.

**New Lean artifacts.** `RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleFiveBound.lean` proves the exact
center-six point/ray envelopes and scale-local `J₆<2800`.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleFive.lean` proves the `q≥7/2` profile chamber and
native D1 positivity for every `x≥15/64`. Direct Lean, targeted module builds, and axiom audits
pass; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — discovered direct recentering reverses the inherited-envelope loss at scale five,
  proving `J₆<2800` and sharpening S6F large-source boundary to `x≥15/64`; remaining compact D1
  chamber is `0≤x<15/64`.

**Half-integral scale chamber at `A≥9/2` `[PROVED HERE]`.** At shifted center `9/2`, direct
positive-coefficient expansion with physical ray ratio `A/B≤3/2` proves
```text
ScoreShift(9/2+s) ≤ 1300000 exp(s),
Ray(3/2,9/2+s) ≤ 4300000 exp(s).
```
A separate rational half-exponential argument combines `exp(-13)<1/440000` with
`exp(-1/2)<61/100`, yielding `exp(-27/2)<1/720000`. Consequently,
```text
dominant sixth-score mass < 65,
complete sixth-score integral < 76,
J₆ < 5100.
```
With this loss, exact coefficient clearing proves the baseline and both curvature-transport
brackets strictly positive from `q≥3`. Native D1 follows by the same exact jet transport and
positive eighth channel. The order-nine Taylor certificate
```text
9/2 < π exp(23/64)
```
places every `x≥23/128` in the chamber. Remaining scalar interval is now
`0≤x<23/128`.

**New Lean artifacts.** `RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleNineHalvesBound.lean` proves the
center-`9/2` score envelopes, rational half-exponential enclosure, and `J₆<5100`.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleNineHalves.lean` proves the `q≥3` profile chamber
and native D1 positivity for every `x≥23/128`. Direct Lean, targeted module builds, and axiom
audits pass; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — proved half-integral scale-local sixth decay and sharpened S6F large-source boundary
  to `x≥23/128`; remaining compact D1 chamber is `0≤x<23/128`.

**Scale-four chamber at `q≥5/2` `[PROVED HERE]`.** Exact recentering at shifted score coordinate
`3`, with physical ratio `A/B≤8/5`, gives
```text
ScoreShift(3+s) ≤ 500000 exp(s),
Ray(8/5,3+s) ≤ 2300000 exp(s).
```
Together with `exp(-12)<1/160000`, these bounds prove
```text
dominant sixth-score mass < 154,
complete sixth-score integral < 165,
J₆ < 11000.
```
Despite the larger likelihood loss, exact profile clearing at `q=5/2` leaves the rank-three
baseline, curvature bracket, and derivative bracket strictly positive. Native D1 follows on the
whole weight chamber. The finite Taylor certificate
```text
4 < π exp(31/128)
```
places every `x≥31/256` there. Remaining scalar interval is now `0≤x<31/256`.

**New Lean artifacts.** `RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleFourBound.lean` proves the
center-three score envelopes and `J₆<11000`.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleFour.lean` proves the `q≥5/2` profile chamber and
native D1 positivity for every `x≥31/256`. Direct Lean, targeted module builds, and axiom audits
pass; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — extended exact recentered sixth-score control to scale four and sharpened S6F
  large-source boundary to `x≥31/256`; remaining compact D1 chamber is `0≤x<31/256`.

**Lower-chamber no-go and `A≥39/10` survivor `[PROVED HERE]`.** Direct recentering remains
effective at `A=7/2`: center `3/2`, ratio `7/4`, and `exp(-21/2)<1/36000` support a local
budget near `J₆<26000`. However, exact endpoint reduction proves the independent-sixth
rank-three baseline is negative at `q=2`; even adding the guaranteed global spectral gain
`A_scale²J₆/69<J₈` leaves the endpoint baseline negative. The analogous direct
`A=15/4`, `q=9/4`, `J₆<16600` endpoint is also negative, with or without that global
eighth compensation. These are genuine scalar no-go results for this loss-erasure method.

The strongest surviving lower chamber comes from `A≥39/10`. At shifted center `27/10` and
ratio `A/B≤13/8`, exact positive-coefficient envelopes prove
```text
ScoreShift(27/10+s) ≤ 400000 exp(s),
Ray(13/8,27/10+s) ≤ 2100000 exp(s).
```
The finite exponential argument `exp(-117/10)<1/118000` then yields
```text
dominant sixth-score mass < 188,
complete sixth-score integral < 199,
J₆ < 13300.
```
All three exact profile certificates are strict from `q≥12/5`, giving native D1 there. The
Taylor landing
```text
39/10 < π exp(7/32)
```
places every `x≥7/64` in the chamber. Remaining scalar interval is now `0≤x<7/64`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleThirtyNineTenthsBound.lean` proves the exact local score
envelopes and `J₆<13300`.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleThirtyNineTenths.lean` proves the `q≥12/5` profile
chamber and native D1 positivity for every `x≥7/64`. Direct Lean, targeted module builds, and
axiom audits pass; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — proved exact no-go endpoints for independent-sixth/global-eighth compensation at
  `q=2` and `q=9/4`; extracted and formalized the `q≥12/5` survivor, sharpening S6F boundary
  to `x≥7/64`; remaining compact D1 chamber is `0≤x<7/64`.

**Corrected scale-`11/2` spectral chamber and sharp shared-spectrum law `[PROVED HERE]`.** The
previous entry for the scale-`11/2` filenames described a coarse inherited `J₆<30000` estimate.
Those modules now contain a direct center-`15/2` expansion instead. Exact coefficientwise bounds
```text
ScoreShift(15/2+s) ≤ 7000000 exp(s),
Ray(11/8,15/2+s) ≤ 24000000 exp(s),
exp(-33/2) < 1/14000000
```
give dominant sixth-score mass `<16`, complete score integral `<27`, and the substantially sharper
literal budget `J₆<1800`. Independently, the exact Fock-loss ledger retains `544` dominant units,
then `1/2400` of the complete leading eighth moment and `8/75` after logarithmic normalization.
Together with the improved log-sixth ratio `207/200` and support recurrence `M₈≥9M₆`, this gives
the clean strict law
```text
(1/69) A_scale² J₆ < J₈.
```
Inserting both `J₆<1800` and this eighth compensation proves the baseline and both transport
brackets from `q≥4`; the effective coefficient is positive on the handoff strip `4≤q<9/2`.
An order-eight Taylor certificate gives `11/2 < π exp(281/500)`, hence native D1 for
`x≥281/1000`. Later scale-four and scale-`39/10` chambers supersede this source endpoint, but the
`J₆<1800` estimate and `1/69` coupling remain strictly stronger reusable inputs.

**Conjecture-loop boundary below scale four.** At the next half-step `A≥7/2`, `q≥2`, exact cleared
profiles reject scalar loss budgets `14000`, `12000`, and `10000`; `8000` succeeds. A proposed
absolute eighth floor and its half-and-half affine combination with the `1/69` spectral law still
fail above a loss budget of roughly `9000`. Meanwhile the direct center-`3/2` ray envelope already
requires constant term `321865957/256`, exposing a sixth mass far above that tolerance. Thus the
half-step cannot close by independent scalar `J₆/J₈` boxes. Surviving compact route must retain a
quantitative fourth displacement or a finer joint sixth--eighth decomposition. The sharper source
landing conjecture `11/2 < π exp(14/25)` was also rejected; `281/500` is the proved nearby landing.

**New Lean artifacts.** `RHTower/ThetaCusp/ThetaCuspLikelihoodSixthEighthSpectralCoupling.lean` now proves
the retained Fock fractions and global `1/69` coupling.
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleElevenHalvesBound.lean` proves the direct score envelopes and
`J₆<1800`.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleElevenHalves.lean` proves the compensated `q≥4`
chamber and `x≥281/1000` capstone. Direct Lean, exact targeted builds, and axiom audits pass;
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — sharpened global sixth--eighth coupling to `1/69`, scale-`11/2` literal sixth loss
  to `J₆<1800`, and isolated quantitative fourth displacement/joint spectral structure as the
  surviving mechanism below the scalar-box boundary.

**Scale-`31/8` survivor and the `q=7/3` scalar boundary `[PROVED HERE]`.** The next natural
endpoint `A=23/6`, `q=7/3` admits a direct local estimate near `J₆<14200`, but exact coefficient
clearing makes its independent-sixth rank-three baseline negative at the endpoint. Thus merely
refining the scalar sixth budget at this rational step does not extend D1.

Moving to `A≥31/8`, with shifted center `21/8` and physical ratio `A/B≤31/19`, exact
positive-coefficient envelopes prove
```text
ScoreShift(21/8+s) ≤ 340000 exp(s),
Ray(31/19,21/8+s) ≤ 1930000 exp(s).
```
The rational factorization
```text
exp(-93/8) = exp(-11) exp(-5/8) < 1/109000
```
then gives
```text
dominant sixth-score mass < 185,
complete sixth-score integral < 196,
J₆ < 13100.
```
All three cleared profile certificates remain strictly positive from `q≥19/8`. Exact jet
transport and the favorable eighth likelihood channel therefore prove native D1 throughout that
weight chamber. The finite Taylor landing
```text
31/8 < π exp(27/128)
```
places every `x≥27/256` there. Remaining scalar interval is `0≤x<27/256`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleThirtyOneEighthsBound.lean` proves the score envelopes,
exponential enclosure, mass bounds, and `J₆<13100`.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleThirtyOneEighths.lean` proves the `q≥19/8` profile
chamber and native D1 positivity for every `x≥27/256`. Both are wired into the RHTower umbrella.
Direct Lean, targeted module build, and axiom audit pass; axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

- 2026-08-28 — rejected the `q=7/3`, `J₆<14200` independent scalar endpoint; formalized the
  surviving `q≥19/8` chamber and sharpened the S6F source boundary to `x≥27/256`.

**Quantitative fourth floor and scale-`7/2` spectral coupling `[PROVED HERE]`.** The ordinary
fourth score now has a sharp lower logarithmic orientation
```text
(19/20) J₄,ordinary < J₄,log.
```
Retaining the dominant square-gap-three atom gives the global, source-uniform floor
```text
7800 A_scale⁴ exp(-3 A_scale) < J₄,log.
```
This is unconditional on the full physical half-line and supplies a reusable quantitative
fourth displacement below every compact scale cutoff.

At `A_scale≥7/2`, a new exact dominant pair/single comparison improves the shared sixth--eighth
law. The positive-coefficient boundary is `5/2`: lower attempted constants `3`, `11/4`, `13/5`,
and `51/20` fail, while
```text
(5/2) PairCore < Taylor20 · SingleCore
```
closes. Consequently the odd Fock reserve retains `1477 A⁸exp(-3A)`, more than `1/900` of the
leading eighth moment, and the literal jets obey
```text
(1/26) A_scale² J₆ < J₈
```
throughout this scale chamber, improving the global coefficient `1/69` by more than a factor of
two and one half.

**Conjecture-loop no-go and survivor.** A proposed pointwise joint fourth--sixth--eighth score,
after paying the provisional bound `J₆<26000`, is strictly positive at the physical corner
`(q,z)=(2,21/2)` but strictly negative at the exact admissible point `(q,z)=(2,11)`. Thus the
simple pointwise linearization is false, not merely inaccessible to coefficientwise positivity.
Independent insertion of the global fourth floor and the local `1/26` coupling also cannot pay
the `J₆²` loss at this endpoint. The surviving mechanism is the exact nonlinear compact reserve
with scale-adapted fourth and sixth bounds. Concurrent corpus work has now realized that survivor
at `q≥7/3`, giving native D1 for `x≥1/10`; the next open compact chamber is `0≤x<1/10`.

The next rational attack point `q=9/4` exposes a sharp design target in closed Lean scratch:
the joint reserve is positive at `(e₄,e₆)=(50,15832)` but negative at `(48,15832)`. Hence a
scale-`15/4` advance must either retain at least fifty fourth-jet units, improve the sixth budget,
or use a still finer joint trace inequality; repeating independent scalar boxes cannot suffice.

**New Lean artifacts.** `RHTower/ThetaCusp/ThetaCuspLikelihoodFourthDominantAtomLower.lean` proves the
dominant atom moment injection and global `7800 A⁴exp(-3A)` fourth-log-jet floor.
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthEighthScaleSevenHalvesCoupling.lean` proves the sharp local Fock
comparison, retained fractions, and `1/26` jet coupling. The fourth lower orientation is in
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthSixthSpectralDomination.lean`. All are wired into the RHTower
umbrella. Direct Lean checks, exact targeted builds, formal lint for forbidden declarations, and
axiom audits pass for these modules; axioms are only `propext`, `Classical.choice`, and
`Quot.sound`. Repository-wide lint still reports unrelated concurrently created unwired modules.

- 2026-08-28 — proved global quantitative fourth displacement and local `1/26` sixth--eighth
  coupling; falsified the naive pointwise joint score at `(2,11)`; isolated the scale-`15/4`
  `e₄/J₆` tradeoff as the next S6F boundary.

**Joint fourth--sixth scale-`23/6` survivor `[PROVED HERE]`.** The negative independent-sixth
endpoint at `q=7/3` is not a dead end for the exact compact reserve. The likelihood source has a
simultaneous fourth-jet floor. First, a global cumulant-retention theorem proves
```text
(19/20) J₄^ordinary < J₄^log.
```
On the compact scale band `23/6≤A≤31/8`, an exact first-atom fourth-moment lower bound then gives
`J₄^ordinary>30`, hence `J₄^log>28`. The matching direct sixth-score analysis at shifted center
`5/2` proves
```text
ScoreShift(5/2+s) ≤ 310000 exp(s),
Ray(23/14,5/2+s) ≤ 1850000 exp(s),
exp(-23/2) < 1/96000,
dominant sixth-score mass < 201,
complete sixth-score integral < 212,
J₆^log < 14200.
```

The new joint reserve keeps both jets instead of erasing fourth displacement. Exact clearing proves
it positive at `(J₄,J₆)=(28,14200)` for every `q≥7/3`. It is increasing in `J₄`; on
`7/3≤q≤19/8`, its concave sixth term is minimized over `0≤J₆≤14200` at the upper endpoint because
the factored sixth-loss coefficient is strictly positive. Therefore the actual sixth-spectral
reserve is positive throughout `23/6≤A≤31/8`. Splicing this compact chamber to the existing
`q≥19/8` result proves native D1 for every `q≥7/3`. The exact Taylor landing
```text
23/6 < π exp(1/5)
```
places every source `x≥1/10` there. Remaining D1 interval is now `0≤x<1/10`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthCompactLowerBound.lean` proves the ordinary fourth-moment floor,
global `19/20` log-retention law, and compact `J₄^log>28` theorem.
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleTwentyThreeSixthsBound.lean` proves the direct scale-`23/6`
sixth-score estimates and `J₆^log<14200`.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleTwentyThreeSixthsJoint.lean` proves exact joint-reserve
monotonicity, compact positivity, the `q≥7/3` splice, and native D1 for `x≥1/10`. All three are
wired into the RHTower umbrella. Direct Lean and targeted module builds pass. Axiom audits return
only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint reports no forbidden declaration
in these modules; repository-wide reachability lint remains red only on unrelated concurrent
unwired modules. A targeted 2026-08-28 primary-literature search found general Hankel determinant
and total-positivity results (including arXiv:0901.1883 and arXiv:2606.31647), but no prior result
for this theta-cusp likelihood source, its `19/20` fourth-cumulant retention law, the joint
fourth--sixth reserve, or the resulting RH-route D1 chamber.

- 2026-08-28 — converted the failed independent-sixth `q=7/3` endpoint into a joint fourth--sixth
  survivor, formalized a global `19/20` fourth-cumulant retention law, and sharpened native D1 to
  `x≥1/10`; remaining compact D1 interval is `0≤x<1/10`.

**C20 conjecture loop below `x=1/10` `[OPEN CORE]`.** Corpus search first exposed two facts that
change the lower-compact problem: native raw D1 is already strictly positive at the modular seam
`x=0`, while scale `A≥7/2` has the stronger shared-spectrum law `A²J₆/26<J₈`. Exact endpoint
probes then rejected successive scalar conjectures. At `q=2`, even the stronger `1/26` reserve is
negative for `(J₄,J₆)=(30,26000)` and `(150,26000)`; it turns positive only by fourth floor `180`.
The direct scale-`7/2` ray transform has unavoidable endpoint coefficient
`321865957/256`, so the existing scalar exponential-envelope method cannot lower the sixth budget
to the roughly `15000--18000` range needed by attainable fourth floors. The global and local
absolute eighth floors are also far too small. This retires independent scalar fourth/sixth/eighth
boxes at the next chamber.

**Positive survivor and named open core.** The remaining interval is a bridge between strict
modular-seam positivity and the proved half-line `x≥1/10`. The surviving mechanism is the
unspecialized self-dual modular ODE: eliminate the completed source jets at an arbitrary basepoint,
obtaining the rank-three reflected D1 as a polynomial in the live modular variables `(H,Z,R,P)`,
then prove that polynomial positive on the exact box swept by `0≤x≤1/10`. Existing corpus only
contains the specialization `Z=P=0` at `x=0`. Named open core:
```text
C20-GENERAL-MODULAR-D1:
  construct the arbitrary-basepoint eighth reflected-Hankel ODE elimination and certify its
  positivity on the physical modular trajectory for 0≤x≤1/10.
```
This route preserves the complete cofinal shell cancellation responsible for seam positivity and
avoids the proved scalar-box obstruction.

**C20 native seam closure `[PROVED HERE]`.** The seam theorem above was initially strict only for
the raw reflected determinant, while its factorization through normalized likelihood jets required
`x>0`. Corpus-guided continuity closes that normalization gap. Each native jet through order eight
is continuous at zero: the eighth likelihood cumulant is expanded into normalized moments, the
Born--Witten eighth jet is continuous because its weight stays nonzero, and all lower jets inherit
continuity from the proved derivative tower. Uniqueness of right-hand limits therefore extends
the positive-side identity to
```text
D1_raw(0) = 4 thetaCuspFullSource(0)^6 D1_native(0).
```
Since `D1_raw(0)>0` and the sixth-power prefactor is nonnegative, the native normalized curvature
is strictly positive at the seam:
```text
0 < D1_native(0).
```
Thus the remaining C20 bridge is now the open interval `0<x<1/10`; no endpoint normalization
burden remains. `C20-GENERAL-MODULAR-D1` stays the named open core for that interval.

**New Lean artifact.**
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthNativeSeam.lean` proves native continuity at zero, exact
raw/native seam factorization, and strict native seam positivity. It is wired into the RHTower
umbrella. Direct Lean and targeted module build pass; forbidden-declaration scan is clean; axiom
audit returns only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — removed the normalized D1 endpoint gap by continuous right-hand transport of the
  raw/native factorization; remaining C20 interval is exactly `0<x<1/10`.

**C20 arbitrary-basepoint modular elimination `[PROVED HERE]`.** The first half of
`C20-GENERAL-MODULAR-D1` is now closed. Instead of manually expanding ten successive ODE jets, the
four-state system is encoded by its polynomial Lie derivative on
`ℂ[H,Z,R,P]`. Iteration constructs universal completed-theta jets; the source operator
`(∂²-1/4)/2` constructs universal theta-cusp source jets. Substitution into the full reflected
product formulas—including all odd jets away from the seam—defines one exact universal polynomial
```text
P_D1(H,Z,R,P) ∈ ℂ[H,Z,R,P].
```
A new real-parameter/complex-target multivariate-polynomial chain rule proves for every smooth
trajectory of the modular ODE that its literal rank-three reflected eighth determinant equals
`P_D1` evaluated at the live state. The actual theta modular functions satisfy that abstract ODE,
and the completed-theta/source jet transfer now holds at every basepoint, not only at zero.
Consequently, for every real `x`,
```text
D1_raw(x) = Re P_D1(H(x),Z(x),R(x),P(x)),
Im P_D1(H(x),Z(x),R(x),P(x)) = 0.
```
The general formula specializes exactly to the independently proved seam closure and is strict at
the self-dual state. The remaining C20 burden is therefore no longer jet elimination: it is the
single semialgebraic/dynamical sign theorem
```text
0 < Re P_D1(H(x),Z(x),R(x),P(x))  for 0<x<1/10.
```

**New Lean artifacts.**
`HTGeometry/PolynomialODEJetRankThreeGeneralClosure.lean` formalizes the chain rule, modular Lie
derivative, universal jets, full arbitrary-basepoint polynomial, and exact closure for every ODE
trajectory. `RHTower/PrimeArchThetaModularDifferentialClosure.lean` now exposes the actual modular
state, proves its vector-field law, extends source-jet transfer to arbitrary basepoint, and
instantiates the universal closure. `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthGeneralModularClosure.lean`
identifies this value with literal raw D1, proves reality, gives the exact positivity equivalence,
and verifies seam specialization. Modules are wired into HTGeometry/RHTower umbrellas. Direct Lean,
targeted builds, forbidden-declaration scans, and axiom audits pass; axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

A targeted 2026-08-28 primary-literature search found classical Hankel identities for Eisenstein
series (Milne, arXiv:math/0009130), general theta/Hankel integrable-system work, and Riemann-xi theta
representations, but no arbitrary-basepoint four-state `(H,Z,R,P)` elimination of this reflected
theta-cusp D1 polynomial or its RH-route positivity problem.

- 2026-08-28 — constructed and formalized the universal arbitrary-basepoint modular D1 polynomial,
  including odd reflected jets; reduced the open interval to one exact polynomial-trajectory sign
  theorem.

**C20 scale-`15/4` affine fourth--sixth chamber `[PROVED HERE]`.** Corpus search and exact endpoint
falsification showed why independent scalar boxes stop below `q=7/3`: at `q=9/4` the joint reserve
is negative at `(J₄,J₆)=(48,15832)` but positive at `(50,15832)`. The surviving conjecture keeps
both source budgets scale-dependent. Writing `A=q+3/2` and `d=A-15/4`, the exact first atom-ray
geometry proves
```text
292 - 108q < J₄,
J₆ < (1656/25)(968 - 324q)
```
throughout `9/4≤q≤7/3`. The fourth bound comes from a new support-edge retention law
`(13/25)z⁴≤thetaLikelihoodFourthScore(z)` for `z≥45/4`, the exact atom-ray fourth moment, and the
live tangent `1-3d≤exp(-3d)`. The sixth bound retains the exact moving ratios `A/B` and `1/B`;
freezing either ratio fails the required affine endpoint. A quadratic exponential envelope and a
degree-fifteen cleared certificate give dominant mass `<228-324d`, complete mass `<239-324d`, and
the displayed logarithmic sixth ceiling.

Substitution into the exact sixth-spectral eighth reserve is coefficientwise positive after
`q=9/4+y`. Separate moving-baseline monotonicity laws in `J₄` and `J₆` transfer that certificate to
the physical source. Hence native D1 is strict for every `q≥9/4`. The exact Taylor landing
```text
15/4 < π exp(9/50)
```
gives native D1 for every `x≥9/100`, improving the earlier `x≥1/10` half-line. Combined with the
proved seam theorem, the remaining C20 sign interval is now exactly `0<x<9/100`; the universal
arbitrary-basepoint modular polynomial remains the complementary mechanism for that interval.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleFifteenFourthsBound.lean` proves the scalar endpoint
`J₆<15832`. `RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleFifteenFourthsAffineLower.lean` proves the live
affine fourth floor. `RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleFifteenFourthsAffineBound.lean` proves
the live affine sixth ceiling. `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleFifteenFourthsAffineJoint.lean`
proves joint reserve positivity and the `x≥9/100` D1 capstone. All are wired into the RHTower
umbrella. Direct Lean checks and exact targeted module builds pass. Axiom audits return only
`propext`, `Classical.choice`, and `Quot.sound`. A targeted 2026-08-28 literature search found
general Hankel total-positivity and Riemann-xi kernel work, but no source-specific affine
fourth/sixth theta-cusp jet chamber, exact moving-ratio reserve, or this D1 threshold.

- 2026-08-28 — proved the coupled affine fourth--sixth chamber at scale `15/4`, sharpened native
  D1 to `x≥9/100`, and reduced the remaining open interval to `0<x<9/100`.

**C20 scale-`359/96` affine fourth--sixth chamber `[PROVED HERE]`.** A second conjecturing loop
tested whether the scale-`15/4` mechanism could cross directly to `A=11/3`. It cannot with the
available first-atom reserve: the proposed dominant sixth mass `<258` is false, and the exact joint
reserve is negative at the proposed `(q,J₄,J₆)` baselines, including strengthened fourth floors.
Coarser midpoint candidates at `A=89/24` and `A=179/48` likewise fail their exact joint endpoint
certificates. This is a proved numerical/algebraic boundary of those proposed profiles, not a
reason to discard the coupled mechanism.

Bisection exposes a surviving chamber of width `1/96`. Set
`A₀=359/96`, `q₀=215/96`, and `d=A-A₀`. Corpus-derived first-atom geometry proves
```text
481 - 192q < J₄,
J₆ < (1656/25)(887 - 288q)
```
throughout `215/96≤q≤9/4`. The fourth floor uses the sharper support law
`(51/100)z⁴≤thetaLikelihoodFourthScore(z)` for `z≥359/32`, a live atom-ray exponential
floor based on `1/75000<exp(-359/32)`, and the exact ray moment at `B≤9/4`. The sixth ceiling
uses the exact moving `A/B` and `1/B` ratios, the elementary enclosure
`exp(-359/32)<1/74000`, and a cleared degree-fifteen certificate giving dominant mass
`<231-288d` and complete mass `<242-288d`.

At the moving baseline, the cleared joint reserve has strictly positive coefficients after
`q=215/96+y`. Fourth-jet monotonicity is also coefficientwise positive. The sixth-loss coefficient
has exactly one negative terminal term `-640000 y¹⁶`; it is absorbed by the preceding positive
`(16884608000/3)y¹⁵` term using `0≤y≤1/96`. These three certificates transfer the baseline
to physical jets and prove native D1 for every `q≥215/96`. The exact Taylor landing
```text
359/96 < π exp(7/40)
```
then proves native D1 for every `x≥7/80`. Together with strict native seam positivity, remaining
C20 sign interval is now exactly `0<x<7/80`; arbitrary-basepoint modular polynomial remains the
complementary mechanism on that interval.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleThreeHundredFiftyNineNinetySixthsAffineLower.lean`
proves fourth floor; `RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleThreeHundredFiftyNineNinetySixthsAffineBound.lean`
proves sixth ceiling; and
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleThreeHundredFiftyNineNinetySixthsAffineJoint.lean`
proves joint reserve and `x≥7/80` D1 capstone. All are wired into RHTower umbrella. Direct Lean
checks and exact targeted builds pass. Forbidden-declaration scan is clean. Axiom audits return
only `propext`, `Classical.choice`, and `Quot.sound`. Existing targeted 2026-08-28 literature audit
for this source-specific affine theta-cusp mechanism found no matching fourth/sixth moving chamber
or D1 threshold result.

- 2026-08-28 — falsified direct `A=11/3` and coarser midpoint profiles, proved surviving exact
  `359/96` chamber, sharpened native D1 to `x≥7/80`, and reduced open interval to `0<x<7/80`.

**C20 scale-local stable tower and `179/48` affine chamber `[PROVED HERE]`.** Corpus search
identified a hidden source of slack in the sixth-jet budget: the stable-atom theorem froze
`A⁶ exp(-Ad)` at `A=π`, although the physical chamber has `A≥179/48`. A scale-monotonicity
certificate now proves, for every `A≥179/48` and stable support depth `d≥8`,
```text
A⁶ exp(-Ad) ≤ (1/20) π⁶ exp(-πd).
```
The elementary anchor `exp(-9/2)<1/80` and the existing corpus stable-tower summation then give
the strict global estimate
```text
∑ stable sixth-score masses < 1,
```
replacing the previous rounded budget `<11`. This is an unconditional scale-local strengthening,
not a numerical evaluation.

With this recovered ten-unit margin, the previously failed `A₀=179/48` candidate survives.
Set `q₀=107/48`, `d=A-A₀`. Exact first-atom ray certificates prove on
`107/48≤q≤9/4`:
```text
265 - 96q < J₄,
J₆ < (1656/25)(1201 - 432q).
```
The fourth profile uses `(51/100)z⁴≤thetaLikelihoodFourthScore(z)` for `z≥179/16` and
`1/72500<exp(-179/16)`. The sixth profile uses `exp(-179/16)<1/72000`, a cleared
degree-fifteen dominant-atom certificate `<237-432d`, and stable mass `<1`, yielding complete
mass `<238-432d`.

Substitution into exact eighth-reflection reserve gives a strictly positive moving baseline.
Fourth monotonicity is coefficientwise positive. Sixth-loss coefficient has one terminal negative
term `-640000 y¹⁶`, absorbed by `(16882048000/3)y¹⁵` using chamber width `0≤y≤1/48`.
Thus native D1 is strict for every `q≥107/48`. Exact Taylor landing
```text
179/48 < π exp(43/250)
```
proves native D1 for every `x≥43/500`. Together with seam positivity, remaining C20 interval is
exactly `0<x<43/500`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleOneHundredSeventyNineFortyEighthsBound.lean`
proves scale monotonicity, factor-`1/20` atom gain, and stable tower `<1`.
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleOneHundredSeventyNineFortyEighthsAffineLower.lean` and
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleOneHundredSeventyNineFortyEighthsAffineBound.lean` prove
moving jet profiles. `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleOneHundredSeventyNineFortyEighthsAffineJoint.lean`
proves joint reserve and `x≥43/500` capstone. All are wired into RHTower umbrella. Direct Lean
checks and exact targeted builds pass. Forbidden-declaration scan is clean. Axiom audits return
only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — strengthened stable sixth tower from `<11` to `<1` on `A≥179/48`, revived and
  proved exact `179/48` chamber, sharpened native D1 to `x≥43/500`, and reduced open interval to
  `0<x<43/500`.

**Novelty audit (literature through 2026-08-28).** Targeted searches covered Riemann-xi theta
derivative positivity, higher Turán inequalities, theta-kernel positivity/no-go results, and the
August 2026 contour-Hankel formulation. Dimitrov--Lucas proves degree-three Jensen/Turán
inequalities for the xi coefficient sequence; Deng--Yang--Lü (arXiv:2608.11520) gives a distinct
zero-contour moment matrix and explicitly leaves independent positivity unresolved. No located
paper contains this normalized theta-cusp likelihood source, the scale-local stable sixth tower
`<1`, the coupled live `J₄/J₆` chamber, or the `x≥43/500` reflected D1 theorem. Search result is
therefore evidence of novelty for exact survivor, not claim of an exhaustive bibliographic proof.

**C20 scale-`89/24` affine chamber `[PROVED HERE]`.** Next conjecturing loop first falsified the
naive extrapolation. At `q=53/24`, exact reserve is nonpositive for fourth floor `51` and complete
sixth mass `247`; coordinated attempted repairs through `(J₄,mass)=(55,246)` and `(52,243)` also
fail. Endpoint reserve turns positive at `(54,242)`. Rather than pivot from unresolved producer
bounds, corpus geometry was sharpened to meet this exact boundary.

Stable scale decay remains strong enough one chamber earlier:
```text
A⁶ exp(-Ad) ≤ (1/20) π⁶ exp(-πd)   (A≥89/24, d≥8),
∑ stable sixth-score masses < 1.
```
New generic infrastructure transfers any almost-everywhere leading-score lower bound directly to
ordinary fourth source jet. Applying it with support edge `z≥89/8`, rational exponential bounds
```text
1/68000 < exp(-89/8) < 1/67800,
```
and exact first-atom ray polynomials proves throughout `53/24≤q≤107/48`:
```text
372 - 144q < J₄,
dominant sixth mass < 665 - 192q,
complete sixth mass < 666 - 192q,
J₆ < (1656/25)(666 - 192q).
```
These profiles glue exactly to previous chamber at right endpoint: fourth floor `51`, complete
mass `238`.

Cleared joint reserve at moving baseline is strictly positive. Fourth monotonicity is
coefficientwise positive. Sixth-loss coefficient again has terminal `-640000y¹⁶`, absorbed by
`(16876928000/3)y¹⁵` on `0≤y≤1/48`. Hence native D1 holds for every `q≥53/24`.
Taylor certificate
```text
89/24 < π exp(83/500)
```
proves native D1 for every `x≥83/1000`, reducing remaining C20 interval to exactly
`0<x<83/1000`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleEightyNineTwentyFourthsBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleEightyNineTwentyFourthsAffineLower.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleEightyNineTwentyFourthsAffineBound.lean`, and
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleEightyNineTwentyFourthsAffineJoint.lean` prove stable,
producer, reserve, and D1 capstones. Generic AE-score transfer theorem was added to
`ThetaCuspLikelihoodFourthScaleOneHundredSeventyNineFortyEighthsAffineLower.lean`. All modules are
wired into RHTower umbrella. Direct Lean checks and exact targeted builds pass. Forbidden scan and
diff check are clean. Axiom audits return only `propext`, `Classical.choice`, and `Quot.sound`.
Global lint still reports only unrelated concurrently created unwired modules; all modules here are
reachable.

Literature audit above also covers this one-step continuation. Located works do not contain the
AE-score source transfer, scale-`89/24` stable tower, moving `(J₄,J₆)` profiles, or
`x≥83/1000` D1 result.

- 2026-08-28 — falsified naive `89/24` profile, solved exact producer boundary, proved coupled
  chamber, sharpened native D1 to `x≥83/1000`, and reduced open interval to `0<x<83/1000`.

**C20 reduced modular Lyapunov closure `[PROVED HERE]`.** Corpus-guided elimination shows the
four-state arbitrary-basepoint system contains a strictly smaller physical dynamical core. Define
```text
S = P + RZ,
A = R²(1-Z²),
W = (2/3)S - RZ,
T = W/R.
```
The actual theta trajectory satisfies the exact autonomous drift and source laws
```text
S' = 3 - S²/3 - 3A/4,
F/H = (2S² + 3A - 18)/48,
S' = -(8 F/H + A/4).
```
Thus the previously mixed source cone is diagonal in `(S,A)`, and source positivity forces
strict global decrease of `S`. The physical trajectory is now proved to lie in
```text
R > 0,  -1 < Z < 0,  S < 0                 (x > 0).
```

The new transverse shear gives a stronger Lyapunov law:
```text
W' = 2 + A/2 + 2S²/9 - (2/3)SW,
T' = (2 + A/2 + 2S²/9)/R > 0,
A' = -2AW.
```
Since `T(0)=0`, exact calculus yields `T(x)>0`, `W(x)>0`, and strict decrease of `A` for every
`x>0`; in particular
```text
0 < A(x) < thetaCuspSelfDualModularScale².
```
This is a genuine dynamical restriction not obtainable from the earlier static sign/source box.
It removes the mixed `P` coordinate, identifies a scale-free strict clock, and supplies the first
monotone compact control on the modular discriminant gap. Remaining compact D1 burden, currently
`0<x<43/500`, is sharpened to positivity of the mass-normalized D1 polynomial along this exact
Lyapunov chamber. Next conjecture loop should rewrite the normalized D1 in `(S,A,T)` and test an
inward-pointing barrier on its zero face; static independent coordinate boxes discard the proved
relations `T'>0` and `A'=-2AW`.

**Lean status.** `RHTower/PrimeArchThetaModularDifferentialClosure.lean` now proves theta-mass
homogeneity, real-state chamber, reduced Riccati equation, diagonal source cone, strict drift
monotonicity, normalized-shear Lyapunov law, exact gap decay, and strict self-dual gap bound.
Direct Lean check and targeted module build pass. Axiom audit for representative reduced and
Lyapunov theorems returns only `propext`, `Classical.choice`, and `Quot.sound`. Existing targeted
literature audit for arbitrary-basepoint theta modular D1 found no matching `(S,A,W,T)` reduction
or normalized-shear Lyapunov law.

- 2026-08-28 — reduced arbitrary-basepoint modular closure to Riccati drift plus discriminant gap,
  discovered/proved strict normalized transverse-shear clock, and proved physical gap decreases
  strictly from self-duality; compact D1 sign remains open on `0<x<43/500`.

**C20 genuine three-state D1 polynomial `[PROVED HERE]`.** The reduction is now polynomial, not
only an identity along the physical orbit. A new universal ring `ℂ[Z,R,S]` carries vector field
```text
Z' = -R(1-Z²),
R' = -(2/3)RS,
S' = 3-S²/3-(3/4)R²(1-Z²),
H' = -(1/6)HS.
```
Iterating its covariant Lie derivative constructs every mass-normalized completed-theta jet and
source jet. Substitution into the full arbitrary-basepoint reflected formulas defines one exact
three-variable polynomial `P_D1^red(Z,R,S)`. For every compatible reduced trajectory, Lean proves
```text
D1_raw(x) = H(x)^6 P_D1^red(Z(x),R(x),S(x)).
```
The actual theta orbit satisfies the reduced vector field, and cancellation of its strictly
positive mass factor proves pointwise equality between `P_D1^red` and the previous normalized
four-state polynomial. Hence the remaining compact burden is literally
```text
0 < Re P_D1^red(Z(x),R(x),S(x))  for 0 < x < 43/500,
```
with no `H` or `P` coordinate and with the proved Lyapunov constraints above.

**New Lean artifact.**
`HTGeometry/PolynomialODEJetRankThreeReducedClosure.lean` defines reduced polynomial ring,
vector field, covariant Lie jets, source jets, and exact rank-three mass-factor closure. It is
wired into HTGeometry umbrella. `RHTower/PrimeArchThetaModularDifferentialClosure.lean` instantiates
the reduced trajectory and identifies reduced/normalized D1 values; general modular connector now
states exact positivity equivalence for reduced value. Direct Lean checks pass.

- 2026-08-28 — eliminated fourth modular coordinate from arbitrary-basepoint D1, formalized exact
  universal `ℂ[Z,R,S]` closure, and reduced compact C20 to one genuine three-variable polynomial
  sign along strict Lyapunov chamber.

**C20 source-positive modular closure and sharp seam no-go `[PROVED HERE]`.** Replacing positive
gap coordinate by literal normalized source
```text
Q = F/H = (6B²+A-6)/16,
U = P,
B = -S/3
```
produces smaller autonomous polynomial system
```text
U' = 9/2 + 4Q + (3/2)B² + 2BU,
B' = 1/2 + 4Q - B²/2,
Q' = (3/4)B(1/2+4Q-B²/2) - (1/8)(16Q+6-6B²)(U+B),
H' = BH/2.
```
Every normalized source jet now begins at literal variable `Q` and iterates one covariant Lie
operator. Lean proves exact arbitrary-basepoint factorization
```text
D1_raw = H^6 P_D1^source(U,B,Q)
```
and pointwise equality of this polynomial with previous normalized modular D1 on actual theta
orbit. On `x>0`, all `U,B,Q` are strict, reconstructed gap `16Q+6-6B²` is strict, and both `U`
and `B` increase strictly. This supplies two source-adapted clocks while eliminating reconstructed
second mass jet from source recursion.

Static positivity conjecture is false and now has exact no-go closure. Universal modular seam
family has
```text
U=B=0,  Q=(X-6)/16,  reconstructed gap=X.
```
Thus normalized source positivity begins at sharp wall `X>6`. At exact rational scale
`R=5/2`, hence `X=25/4` and `Q=1/64>0`, universal rank-three seam polynomial is strictly negative.
Consequently positive source plus positive discriminant gap cannot alone prove D1; actual orbit
dynamics or stronger scale data is indispensable. Positive survivor is exact source-positive flow,
strict clocks, and sharp seam classification. Physical theta seam remains safely in proved chamber
`X>191/10`; remaining actual C20 interval is still `0<x<83/1000`.

**New Lean artifacts.** `HTGeometry/PolynomialODEJetRankThreeSourcePositiveClosure.lean` defines
source-positive ring, vector field, covariant jets, and exact mass-factor closure.
`HTGeometry/PolynomialODEJetRankThreeSourcePositiveSeamNoGo.lean` proves sharp seam source wall and
exact negative rational witness. `RHTower/PrimeArchThetaModularDifferentialClosure.lean`
instantiates physical flow, exact source factor, strict clocks, and source-positive/normalized D1
identity. `RHTower/ThetaCusp/ThetaCuspFullReflectionEighthGeneralModularClosure.lean` exposes reality,
physical chamber, and exact positivity equivalence. Modules are wired into umbrellas; direct Lean,
targeted builds, and axiom audit pass with only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-08-28 — formalized literal-source `(U,B,Q)` closure and two strict clocks; disproved static
  source-plus-gap D1 positivity at exact seam scale `25/4`; retained orbit-dynamical chart as
  strongest positive survivor. Global physical D1 remains open only on `0<x<83/1000`.

**C20 scale-`59/16` likelihood chamber `[PROVED HERE]`.** The next cusp chamber exposed a new
support-gap cooling law rather than merely another numerical endpoint. For any two likelihood
scales `B₀ ≤ B`, spectral support `t ≥ 3` gives the unconditional comparison
```text
M₀(B) ≤ exp(-3(B-B₀)) M₀(B₀).
```
Combining this with the seam calibration `399 p(B₀)<1`, `B≥59/16`, and
`exp(-13/8)<1/5` proves the new scale-local tail law
```text
1995 p(B)<1.
```
The Bell decomposition then retains more than `99/100` of the ordinary fourth jet. This cooling
survivor is the decisive gain: the previous global `19/20` retention is too weak at this scale.

The successful moving profiles on `35/16≤q≤53/24` are
```text
1300 - 336A < J₄,
796 - 336q < J₄,
dominant sixth mass < 501/2 - 432(A-59/16),
complete sixth mass < 251 - 432(A-59/16),
J₆ < (1656/25)(251 - 432(A-59/16)),
J₆ < (1656/25)(1196 - 432q).
```
The stable sixth tower is now sharpened from `<1` to `<1/2`: support gives the same `1/20`
stable-edge factor, while `π⁶<970` turns the exact tail estimate into the half-unit bound.

Naive continuation was falsified before this profile was selected. Reusing the scale-`89/24`
fourth/sixth constants fails at the new left endpoint. The candidate joint profile `(J₄,J₆) =
(56,246)` fails. Raising only the fourth floor to `58` makes a coarse joint polynomial positive,
but exact dominant-mass targets `246`, `247`, and `249` all fail; the exact estimate first closes
below `250`. Coupling the sharpened stable half-unit shows that the integral affine profile above,
with fourth endpoint `61` and complete sixth mass `251`, is the first profile in this loop that
simultaneously closes every endpoint and monotonicity coefficient.

The joint reserve required a new factorization rather than coefficientwise positivity. Its change
under a fourth-jet increment `a≥0` is
```text
a(68a² + (204L+C)a + (204L²+2CL+D) + e₆K),
```
and both `q`-dependent coefficients are positive throughout the chamber. Sixth loss again has a
positive coefficient after pairing its only terminal negative term
`-640000 y¹⁶` with `5630176000 y¹⁵`. Consequently native D1 holds for every `q≥35/16`. The Taylor
certificate
```text
59/16 < π exp(81/500)
```
proves native D1 for every `x≥81/1000`, reducing the remaining C20 interval to
`0<x<81/1000`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodScaleLocalTailCooling.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleFiftyNineSixteenthsBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleFiftyNineSixteenthsAffineLower.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleFiftyNineSixteenthsAffineBound.lean`, and
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleFiftyNineSixteenthsAffineJoint.lean` formalize the
cooling law, stable half-unit tower, affine producers, joint reserve, and D1 capstone. All are wired
into the RHTower umbrella. Direct `lake env lean` checks and exact targeted build of the capstone
pass. Forbidden-declaration scan and diff check are clean. Representative axiom audits return only
`propext`, `Classical.choice`, and `Quot.sound`. Global lint failure is confined to unrelated
concurrently created unwired modules; this five-module chain is reachable.

**Novelty audit (2026-08-28).** Corpus searches found no prior scale-local normalized theta-cusp
support comparison, `99/100` fourth-jet retention, stable sixth half-unit tower, or this coupled
`(J₄,J₆)` chamber. Targeted current-literature searches located Planat's 2026 theta-kernel growth
criterion (https://www.mdpi.com/2073-8994/18/8/1283), Planat--Solé second-level concavity
(https://arxiv.org/abs/2608.19160), and Deng--Yang--Lü contour Hankel dynamics
(https://arxiv.org/abs/2608.11520). None contains this normalized support-gap cooling mechanism or
the resulting scale-`59/16` D1 closure. This is a targeted-search conclusion, not a claim of an
exhaustive literature classification.

- 2026-08-28 — falsified coarse scale-`59/16` continuations, discovered/proved scale-local
  support-gap cooling and `99/100` fourth retention, sharpened stable sixth tower to `<1/2`, proved
  the coupled chamber, and reduced native C20 to `0<x<81/1000`.

**C20 source-positive/Lyapunov differential atlas `[PROVED HERE]`.** The attempted direct
expansion of the source-positive D1 polynomial on the seam was computationally intractable even
for one exact rational witness. The successful pivot avoids eighth-jet expansion entirely. The
source-positive and Lyapunov coordinate rings are polynomially isomorphic under
```text
S = -3B,                 B = -S/3,
A = 16Q + 6 - 6B²,      Q = A/16 + S²/24 - 3/8,
W = U + B,              U = W + S/3.
```
Lean proves both substitutions compose to the identity. More strongly, the pullback conjugates
the autonomous vector fields and covariant Lie operators. In particular the reconstructed gap is
an exact Darboux polynomial
```text
L_source(16Q+6-6B²) = -2(16Q+6-6B²)(U+B),
```
and every completed-theta jet, normalized source jet, and full rank-three reflected eighth D1
polynomial transports through the atlas. Thus the `(U,B,Q)` closure is not a second unrelated
elimination: it is exactly the literal-source chart of the proved `(S,A,W)` Lyapunov differential
system. Any future inward-pointing barrier may now be proved in whichever chart makes its sign
visible and transferred algebraically, with no physical-orbit cancellation or jet recomputation.

**New Lean artifact.**
`HTGeometry/PolynomialODEJetRankThreeSourcePositiveChartEquivalence.lean` proves inverse ring
substitutions, injectivity, vector-field and covariant-Lie intertwining, reconstructed-gap Darboux
law, normalized-jet transport, and exact D1-polynomial transport. It is wired into the HTGeometry
umbrella. Direct `lake env lean` and targeted module build pass. Representative axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`. Remaining physical C20 interval is unchanged:
`0<x<81/1000`; the atlas removes duplicate algebraic proof burden rather than asserting its sign.

- 2026-08-28 — proved exact polynomial differential-ring equivalence of Lyapunov and
  source-positive C20 charts; transported all source jets and D1 without expansion; retained
  `0<x<81/1000` as live physical sign interval.

**C20 exact-atom scale-`11/3` likelihood chamber `[PROVED HERE]`.** Corpus-guided continuation to
the adjacent chamber
```text
11/3 ≤ A ≤ 59/16,       13/6 ≤ q ≤ 35/16
```
first sharpened the scale-local cooling mechanism. Spectral support and the already formalized
seam calibration give
```text
exp(-3/2) < 1/4,        1596 p(A) < 1,
(989/1000) J₄^ordinary < J₄^log.
```
Thus Bell conversion loses less than `11/1000`. Independently, the exact scale ratio
`(11/3)^6 < (13/5)π^6` and `exp(-4)<1/54` preserve the stable atom factor `1/20` and prove that
the complete stable sixth tower is still `<1/2`.

The fourth producer exposed the essential new survivor. The natural support comparison
```text
(681/1331) z^4 ≤ thetaLikelihoodFourthScore z,   z≥11
```
is sharp at the support edge but proves only `J₄>63`; attempted continued floors `64` through `67`
cannot close the coupled left endpoint. Holding that fourth floor at `63`, sixth masses `255` and
higher fail the joint reserve, while mass `250` passes. Conversely the actual sixth endpoint
`521/2` requires a fourth floor at least `68`. Hence no constant monomial comparison can bridge
this chamber.

The successful pivot integrates the literal dominant mixed atom-ray fourth score rather than
replacing it by a support monomial. Its exact value is
```text
exp(-3A) * thetaCuspLikelihoodFourthScale11Over3ExactDominantPolynomial(A-11/3).
```
After exact normalization and the `989/1000` Bell retention, this recovers the full moving floor
```text
1300 - 336A < J₄,       796 - 336q < J₄.
```
This is strictly stronger than the sharp support-only consequence and is precisely the missing
continuous-ray surplus identified by the failed joint probes.

For the sixth jet, candidates `259.5-432d` and `259.75-432d` fail at the left endpoint. The profile
`260-432d` passes locally but does not glue to the next chamber. Increasing slope instead gives the
seam-compatible dominant bound and complete bound
```text
dominant sixth mass < 260 - 456d,
complete sixth mass < 521/2 - 456d,
J₆ < (1656/25)(2497/2 - 456q).
```
The exact joint baseline is positive on the full chamber. Fourth-direction monotonicity follows
from the same cubic increment factorization as the outer chambers, while every coefficient in the
re-expanded sixth-loss polynomial is nonnegative and its constant term is strict. Therefore the
physical sixth-spectral reserve is positive on `11/3≤A≤59/16`, and dispatch to the already proved
outer chamber gives native D1 for every `q≥13/6`. The Taylor certificate
```text
11/3 < π exp(39/250)
```
then proves native D1 for every `x≥78/1000`. Remaining actual C20 interval is now
`0<x<78/1000`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodScaleLocalTailCoolingElevenThirds.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleElevenThirdsBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleElevenThirdsExactAtomLower.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleElevenThirdsAffineBound.lean`, and
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleElevenThirdsAffineJoint.lean` formalize cooling,
stable sixth control, exact atom-ray integration, affine fourth/sixth bounds, coupled reserve, and
the `78/1000` D1 capstone. All five are wired into the RHTower umbrella. Direct Lean checks and the
exact targeted capstone build pass (`9655/9655`). Forbidden-declaration and diff checks are clean.
Representative axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. Global lint
fails only on unrelated concurrently present unreachable modules; all five new modules are
reachable.

**Novelty audit (2026-08-28).** Required corpus search found prior outer affine chambers and their
joint factorization, but no scale-`11/3` producer, exact dominant atom-ray fourth evaluation,
`989/1000` retention law, or inward D1 result. Targeted arXiv, zbMATH, and MathSciNet searches for
Riemann-xi/theta-cusp likelihood jets, Bell-polynomial eighth reflection, and corresponding Hankel
curvature found no work matching this construction; returned literature concerns unrelated
Riemann-theta Hankel determinants, period polynomials, and general physical RH models. This is a
targeted-search novelty conclusion, not an exhaustive classification.

- 2026-08-28 — falsified support-monomial and shallow-slope continuations, extracted/proved the
  exact dominant atom-ray fourth survivor, closed the scale-`11/3` fourth/sixth joint chamber, and
  reduced native C20 to `0<x<78/1000`.

**Next C20 chamber work log: scale `175/48` `[OPEN CORE]`.** Required corpus search selects the
adjacent chamber `175/48≤A≤11/3`, equivalently `103/48≤q≤13/6`. Exact scratch certificates have
already separated marginal feasibility from the remaining joint problem:
```text
fourth exact-atom floor:        72 - 192d,
dominant sixth ceiling:         280 - 912d,
complete sixth ceiling:         561/2 - 912d,
d = A - 175/48,                 0≤d≤1/48.
```
The inherited exponential lower enclosure `1/60000` fails even at the left endpoint for proposed
fourth floor `75`. Strengthening it to `1/56500` still falsifies seam-compatible floors `75`, `74`,
and `73`; floor `72-192d` closes uniformly. On the sixth side, the sharpened upper enclosure
`exp(-175/16)<1/56100` makes the first tested uniform profile close at right-end dominant mass
`261`; candidates through `260` fail. The valid convenient profile above has left dominant mass
`280` and right dominant mass `261`.

Independent insertion of these two valid marginals is false at the left endpoint. With complete
mass `561/2`, reserve remains negative for fourth floors through `80` and first turns positive at
`81`. Holding fourth floor `72`, reserve passes at complete mass `529/2` but fails at `531/2`.
Thus separate marginals miss at least nine fourth units or sixteen sixth-mass units. Corpus search
locates the relevant existing shared-spectrum infrastructure, but its published direction
`J₄^ordinary ≤ (3/80)J₆^ordinary` cannot supply the needed upper control.

**Named open core.** Retain the dominant mixed atom-ray amplitude as a common variable through both
fourth and sixth log-jet transfers, and prove reserve positivity along that correlated ray plus the
stable residual box. Rectangle replacement by independent fourth/sixth bounds is now a proved
dead end for this chamber. Current exact probes are
`/tmp/ThetaCusp175FourthProbe.lean`, `/tmp/ThetaCusp175SixthProbe.lean`,
`/tmp/ThetaCusp175JointProbe.lean`, and `/tmp/ThetaCusp175BaselineProbe.lean`.

A second-pass probe retains the dominant amplitude exactly as
`r=exp(-3A)/P`, using
```text
J₄ > 16(989/1000) r F₄(d),
J₆ < (1656/25)(r F₆(d)+1/2).
```
Even this correlated dominant ray is negative at the left endpoint when the stable sixth tower is
inserted as an independent `1/2` box. Therefore the surviving open core is sharper: retain
fourth/sixth correlation for every stable atom-ray (or prove an aggregate stable rebate), not only
for the dominant ray. The exact failed certificate is
`/tmp/ThetaCusp175CorrelatedEndpoint.lean`.

**C20 arbitrary-scale full-D1 seam restriction and literal source no-go `[PROVED HERE]`.** Earlier
rational seam obstruction established negativity only for independently eliminated seam
polynomial. It did not prove source-positive D1 polynomial itself takes same value; direct
degree-12 source/Lyapunov expansion exceeded practical elaboration budgets. Corpus search exposed
iterated Leibniz theorem for bundled derivations and existing abstract seam jet elimination,
forcing structural pivot.

Modular four-state vector field is now bundled as derivation. Its iterates satisfy exact binomial
jet convolution for all four coordinates, and formal H jets agree with existing Lie jets. New
reflection involution fixes `(H,Z,R,P)=(1,0,R,0)`, anti-commutes with modular Lie derivative, and
proves all odd H/source jets vanish at every complex seam scale. Combining parity with abstract
even-jet elimination proves
```text
eval generalD1 (1,0,R,0)     = seamPolynomial(R²),
eval normalizedD1 (1,0,R,0) = seamPolynomial(R²).
```

New quotient chart
```text
S=P+RZ,   A=R²(1-Z²),   W=(2/3)(P+RZ)-RZ
```
intertwines four-state and Lyapunov vector fields, Lie operators, covariant normalized operators,
every normalized H/source jet, and full D1 polynomial. Hence
```text
eval lyapunovD1 (S,A,W)=(0,R²,0) = seamPolynomial(R²)
```
at arbitrary complex scale, without high-jet expansion. Composing with proved
Lyapunov/source-positive atlas yields literal rational obstruction
```text
eval sourcePositiveD1 (U,B,Q)=(0,0,1/64)
  = seamPolynomial(25/4) < 0,
```
while `Q>0` and reconstructed gap is `25/4>0`. Thus source and reconstructed-gap positivity is
formally insufficient for D1; successful chamber proof must use extra orbit inequalities. Positive
survivor is exact arbitrary-scale seam restriction plus differential quotient atlas.

**New Lean artifact.**
`HTGeometry/PolynomialODEJetRankThreeSeamRestriction.lean` proves derivation closure, parity,
arbitrary-scale full/normalized/Lyapunov seam identities, and four-to-three differential quotient
transport. `PolynomialODEJetRankThreeSourcePositiveSeamNoGo.lean` now proves negativity of literal
source-positive D1 rather than proxy seam polynomial. Both are wired into HTGeometry umbrella.
Direct Lean checks and targeted builds pass. Representative axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden-declaration and diff checks are clean. Global lint
fails only on unrelated concurrently present unreachable modules.

**Novelty audit (2026-08-28).** Required corpus search found no four-state/Lyapunov quotient
pullback or arbitrary-algebraic-scale full-D1 seam theorem. Targeted current arXiv search found
Planat--Solé's first-Laguerre concavity theorem and unrelated theta/Hankel work, but no reflected
eighth rank-three D1 seam restriction, differential quotient atlas, or literal source-positive
counterexample. This is targeted-search evidence, not exhaustive classification.

- 2026-08-28 — proved arbitrary-scale full-D1 seam restriction structurally; transported through
  general/Lyapunov/source-positive charts; strengthened chamber no-go to literal D1 negativity.

**C20 tail-polynomial Bell compiler `[PROVED HERE]`.** Repeated chamber proofs had separately
reconstructed fourth- and sixth-order Bell losses after each new support-gap estimate. Corpus
search exposed that every such proof uses the same literal tail probability `p`. The exact
unconditional envelopes are now formalized for every physical source `x≥0`:
```text
(1 - (35/2)p - 15p³) J₄^ordinary < J₄^log,
J₆^log < (1 + 5400p² + 10800p⁴) J₆^ordinary.
```
Strictness is structural: positive Bell grade `12b₁²b₂` for the fourth inequality and positive
grade `q₂` for the sixth. A shared compiler turns the single scalar certificate `1596p<1` into
the chamber factors `989/1000` and `1003/1000`; no scale-specific Bell expansion remains.

**New Lean artifact.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodBellTailPolynomialEnvelope.lean` proves positivity of literal tail
mass and ordinary fourth score, both exact polynomial envelopes, and the shared `1596p<1`
compiler. It is wired into the RHTower umbrella. Direct `lake env lean`, targeted module build,
forbidden-declaration scan, diff check, and representative axiom audits pass; axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

**Next C20 conjecture: scale `29/8` `[ACTIVE]`.** The adjacent untouched chamber is
```text
29/8 ≤ A ≤ 175/48,      17/8 ≤ q ≤ 103/48.
```
Required corpus search found no existing `29/8` likelihood or joint-reserve theorem. Work starts
from the proved `175/48` capstone and will use the tail-polynomial compiler; candidate marginal
and correlated-ray bounds must be falsified or closed exactly before any source module is added.

- 2026-08-28 — proved scale-free fourth/sixth Bell tail-polynomial envelopes; opened adjacent
  scale-`29/8` chamber without modifying frontier map.

**Scale `175/48` chamber resolution `[PROVED HERE]`.** The named correlated stable-ray open core
above is superseded. Its premise was the inherited global logarithmic-sixth transfer
`J₆^log < (207/200)J₆^ordinary`, not an intrinsic fourth/sixth correlation defect. Required corpus
search exposed the coefficient-faithful sixth Bell grading and the already proved scale-local tail
cooling mechanism. Re-running that Bell argument under `A≥175/48` proves the new unconditional law
```text
1596 p < 1,
J₆^log < (1003/1000) J₆^ordinary.
```
This repairs the failed independent rectangle without assuming a new spectral correlation.

The heavy conjecturing loop also sharpened the sixth mass certificate. Profiles with inherited
right-end dominant masses through `260` fail; `280-912d` passes but is wasteful. Exact degree-15
clearing proves the stronger uniform profile
```text
d = A - 175/48,                     0≤d≤1/48,
dominant sixth mass < 272 - 528d,
complete sixth mass < 545/2 - 528d,
J₆^log < (8024/125)(545/2 - 528d)
       = (8024/125)(2811/2 - 528q).
```
On the fourth side, the exact dominant atom-ray integration and
`exp(-175/16)>1/56500` prove
```text
J₄^log > 772 - 192A = 484 - 192q.
```
Substitution into the exact eighth-reflection reserve is strictly positive throughout
`103/48≤q≤13/6`. The fourth increment cubic and sixth-loss factorization extend this baseline to
the physical jets. Dispatch to the outer `q≥13/6` result gives native D1 for every `q≥103/48`, and
the exact Taylor certificate
```text
175/48 < π exp(3/20)
```
gives native D1 for every `x≥75/1000`. Remaining actual C20 interval is `0<x<75/1000`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodScaleLocalBellCoolingOneHundredSeventyFiveFortyEighths.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleOneHundredSeventyFiveFortyEighthsBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleOneHundredSeventyFiveFortyEighthsExactAtomLower.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleOneHundredSeventyFiveFortyEighthsAffineBound.lean`, and
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleOneHundredSeventyFiveFortyEighthsAffineJoint.lean`
formalize local Bell cooling, stable mass, exact fourth atom integration, sharpened sixth mass, the
joint chamber, and the `75/1000` capstone. All are wired into the RHTower umbrella. Direct Lean
checks and exact targeted capstone build pass (`9660/9660`). Forbidden-declaration scan is empty;
representative axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. Global lint
fails only on unrelated concurrently present unreachable modules; all five artifacts are reachable.

**Novelty audit (2026-08-28).** Required corpus searches found no `175/48` local-sixth Bell law,
exact atom-ray profile, affine joint chamber, or `75/1000` D1 theorem. Targeted current arXiv
search checked xi Jensen-polynomial hyperbolicity, truncated Hankel-positivity relaxations, and
Dirichlet-series Hankel determinants; none contains this theta-cusp likelihood/Bell-transfer
construction or these chamber constants. This is targeted-search evidence, not exhaustive
classification.

- 2026-08-28 — falsified inherited independent-marginal and dominant-only correlation closures,
  identified local sixth Bell loss as the true obstruction, proved the `175/48` chamber, and reduced
  native C20 to `0<x<75/1000`.

**Scale `1399/384` dyadic survivor `[PROVED HERE]`.** The first attempted continuation to the full
`29/8 ≤ A ≤ 175/48` chamber kept the inherited `1596p<1` Bell compiler and the global affine
profiles. Exact endpoint probes falsified that producer scheme: the independent reserve demands a
fourth floor near `80`, while that exact dominant envelope supplies only about `76`; holding the
fourth floor at `76` demands a sixth budget near `277`, already below the dominant sixth mass; and
the corresponding dominant-amplitude correlation still fails even after setting stable sixth mass
to zero unless an unavailable stable-fourth rebate of about `2` is inserted. This is not a no-go for
the `29/8` route: concurrent work now pursues the stronger local certificate `1695p<1`.

The positive survivor from the failed inherited-profile attempt is the first dependency-closed
dyadic subchamber
```text
1399/384 ≤ A ≤ 175/48,       823/384 ≤ q ≤ 103/48.
```
A scale-free exact dominant fourth-atom identity removes the prior repetition of the atom-ray
integral. On this width-`1/384` chamber, exact rational exponential and tail certificates give
```text
J₄^log > 772 - 192A = 484 - 192q,
d = A - 1399/384,
dominant sixth mass < 2187/8 - 528d,
complete sixth mass < 2191/8 - 528d,
J₆^log < (8024/125)(2191/8 - 528d)
       = (8024/125)(2811/2 - 528q).
```
Substitution into the literal eighth-reflection joint reserve is strictly positive throughout the
whole q-window. Exact fourth-direction and sixth-loss monotonicity then lift the baseline to the
physical jets. Dispatch to the proved `q≥103/48` chamber yields native D1 for every
`q≥823/384`. Finally, the exact Taylor certificate
```text
1399/384 < π exp(149/1000)
```
yields native D1 for every `x≥149/2000`, reducing the formally open positive C20 interval from
`0<x<75/1000` to `0<x<149/2000`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthDominantAtomExact.lean` proves the scale-free exact fourth
atom-ray integral. `RHTower/ThetaCusp/ThetaCuspLikelihoodScaleLocalBellCoolingOneThousandThreeHundredNinetyNineThreeHundredEightyFourths.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleOneThousandThreeHundredNinetyNineThreeHundredEightyFourthsBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleOneThousandThreeHundredNinetyNineThreeHundredEightyFourthsExactAtomLower.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleOneThousandThreeHundredNinetyNineThreeHundredEightyFourthsAffineBound.lean`, and
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleOneThousandThreeHundredNinetyNineThreeHundredEightyFourthsAffineJoint.lean`
prove local Bell cooling, stable sixth mass, fourth and sixth affine profiles, full joint chamber,
and the `149/2000` capstone. Together with the generic Bell envelope, all seven modules are wired
exactly once into the RHTower umbrella. Direct Lean checks pass; targeted capstone build passes
(`9667/9667`). Forbidden-declaration and diff checks are clean. Representative axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`. Global lint reports only concurrent unwired
modules; every artifact named here is reachable.

**Novelty audit (2026-08-28).** Required corpus searches found no scale-free exact fourth atom-ray
identity, `1399/384` affine chamber, or `149/2000` D1 theorem. Targeted current literature search
checked Planat--Solé's 2026 second-level theta-kernel concavity theorem (arXiv:2608.19160), the
2026 theta-kernel growth reformulation, xi orthogonal-polynomial expansions, xi derivative
positivity, and general Bell/Hankel determinant work. None contains this normalized likelihood-tail
Bell compiler, exact reflected eighth joint reserve, or these chamber constants. This is
search-bounded novelty evidence, not exhaustive classification.

- 2026-08-28 — falsified inherited `1596p<1` full-`29/8` producer, extracted and formalized the
  `1399/384` dyadic survivor, and reduced native C20 to `0<x<149/2000` without modifying frontier map.

**Scale `29/8` direct-eighth chamber `[PROVED HERE]`.** The stronger local tail certificate
```text
1695 p < 1
```
sharpens the Bell conversions to fourth retention `9896/10000` and sixth inflation
`10019/10000`. Exact atom and stable-tower profiles then give, throughout
```text
29/8 ≤ A ≤ 175/48,       17/8 ≤ q ≤ 103/48,
```
the unconditional marginal bounds
```text
J₄^log > 1545/2 - 192A = 969/2 - 192q,
J₆^log < (40076/625)(2605/2 - 480q).
```
The heavy-conjecturing loop falsified the independent fourth/sixth rectangle even with these
sharper constants: its exact left-end reserve remains negative. The obstruction exposes a positive
survivor unavailable to the rectangle abstraction. Scale-local pair absorption proves that
`123/40` times the dominant pair sector is paid by the dominant single sector. After subtracting
the exact `(2,2)` pair, nondominant-pair tail, and higher-even Fock losses, this yields
```text
1739 A^8 exp(-3A) < eighth Fock odd weight,
444900 A^8 exp(-3A) < J₈^log.
```
Keeping this eighth floor inside the literal nonlinear compact reserve, rather than eliminating it
through a sixth/eighth coupling, gives a strictly positive exact degree-25 baseline. Positivity of
the fourth increment cubic, sixth-loss factor, and eighth-gain coefficient lifts that baseline to
the physical jets. Dispatch to the proved outer chamber gives native D1 for every `q≥17/8`.
Finally, the exact Taylor certificate
```text
29/8 < π exp(18/125)
```
gives native D1 for every `x≥72/1000`, reducing the formally open positive C20 interval from
`0<x<149/2000` to `0<x<72/1000`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodScaleLocalBellCoolingTwentyNineEighths.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleTwentyNineEighthsBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleTwentyNineEighthsExactAtomLower.lean`, and
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleTwentyNineEighthsAffineBound.lean` prove the sharpened local
Bell and marginal profiles. `RHTower/ThetaCusp/ThetaCuspLikelihoodEighthScaleTwentyNineEighthsFockFloor.lean`
proves pair absorption and the literal eighth-jet floor.
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleTwentyNineEighthsDirectAffineJoint.lean` proves the
fourth/sixth/eighth joint chamber, physical compact reserve, native D1 dispatch, and `72/1000`
capstone. All are reachable from the RHTower umbrella. Direct Lean checks pass; targeted capstone
build passes (`9726/9726`). Forbidden-declaration scan is empty. Representative axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`. Global lint reports only unrelated concurrent
unreachable modules; none is an artifact named here.

**Novelty audit (2026-08-28).** Required corpus searches found no `29/8` direct eighth Fock floor,
dominant-single/dominant-pair absorption law, four-six-eight compact joint chamber, or `72/1000`
D1 theorem. Targeted current literature search checked Planat--Solé's second-level Xi-kernel
concavity result (arXiv:2608.19160), the 2026 theta-kernel growth/blockwise-positivity obstruction,
xi derivative-positivity work, and current Hankel-criterion papers. None contains this normalized
likelihood Fock-sector absorption, literal reflected eighth compact reserve, or these chamber
constants. This is search-bounded novelty evidence, not exhaustive classification.

- 2026-08-28 — falsified independent fourth/sixth closure at `29/8`, retained direct eighth Fock
  gain, proved the full `29/8` chamber, and reduced native C20 to `0<x<72/1000` without modifying
  frontier map.

**Attempted full `173/48` continuation and dyadic `1391/384` survivor `[PROVED HERE]`.**
The next conjecture attacked the entire adjacent chamber
```text
173/48 ≤ A ≤ 29/8,       101/48 ≤ q ≤ 17/8
```
with the direct-eighth mechanism rather than reverting to an inherited marginal rectangle. Exact
endpoint certificates falsified this full-width producer package. The dominant fourth atom supplies
a floor strictly between `79` and `80` at the lower endpoint, while the tested joint reserve still
fails at fourth floor `82` and only passes after an unavailable increase to `90`. The dominant sixth
mass is near `292.5` there: a `288` budget already fails, whereas `280` would be needed for the tested
reserve. Increasing the direct eighth coefficient from `440000` through `500000`, `600000`, and
`800000` does not repair the exact lower-end reserve. Thus the current independent producer plus
direct-Fock package cannot cross the full `173/48` chamber. This is a falsification of that package,
not a no-go for native D1 or for alternative correlated producers.

The strongest positive survivor is the adjacent exact dyadic chamber
```text
1391/384 ≤ A ≤ 29/8,       815/384 ≤ q ≤ 17/8,
d = A - 1391/384 ∈ [0,1/384].
```
A new local tail certificate and Bell compilation prove
```text
1680 p < 1,
fourth Bell retention = 9895/10000,
sixth Bell inflation = 501/500,
J₄^log > 1545/2 - 192A = 969/2 - 192q,
J₆^log < (8016/125)(1135/4 - 480d)
       = (8016/125)(2605/2 - 480q).
```
The sixth proof separates an exact degree-15 dominant certificate
`dominant mass < 1133/4 - 480d` from an unconditional stable-tower bound `<1/2`. For the eighth
producer, the exact dominant pair/single certificate proves that `61/20` times dominant pair mass
is absorbed by dominant single mass. After all pair and higher-even losses, this leaves
```text
1725 A^8 exp(-3A) < eighth Fock odd weight,
440000 A^8 exp(-3A) < J₈^log.
```
Using the fourth exponential floor
```text
(1/52450)(1-3d) < exp(-3A)
```
inside the eighth profile produces a strict exact degree-25 joint reserve across the whole dyadic
window. Fourth, sixth, and eighth monotonicity lift the rational baseline to physical log jets.
Dispatch to the proved `q≥17/8` chamber therefore proves native D1 for every `q≥815/384`.
Finally,
```text
1391/384 < π exp(143/1000)
```
is proved by a finite Taylor lower certificate, yielding native D1 for every `x≥143/2000` and
reducing the formally open positive C20 interval from `0<x<72/1000` to `0<x<143/2000`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodScaleLocalBellCoolingOneThousandThreeHundredNinetyOneThreeHundredEightyFourths.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsExactAtomLower.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsAffineBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodEighthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsFockFloor.lean`, and
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsDirectAffineJoint.lean`
formalize the complete producer and reserve chain. All six are wired exactly once into the RHTower
umbrella. Direct Lean checks pass; targeted capstone build passes (`9732/9732`). Representative
axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.

**Novelty audit (2026-08-28).** Required corpus searches found no `1391/384` tail/Bell chamber,
`61/20` dominant-pair absorption law, `440000` literal eighth floor, direct degree-25 compact
reserve, or `143/2000` D1 theorem. Targeted current literature search checked Planat--Solé's 2026
second-level theta-kernel concavity theorem (arXiv:2608.19160), the 2026 theta-kernel blockwise
positivity obstruction, xi derivative-positivity work, and current Hankel-criterion papers. None
contains this normalized likelihood Fock-sector construction or these chamber constants. This is
search-bounded novelty evidence, not exhaustive classification.

- 2026-08-28 — falsified the full-width `173/48` direct-producer package, extracted and formalized
  the `1391/384` dyadic survivor, and reduced native C20 to `0<x<143/2000` without modifying the
  read-only frontier map.

**Scale-local cubic Fock cooling and adjacent `695/192` chamber `[PROVED HERE]`.**
Corpus inspection exposed that the global higher-even Fock estimate discarded the much stronger
response available inside the current scale chamber. The new conditional cooling law is reusable:
```text
1670 r < 1
  ⇒ higher-even sector tail < 1/200000
  ⇒ eighth higher-even Fock loss ≤ 13/2.
```
This replaces the global response hypothesis `399r<1`, tail `<1/3000`, and loss `≤1300/3` without
changing any source definition. At scale `A≥695/192`, a rational exponential certificate proves the
required local response bound. The same local Bell compilation retains `9895/10000` of the ordinary
fourth jet and inflates the sixth jet by at most `501/500`.

A second independent sharpening resolves the stable sixth tower. Factoring its first stable atom
from the geometric tail proves
```text
first stable Gaussian weight < 59/40000,
remaining stable Gaussian tail ≤ 3/2000,
stable sixth score tower < 1/4,
```
replacing the inherited `<1/2` loss. These two invariants open the exact adjacent dyadic chamber
```text
695/192 ≤ A ≤ 1391/384,       407/192 ≤ q ≤ 815/384,
d = A - 695/192 ∈ [0,1/384].
```
The resulting physical producer bounds are
```text
J₄^log > 1545/2 - 192A = 969/2 - 192q,
J₆^log < (8016/125)(2849/10 - 480d)
       = (8016/125)(6512/5 - 480q).
```
The dominant pair/single comparison retains the sharp `61/20` absorption factor. Combining it with
local cubic higher-even cooling yields
```text
2150 A^8 exp(-3A) < eighth Fock odd weight,
550000 A^8 exp(-3A) < J₈^log.
```
The exact fourth exponential profile
```text
(1/52050)(1-3d) < exp(-3A)
```
then closes the literal degree-25 fourth/sixth/eighth compact reserve throughout the chamber.
Monotonicity in each jet lifts the rational baseline certificate to the physical source jets.
Dispatch to the prior `q≥815/384` theorem proves native D1 for every `q≥407/192`. The finite Taylor
certificate
```text
695/192 < π exp(71/500)
```
therefore proves native D1 for every `x≥71/1000`, shrinking the formally open positive C20 interval
to `0<x<71/1000`.

**New Lean artifacts.**
`RHTower/ThetaCusp/ThetaCuspLikelihoodEighthHigherEvenLocalCooling.lean` formalizes the reusable cubic
response-to-Fock-loss law.
`RHTower/ThetaCusp/ThetaCuspLikelihoodScaleLocalBellCoolingSixHundredNinetyFiveOneHundredNinetySeconds.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthStableTowerScaleSixHundredNinetyFiveOneHundredNinetySecondsBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodFourthScaleSixHundredNinetyFiveOneHundredNinetySecondsExactAtomLower.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodSixthScaleSixHundredNinetyFiveOneHundredNinetySecondsAffineBound.lean`,
`RHTower/ThetaCusp/ThetaCuspLikelihoodEighthScaleSixHundredNinetyFiveOneHundredNinetySecondsFockFloor.lean`, and
`RHTower/ThetaCusp/ThetaCuspFullReflectionEighthScaleSixHundredNinetyFiveOneHundredNinetySecondsDirectAffineJoint.lean`
formalize the complete local producer, reserve, and source-threshold chain. All seven are wired
exactly once into the RHTower umbrella. Direct Lean checks pass; targeted capstone build passes
(`9739/9739`). Forbidden-declaration scan is empty. Representative axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound`. Global lint reports only unrelated concurrent
unreachable modules; none is an artifact named here.

**Novelty audit (2026-08-28).** Required corpus searches found no `1670r<1` cubic higher-even Fock
cooling law, `13/2` local Fock-loss theorem, split stable-sixth `<1/4` theorem, `695/192` producer,
`550000` literal eighth floor, or `71/1000` D1 theorem. Previously audited current literature on
second-level theta-kernel concavity, theta-kernel blockwise positivity obstructions, xi derivative
positivity, and Hankel criteria contains none of this normalized likelihood-sector mechanism or
these constants. This is search-bounded novelty evidence, not exhaustive classification.

- 2026-08-28 — extracted local cubic Fock cooling and split stable-sixth invariants, formalized the
  `695/192` dyadic chamber, and reduced native C20 to `0<x<71/1000` without modifying the read-only
  frontier map.
