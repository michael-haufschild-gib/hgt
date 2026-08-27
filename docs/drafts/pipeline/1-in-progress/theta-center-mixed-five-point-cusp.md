# Theta center-mixed five-point cusp

- **ID:** TCD-C12-FIVE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** rh-current-frontier-map.md · route TCD
- **Statement:** For every aperture `a > 0`, the equispaced five-node Gram matrix of the theta center-mixed density is positive definite on a punctured neighborhood of the coalesced node.
- **Status:** `[RANK-FIVE SOURCE SEAM LEAN-PROVED] [OPEN D1 CHAMBER LEAN-PROVED] [ORDER-EIGHT LIKELIHOOD LADDER LEAN-PROVED] [FULL EVEN-FOCK BUDGET ABSORPTION LEAN-PROVED] [ORDINARY SOURCE LANDING LEAN-PROVED] [EXACT BELL-GRADE DECOMPOSITION LEAN-PROVED] [HIGHER EVEN BELL GRADES ABSORBED] [GRADE-TWO PAIR TRACE OPEN] [GLOBAL D1 OPEN]`

## Goal

Close rank five in the TCD cofinal positive-definiteness programme. The target is source-pure: it uses the already formalized theta cusp source and center-mixture representation, not RH or a zero-free hypothesis. Rank five is the first step not controlled by the proved second--sixth reflected Hankel curvature.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
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

If D1 holds pointwise for the reflected source field, integrate its quadratic forms against the positive center-mixed radial weight. Prove strict positivity of the integrated matrix, then its determinant. This generalizes the corpus theorem `integral_twoByTwo_det_pos` by one rank.

### D3 — five-point parity cusp

Formalize reversal-parity congruence, Taylor jets through the first nonzero even and odd block determinants, and positivity on a punctured right neighborhood. Expected smoothness burden is order twelve. Build generic center-product jets if explicit differentiation becomes duplicative.

### Pivot criteria

If D1 is false, prove the exact sign obstruction and audit D2 directly: pointwise failure need not imply failure after positive mixing. If the center determinant is also false, extract the sharp aperture/radial boundary or maximal rank-four survivor before retiring this branch. Missing order-eight or order-twelve infrastructure is not a pivot criterion.

## Novelty collision audit

Closest August 2026 item is Planat--Solé's second-level concavity theorem for the classical Xi kernel. Its inequality uses derivatives through order eight and may be algebraically related to one principal-minor expression. Before any novelty claim, compare its exact transformed kernel and determinant polynomial with D1 and with the center-mixture theorem. No corpus theorem currently proves D1--D3.

Exact comparison now separates the statements. Planat--Solé prove negativity of the successive-derivative Hankel determinant `det(s^(i+j))_(0≤i,j≤2)` for `s(t)=Φ(√t)` in radial-square coordinate, equivalently strict log-concavity of `s'²-ss''`. D1 is positivity of the signed even reflected-product jet determinant of `u↦Φ(x+u)Φ(x-u)` in logarithmic source coordinate, for every center `x`. Derivative order overlaps, but kernel, coordinate, determinant, and sign differ. The seam theorem above is therefore not obtained from their result.

## Lean artifacts

- `HilbertMetric/ReflectionEighthJet.lean`: exact eighth reflected product jet and even-log determinant polynomial.
- `HTGeometry/PolynomialODEJetRankThreeClosure.lean`: exact ten-jet self-dual ODE elimination.
- `RHTower/PrimeArchThetaModularDifferentialClosure.lean`: actual theta-source modular connector.
- `RHTower/PrimeArchThetaBornWittenEighthJet.lean`: actual Born--Witten seventh/eighth jets and atomwise D1 positivity.
- `RHTower/ThetaCuspLikelihoodSeventhEighthCumulant.lean`: exact cumulants and quantitative `κ₈>(2/3)m₈`.
- `RHTower/ThetaCuspLikelihoodSeventhEighthSourceJets.lean`: actual source jets and exact pointwise low-score obstruction.
- `RHTower/ThetaCuspLikelihoodEighthScoreRayTransform.lean`: exact one- and two-ray incomplete-Laplace transforms, dominant Dirac--ray compensation, and `1/30` core certificate.
- `RHTower/ThetaCuspLikelihoodEighthOrdinaryPositivity.lean`: strict full ordinary eighth-jet positivity and sharpened `(128/15)A⁸m₈` normalized-moment lower bound.
- `RHTower/ThetaCuspLikelihoodEighthDominantPairCompensation.lean`: degree-twenty exponential fusion and strict dominant grade-two absorption.
- `RHTower/ThetaCuspLikelihoodEighthStablePairCompensation.lean`: exact atom-pair core, factor-nine transform envelope, Gaussian stable-tail budgets, and complete ordered grade-two absorption.
- `RHTower/ThetaCuspLikelihoodEighthFockSector.lean`: sharp stable Gaussian bounds, full one-particle monomial budget, `q⁷` higher-even summability, and strict completed even-Fock reserve.
- `RHTower/ThetaCuspLikelihoodEighthFockTraceConnector.lean`: positivity of completed losses and strict coefficient-faithful landing inside literal ordinary eighth source jet.
- `RHTower/ThetaCuspLikelihoodEighthBellGrades.lean`: exact literal log-J8 Bell decomposition, positivity of all favorable odd grades, and reduction to four even losses.
- `RHTower/ThetaCuspLikelihoodEighthBellHigherEvenAbsorption.lean`: iterated normalized-moment product laws, exact monomial trace, and absorption of Bell grades four, six, and eight into higher-even Fock loss.
- `RHTower/ThetaCuspFullReflectionEighthLogJets.lean`: actual complete-source seventh/eighth log jets and normalized D1 polynomial.
- `RHTower/ThetaCuspFullReflectionEighthBellTransfer.lean`: exact raw-to-log D1 connector through Bell order eight.
- `RHTower/ThetaCuspFullReflectionEighthHankelSeam.lean`: strict source seam theorem and nontrivial open D1 chamber.

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
