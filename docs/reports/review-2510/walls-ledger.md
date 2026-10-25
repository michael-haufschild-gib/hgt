# Walls ledger

Status: 2026-10-25, corpus `e4965f55a` with the working tree of that day. Every obstacle in the corpus belongs to one of three core families:

- **Wall 1 — critical arithmetic sign.** Estimates, signs and oscillatory payment at the critical endpoint.
- **Wall 3 — transfer.** Readings, norms, completions, limits, shared budgets and selection.
- **Wall 14 — realization and forcing.** Faithful arithmetic objects, orientation, invariants and the forcing of the actual source into its blind carrier.

**Organizing principle.** Every unconditional positivity theorem is positivity on a carrier blind to off-line zeros; for single-channel sharp-stable carriers this is a theorem (14.10). RH says that the actual source is itself blind. Wall 1 measures blindness as a rate. Wall 3 governs how blindness transfers between readings and limits. Wall 14 asks what forces the source into its blind carrier. Three forcing laws are proved, and each stops at a computed boundary:

- Multiplicative positivity forces the boundary line and its capacity: a pole of order `k` carries at most `⌊k/2⌋` boundary zeros. Inside the strip it forces only what growth input pays, and it contains no quantized inequality at the critical line (14.11).
- Positivity, the functional equation and the simple pole force the coefficient measure to be ζ's (14.12). They do so linearly in the measure and do not locate zeros.
- Pole order forces the zeros of relative deformations exactly: the index–pole conservation identity holds, the simple pole is rigid and pole order two admits every off-line type (14.13). Pole order pays for inserted zeros only.

ζ's own zeros are paid, if at all, by oscillation of the zero sum. That payment is a rate, so the open core of the budget question lives in Wall 1 (1.16). Every amplification tested gains on a zero's depth as fast as it pays in arithmetic length (1.15). Breaking that homogeneity needs a term that does not scale: a base for coefficient systems (14.14) or Riemann–Roch for oscillatory payment (14.4).

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, logged in `logs/review-2510-update/working-log.md`. No compilation. A countermodel excludes the mechanism it was built against, not every route that touches that wall.

**Markers.** `[S]`: listed by the frontier map as not yet integrated. `[P]`: paper proof, Lean formalization in progress. `[R]`: assessment or model calculation of the review, not a theorem. F1–F3 are the review's focus questions: F1 the base problem (B3.19), F2 signed near-coincidence cancellation beyond the square-root threshold (B3.20), F3 Riemann–Roch for oscillatory payment (a face of B1.6).

**Status column.**

- *Open*: no answer; the boundary listed is the present one.
- *Sharpened*: still open, with a new exact boundary or survivor that changes what must be proved.
- *New*: a face not in the previous ledger.
- *Resolved*: the face's question is answered; the answer is recorded and the face carries no open task.

## 1. Wall 1 — critical arithmetic sign

With `Δ = sup_ρ |Re ρ − 1/2|`, a receiver bounded at a fixed rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is `Δ = 0`.

| Face | Status | Present obstacle | Established boundary / survivor | Missing input |
|---|---|---|---|---|
| **1.0 Quasi-RH first rung** | Sharpened | Graded cancellation receivers, multiplicative forcing and admission at a fixed damping have no target between Vinogradov–Korobov and a fixed strip. | Fixed-strip equivalences: balanced statistic, centred-prime band, short windows, JAS level one, PBM abscissa, WL rate `σ`, RW/ACS floors, every Vaughan power improvement [S]. Completed positive systems reach only a collar of width `≍ 1/(d log T)` with at most `κ²` exceptions [S]. Visible-pole index: uncancelled zeros right of `1/2 + ε` obstruct the paid ideal. Unconditional regions: dlVP, Littlewood, VK. | A fixed zero-free strip (B2.1), or a handle that is not depth-homogeneous (1.15). |
| **1.1 Critical signed cancellation** | Open | Lag, Abel, history, series and bilinear bounds must reach rate zero with every counterterm and tail paid. | Exact endpoint laws; high-zero tail `O(1)`; all-modulus `Q^{−δ/32}`; Heath–Brown all-length; sharp `S₂`; `M(x) = Ω±(√x)`. | Source cancellation at every positive slack (B1.1). |
| **1.2 Axis orientation** | Open | A nonnegative defect, winding count or faithful spectrum does not force line support. | Ward cap and trace; cubic trace = winding; subharmonic Newton margin; KKL horizon. | Vanishing or a forcing all-height sign (B1.6). |
| **1.3 Complete Weil positivity** | Open | Low and mixed sectors are unsigned pointwise at large aperture. | Windows `3/10` full, `181/500` odd, `(log 2+1/50)/2` primitive; averaged positivity at `κ₀ log Γ` on `[Γ, 2Γ]`; subpower coercivity to `Γ^{4/3}`; finite-level existence ⇔ RH. | Sign at every aperture (B1.3) or selection (3.14). |
| **1.4 Arithmetic cone membership** | Open | Identifying the source is not proving its positivity. | Pair tests recover every node; single-node perturbations fail; positive-measure rigidity identifies the source among positive measures with the theta law (14.12). | `Λ` in the full Weil cone, i.e. RH. |
| **1.5 Contrast equality** | Open | Exact Jensen, BSY and Li accounting leaves a residual. | BSY: the off-line sum `Σ log|ρ/(1−ρ)|` is nonnegative and vanishes on critical zeros; Li depth `≤ 1/431`, `β < 1/300`. | An arithmetic upper bound forcing the residual to zero (B1.7). |
| **1.6 Required uniformity** | Open | Fixed rank, order, history or height does not reach the receiver's quantifier. | All-rank orthant sign; PA order thresholds and the order-24 finite moment sign; fixed-rank coercivity. | All-rank or order-uniform estimates (B1.5, B3.12). |
| **1.7 Amplification** | Resolved | Raising a receiver to a power multiplies its rate. | Exact exponent bookkeeping. | — (depth amplification is 1.15) |
| **1.8 Critical pronic energy** | Open | Horizon-uniform signed energy at cofinally small damping. | Half damping: actual receiver bounded, actual Gram rank two, moving limits a rank-three ray. Above half: admission with a common critical-Wiener majorant. Below half: leading order classified; every power improvement of the residual is a fixed strip [S]. Size-cutoff receiver paid on the exterior and at `ε = 1/2`. | Signed interior energy below `T^{1−2ε}` (B1.2). |
| **1.9 Signed continuation** | Open | Integrated signed loss must stay bounded uniformly in the horizon. | Canonical corrector; integer local exponents of paid patterns below half damping. | Flux control at closing damping (B1.2). |
| **1.10 Absolute compensation** | Open | A vanishing relative error coexists with unbounded raw energy. | Power-plus-bounded forcing; residual pairing → `−1` on escape; quantile and moving localizations keep the antipodal density; record-minimum limits with `K_pp ≥ p^{2ε−2}`. | Absolute energy bound (B1.2); escape exclusion at fixed `ε` is a fixed strip (3.15) [R]. |
| **1.11 Rates and clusters** | Open | Physical ground rate versus zero width. | `groundRate = polarRate`; form-norm and Birman–Schwinger rates `= Δ`; `RH ⇔ groundRate = 0`; bounded local depth gives `polarRate = Δ`. | Physical `polarRate = Δ` (B3.1). |
| **1.12 Interior anti-alignment** | Open | The gap `θ(ε,t) < 1` between the proved collars. | High-height and small-damping collars; planted factors keep them. | Interior decorrelation (B1.1, B2.6). |
| **1.13 Aperture shell flux** | Open | A strictly decreasing ground energy can cross zero. | Zero birth jumps; RH ⇔ cumulative frozen relaxation `≤ μ(3/10)`; collar bound; frozen finite families fail. | Signed collar estimate along the moving ladder (B3.6). |
| **1.14 Actual divisor heat sign** | Open | Local repair costs do not sign actual Ξ heads. | Every positive heat repairs every high head; Hermite barrier and optimum; positive monomial reflectors; `Λ < 1/8`. | Zero-heat sign on the residual region (B1.5, B3.9). |
| **1.15 Depth homogeneity** | Sharpened | Every amplification, coupling or averaging over `ℤ` tested gains on a zero's depth as fast as it pays in arithmetic length, so it yields no rate. | Harmonic twists `n^{−ikt}` are tensor powers of unitary characters: their zeros keep the real part while the growth `G` rises with the degree. Følner coupling in completed systems [S]: depth enters only through `1 − β`, giving the boundary collar `≍ 1/(d log T)` and `κ²` sparsity. Quantum budget: every Fejér certificate has `b(½) ≥ 1` once `L ≥ 0.17` and `b(½) ≥ 2` once `L ≥ 1` (14.11). Family averaging over `χ mod q`, `k`-level forms and absolute tensor powers give `Θ − ½ ≲ 1/S`, independent of the degree [R]. | A term that does not scale with the amplification: a fixed base loss (14.14) or Riemann–Roch for oscillatory payment (14.4). The homogeneity law as a theorem per class (W8). |
| **1.16 Payment of ζ's own zeros** | New | Pole order pays only for inserted zeros; ζ's own off-line zeros, if any, are paid by oscillation of the zero sum, which no pole count reaches. | Index–pole conservation identity; the absolute inequality `ind₋ ≤ ord₁F − 1` is false; every deformation gives only lower bounds `ind₋(W_ζ) ≥ R_off − I_off`; simple-pole rigidity [S] (14.13). | An oscillatory capacity: a positive structure bounding ζ's own interior zero charge. As a rate statement this is B1.1; as a section count it is F3 (14.4). |

Key sources: [endpoint](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean), [Vaughan power bounds](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean), [half-damping Vaughan](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheHalfDampingVaughanGramLimitsFormARankThreeRay.lean), [filtered Weil](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity.lean), [rate equality](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/UnconditionalEqualityOfPolarAndFullGroundEnergyRates.lean), [shell ladder](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThresholdVanishingAndCollarDominanceOfThePrimeShell.lean), [radius head](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity.lean), [VK region](../../../formal/GaloisForLFunctions/RHTower/Sieve/VinogradovKorobovZeroFree.lean), [collective repulsion](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/CollectivePoleRepulsion.lean), [index–pole conservation](../../../formal/GaloisForLFunctions/RHTower/WeilIndexConservation.lean).

**Aperture ceiling.** `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`. No positive exponential floor exists; finite-aperture positivity and doubly exponentially vanishing floors remain admissible.

## 2. Wall 3 — transfer: readings, norms, limits, budgets, selection

Closing a face here enables a route but supplies no Wall 1 sign. Three faces reduce to other walls: closedness of the blind ideal is zero-location data (3.3); selection beyond aperture `½ log Γ` is F2 at one height (3.14) [R]; escape exclusion at a fixed damping is a fixed strip (3.15) [R].

| Face | Status | Present limitation | Established boundary / survivor | Missing transfer |
|---|---|---|---|---|
| **3.1 Readings** | Open | Magnitudes, orientation-blind samples, moment families and finite linear readings (even with exact `L²` mass) erase the signed data. | Exact recovery classifications; logarithmic moments; smooth detectors. | Orientation-retaining source readings. |
| **3.2 Aperture/height escape** | Open | Finite windows, radii and prefixes admit mimics. | Cofinal criteria; quantitative visibility. | Containment along the full exhaustion. |
| **3.3 Norms and completions** | Resolved | One norm does not replace another without a theorem; closure can lose payment. | Origin-`L²` completion supports no faithful reading. Golden payment domain: not closed, closure = kernel of total evaluation, continuous dual one-dimensional, closure gap of dimension continuum; the graph norm retains payment. The maximal blind ideal is closed in the natural Fréchet topology with every critical jet continuous; it is dense in the critical-jet topology, and closed there or in any coarser topology iff RH. | — Closedness of the blind ideal is information about the off-line divisor; spectral synthesis inside the ideal is B3.4. |
| **3.4 Shared signed resources** | Open | Local payments can spend one surplus twice. | Frustration and holonomy law; exact descent (excess `kB`); horizon-uniform Schur payment; two-tower box law. | One continuum budget (B1.3, B3.8). |
| **3.5 Endpoint logarithms** | Open | Pole cancellation alone does not pay the endpoint. | Partial-pole-sum logarithmic law; Dini thresholds; monotone-defect Dini law. | The logarithmic remainder for a new source. |
| **3.6 Moving horizons and origins** | Open | Generic below-half interchange and unbounded drift fail. | Priced shifts; reset-origin limits `(K + cKmax)/(1+c)` faithful; raw moving origins add constant mass and violate zero-origin contraction. | Source-specific moving-tail bounds. |
| **3.7 Damping topology** | Open | Hilbert–Schmidt and inverse estimates fail before boundedness does. | Chain bounded, not Hilbert–Schmidt, at half damping; hypercube endpoint bounded for all squarefree `P`; Vaughan admission at and above half damping; integer local exponents below half. | Signed sub-half estimates (B3.11). |
| **3.8 Multiplicity and index** | Open | Packet `m²`, Weil `m`, distinct index and reciprocal depth are different currencies. | Meyer: numerical = principal ⇔ simple; quotient index finite or continuum; trace-bounded ideal keeps every jet and reads RH alone. | Keep trace data separate from operator-norm data. |
| **3.9 Observation cost** | Open | Recovery at arbitrary phase has no universal linear horizon. | Explicit recurrence recovery. | A source-specific horizon bound. |
| **3.10 Filters and hulls** | Open | Invertible critical-Wiener filters preserve admission classes. | Unit-orbit dictionaries; Möbius ≅ Liouville cofactor modules; visible-pole index bounds transfer along unit orbits. | Non-unit repair preserving the source. |
| **3.11 Coupled quantifiers** | Open | Weil margin → heat-Hankel couples degree and time. | Exact bridges with costs kept. | Decoupling where needed (B3.12). |
| **3.12 Residual reconstruction and cofactor limits** | Open | Algebraic injectivity gives no bounded inverse. | Common limit carries a cyclic Wiener module; contraction calculus; cofactor-graph closedness ⇔ a uniform estimate. | Quantitative inverse (B3.3). |
| **3.13 Joint orientation of families** | Open | Individually positive orbits can choose incompatible endpoints. | Common-endpoint classification; spline-orbit index ≤ 1 ⇔ RH. | A compatible source family (B3.10). |
| **3.14 Average to selected heights** | Open | Averaged positivity at logarithmic aperture is proved on `[Γ, 2Γ]`; its main term is the local critical-zero weight. Bad phases recur syndetically. | Phase-selective single-height law; positive-measure positive frequencies; bad-frequency volume bound. | A selection theorem (B1.4). Short windows are the graded path (B3.7). Beyond aperture `½ log Γ` this is signed near-coincidence cancellation at one height (B3.20) [R]. |
| **3.15 Escape states of actual limits** | Sharpened | Subsequential cofactor limits can differ along horizons. | Some actual limit has `K_pp ≥ p^{2ε−2}`; families are singleton or continuum; augmentation is never the unique state; eigencharacters have modulus `p^{−s}`, `s ≥ ½`; finite hulls lie in the half-plane closure; visible interior multiplicities and boundary poles bound the paid quotient; white noise survives every proved constraint. Spectral reading [R]: the cofactor Gram is the truncated translation Gram of `b(u) = e^{−u/2}A_ε(⌊e^u⌋)` with `b̂(τ) = G(½ + iτ)`, `G(s) = ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s`; admission ⇔ `G` in the Hardy space of `Re s > ½`; escape states are horizon Grams of the translated top zeros `ρ − ε`, annihilated by the paid ideal automatically. | The classification of escape states (B3.2): the spectral identity in Lean (W7), then whether actual escape hulls are exactly the translated zeros. A nonzero paid ideal (B3.16) excludes white noise but not the translated-zero states [R]. |
| **3.16 Prime-to-spectral positivity** | New | Positivity is known on the prime side of the explicit formula and is the theorem on the spectral side. | Prime measure finite and positive with characteristic function `Re(−ζ'/ζ)(1+x+iu)`; spectral measures for every `C²` test ⇔ RH. The prime-free gap `|x| < log 2` lies on the positive side, so Poisson-gap rigidity gives only uniform local mass. Unit-gap self-dual positive measures are Dirac combs; narrower gaps admit dual-lattice non-combs. Two-prime spline orbit: RH ⇔ positive measure on `T²`. Affine positivity is induced from the dilations, successor coordinates free. | A self-dual identity with its gap on the spectral side, or source-prescribed successor coordinates (B3.21). |

Sources: [origin obstruction](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OriginHilbertCohomologyObstruction.lean), [blind-ideal closedness](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheBlindIdealIsClosedOnlyWhereOffLineZerosAreSeen.lean), [payment domain](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/CriticalContinuousDual.lean), [shared budget](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/SharedBudgetDescent.lean), [record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean), [kernel families](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/ActualCofactorKernelFamiliesAreSingletonOrContinuum.lean), [eigencharacters](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/CofactorEigencharacterMagnitudesArePowers.lean), [visible-pole index](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/VisibleInteriorAndBoundaryPolesBoundThePaidIndex.lean), [phase-selective heights](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/SingleHeightPhaseSelectiveApertureAndPowerSaving.lean), [both sides](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositivityOnBothSidesOfTheExplicitFormula.lean), [gap rigidity](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveSelfDualMeasuresWithAGapAreDiracCombs.lean), [affine induction](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/AffinePositivityIsInducedFromTheDilations.lean).

## 3. Wall 14 — realization, invariants and forcing

| Face | Status | Obstructed shortcut | Established boundary / survivor | Missing construction |
|---|---|---|---|---|
| **14.1 Capacity and limits** | Open | Fixed finite passive carriers; trace-class transport; a prescribed gap; finite-dimensional affine-unitary carriers. | Growing carriers; `det₂` renewal; nonlocal ports. | A source-preserving limit with orientation. |
| **14.2 Algebra without orientation** | Open | Functional equation, integrality, finite-rank Frobenius, λ-ring or Rosati data, each separately. | Rosati cones have Bézout without unitarity; genus-one Hasse = degree positivity of `ℤ[F]`; Hecke graphs of `ℤ` have no theorem of the square; integer positive-definite functions are sign characters on every group. | An orientation principle; a ring of correspondences over `Spec ℤ`. |
| **14.3 Detector without producer** | Open | A zero-indexed object proves its own input. | Exact depth diagnostics. | Construction first, sign second (B1.6). |
| **14.4 Effectivity** | Open | Naming an ample cone or imposing RR as a field. | Exact source RR; reserve rigidity; majorants give Bézout, never RR; Meyer trace RR, Bézout ⇔ RH. | An independent effectivity source; the surface section law (B3.5). The section count must register oscillatory payment, since pole-order payment reaches only inserted zeros (14.13), and must bound the Hodge defect below its first quantum, `D < 2` (F3) [R]. |
| **14.5 Pre-divisor weld** | Open | Assuming reservoir data satisfy the global identity. | Prime and Gamma reservoir; reflection identities. | Stabilization at every spectral point. |
| **14.6 Section selectivity** | Open | Rank or count readings; Boolean `h⁰ ≤ 1`. | Source-selection obstructions. | A selective section law. |
| **14.7 Base-to-surface theta coupling** | Open | Base `h⁰` supplying the surface cone. | Theta `h⁰(d) = log θ(e^{−2d})`; RR; Mellin to completed ζ. | Surface coupling (B3.5). First trial: indefinite theta series on finite-rank Hecke sublattices, whose modularity holds exactly under a signature condition; not in the corpus [R]. |
| **14.8 Blind-carrier exhaustion** | Open | Positivity on a carrier blind by construction; zero-free-region transfers. | Maximal blind ideal identified, all jets, restricted geometry, `= ⊤ ⇔ RH`; natural Fréchet-closed, critical-jet dense. `ArithmeticForcesBlindness` transfers sources supported outside a zero-free region into it; that is not forcing. | A forcing law with input outside 14.10–14.13 (B1.6); spectral synthesis in the ideal (B3.4). |
| **14.9 Positivity–faithfulness dilemma** | Open | Operator-norm faithful positivity used for RH alone. | Faithful degree ⇔ RH + simple; trace-bounded ideal reaches RH alone. | RH routes through trace-bounded data. |
| **14.10 Single-channel exhaustion** | Sharpened | Forcing inside single-channel quadratic positivity. | Every sharp-stable positive convolution ideal lies in the blind ideal; scale-shift-invariant positive test spaces are blind. Coupled height-channel positivity exists and is mapped: the strip Bochner–Weil form is positive definite in the heights; its boundary shadow is the MPG divisor, its polar-surface shadow has Hodge index ⇔ `L(x,x) ≤ 2κ ℓ_H(x)ℓ_V(x)`; in completed positive systems Følner coupling forces only that not all of `r` zeros with `2Σm > κ` lie on `Re s = 1`, sharply at odd `κ = 2r + 1`, with a `1/log T` collar and `κ²` sparsity [S]. | Scale-side coupled positivity outside the maximality class, or a coupled maximality theorem (B3.17); positivity on tensor powers over a base (14.14) [R]. |
| **14.11 Multiplicative forcing** | Resolved | Imported regions read as forced; finite or coupled certificates read as beating growth; quantization at the critical line. | Boundary: positive-definite divisor, simple-pole trichotomy, four-invariant forcing law with each invariant necessary, finite-profile realization at arbitrary heights, total zero mass `≤ D(0)/2`, capacity `⌊k/2⌋` with every placement realized [S]; interior invisible to boundary data. Interior: exact Fejér barrier `2cos(π/(K+2))`; certified width `(√B−√A)²/G`; universal cap `(3−2√2)/(2L)`; fibre splitting; dlVP optimal for its input. Quantum budget: order `m` at distance `η` survives iff `m ≤ b(η) = (√A + √(Gη))²/B`; `b(0) = A/B ∈ (½, 1]`; every Fejér certificate has `b(½) ≥ 1` once `L ≥ 2(1 − 2^{−1/2})²` and `b(½) ≥ 2` once `L ≥ 1`. | — Better growth input (B2.8) lies outside multiplicative positivity; a quantized inequality in the strip must come from another object (14.4, 14.14). |
| **14.12 Completeness of invariants** | Resolved | Assuming a full-invariant countermodel exists, or that none does. | Positive measure on `[1,∞)` + degree-one theta law ⇒ ζ; Beurling prime measure ⇒ `Λ/log`; discrete systems ⇒ rational primes [S]; Hamburger stability under sublinear critical-line defects. Relaxations: pole order 2 (real pair; refunded quartet), pole order 3 (quartet), strip poles, no FE (over-regular), no positivity (non-uniqueness). | — |
| **14.13 Zero–pole budget** | Resolved | Treating pole order as irrelevant to zero location; treating it as payment for ζ's own zeros; an absolute budget inequality. | Boundary: capacity `⌊k/2⌋` (14.11). Relative interior: `(Weil-index increment) = (pole-order increment) + R_crit − I_crit`, an identity; the refunded quartet raises the pole order by one and the index by two, so `ind₋ ≤ ord₁F − 1` is false. Pole order one is rigid: positive Laplace corrections of ξ with the functional equation force `E = cξ` [S]. Pole order two admits real pairs and, with one critical refund, complex quartets. Completed gauges without an archimedean factor are monic polynomials of degree `2κ` with `2Σm ≤ κ` [S]. Critical zeros force `κ = d`, `T = ζ^d`. | — The relative theory is complete. Payment of ζ's own zeros is Wall 1 (1.16). |
| **14.14 Base for coefficient systems** | Open | Amplifying ζ itself: harmonic twists, absolute (Kurokawa) tensor powers, family averages. `Spec ℤ` is its own base; the class of positive completed systems at pole order one is `{ζ}`, and at pole order two it admits every off-line type, so no class graded by pole order supports a family theorem with RH as base case [R]. | Over `𝔽_q` (Deligne): even tensor powers of a self-dual system on a curve have nonnegative traces, monodromy invariants compute their pole part, and the base loss is fixed and disappears under `2k`-th roots. Over `ℤ` the only class theorem is boundary-level: `κ²` collar sparsity for completed positive systems [S]. | A base `B` with a simple pole and no zeros; a self-dual system `F` whose even tensor powers have nonnegative log-coefficients; a computable pole part of `L(B, F^{⊗2k})`; ζ's zeros among those of `L(B, F)` (B3.19, F1) [R]. |

Sources: [maximal blind ideal](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MaximalBlindIdealOfTheMeyerSource.lean), [forcing transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean), [boundary completeness](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/BoundaryCompleteness.lean), [boundary capacity](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/BoundaryZeroCapacity.lean), [total zero mass](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/TotalZeroMass.lean), [growth-to-forcing](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/GrowthToForcing.lean), [multi-frequency cap](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/MultiFrequencyCap.lean), [quantum budget](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheQuantumBudgetOfMultiplicativePositivity.lean), [strip shadows](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/StripBochnerShadows.lean), [gauge and refund rigidity](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/InfiniteGaugePoleRigidity.lean), [positive-measure rigidity](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean), [pole order two](../../../formal/GaloisForLFunctions/RHTower/PoleOrderTwoRealStray.lean), [refunded quartet](../../../formal/GaloisForLFunctions/RHTower/RefundedComplexStray.lean), [entire FE model](../../../formal/GaloisForLFunctions/RHTower/EntireFunctionalEquationOffLine.lean), [strip-pole model](../../../formal/GaloisForLFunctions/RHTower/LambdaPositiveFunctionalEquationOffLine.lean), [pole-order rigidity](../../../formal/GaloisForLFunctions/RHTower/TwinRigidityPoleOrder.lean), [faithful degrees](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FaithfulPositiveMeyerDegrees.lean), [theta sections](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheThetaH0OfSpecZ.lean).

## 4. Resolved local walls

A resolved local passage is not a research task.

| Local question | Disposition | Remaining wall |
|---|---|---|
| Summation-scope "defects" (BVI, APT, ACS) | Never existed: Mathlib parses the `∑` body at precedence 67, and the proofs use that reading. | — |
| Balanced Möbius and centred-prime band ⇔ `Θ < 1` | Established. | 1.0 |
| Vaughan power improvements ⇔ `Θ < 1` | Established [S]. | 1.0 |
| Vaughan at and above half damping | Admission; actual Gram rank two; rank-three ray at `ε = 1/2`. | 1.8 below half |
| Filtered Weil coercivity, averaged positivity on `[Γ, 2Γ]` | Complete. | 3.14 |
| Polar versus full ground-energy rate | Equal. | 1.11 |
| Maximal sharp-stable positive Meyer ideal | Identified and maximal; natural-closed, critical-jet dense. | 14.8, 14.10 |
| Boundary-line nonvanishing as a forcing law | Complete, with necessity of each invariant. | 14.11 |
| Boundary zero capacity | `⌊k/2⌋` per pole of order `k`, every placement realized [S]. | 14.11 |
| Interior multiplicative forcing by finite or coupled certificates | Excluded beyond growth input. | B2.8 |
| Quantum budget of multiplicative positivity | Computed exactly; no quantized inequality at the critical line. | 14.4, 14.14 |
| Coupled height channels in completed systems | Boundary capacity, `1/log T` collar, `κ²` sparsity [S]. | 1.15, B3.17 |
| Absolute pole-order budget | False; index–pole conservation identity exact. | 1.16 |
| Rigidity threshold of positive relative deformations | Pole order one rigid [S]; pole order two admits every off-line type. | 1.16 |
| Completed multiplicative gauges | Monic polynomial of degree `2κ`; `2Σm ≤ κ` [S]. | — |
| Invariant completeness in degree one | Resolved: rigidity plus relaxation models. | 14.13 |
| Positive self-dual measures with a gap | Unit gap ⇒ Dirac comb; wider gap ⇒ zero; narrower gaps admit non-combs. | 3.16 |
| Affine positivity as an extra constraint | Induced from the dilations; successor coordinates free. | B3.21 |
| Augmentation as the escape picture | Excluded as unique state. | 3.15 |
| Half-damping hypercube endpoint | Bounded for all squarefree `P`. | 3.7 |
| Integer local exponents below half damping | Proved. | 3.7 |
| Vaughan subcritical leading-order limits | Classified. | 1.8 |
| Functional equation versus decaying count error | Incompatible. | 14.12 |
| Sparse-spectrum annihilators | Constructed for `Σ|a|^{−s} < ∞`, `s < 1`. | Not applicable to ζ zeros. |
| Finite-level weight existence | ⇔ RH. | 1.3 |
| Large-height head repair | Complete at every positive heat. | 1.14 |
| PA order-24 finite moment sign | Closed by rational enclosures with outward rounding. | 1.6 |
| Smoothed Landau formula; endpoint attainment; CHMD domains; Suzuki limits; Heath–Brown; smooth detector | Complete. | 1.1, 1.3, 3.1 |
| Local divisor repair; Hermite barrier and optimum | Complete. | 1.14 |
| SSA odd-shift `1/3`, lag-2 `1/4` floors | Exact. Beaten ineffectively in the literature: Tao's logarithmic two-point Chowla gives logarithmic agreement density `½` at every fixed shift; the corpus holds averaged Chowla only as an interface [R]. | B3.13 (effective constants) |

## 5. Scoped obstruction register and positive survivors

These distinctions govern which mechanisms may be proposed. None retires a live route.

| Mechanism excluded or limited | Positive survivor / permitted target |
|---|---|
| Positive exponential aperture floor | Finite-aperture positivity; doubly exponentially vanishing floors; graded negative floors. |
| Permanently freezing finitely many primes | The moving prime-threshold ladder. |
| Eventual all-height phase saving | Single-height phase-selective law; averaged positivity. |
| Average used to sign a selected height | Short-window averages as a graded path (B3.7); beyond aperture `½ log Γ`, signed near-coincidence cancellation at one height (B3.20) [R]. |
| Single-channel sharp-stable positive ideal as forcing carrier | Scale-side coupled carriers (B3.17); tensor powers over a base (14.14). |
| Coupled height channels as interior depth forcing [S] | Boundary capacity for completed systems, `1/log T` collar, `κ²` sparsity: a class theorem at the boundary. |
| Harmonic coupling, family averaging, `k`-level forms or absolute tensor powers as depth amplification | Weight-raising amplification over a base; the homogeneity law as a no-go per class (W8) [R]. |
| Absolute pole-order budget `ind₋ ≤ ord₁F − 1` | Index–pole conservation identity; lower bounds `ind₋(W_ζ) ≥ R_off − I_off`. |
| Pole order as payment for ζ's own off-line zeros | Dominated payment of inserted zeros (complete); ζ's zeros only through oscillatory payment (1.16). |
| Positive relative deformation of ξ at pole order one [S] | `E = cξ`: ξ is rigid in the relative-positive class; pole order two admits every off-line type. |
| Multiplicative positivity as source of a quantized strip inequality | None inside the class (`b(½) ≥ 1` once `L ≥ 0.17`); objects outside multiplicative positivity (14.14, 14.4). |
| Absolute-averaged power-saving Hardy–Littlewood as sub-strip progress | Signed, kernel-weighted near-coincidence forms (B3.20); the absolute versions are expected to start at a fixed strip [R]. |
| Prime-side positivity plus the prime-free gap as spectral positivity | Uniform local mass bounds only; the two-prime Bochner receiver on `T²`. |
| Free affine extension as forcing | Source-prescribed successor coordinates (B3.21). |
| Fourier-quasicrystal rigidity from "pole part minus positive counts" | Must use the archimedean density: the golden datum has the same sign structure and impure zeros [R]. |
| Lee–Yang restriction along the archimedean chirp | Symmetrized Euler exponentials have their zeros on the line above `2π exp(2ψ(N)+1)`; convergence to ζ needs zero location. |
| Harmonic positivity with a double pole or with harmonic poles | Simple pole + pole isolation + integer orders force the boundary. |
| More finite frequencies against a fixed growth payment | Exact width `(√B−√A)²/G`; better growth input. |
| Imported zero-free collar read as forced; zero-free-region transfer read as forcing | Classical regions with explicit growth input. |
| Coupled off-line ceiling read as exclusion | A sign for off-line summands. |
| `Λ ≥ 0` + exact FE without the simple pole | Pole order 2 admits real pairs and refunded quartets; pole order 3 admits unrefunded quartets. |
| `Λ ≥ 0` + exact FE without strip holomorphy | Holomorphy of the completion is a required input. |
| Over-regular count with the FE | Counts fluctuate at least like `⌊x⌋`; positive measures with the theta law are rigid. |
| Signed coefficients with the theta law | Only `Σ a_n sinc²(λ_n) = 0` survives; positivity is essential. |
| Non-monomial universal positive reflector | Source-specific cofactor information. |
| One-factor repair of arbitrary off-line pairs | Exact `δ² ≤ 3u²` boundary and multiplicity costs. |
| Individual orbit positivity for a joint span | Common-endpoint compatibility. |
| Finite readings (with mass) as Bézout source | Infinitely many degrees, or exact source control. |
| Positive quadratic majorant as RR | Bézout and ampleness only. |
| Origin-`L²` completion; Wiener closure of payment | Graph topology retaining jets and payment. |
| Positive Hermitian degree as off-line detector | Faithful variants need simplicity. |
| PSD + dilation + antipodality as escape exclusion | Full paid-ideal annihilation excludes white noise only; translated-zero escape states are annihilated automatically [R]. Permitted target: the escape classification (B3.2). |
| Augmentation as unique escape state | Record-minimum limits with positive diagonals. |
| Raw moving origins as fixed-origin limits | Reset-origin faithful mixtures; fixed-origin paid-ideal constraints. |
| Contraction laws + horizon order as Kronecker selection | Contraction calculus; eigencharacter moduli; rank-one sign law. |
| Diagonal power law as mixed homogeneity | Three-metric averaged repair. |
| Finite-dimensional affine-unitary successor carrier | Infinite-dimensional carriers only. |
| Absolute Vaughan budget as power saving | Signed remainder `≤ CT^{1−2ε}`. |
| Vaughan leading-order limits as residual control | Residual below `T^{1−2ε}` untouched. |
| Unique moving half-damping Vaughan limit | Harmonic subtraction; product horizon selects rank two. |
| Dini or completely monotone defects below half damping | Payable only at `ε = 1/2`. |
| Finite-aperture negative index as global purity | `D` finite ⇔ eventual confinement; RH ⇔ `D < 2`. |
| Zero-indexed action (PW-B) as construction | Independent realization required. |

### Catalogue crosswalk

The 44 mechanism codes in the [killed-routes catalogue](../rh-killed-routes.md) map as follows. This is navigation, not re-certification of legacy entries.

| Codes | Family | Positive direction |
|---|---|---|
| WIP, INT, DEF | Integrality, finite-rank purity, deformation-stable inequalities | 14.2, 14.12, 14.13 |
| ODR, HCT, WHL | Drift, transport, endpoint poles | 3.5–3.7 |
| LGP, ADJ | Local payment; cross-prime majorants | 3.4 |
| PAF | Positive aperture floors | 1.13 |
| AUT, SEL | Automorphic gaps and scattering poles | 14.1–14.3 |
| LLM, UCF, HUS | Averages or reflection-even readers | 3.1, 3.14 |
| GEN | Fixed-part localization | 3.8 |
| TEQ, CAL, JPR, HFR, CCP | Equilibrium, collisions, degree, parity | 1.2, 1.6 |
| TWN, NEV | Unconstructed roots, termwise signs | 1.5, 14.3 |
| ISG, FPR, TRC, GAP, PTR | Fixed or local carriers | 14.1 |
| SRP, APW, CRT | Pole weight, perturbed sources, finite mimics | 1.4, 3.2 |
| BAG, RAW | Finite Euler recurrence; unregularized series | 1.1, 1.2 |
| R1, R2, R3 | Trace, renewal or quantization forcing its own defect | 1.2, 14.3, 14.13 |
| BD, COS, POI | Markov kernels, local inversion, Poisson transport | 3.3, 14.1 |
| DSA, TOR, REF, CPF, TMD, TK | Legacy entries, not re-certified | — |

## 6. What counts as crossing a wall

- **Wall 1.** Insert a newly proved source estimate into an existing receiver with every tail and quantifier intact. Because of face 1.0, any graded gain beyond Vinogradov–Korobov is a fixed strip. A new mechanism must contain a term that does not scale with its amplification (1.15), and for ζ's own zeros it must measure oscillatory payment, not pole charge (1.16).
- **Wall 3.** Prove a transfer, sharp boundary or quantitative reconstruction on a stated class, norm and limit, and show that the source satisfies its hypothesis. For 3.14, a selection theorem; a shorter averaging window is graded progress. For 3.15, the escape classification; a nonzero paid ideal does not suffice [R]. For 3.16, a self-dual identity with its gap on the spectral side.
- **Wall 14.** Construct the arithmetic object independently and prove fidelity at the strength needed, then a forcing law placing the source in the maximal blind ideal with input outside every mapped class: single-channel quadratic (14.10), finite or height-coupled multiplicative (14.11), linear in the coefficient measure (14.12), pole order (14.13). The law must fail on the relaxation models, reproduce pole-order-one rigidity, and reach ζ's own zeros through a term that does not scale: a base (14.14) or Riemann–Roch on the scaling surface (14.4). Blindness of a sub-carrier, however rich, does not cross the wall; neither does a transfer from a zero-free region.
