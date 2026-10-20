# Hard mathematical obstacles on every RH route

Companion: [routine work, open problems and the shape of a missing field](hard-obstacles-summary-2010.md).

Sources: the [route ledger](../rh-current-frontier-map.md) (29 live routes, 18 candidates, PM's PW-B sub-branch), the [walls ledger](../walls/walls-ledger.md) (15 walls), the [proof-constraints brief](../STATUS.md) and the [retired-mechanism ledger](../rh-killed-routes.md). Evidence tags follow the route ledger: [L] umbrella-imported Lean, [S] Lean source not yet audited into an umbrella, [P] paper only.

## 1. Assessment

**No route has a remaining step that is routine.** Every live route ends in one unproved arithmetic statement that implies RH, and every candidate ends in one unconstructed object whose construction would be such a statement. What the corpus owns on each route is exact: the receiver (an implication to RH, usually an equivalence), the complete expression of the quantity to be signed or bounded with every term retained, the positive pieces, the sharp boundary of every shortcut that has been tried, and small-parameter or restricted-family positivity that holds whether or not RH does.

Three ledger-wide facts determine what counts as "just work" below.

1. **No graded relaxation of a surveyed route is easier than a zero-free half-plane.** A one-sided power bound `O(x^θ)` on a Chebyshev or Möbius quantity is the statement `Θ ≤ θ` (the `QuasiRH*` abscissa laws [L]); every `θ < 1` is an unsolved quasi-Riemann hypothesis, and the unconditional savings in the corpus are of Vinogradov–Korobov shape. For the damped PM/BVI receiver, a horizon-uniform energy bound at one fixed damping `ε ∈ (0, 1/2)` yields the zero-translation law `ζ(ρ) = 0, 1/2 + ε < Re ρ < 1 ⟹ ζ(ρ − ε) = 0` (`pmPowerDamped_zero_translation` [L]); no method produces even this, and the unsigned methods stop exactly at `ε = 1/2`, the absolute-convergence line.
2. **The positivity problem has no slack anywhere.** The full Weil cone is the single point `Λ` [L]; prime-blind positivity is node-critical (deleting `log 4` makes it false) [L]; in the arithmetic criticality coordinates the odd form admits no Hardy weight, every prime rate `Λ(n) n^{−1/2}` is the least admissible rate, the variance term is indispensable, and the capacity ratio tends to its critical value `1` as the aperture grows [L]. Near-null test families exist under RH, so no certificate with a margin can exist; exact cancellation is required (Wall 12).
3. **A new mechanism must supply one of five things** (walls ledger): square-root cancellation of a prime sum (Wall 1), equality in Jensen for `log|ζ|` (Wall 2), a Frobenius-type fibration (Wall 5), a Bochner-cone positivity transfer compatible with blindness (Wall 13), or a definite spectral realization of the zeros whose prime part is as large as `S(T)` (Walls 12 and 14). Any proposed mechanism must fail for Beurling systems and for `ζ(s−a)ζ(s+a)`, must survive the degenerate point (one character, modulus one, no family average), must carry information beyond polynomial length equal to height at square-root precision, and must distinguish `log 4` from `log 6`.

### Classification used in every entry

| Label | Meaning |
|---|---|
| **Established** | Proved, with its scope. |
| **(a) Just work** | Finishable with known methods. Three kinds occur: **(a1)** Lean closure, moving an [S] or [P] statement into an audited umbrella theorem; **(a2)** receiver bookkeeping, proving or refuting a stated equivalence, converse or identification whose proof uses only known tools and changes the ledger but not the open problem; **(a3)** a finite calculation or constant the route itself names. No (a) item supplies the missing sign or bound. "None" means no such item exists on that route. |
| **(b) Open, B-RH** | An unproved statement that implies RH (equivalence stated only where proved). |
| **(b) Open, B-C** | An unconstructed object or transfer whose existence is itself a research question; it may be false or stronger than needed. |
| **Walls** | Numbers from the walls ledger. **Refuted shortcuts** are entries of the retired-mechanism ledger; they retire a mechanism, not the route. |

## 2. Live routes

### WL — Weil lag function

- **Receiver.** Exact prime data → one-sided bound on the lag function `Φ(log n)`, on prime lags, or on the integrated Chebyshev deficit → RH. By Landau, a one-sided bound `±∫₀ᵀ (eᵗ − ψ(eᵗ)) dt ≤ B e^{T/2}` already forces RH [L].
- **Established.** Either one-sided bounded-lag criterion is RH-equivalent; power-gap, prime-mesh, progression and thin-exception samplings transfer the bound. Packet laws: every nonzero compact `C²` source has prime-minus-polar packet values `> c` and `< −c` arbitrarily late (packets cannot converge); narrow probes have amplitude `> √(c t log(1/t))`; a universal probe sees every zero and its one-sided boundedness is RH-equivalent; under RH the packet obeys a Parseval law. The packet energy has the exact Plancherel form `∫|𝓕f|²(¼ + 4π²ξ²) S_N(ξ) dξ`; outside the band `|ξ| ≤ √(N+2)` the energy is bounded; a linear band `∫₀^L Ẽ² = O(L)` is RH in both directions, the band's exponential rate is the zero width, and its slope bounds `Σ m_ρ²/|ρ|²` [L]. Cramér's mean square holds under RH [L]. Unconditional Chebyshev and sawtooth errors carry Vinogradov–Korobov rates; Halász-type large-value bounds hold on the critical band [L].
- **(a) Just work.** (a1) The window sign-gap law for bounded packets (`BiScaleUncertainty/PacketSignGapLaw.lean`, source present, not in the umbrella) needs audit and wiring. Nothing else; both directions of the band equivalence are already [L].
- **(b) Open, B-RH.** A source-derived one-sided bound at exponent zero on the lag function or the Chebyshev-deficit primitive, equivalently the linear band bound. Littlewood's `Ω±(√x log log log x)` forbids an `O(√x)` target and either eventual fixed sign; the receiver tolerates a logarithmic loss. A power saving `x^θ`, `θ < 1`, is a zero-free half-plane; the band laws repackage the same estimate. This is Wall 1 in its original form.
- **Walls** 1, 7, 10. **Refuted shortcuts:** packet convergence to zero; thin lag sampling (single base, two bases, countable progressions miss a non-attained off-line top); sub-`√x` Mertens cancellation.

### RW — Restricted Weil ground energy

- **Receiver.** Complete prime−Gamma−polar form → nonnegative constrained ground energy at every aperture → RH; equivalently the sinh-capacity bound at every level, equivalently vanishing all-aperture negative index [L].
- **Established.** Exact split `W = (Markov creation/jump energy) + ½⟨cosh,g⟩² − ½⟨sinh,g⟩²`; on real compact `C²` tests the archimedean functional is `Ω(0)h(0) + ∫₀^∞[(h(0)−h(x))e^{x/2}/sinh x + 4h(x)cosh(x/2)]dx` with nonnegative jump integrand. Positivity holds unconditionally on every test of aperture `≤ 1/100` with margin `‖f‖²/25` [L] and, by a plateau gauge, on supports below `e^{−2}/2` with margin `(3/40)∫F²` [S]. The constrained even-polar form has a self-adjoint ground operator with compact resolvent. Factorial-tent patterns of unrestricted scales, translations and coefficients are RH-complete: RH iff the complete form is nonnegative on all of them; on each fixed pattern support sufficiently high translates are coercive with arbitrarily large constant while the limiting critical prime channel is negative definite, so fixed-support high-scale positivity is nonselective [L]. The corrected-factorial, Müntz-repaired and ramp–tent families all have eventually positive complete energy without RH. Canonical odd primitive cutoff differences converge in graph norm to a nonzero radical vector with complete energy `O((n+1)^{−2})`: no uniform positive gap exists in the original source-graph norm [L]. The pointwise and Bochner cones differ in both directions [L].
- **(a) Just work.** (a1) Audit of the plateau-gauge window module into umbrella status. (a3) Extending the plateau-gauge aperture from `e^{−2}/2` toward the archimedean threshold `t₀/2 ≈ 0.14` by retaining the pole-product potential is finite calculus below the first prime; it stays nonselective because no prime shift enters.
- **(b) Open, B-RH.** The sign of the complete form on arbitrary compact tests at every aperture. In every coordinate system the unpaid term is the signed prime−polar pairing `Σ Λ(n)n^{−1/2}h(log n) − ∫ 2cosh(x/2)h(x)dx`, which equals a Chebyshev-error gauge [L], against the nonnegative Markov energy; so this is O2 with O1 inside it. Factorial-tent completeness moves the same obligation to all scales and patterns.
- **Walls** 8, 11, 12, 13. **Refuted shortcuts:** uniform primitive graph-norm gap; even-ground parity selection (KR-CCP); cofinal Markov ground-state positivity (KR-BD); free-lag scalar trace certificates; reflected-factorial negative witnesses; mixed Gram error as pole payment; corrected tails as negligible energy; pointwise positivity as Bochner positivity.

### FU — CCM-FU signed prime scheduling

- **Receiver.** Signed Möbius/prime scheduling → completed Abel moment `A(M)/M` bounded above → RH; one-sided power bounds give `Θ ≤ 1/2 + max(0,c)` [L].
- **Established.** Prescribed finite prime blocks admit helper cores with positive Boolean energy differences; a prime-exhaustive history decreases complete clock energy at each block cutoff. The closed cone of late compact-cutoff Abel clocks contains every cutoff-fixed target and its negative, so cone membership carries no sign. Distinct deep terminal-prime clocks approximate any source-graph vector with vanishing diagonal cost; for a resolvent eigenvector `μ > 1/2` their off-diagonal pairing is strictly negative at large scale, a conditional negative certificate [L]. Growing-cutoff actual-prime packets with bounded norm and vanishing diagonal stay pairwise separated: low diagonal cost is not compactness [L].
- **(a) Just work.** None. Instantiating finite schedules with their constants does not pay the history.
- **(b) Open, B-RH.** A uniform upper bound on the completed Abel moment paying the seed, the inherited action, the covariance between blocks and the endpoint drift. The decisive premise is nonnegativity of the off-diagonal prime-clock interaction on low-diagonal approximants; it is a premise for the actual primes, not a theorem.
- **Walls** 1, 7, 10, 14. **Refuted shortcuts:** bounded graph norm plus vanishing diagonal as compactness; fixed smoothing for growing prime packets; coarse Selberg inputs; weighted Suzuki first-moment bound (premise false under RH).

### RP — Route-P / SP-E history floor

- **Receiver.** Literal matched−quantile prime history → eventual linear defect floor → RH [L].
- **Established.** Signed hyperbola, centroid and square-debt identities; low-LCM payment; exact Abel/RP tail representations. The native first clock jet is bounded, noncompact, strongly but not operator-norm differentiable. Positive Burnol damping shells tend strongly to zero while their trace tends to `log(c)/4 > 0`, so trace-norm vanishing is impossible [L]. Absolute high-LCM fibre variation diverges and pointwise coprime positivity fails; the complete fibre of two primes `p, q ≤ M < pq` is `2a(p)a(q)` [L].
- **(a) Just work.** None.
- **(b) Open, B-RH.** The complete-history floor with centroid and square debt, high-LCM terms, moving core and singular-domain transport paid together; the required cancellation is signed between full LCM fibres and cannot be absolute.
- **Walls** 1, 10, 14. **Refuted shortcuts:** shell trace-norm vanishing; absolute complete-fibre payment; independent biased two-channel saving; separate late-prime mixed payment; causal mass compensation.

### PA — Prime–archimedean source passivity

- **Receiver.** Continued exact prime−archimedean trace → high-frequency passivity, a thin Bernstein mismatch envelope, or a signed compact moment completion → RH.
- **Established.** Finite-frequency trace and source recovery are exact; signed current multiplier positivity on all upper half-strip slices is RH-equivalent; arbitrarily thin exponential envelopes for the coupled-Sonin Bernstein mismatch imply RH with every Hausdorff positivity premise discharged. For each fixed Hausdorff order `k` the calibrated moment differences are nonnegative beyond an order-dependent shift, and any finite block of orders simultaneously; no order-uniform threshold exists [L]. A bounded-support signed-measure representation of all normalized moments is RH-equivalent, so constructing it is RH. If RH fails, Bernstein index measures recover the maximal off-line packet (tomography, not exclusion). At the critical Stokes carrier every exact completion must raise infinitely many singleton masses, so passive deletion and finite atom repair fail [L]. A positive quadratic saddle band carries half the absolute atom mass; its complement is uncontrolled.
- **(a) Just work.** (a3) Checking finitely many shifts for finitely many orders is bounded; the orders are unbounded, so this does not close the criterion.
- **(b) Open, B-RH.** The arithmetic sign of the high-frequency current numerator; or an order-uniform shift threshold (common all-order positivity, O3); or the signed complement of the saddle band.
- **Walls** 2, 6, 12, 15. **Refuted shortcuts:** fixed finite passive realization (KR-FPR); thermodynamic ensemble change (KR-TK); termwise Nevanlinna sign (KR-NEV); passive deletion / finite atom repair.

### MC — Möbius cancellation at half power

- **Receiver.** Signed Möbius source → half-power cancellation, subpower energy, or a square-sampled Chebyshev bound → RH. For every fixed `θ > 0`, a one-sided subpower bound on the Möbius–divisor quotient head at cutoff `M^θ` is equivalent to RH; the cumulative square energy of the normalized Abel action has exact exponent `2Θ` [L].
- **Established.** Hilbert, Liouville, Riesz and square-source receivers; exact signed bilinear and divisor decompositions; the Vaughan two-cutoff identity and the Type-II dictionary `typeIIShort_N(k) = 1_{k=1} − sieveSeq_{N,μ}(k)`; all-horizon unsigned energy `≤ M·invSum(M)³`; Vinogradov–Korobov window rates; Mertens `Ω±(√x)`. On a moving high-dilation cutoff the squared tail is diagonal plus signed covariance, the diagonal prefix is `≤ 9N/25`, and the signed covariance at cutoff exponent `1/2` is the RH-equivalent term; replacing it by the positive absolute envelope fails (energy `J^{m+1}`) [L]. BVI supplies every finite law of the trans-horizon source (first octave `= −μ`, sharp moment cones, fixed-ratio limit laws with both signs persisting), and the renormalized defect is nonpositive at every prefix for large horizons [L]. At fixed damping `ε > 0` the receiver-row variance has a horizon-uniform ceiling that vanishes as `ε ↓ 0` while the literal-μ floor stays `≥ 1/288`; the limits do not commute [L].
- **(a) Just work.** (a1) The small-damping rates `R(ε)/ε → 1/2`, `R(ε)/variance → 1` [S] need umbrella audit. (a2) Rewriting the complete log-renormalized interior remainder of the pronic receiver through the existing Heath-Brown/Vaughan dictionary as an explicit Type-II bilinear form plus `O_ε(1)` is bookkeeping; the dispersion estimate for that form is not.
- **(b) Open, B-RH.** The global signed bilinear bound at half-power scale, principal counterterm and high-product remainder together, that is `M(x) = O_ε(x^{1/2+ε})`. Divisor-sum (Type I) information gives the constant `2` and never `1` (parity); every power saving is a zero-free half-plane; a fixed-ratio limit does not bound a ratio growing with the cutoff.
- **Walls** 1, 7, 10, 11. **Refuted shortcuts:** positive high-dilation envelope; termwise completed double-pair payment; summable scalar Dirichlet square root; separate moving hyperbola head; absolute squarefree-discrepancy contraction; periodized uniform-cycle budget; deformation-stable inequalities (KR-DEF).

### TT — Theta-tail and heat–Cassini currents

- **Receiver.** Theta source → directed signed covariance/Wold decay or odd Weil-form sign → RH.
- **Established.** Exact seam, tail and odd-four identities; sharp Wold boundedness threshold `t < 1/2`; natural-cutoff energy criterion; the odd/primitive form has an exact half-line reflected-prime inequality and Φ-Doob form. Full translation averages of entire strip-decaying tests are independent of a zero's transverse depth [L]. A continuous periodic Kelvin-chirp profile cannot give a positive-definite separator once `e^L > 4 + 2√2` [L]. The enriched clock current is positive in the inner chamber `0 < t ≤ min(2,u)` at action `Z ≥ 4050e⁴` [L]. The abstract Ruelle continuation has no proved identification with ζ.
- **(a) Just work.** (a3) Enlarging the inner-chamber positivity region (bounded action, `0 < t < 2`) is finite calculus; it does not transfer to the global signed receiver.
- **(b) Open, B-RH.** Signed nonlocal covariance or Wold decay, or full odd/primitive positivity, across every rapidity and test scale.
- **Walls** 4, 7, 13, 15. **Refuted shortcuts:** transverse equilibrium (KR-TEQ); pair-heat monotonicity (KR-CAL); translation averaging; pointwise centred curvature; fixed seam directions, kinetic concavity and fixed-endpoint source controls; positive displacement coefficients.

### LA — Line anchor

- **Receiver.** Literal theta source → all-height Laguerre/Hadamard or Jensen sign → real-rooted `Ξ` → RH; `RH ⇔ Re(ξ′/ξ) ≥ 0` on `Re s > 1/2` [L]; heat-slice Taylor positivity at time `λ` is equivalent to `newmanConstant ≤ λ` [L].
- **Established.** Unconditionally `newmanConstant ≤ 1/8` (the strip width, Wall 4); the slice coefficient operator has exact negative index; the Riemann–von Mangoldt remainder is not integrable [L]; the Balazard–Saias–Yor identity identifies the critical-line `log|ζ|` integral with the multiplicity-weighted sum over right-of-line zeros [L]; fixed-degree Jensen–Hermite limits hold, and hyperbolicity in the regime `n³ log²(n+2) ≥ K d⁵` is unconditional and nonselective (KR-JPR). Zero clusters persist under the heat flow.
- **(a) Just work.** None. Finite-height verification is bounded work and leaves exceptions.
- **(b) Open, B-RH.** The all-height arithmetic sign, including the low-order slices and an arithmetic separator for near-double off-line pairs; the needed direction of the de Bruijn–Newman constant is the upper bound `≤ 0`, while the strip gives only `≤ 1/8`.
- **Walls** 3, 4. **Refuted shortcuts:** KR-JPR, KR-CAL, KR-TEQ; Laguerre–Pólya inverse differential filters; mass-calibrated score floors.

### TG — Topological sub-unit gate

- **Receiver.** Pre-divisor Euler/Gaussian source → positive-residual cubic transgression and integer trace `< 1` → RH.
- **Established.** Boundary winding and index identities; source-sensitive transgression; the original proper-prime-power nuclear assembly is summable while the raw linear-prime trace is not; the Gamma remainder response, physical maximal domain and fixed-test Hardy nuclear limits are closed [L]. Factorial cubic windows can have zero surviving-prime work and unbounded positive renewal mass; prime masks are unbounded on the ground grid; no fixed-carrier meromorphic current continuation exists [L].
- **(a) Just work.** (a3) The final integrality implication once a nonnegative integer is shown `< 1`; finite matrix identities on their declared domains.
- **(b) Open, B-RH.** The matrix-complete identity `E_base = E_residual + Tr T_D` with `E_residual ≥ 0` and the sub-unit trace on every disc; or the source central-gap bound at exponent zero. **B-C:** the source-to-divisor transgression itself (what KR-DSA leaves).
- **Walls** 12, 14, 15. **Refuted shortcuts:** anchored chiral-loss passage (KR-R1); discrete escape indicator (KR-DSA); cubic-causal positive contraction; raw Gamma ground repaired by distant clocks; universal physical arithmetic selector.

### HF — Positive Hodge form on arithmetic cohomology

- **Receiver.** Original arithmetic cohomology → positive Hodge-compatible form, or a full-positive arithmetic weight → RH; equivalently prime-blind positivity (PBAP) [L].
- **Established.** Full-positive weights are rigidly `Λ`; the Meyer quotient has global Xi-jet synthesis, faithful Hasse admission, nondegenerate Paugam pairing, compact inverse with determinant `Ξ`, trace-class arithmetic flow and the complete prime−Gamma−polar trace [L]. A positive-definite rational-dilation-invariant form on the Xi zero algebra exists iff RH and all zeros are simple; it is built from the divisor (circular). Odd-sector Farkas equivalences, M. Riesz extensions, and a secular counterterm hierarchy give coercivity up to ratio `S/L ≤ 27`, but every nonzero smooth prime-blind even-polar test has `S/L > 27`; the all-ratio Markov bound still assumes `2 sinhHalfMoment(f)²` dominance [L]. On sparse blind node sets (fixed logarithmic gaps, sub-square-root density) zero-pole positivity fails; full integer-log blindness remains the RH-equivalent receiver [L]. Bounded-energy all-grid correlations have compact limits but can lose Lévy energy at the origin, so limit passage needs uniform origin control [L]. A measurable dual witness with Carlson-rate admission blind on a set of positive logarithmic density vanishes [L].
- **(a) Just work.** (a1) The exact single-integer blind symbol slack [S] needs audit. (a3) Finite-grid collar optimizations and their constants; these bound archimedean energy only.
- **(b) Open, B-RH.** PBAP on unrestricted prime-blind tests in the actual `S/L > 27` regime without the unpaid high-frequency `sinh`-moment premise. **B-C:** a source-defined positive Hodge/cup/trace structure on the original cohomology, with the correct trace and no simplicity premise; a faithful whole-quotient native completion, which requires changed topology, regularization or normalization because the unregularized extension is obstructed [L].
- **Walls** 5, 11–15. **Refuted shortcuts:** zero-algebra invariant form; sparse-node positivity; `S/L ≤ 27` closure; finite global Weil certificates; uniform strict relative moment gap; subcritical Gamma domination; unit-mass joint phase correction; the Weil-work families (exposing-ray margins, settled phase, translated-radical repair, finite-observation determination).

### CHMD — Causal Hyperbolic–Modular Duality

- **Receiver.** Exact Weil source → causal prime wave, Chebyshev-discrepancy derivative pairing, Möbius-rest one-sided bound, or theta-Doob odd-sector half-bound → RH. RH iff `∫₀^∞ ∂_s K_y(s) Δ(s) ds` is bounded above (or below) for `y ≥ 0`, with `Δ` the classical discrepancy; iff the odd bound-state space is zero; iff the complete odd archimedean-plus-prime-chain Poincaré inequality holds [L].
- **Established.** The arithmetic resolvent has simple eigenvalue `1`; nonzero primitive eigenvalues lie below `1`; if off-line zeros are finite the odd/even/total bound-state dimensions are `(q, q+1, 2q+1)`. One-signed odd eigenstates above `1/2` vanish; sign-changing ones are not excluded. The signed radical is `ker(resolvent − ½)`; the polar-constrained quotient is nondegenerate; original source mass does not descend through the radical; translated cardinal projections span the primitive bound band without assuming finitely many off-line zeros [L]. Beurling–Deny nodal contraction, five-term lobe balances and nodal-modulus identities hold; `RH ⇔ sourceEnergy(absGraph) ≥ 4·sourcePair(posGraph, negGraph)` on every odd eigenvector above `1/2`. For every finite `θ` the fixed-coefficient cosh-by-sinh absorption fails on some compact even multiplier at `0 < a ≤ (log 2)/2`; the minimal nonnegative local correction is `max(oddPolarDefectDensity, 0)`. The Schur ratio pays every finite prime collar sum by half-line jumps plus a support budget, and `coshSinhPolarRatio ≤ θ ≤ 1` would absorb all collars, but that ratio is not attainable in general (it fails at `R ≥ log 2`). Finite Möbius folds stay uniformly separated from the completed wave [L].
- **(a) Just work.** None.
- **(b) Open, B-RH.** An actual-source inequality excluding sign-changing odd eigenstates with `μ > 1/2`: payment of the primitive `oneL` defect, equivalently a sign for the nodal cross-prime term; or the one-sided bound on the discrepancy-derivative pairing, which is the Chebyshev deficit again (O1).
- **Walls** 1, 12–15. **Refuted shortcuts:** one-signed exclusion as full proof; compact primitive source projection; strict coercivity of the unrestricted quotient; finite folds as uniform approximants; fixed-coefficient absorption; even-Θ Doob positivity on odd tests; positive clock-cone membership as a sign.

### TH — Theta moment positivity

- **Receiver.** Exact theta/prime−Gamma moments → all-degree Hankel/Bezoutian positivity at one positive heat time → RH.
- **Established.** Moment and heat-current receivers; finite-rank sign regions; fixed-rank positivity is unconditional, and rank-`N` tests cannot see off-line zeros above height `O(N√log N)` (KR-HFR). The quartic Schur charge is the squared norm of a nonlinear two-coordinate feature, so no linear norm-square receiver exists on degree-one coordinates [L]. The enriched clock current is positive on `2 ≤ t ≤ u` and in the inner chamber at large action.
- **(a) Just work.** (a3) Evaluating specified finite moment matrices; enlarging the inner-chamber region.
- **(b) Open, B-RH.** Positivity at all degrees at one common admissible heat time with the full discrete-prime remainder; "for every degree, eventually in another parameter" is not "at one parameter, for every degree" (O3).
- **Walls** 3, 4, 12. **Refuted shortcuts:** fixed-rank heat-Hankel completion (KR-HFR); heat transport as same-time positivity; coarse eighth-moment absorption; pointwise-positive compensation kernels; quadratic clock-current relaxation; linear quartic Hilbert receiver.

### RN — Theta renewal and singular comparison

- **Receiver.** Literal theta renewal/connection source → divisor-faithful winding or directed boundary-work sign → RH.
- **Established.** Global native Green/whole-BV solver, full-multiplicity Meyer packets, fixed-Gaussian realization and generator intertwining; the literal causal renewal kernel is Hilbert–Schmidt and cone-positive with `det₂(zK) = exp(−dz)D(z)/D(0)` for the actual renewal denominator; every resonance is an eigenvalue of matching multiplicity, and cone positivity does not confine complex resonances [L]. The reduced theta-ratio slope has positive physical value but negative conjugate value, norm and trace on a boundary strip. The fixed Cauchy-pole quartet defect vanishes iff RH (zero-side). The unregularized native extension of finite synthesis has no continuous extension; the unrestricted nonlinear action tends to `−∞` on two-plateau tests [L].
- **(a) Just work.** None.
- **(b) Open, B-RH.** The mixed prime+Gamma ≥ pole inequality with all cusp terms, global seam/cusp gluing and the arithmetic boundary-current orientation. **B-C:** a source-faithful native completion in a changed topology, regularization or normalization.
- **Walls** 10, 13–15. **Refuted shortcuts:** trace-ideal transport (KR-TRC); dyadic renewal winding (KR-R2); native extension; nuclear Ruelle zeta; uniform local source orientation; positive reduced-slope norm.

### WD — Ward orientation and horizontal collision

- **Receiver.** Directed source current → global negative-cross control or collision charge `< 2` → RH; the nonnegative global cap vanishes iff RH [L].
- **Established.** Exact Ward and collision receivers, source formation, cap integrability, strict-right multiplicity readout; the oriented extension of the collision charge vanishes under pair exchange, and the surviving quantity is the squared displacement, which cannot choose a sign [L]. Gaussian-height-averaged slice positivity is Euler-blind (KR-HUS).
- **(a) Just work.** None.
- **(b) Open, B-RH.** Source-derived vanishing of the global cap, or a complete signed prime−Gamma contraction with uniform owner/absorber bounds for every zero block. Nonnegativity is the wrong endpoint: the cap must be zero.
- **Walls** 3, 12, 15. **Refuted shortcuts:** uniform free-orbit count (KR-UCF); holomorphic collision quantum (KR-R3); averaged Husimi positivity (KR-HUS).

### LI — Paired Li and prime–Gamma balances

- **Receiver.** Literal prime−Gamma history → signed lower floor → Li positivity → RH; RH iff an eventual finite lower bound on the literal primitive [L].
- **Established.** Exact paired histories and finite primitive receivers; closed-ideal operators classify RH-equivalent compactness. Unconditionally the actual clock series has `liminf |S| = 0`, both jet signs occur cofinally, the resolvent and causal inverse take negative values, the low cumulants are negative, every absolute exponential history envelope fails, and no fixed-history truncation converges [L].
- **(a) Just work.** None; finite coefficients compute with certified error and give no eventual sign.
- **(b) Open, B-RH.** `Re H_N ≥ K_N − C` on `0 < t ≤ c log(2N+1)`, or the equivalent finite lower bound for the literal primitive, with first-crossing and outside correlations retained.
- **Walls** 1, 10, 12. **Refuted shortcuts:** all-even Euler-jet positivity; fixed-prefix completion compensation; radial-density monotonicity; positive-kernel inverse; absolute forcing-history domination; raw positivity/cumulant promotion.

### SZ — Suzuki screw and shifted-kernel limits

- **Receiver.** Complete signed boundary pairing → screw nonnegativity or shifted-`Ξ` confinement → RH.
- **Established.** Screw and shifted-`Ξ` receivers; supported phase recovery; the literal arithmetic Hankel operator is compact self-adjoint at every positive shift and aperture; the two-leg Suzuki Gamma source has exact graph closure and Cesàro admission; Cayley moment partial sums reconstruct the carrier density a.e. [L]. The quadratic-contact residual is `o(N)` from the prime number theorem with no power saving; finite-contact residuals and formation energy have exact `Θ` exponent laws; cumulative formation mean square has exponent `2Θ` [L]. On the common compact core the screw quadratic equals the RW restricted form and the CHMD signed quotient energy; the completed norms are not identified. Prescribed and raised shift carriers collapse on `1/2 < s < 1`; the Gamma–polar–prime symbol at frequency zero takes both signs on late windows [L].
- **(a) Just work.** (a2) Deciding whether the RW/SZ/CHMD common-core equality extends to the completed source norms is receiver bookkeeping; it does not supply a sign.
- **(b) Open, B-RH.** The source Wronskian law paying the moving infinite head and shell leakage, and a cusp-preserving passage to unshifted `Ξ` as the shift tends to zero; self-adjointness permits negative spectrum and compactness at each positive shift gives no uniform unshifted limit.
- **Walls** 2, 4, 12, 14. **Refuted shortcuts:** termwise Nevanlinna/HB sign (KR-NEV); cofinal Markov ground state (KR-BD); prescribed shift as direct Xi target; exact independent two-prime phase density; eventual one-sign flux; exterior constant-lift positivity.

### PM — Physical-model routes: FZZ-P (live), PW-B (candidate)

- **Receiver (FZZ-P).** For `φ_a(t) = {1/(at)} − 2{1/(2at)}` on `(0,1]`, approximation of the dyadic Haar target in `L²(0,1]` is RH-equivalent [L]. Sufficient: cofinal canonical admission of the power-damped Möbius source, that is `L²` membership of `pmPowerDampedFermiSource ε` for dampings `ε` arbitrarily close to `0` (`riemannHypothesis_of_pmPowerDamped_cofinal_admission` [L]); sufficient for that: a horizon-uniform bound on the complete pronic energy `Σ_{n≤T} I_ε(n)²/(n(n+1))` at a cofinal sequence of dampings (`riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded` [L]), with constants allowed to depend on `ε`.
- **Established.** Admission and horizon-uniform energies hold for every `ε ≥ 1/2`, including the endpoint [L]; for `0 < ε < 1/2` admission is equivalent to a uniform centred-sawtooth variance bound, which is a premise. The Mellin identity is `(1 − 2^{1−s})ζ(s)/(sζ(s+ε))`; under admission at fixed `ε ≤ 1/2` it continues across the right strip and yields the zero-translation law `ζ(ρ)=0, 1/2+ε<Re ρ<1 ⟹ ζ(ρ−ε)=0` [L]. At each fixed `ε > 0`: the cofactor-row renormalized defect is nonpositive at every prefix for large cutoff; the receiver row has cutoff-uniform variance ceilings vanishing with `ε`; the active-deleted, predecessor-peak and adjacent fields have `O_ε(1)` compensated remainders; the renormalized interior bracket tracks the actual energy within `O_ε(1)`, so strict interior contraction is equivalent to boundedness, not a proof of it [L]. The complete energy is a five-piece Vaughan expansion with 25 signed Gram entries whose available logarithmic majorant is nonsummable below half damping; the active-pair plus predecessor-peak drift is unbounded at small fixed `ε` with slope `≥ 1/24`, so only the log-renormalized complete energy can be bounded [L]. Witness germ rigidity, fold-free equivalence, exact first-octave cell energies `(1 + Σ_{N<k≤n} μ(k))²/(n(n+1))`, selected-trace inverse loss `(4/π²)(log₂N)²`, and the dyadic-antichain capacity classification are exact [L]. The Báez–Duarte residual of the cofactor row is `(1 − energyMean)² + energyVariance` with floor `κ/log(Q+1)` [L].
- **(a) Just work.** (a1) The small-damping rate module [S]. Nothing else: the `ε = 1/2` endpoint is proved, and every statement at fixed `ε < 1/2` that is bookkeeping (compensated remainders, defect sign, variance ceilings) is already [L].
- **(b) Open, B-RH (FZZ-P).** Unconditional global Haar approximation; equivalently top-octave domination or the linear origin-mass bound for every witness; sufficient: the horizon-uniform complete log-renormalized pronic budget at arbitrarily small fixed `ε`, paying the positive active-pair drift, conditional-head mean, interior orbit means and signed prime-clock complement. A bound at one fixed `ε ∈ (0, 1/2)` is not a step of lesser difficulty: it gives the zero-translation law, which no known method produces, and the unsigned method (`{N/d} ≤ (N/d)^a`) stops exactly at `ε = 1/2`.
- **(b) Open, B-C (PW-B).** A pre-divisor source formulation removing the `XiZeroCopy` indexing; a complete small-damping energy ceiling as `c → 0⁺`; proof that the source-contact action implies the optical-magnitude, ordered-cap and all-divisor-extinction receiver. The Eisenstein value at `i` factors through `ζ` and `L(s, χ₋₄)`, so it does not isolate `ζ`.
- **Walls** 1, 2, 7, 10. **Refuted shortcuts:** local `(δ,1]` completeness as global approximation; damping monotonicity; uniform prime-subset budgets; raw positive-divisor cutoff; separate Ramanujan pair/support budgets; isolated growing-cofactor sectors; compact normalized band profiles; imaginary-damping interpolation; bounded uncentred active-pair payment; HB and its producer classes.

### JAS — Joint ancestry

- **Receiver.** Arithmetic prime-product Weil form → level-one positivity on sufficiently large-prime tests → RH; or square-shell arithmetic Riesz sums → subpower bounds on the finite power window `m < k ≤ m + m/log(m+1)` for every exponent → RH [L].
- **Established.** Level-one full-product and dyadic constant-vector positivity, cosine-kernel and harmonic Euler positivity on large primes, PSD at infinity at every level `σ > 1` and torus-density nonnegativity are all RH-equivalent without side conditions; the synchronized Gamma–theta source is admitted over all finite prime supports and Mellin grades with forward creation covariance [L]. The native prime-product form is nonnegative on finite prime sets above a cutoff with budget `Σ_P p^{−(σ−1/2)} ≤ ((log y)/(128·10⁸))^{3/2}/(log log y)⁴`; the level-one receiver needs budget `y^{1/2}` [L].
- **(a) Just work.** (a3) Improving the logarithmic budget constant; no finite improvement reaches a power.
- **(b) Open, B-RH.** The source sign at the power budget on sufficiently many shells, all-amplitude damped-shell positivity, or the subpower Riesz bound on the moving window; typical phases are positive, exceptional vectors are the problem (O5).
- **Walls** 3, 6, 7, 12. **Refuted shortcuts:** closed-flat unit-residue certificate (circular); logarithmic-budget positivity as the power-budget receiver.

### CTF — Chronological tail and Báez–Duarte approximation

- **Receiver.** Bounded chronological Bose/Möbius rows, or finite Báez–Duarte dilates → vanishing `L²` error → RH; `d_N → 0 ⇔ RH`; bounded rows with vanishing error ⇔ RH [L].
- **Established.** The discrete Gram at reciprocal-integer arguments has an exact Vasyunin formula. For every finite row the squared residual is `Σ_{M≥1}(1 + sievePrefixDiscrepancy(N,M,c))²/(M(M+1)) = (1 − Λ-readout)² + energy-centred pronic Gram`; every level-`N` row has residual `≥ κ/log N` and obeys `κ·readout² ≤ (log N − κ)·energy` [L]. For truncated literal `μ` the readout tends to the required value while the centred pronic energy has floor `κ/(4 log N)` [S]. Bounded vanishing-error rows must have the Möbius coefficients; every coefficient budget `exp(ε^{−θ})`, `θ ≤ 2`, fails if RH fails; rows retaining literal `μ` through `N/2` have Selberg diagonal `≥ 1/2359296`; `ker P` centring cannot make the Selberg diagonal `o(1/log N)` [L].
- **(a) Just work.** (a1) The literal-μ readout and energy-floor module (source present, untracked) needs audit into the umbrella.
- **(b) Open, B-RH.** Rows whose centred pronic energy tends to zero (the readout is already aligned for `−μ_N`), that is `d_N → 0`; whether rows attain residual `O(1/log N)` is a quantitative form of RH. The signed LCM/Bézout boundary defect needs a uniform cofinal bound.
- **Walls** 1, 2, 7, 10. **Refuted shortcuts:** vanishing Selberg diagonal with a literal Möbius prefix; sub-logarithmic `ker P` diagonal; uncorrected Dirichlet-polynomial mollifiers (ratio `≥ 49/48`); regular exact-null certificates.

### HCF — Gaussian heat trace / critical feature variance

- **Receiver.** Exact arch−prime heat trace → one-sided vertical growth, or all-degree positivity on two prime-log grids after polar cancellation → RH. Complete Hankel positivity on two grids with spacings `log p`, `log r` for distinct primes is RH-equivalent; `(2,3)` suffices [L].
- **Established.** Seven equivalent capstones at any fixed heat time; fixed-rank positivity is unconditional; singular blocks have exact negative-index, Toda contact and escaping-branch laws. A nonreal conjugate packet inside the spectral parabola can mimic a positive atom on one complete grid and on any finite family of same-step offsets; two marginal grids do not reconstruct four-atom packets; mixed two-step moments determine summable packets under separation hypotheses [L]. Compact-source alias and phase variance obey a phase-uniform budget controlled by the Xi phase-histogram entropy deficit.
- **(a) Just work.** None beyond fixed-rank evaluations.
- **(b) Open, B-RH.** Positivity of both literal prime–archimedean grid forms at all polynomial degrees on their polar hyperplanes; or the one-sided prime-chirp/vertical bound; or a cofinal entropy-deficit bound (O3).
- **Walls** 3, 4, 7, 12. **Refuted shortcuts:** one-grid or finite-offset aliases; marginal reconstruction; fixed-rank completion (KR-HFR).

### XN — Xi Newton invariant discs

- **Receiver.** Xi first-jet source → line-centred Newton self-map discs covering every zero → RH; disc coverage with nonnegative interior margin is RH-equivalent [L].
- **Established.** Inside each disc `ΔQ = 4(r² − |z − c|²)|ξ″(z)|² ≥ 0`, so boundary positivity does not imply interior positivity; an entire scalar damping makes the Newton map globally holomorphic iff it is zero; each fixed disc has a polynomial pole repair preserving reflection and first root jets but not self-mapping [L].
- **(a) Just work.** (a3) Evaluating an explicitly specified finite disc and its Green potential.
- **(b) Open, B-RH.** An arithmetic construction of line-centred discs covering every zero with `Q ≥ 0` throughout each disc, paying the interior curvature Green potential.
- **Walls** 3, 4, 15. **Refuted shortcuts:** global scalar damping of Newton poles.

### BAG — Deterministic zeta self-return

- **Receiver.** Reflected approximate functional equation → unbounded physical self-returns of `ζ` on each right-strip disc → RH (sufficient direction proved; converse not asserted) [L].
- **Established.** Finite Dirichlet polynomials have positive-density uniform self-returns; Carlson's unconditioned vertical `L²` tail mean tends to zero with head length; the unadjusted centred tail at `1/2 < Re z < 1` retains an Abel pole of size `M^{1−Re z}` with divergent mean square and density-zero return sets, while the Abel-centred tail has vanishing mean square and density-one good heights [L]. On discs whose doubled closure lies in the strip the shifted Carlson tail is uniformly small off a set of small upper density; finite-head almost periods give `ζ` self-returns on typical translated base discs, not on the prescribed disc; a finite head with a zero inside the disc has pole-shifted return set of density zero; isolated head-zero heights have vanishing upper density; the translated orbit is precompact outside small-density exceptional sets [L]. Bohr–Fourier coefficients of `ζ` on `σ + it` are `n^{−σ}` at `log n` and zero elsewhere [S].
- **(a) Just work.** (a1) The Bohr–Fourier coefficient module (source present, untracked) needs audit.
- **(b) Open, B-RH.** Fixed-base-disc physical self-return: control of the centred tail on the same finite-head return heights, uniformly on a right-strip disc, with the Abel base-point pole paid, through a mechanism that survives a head zero inside the disc. Conditioning on a return event of density `κ` costs `1/κ` generically; typical translated-height recurrence is nonselective (Wall 7).
- **Walls** 2, 7. **Refuted shortcuts:** finite Euler recurrence (KR-BAG); independent phase transfer (KR-TOR); mollified Littlewood–Levinson (KR-LLM); unadjusted centred-tail returns; automatic fixed-base head/tail overlap.

### EWU — Even pole-weight uniqueness

- **Receiver.** Actual even blind minimum nonnegative at every aperture → even positivity → `λ = Λ` → RH [L].
- **Established.** Blind minimizers exist at every aperture; the minimum is antitone in the aperture, at least `1/20` for `a ≤ (log 2 + 1/50)/2`, and nonnegative at every aperture iff RH; constant archimedean shifts preserve minimizers and residuals while moving the minimum's sign [L]. Every nonzero smooth prime-blind even-polar test has `S/L > 27`. Endpoint-collared critical factorial sources have complete collared energy positive above an absolute scale [L]; the uncollared critical prime channel is `ℓ²`-bounded on dyadic blocks, and the complete uncollared critical form is positive definite on every sufficiently high dyadic block for patterns of any size [S]; the limiting critical prime channel alone is negative definite, and unrestricted factorial-tent patterns are RH-complete, so fixed-support or single-block positivity does not settle the minimum [L].
- **(a) Just work.** (a1) The uncollared prime-channel bound and the high-block complete-form positivity [S] need audit. (a3) The explicit block threshold `M₀`, slopes and offsets.
- **(b) Open, B-RH.** The nonnegative even blind minimum at every aperture: the complete `Λ` prime−polar form plus constant on arbitrary even-polar tests. **B-C:** a passage from the critical family, positive on high blocks, to the compact tests of the receiver with a margin surviving truncation; a multi-block Gram law or asymptotic orthogonality of critical sources on distinct blocks.
- **Walls** 8, 11–13. **Refuted shortcuts:** positivity of the limiting critical prime channel; sub-unit pole-weight periodization; blind-ground geometry as absolute sign; prime-2 blindness as a pointwise interior deficit; supercritical Nyquist residuals; correlation compactness as energy continuity.

### GTA — Transverse Schur charge

- **Receiver.** Actual theta-stage positive quartic Schur charge → rank-uniform transverse decay → RH [L].
- **Established.** Uniform decay across all late actual packets is RH-equivalent; finite truncations converge strongly even off RH; strictly concave positive log-sine quantile profiles satisfy every shifted conductance-Hankel inequality yet have nonreal transform zeros [L].
- **(a) Just work.** None.
- **(b) Open, B-RH.** Source-derived transverse-energy decay uniform in packet rank, independent of the zero divisor; strong convergence of each fixed packet does not give it.
- **Walls** 7, 12, 15. **Refuted shortcuts:** symmetrizing/positive-kernel substitutes; bare conductance-Hankel selector.

### OWU — Odd Weil-weight uniqueness

- **Receiver.** Actual `Λ` odd Weil positivity, or an odd-positive arithmetic weight with all-scale dilation-ray sign → RH [L]. On odd compact tests `W(g) = M_N(g) − sinhPairing(g)²/2`, so odd positivity is the capacity inequality `sinhPairing² ≤ 2M_N` [L].
- **Established.** Odd-positive minorants `λ ≤ Λ` and ray-positive weights are rigidly `Λ`; odd blind fibres, dual attainment and the arithmetic-corrected ground operator exist at every aperture, with every blind minimizer an eigenvector. The coherent price `log 2` is sharp and attained; the finite-filter Schur gain is strict; the plastic infimum on a fixed-fold class is `−2·fiberMoment²`; no scalar bounds odd source energy by coherent price [L]. For `0 < a ≤ (log 2)/2` no finite `θ` absorbs cosh mass by sinh potential on all smooth compact even multipliers; canonical odd primitive differences have both polar moments zero and complete energy `O((n+1)^{−2})` [L]. The Schur ratio pays finite collar sums by half-line jumps plus a support budget independent of the prime cutoff; the full continuum passage retains integrability premises and a budget not matched to the fixed archimedean coefficient.
- **(a) Just work.** None.
- **(b) Open, B-RH.** Odd positivity for actual `Λ`: payment of the complete reflected-prime and cosh-pole terms for arbitrary apertures and odd tests, including negative `sinh` moment; the diagonal potential left by low-prime collar duality and the unpaid `θ·sourcePair`.
- **Walls** 11–15. **Refuted shortcuts:** fixed-coefficient cosh-by-sinh absorption; uniform folded-cell residual; coherent price as universal control; fixed-fold nonnegative plastic cone; finite-filter Schur equality; odd blindness inherited by the hyperbolic multiplier.

### PBM — Regularized prime / log-ζ abscissa

- **Receiver.** RH iff `Σ_{n≥2}(1_ℙ(n) − 1/log n) n^{−σ}` or `Σ_{n≥2}((Λ(n)−1)/log n) n^{−σ}` converges at every real `σ > 1/2` [L].
- **Established.** The raw prime series diverge at every `Re s < 1` (KR-RAW); the regularized diagonal shift operators have Calkin gap `1/2`; the gap-weighted prime series `Σ_k (p_{k+1} − p_k) p_k^{−s}` continues to `Re s > 71/100` as `1/(s−1) + G(s)` [L].
- **(a) Just work.** None; monodromy belongs to DR.
- **(b) Open, B-RH.** Critical-abscissa cancellation of the fixed regularized coefficients at every `σ > 1/2`; alternatively a prime-gap second-moment exponent `θ ≤ 1/2` together with zero-freeness. Regularization is not cancellation.
- **Walls** 1, 6, 10. **Refuted shortcuts:** raw positive prime Dirichlet series (KR-RAW).

### RB — Robin/Nicolas divisor-sum criterion

- **Receiver.** Eventual Robin or Nicolas inequality → RH; equivalence proved, and Robin on all integers is equivalent to Robin on colossally abundant integers [L].
- **Established.** With `N = ⌊log n⌋` and the moving valuation defect `D(n,N) = Σ_{p≤N} p^{−(v_p(n)+1)}`, `σ(n)/n ≤ e^γ log log n · exp((1+ε)/log log n − D)` eventually; every large Robin counterexample has `D ≤ (1+ε)/log log n` and is divisible by every `m ≤ η log log n` [L]. Fixed `k`-free and positive exponent-defect classes satisfy partial margins.
- **(a) Just work.** None; finite ranges can be certified and leave the criterion open.
- **(b) Open, B-RH.** The sign on increasingly prime-saturated extremal integers at square-root remainder scale; the converse runs through a one-sided bound on `ψ(x) − x` at exponent `1/2` (Wall 1). Leading Mertens asymptotics do not determine the critical remainder.
- **Walls** 1, 9, 11.

### SRT — Prime-side two-bump localization

- **Receiver.** For any bump width `w > 0` and lag threshold `V`, RH iff the Weil form is nonnegative on every difference two-bump test `κ_γ(t + v/2) − κ_γ(t − v/2)`, `γ ∈ ℝ`, `v ≥ V` (ζ has no real zeros) [L]. For `0 < w < log 2/2` each test reads `Λ(n)` only on the dyadic window `|log n − v| ≤ 2w ⊂ (X/2, 2X)`, `X = e^v`; in the polar-free class, RH iff for every height and every late lag the dyadic-window prime sum is at most the archimedean term [L].
- **Established.** An off-line zero of depth `> σ` drives the window functional below `−K e^{σv}` in windows beyond every `X₀`; the negativity rate equals the maximal depth; every off-line zero of a tempered configuration is visible at some aperture, and the all-aperture form determines the configuration [L]. The prime symbol has the sharp horizon `μ + P_X ≥ (log(1+|τ|/4) − C − (4+ε)√X)/2π`, so localized forms at height `T` are positive once `√X ≤ (¼ − ε) log T`; no coefficient below `2` is height-uniform. Positivity holds on every test of aperture `≤ 1/100`. In synthetic configurations finite-aperture positivity coexists with off-line lattices, clusters and dilute sublattices, crystallization can restore positivity after adding off-line zeros, and only uniform-depth crystals remain invisible up to the square-root threshold [L]. The windowed Gram is diagonal for `2rX ≤ 1`; beyond that the off-diagonal is a near-frequency pair sum, and the pair-correlation exchange at bandwidth above `1` is a conditional identity. Finite prime polynomials attain both ends of their `ℓ¹` envelope along Kronecker heights; under RH a large prime excursion occurs only at an exponentially large height, paid by the archimedean term [L].
- **(a) Just work.** (a3) Pushing the unconditional aperture `1/100` toward Yoshida's constant; the horizon coefficient `4` is already optimal.
- **(b) Open, B-RH.** The complete same-height inequality, prime window at most pole plus archimedean term, for every centre `γ` and every late lag, from actual `Λ`: a bound on one dyadic prime window at one height at square-root precision at every height. This is Wall 1 (precision) joined to Wall 7 (every height, not almost every). Beyond the square-root threshold the off-diagonal prime pairs at bandwidth `λ = log X/log T > 1` are the parity problem, and the density hypothesis gives `λ ≤ 1` exactly. Open problem 2, visibility of a non-attained top level at a controlled lag at ζ-density, is the every-height question in zero-side form.
- **Walls** 1, 3, 7, 13. **Refuted shortcuts:** small-aperture, windowed or fixed-profile eventual positivity as exclusion; frozen-height pole comparison; sub-`2√X` symbol floor; dilute periodic spectra; monotone visibility under adding zeros.

### ACT — Arithmetic criticality / single-shift variation

- **Receiver.** Fix any `a > 0`. RH iff `markovEnergy(Φ ω_a u) ≥ 0` for every even compact `C²` profile `u` (profiles vanishing near `0` suffice), iff the pole-free variation inequality `D_a(u) ≤ 2S_a(u) + V_a(u)`, iff the ground remainder dominates the reflected defect [L]. Equivalent cone form: RH iff `Lévy_arch(v) + Lévy_prime(v) + 2(∫Φv e^{x/2})(∫Φv e^{−x/2}) ≥ ∫Φ cosh(x/2) v²` for every nonnegative compact `C²` profile `v`, with no signed term; the factor `1 + ε` on the potential fails [L].
- **Established.** Every nonnegative profile is a strict folded subsolution near the origin (the folded source there is `−2∫M dm`, a jump-measure moment) and on a half line (the source at infinity is `−2∫₀^∞ M cosh(r/2)`, a pole moment); sign-changing profiles with negative cosh moment are supersolutions at infinity; the collar/source ratio `R(a) > 2` tends to `2` [L]. In every smeared gauge RH is the pure jump form `J_M(u) + V_μ(u) ≥ 0` with conductances `M(x)M(y)(dm(|x−y|) + sinh(x/2)sinh(y/2))`; the negative conductances are confined to the prime anti-diagonals `|x| + y = log n` and the axes near the origin [L]. The form admits no Hardy weight on the odd sector or primitive hyperplane, every prime rate is minimal, the variance is indispensable, the capacity ratio tends to `1` [L]. Shift averaging gives the inequality under RH; its converse is not proved. A plateau gauge gives `Ẑ(F) ≥ (3/40)∫F²` for supports in `[−r, r]`, `r < e^{−2}/2` [S]. The finite Allegretto–Piepenbrink equivalence holds on connected finite kernels [L].
- **(a) Just work.** (a1) The plateau-gauge module [S]. (a2) Proving or refuting the RH converse of the shift-averaged inequality (whether averaging enlarges the radical). (a3) The exact window radius of the plateau mechanism and the rate at which the capacity ratio approaches `1`.
- **(b) Open, B-RH.** The single-shift inequality at one `a > 0` for all even compact profiles; in jump-form coordinates, a prime-side inequality paying each anti-diagonal atom `Λ(n)n^{−1/2}` at `|x| + y = log n` by same-side atoms at `|x − y| = log m` and by the variance, with no slack to lose. The smallest instance is extending a gauge argument through the first prime window past `log 2/2`, where the first conductances turn negative. **B-C:** a supersolution built from arithmetic; by the two-moment law it cannot be nonnegative, and any folded one must have `∫M dm ≤ 0` and `∫₀^∞ M cosh ≤ 0`.
- **Walls** 11, 12, 13, 15. **Refuted shortcuts:** pointwise folded supersolutions (single shift, finite signed superpositions, theta convolutions, any nonnegative profile); coercive Hardy-weight shortcuts; the monotone-cone weight criterion; short-window positivity as selection.

## 3. Route candidates

Candidate status means the source, the decisive estimate or the source-to-receiver landing is unconstructed. A zero-indexed construction is legitimate once its decisive premise is proved independently; what cannot be assumed is the zero property the construction is meant to produce.

### APF — Arithmetic paired Fredholm
- **Established.** Fredholm index and actual cycle-trace Fourier reconstruction [L].
- **(a)** None; finite trace algebra on a specified admissible subspace is bounded work and the full CHMD resolvent is not compact (infinite threshold eigenspace).
- **(b) B-C.** A zero-independent exhaustion with vanishing of all trace coefficients; the reconstructed coefficients already carry the off-line terms. Walls 12, 14, 15.

### BSH — Arithmetic mate curvature
- **Established.** Framed curvature/compact-ideal diagnostics distinguish fibres by the radial character `n^{2Re s − 1}`; finite cutoffs are trace-blind [L].
- **(a)** None.
- **(b) B-C.** A pre-divisor arithmetic section and mate identity coupling `s` to `Ξ(s) = 0` without setting the radial character to zero. Walls 12, 15.

### BVI — Bézout–valuation incidence
- **Established.** Pronic positivity of the Vasyunin prime kernel, two-sided cotangent reciprocity, the Vasyunin formula for the discrete Gram; the Báez–Duarte bridge `(1 − Λ-readout)² + energy-centred pronic Gram` with floor `κ/log N`; sharp finite cones (two-moment, two-lag, primitive-energy); exact observability horizons and phase-recovery orders; the renormalized defect nonpositive at every prefix for large horizons, uniformly over damping `0 ≤ ε ≤ 1`; fixed-`ε` compensated `O_ε(1)` remainders; the whole obligation sits in the Bézout interior martingale with required small-damping slope `≥ 7/24`; the complete 25-entry Vaughan Gram; damping laws and non-commuting limits; classical bridges (Type-II dictionary, Vinogradov–Korobov window rates, short-interval mean squares, log-free large sieve) [L].
- **(a)** (a1) The literal-μ readout floor and the small-damping rate modules [S]. (a2) The Type-II rewrite of the interior bracket. (a3) Whether the renormalized defect sign holds at every horizon `N ≥ 2` and the least long-window threshold (universal-weight statements, no RH content).
- **(b) B-RH.** The complete log-renormalized signed remainder at arbitrarily small fixed `ε`: the four named tools, each missing, are cross-depth cancellation uniform in the cutoff, Bézout coupling at high scale controlling the signed complement of all other lags, an internal bilinear dispersion estimate on `Σ a_p b_q 𝒢^{ec}(p,q)` using `p̄ mod q` without an external character average, and a coercive contraction `2M^{int}_T + 2·Counterterm·H^{comp}_T ≤ (1−δ)E_T + C_ε`. **B-C:** a direct BVI-to-CHMD sign transfer. Walls 1, 7, 10, 11. **Refuted shortcuts:** direct `Λ` readout (`Λ(k(k+1)) = 0`); universal two-moment or two-lag improvement; raw-defect sublinear bounds; unit-response envelope beyond `5N+4`; dropped signed complement; automatic interior centring; nonsummable log majorant; squarefree Hölder exponent above `1/3`.

### CDC — Constitutive dagger
- **Established.** Calibrated confluence holds at `s` iff `Re s = 1/2`; logistic relative entropy bounds the exchange defect; total exchange work tends to `1/8` along deep diffusive grades [L].
- **(a)** None.
- **(b) B-C.** One pre-divisor potential descending on all closed error fibres and coupling `s` to `Ξ(s) = 0` without assuming the critical character. Walls 12, 15.

### DR — Dyadic Xi roots
- **Established.** Common zero-free cusp roots, finite monodromy/Kummer data, capped atlas; naive smooth prime-germ and positive-root producers fail; finite-quotient monodromy does not give the full group; `Ξ` has no entire left factor with finitely many critical values [L].
- **(a)** None.
- **(b) B-C / B-RH.** Global continuation and a common compatible root on the strict-right domain; or source convergence of the regularized log-ζ series (PBM's target). Walls 1, 4, 6, 15.

### EGC — Pole-safe contour
- **Established.** Admissible cofinal rectangles enclose both poles and any finite zero packet; after mass subtraction the inner contour equals the exterior-copy tail uniformly, without RH; on the source ray the pole/Gamma-subtracted remainder keeps every `Λ` coefficient and tends to its prime-2 coefficient; the complete correction has the Gamma floor `(m+1)·correction → −ε²/2` [L].
- **(a)** (a3) The explicit remainder at a specified cutoff.
- **(b) B-C.** The outer expanding-contour covariance or sign excluding off-line copies; inner cancellation and the centred prime-2 sign are nonselective. Walls 1, 10, 15.

### EWJ — Euler/Wold jets
- **Established.** Exact finite-depth jets and compact-quotient character; fixed-history recovery misses transverse operator gaps [L].
- **(a)** None.
- **(b) B-C.** Zero-independent admission and norm exhaustion at unbounded depth, then an RH landing. Walls 7, 14, 15.

### FEL — Theta likelihood
- **Established.** Exact probability, conditional KL and adaptive reveal accounting; the Balazard–Saias–Yor identity as a convergent zero sum [L].
- **(a)** None.
- **(b) B-C.** A source-derived cofinal zero-to-contrast balance selecting the line; accounting describes either outcome. Walls 7, 12, 15.

### HJ — Hurwitz reflection
- **Established.** The two-seed residual `2^{ρ−2} − 2^{−ρ̄−1}` depends on prime `2` only and vanishes iff `Re ρ = 1/2`; all-divisor vanishing is equivalent to HCF's two-grid signs; the original witness is FE-odd, an involutive isometry moves it to an FE-even vector with the same negative energy, and eventual nonnegativity of the zero-indexed even witnesses is RH-equivalent [L].
- **(a)** None.
- **(b) B-C / B-RH.** A pre-divisor source that makes the residual vanish or the even witness nonnegative at actual zeros; HCF's grid sign is the equivalent open target. Walls 4, 12, 15.

### IRK — Rotation-algebra trace
- **Established.** Finite-word traces, local winding, quotient-ideal diagnostics; the completed Xi-jet relation is invertible exactly off the line with logarithmic trace equal to boundary winding; the pre-completion relation has nonzero cokernel at every zero, not identified with the Poisson source [L].
- **(a)** None.
- **(b) B-C.** A global arithmetic Poisson/projective lift with integral analytic count and the correct source defect. Walls 5, 12, 14, 15.

### MSC — Möbius−Sonin transport
- **Established.** The full squarefree discrepancy gives an unconditional critical logarithmic `L²` source; strict-right evaluation columns pair to the actual discrepancy moment; real-power rigging and polynomial/LP transports move or lose the divisor [L].
- **(a)** None.
- **(b) B-C.** A source-faithful bridge from this Hilbert observation to a nonnegative Sonin/Weil energy retaining the complete signed source. Walls 1, 12, 13.

### PCS — Singular co-shift
- **Established.** Explicit wall ground; finite-prime co-shift projections converge strongly with norm and ideal gaps retained; the native prime shift is non-surjective and the co-shift non-injective while chronological dilation is invertible, so no isometric or injective intertwiner identifies the carriers [L].
- **(a)** None.
- **(b) B-C.** Source-natural wall-class annihilation preserving the forward mode and the nonzero shift defect. Walls 7, 14, 15.

### PTR — Photonic source
- **Established.** Finite lossless stacks are real-rooted; RH iff `Ξ` is a locally uniform limit of lossless stack products, but the proved converse inserts the unknown zeros into the impedances; the continuum Poisson port stays at operator norm and Calkin distance `1` from the identity at every positive depth gap; local, shift-average and analytic cosine ports fail; positive Poisson ports lose real zeros on two-tone sources [L].
- **(a)** None.
- **(b) B-C.** A prime-faithful nonlocal continuum port preserving the exact divisor before the divisor is inserted, or an independent zero-loss theorem across the unit Calkin gap. Walls 5, 12–15.

### RFHM — Support grade
- **Established.** Exact survival/KL/entropy accounting; reversible sewing is inverse-covariant; the synchronized Gamma–theta source is admitted over every finite prime support and unbounded Mellin grade, with forward creation covariance [L].
- **(a)** None.
- **(b) B-C.** A source-defined non-inverse-covariant phase/depth/compound law orienting the wall. Walls 7, 12, 15.

### SC — Stokes/Witt−Krein
- **Established.** Rigged fibres are chamber-constant; Fourier reconstruction has a common null set; canonical polarization is wall-singular; big-Witt ghosts have exact Selberg-coordinate realization [L].
- **(a)** None.
- **(b) B-C.** A source-fixed cross-fibre indefinite restriction or index selecting the critical wall. Walls 12, 14, 15.

### SEC — Adjacent prime seam
- **Established.** Essential norm equals the seam jump; compact-ideal cost vanishes at `ρ` iff `Re ρ = 1/2`; asymptotic smallness across large primes is automatic; at Meixner time `θ = 1` factorial-Fock jet boundedness at every `ρ` in the divisor support is RH-equivalent [L].
- **(a)** None.
- **(b) B-C / B-RH.** Pre-divisor eventual compactness or jet boundedness at actual zeros without divisor indexing. Walls 4, 12, 14, 15.

### W1C — Clifford–Dirac / centred Lee–Yang
- **Established.** The bare operator lacks point spectrum and compact resolvent; Lee–Yang holds on finite ferromagnetic graphs and an Ising magnetization limit `Ξ/Ξ(0)` would imply RH; constant normalization never converges, ferromagnetic inequalities do not imply Lee–Yang, balanced prime trees and harmonic chains fail, unitary Euler factors have modulus one, Hermitian pencils cannot match a local Euler factor at nonreal points [L].
- **(a)** None.
- **(b) B-C.** Source-defined couplings with a centred slow-field law converging to Riemann's measure, or a faithful arithmetic scattering denominator; interaction-driven critical edge density is required. Walls 5, 12–15.

### WBF — Source certificates
- **Established.** Abstract genealogy Gram/determinant theorems on bounded scalar streams, with finite-prefix versus completed Calkin gaps; no primes, `ζ` or `Ξ` appear [L].
- **(a)** None; the arithmetic stream is not yet defined.
- **(b) B-C.** An arithmetic certificate stream and a depth-uniform completion landing on `Ξ` or Weil positivity. Walls 6, 12, 14, 15.

### PM–PW-B — Physical cusp forcing (embedded candidate)
See the PM entry: pre-divisor source formulation, small-damping complete-energy ceiling, and the landing on the optical-magnitude/ordered-cap/all-divisor-extinction receiver. Walls 1, 7, 12–15.

## 4. The fifteen walls

| Wall | Statement | Routes it binds | Status and work |
|---|---|---|---|
| 1 Square-root barrier | A one-sided prime or Möbius bound at exponent `1/2` is RH; every power saving `x^θ`, `θ<1`, is a zero-free half-plane; unconditional savings are `exp(−c(log x)^{3/5})`. | WL, MC, PM, CTF, PBM, RB, FU, RP, LI, SRT, BVI, EGC, DR, MSC | All Lean [L]. No work item; the receivers are exact. |
| 2 Jensen gap | Square means and mollified moments bound `log` of a mean; the criterion needs the mean of `log|ζ|` (BSY equality, outerness). | PA, SZ, PM, CTF, BAG, FEL | [L]. |
| 3 Local clustering | A window of width `1/log γ₀` may hold `≍ log γ₀` zeros; Turán's loss beats every power gain; density counts strips, not windows. | LA, TH, HCF, XN, WD, JAS, SRT | [L]. |
| 4 Axis outside the zero set | Shifted, differenced, heat-flowed or `1 + λξ′/ξ` constructions are real-rooted exactly beyond the strip edge; the dominance parameter is the strip. | LA, TT, TH, HCF, XN, SZ, HJ, SEC, DR | [L]. |
| 5 No Frobenius, no `F₁` | No archimedean object has the primes as fixed points; analytic amplification returns the Landau abscissa; twins add no freedom. | HF, IRK, PTR, W1C, TG | [L]; the function-field purity statement `|ω| = √q` is not formalized. |
| 6 Probability cone | Euler-product positivity lives on `Re s > 1`; continuation into the strip is not positivity-preserving. | PA, JAS, PBM, DR, WBF | [L]. |
| 7 Almost-all versus all | Density-one, positive-proportion and typical-phase statements are separated from the pointwise statement exactly by the zeros to be excluded. | BAG, SRT, WL, MC, FU, TT, HCF, JAS, GTA, EWJ, FEL, PCS, RFHM | [L]. |
| 8 Infinitesimal admixture | The Weil cone is the point `Λ`; every direction out of it is RH-equivalent at any amplitude. | RW, EWU, OWU, HF | [L]. |
| 9 Temperedness gate | `ζ(s−a)ζ(s+a)` has Euler product, functional equation, growth and nonnegative coefficients, and off-line zeros; its poles are at `1 ± a`. | every positivity route; RB | [L]. Selectivity audits against this pair are routine (summary §2.1). |
| 10 Oscillation–transport | Power savings exist for oscillating sums; zero-sensitive sums do not oscillate; transport either keeps the poles (no saving) or adds a phase (no zeros). | WL, MC, FU, RP, LI, PBM, PM, CTF, RN, EGC | [L]. |
| 11 Node criticality | Prime-blind positivity on `S` is RH together with `S ⊇ {prime powers}`; deleting `log 4` makes it false; generic sampling arguments cannot work. | RW, HF, EWU, OWU, MC, BVI, RB | [L]. |
| 12 Forced dual measure | Every certificate of positivity is the critical-zero measure; near-null tests forbid margins; a positivity producer is a spectral realization. | RW, HF, CHMD, EWU, OWU, PA, TH, HCF, TG, WD, LI, SZ, ACT, all candidates | [L]. |
| 13 Cone mismatch | Pointwise cones (maximum principles, transfer operators) and the Bochner cone meet only on the window sector `|supp| ≤ log 2`; in the odd sector the minimizer is sign-changing. | RW, HF, EWU, OWU, CHMD, TT, RN, ACT, MSC | Mismatch witnesses [L]; the Mehler–Fock/Bochner–Godement dictionary that identifies the Bochner cone with positive-definite zonal functions is **[P]**: formalizing it is (a1) work. |
| 14 Size law | The primes are not a trace-class, finite-rank or finite-deficiency modification of the archimedean reference; `S ∉ L¹`; prime-power-factorized unitary scattering is block diagonal. | FU, RP, TG, RN, SZ, HF, CHMD, OWU, APF, EWJ, PCS, IRK, SC, SEC, PTR, W1C, WBF | Non-integrability [L]; the classical unboundedness of `S(T)` is **[P]** (excludes finite rank): formalizing it is (a1) work. |
| 15 Support versus positivity | Positive currents, positive-definite transforms and Schur products are orientation-blind; the oriented collision reading vanishes under exchange. | TT, WD, XN, TG, RN, HF, CHMD, OWU, ACT, BSH, CDC, HJ, IRK, FEL, RFHM, SC, SEC, PTR, W1C, EGC | [L]. |

The walls have different roles. Walls 1, 2, 11 and 12 are RH-strength targets in disguise. Walls 3, 4, 6, 7, 10 and 15 state what a class of evidence cannot do. Walls 5, 8, 9, 13 and 14 constrain the shape of any construction. None states that a proof must be nonlinear, singular, noncompact or of any particular architecture.
