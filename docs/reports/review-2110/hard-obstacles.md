# Hard mathematical obstacles on every RH route

Companions: [walls ledger](walls-ledger.md) (seventeen walls), [summary and the missing field](hard-obstacles-summary.md).

Sources: the [route ledger](../rh-current-frontier-map.md) (29 live routes, 19 standalone candidates, PM's PW-B sub-branch), the Lean corpus at checkpoint `9e90e2b19` with its working-tree additions, the seven programme READMEs (ACT, AIP, SRT, BVI, THIM, BiScale, APT) and their cards, the [proof-constraints brief](../STATUS.md) and the [retired-mechanism ledger](../rh-killed-routes.md). Evidence tags: [L] committed umbrella-imported Lean; [S] working-tree Lean (uncommitted file or umbrella import, or not umbrella-imported); [P] paper only. Module prefixes as in the walls ledger (`R:` RHTower, `B:` BiScaleUncertainty, `V:` BezoutValuationIncidence, `T:` TransHorizonIncidenceMechanics, `A:` arithmetic-positivity-theory, `C:` ArithmeticCriticalityTheory, `I:` ArithmeticIncidencePositivity, `Q:` SquareRootThreshold, `H:` HTGeometry).

## 1. Assessment

**No route has a remaining step that is routine.** Every live route ends in one unproved arithmetic statement that implies RH; every candidate ends in one unconstructed object whose construction would be such a statement. What the corpus owns on each route is exact: the receiver (an implication to RH, usually an equivalence), the complete expression of the quantity to be signed or bounded with every term retained, the positive pieces, the sharp boundary of every shortcut that has been tried, and small-parameter or restricted-family positivity that holds whether or not RH does.

Six ledger-wide facts fix what counts as "just work".

1. **No graded relaxation is easier than a zero-free half-plane.** A one-sided power bound `O(x^θ)` on a Chebyshev or Möbius quantity is `Θ ≤ θ` (`R:QuasiRHMeanSquareAbscissa`, `R:QuasiRHDilationCovarianceAbscissa` [L]); a horizon-uniform bound on the damped Möbius receiver at one fixed `ε ∈ (0, 1/2)` yields the zero-translation law (`pmPowerDamped_zero_translation` [L]). Below half damping the receiver is not decided by any sign-blind data (Wall 16), and no `ℓ²` Type-II input reaches it at one modulus (Wall 17).
2. **The positivity problem has no slack anywhere and its ground-energy path is known at both ends.** The full Weil cone is the point `Λ`; prime-blind positivity is node-critical with exact Euler-product deletion prices; the odd form admits no Hardy weight, every prime rate is minimal, the capacity ratio tends to `1`. The restricted ground energy `μ(A)` is `≥ 1/5000` for `A ≤ 3/10` [S], `≥ 1/1000` for `A ≤ 29/100` [L], tends to `0` doubly exponentially, and RH is `μ(A) → 0`, equivalently `μ(A) ≥ 0` at every aperture (Wall 12).
3. **The prime side of RH is one inequality per dyadic window, and its best unconditional floor is of de la Vallée Poussin strength.** For a generic width, RH iff `P_v ≥ 0` for all `v ≥ V`; unconditionally `P_v ≥ −|φ(0)| − C_w exp(v/2 − √v/10)`; the window ceiling is `e^{L/2}(1 + o(1))` and RH is the remainder `O(L)` (Wall 1).
4. **The odd sector of the Weil form is proved positive past the first prime; the even sector is not.** Odd tests: `Ẑ(F) ≥ (1/1000)∫F²` on `[−353/1000, 353/1000]` with the atom `Λ(2)/√2` paid from the archimedean strip surplus [L]. All tests: `Ẑ(F) ≥ (1/5000)∫F²` on `[−3/10, 3/10]` [S], short of the first prime at `log 2/2 ≈ 0.3466`, which is also the window of Connes–Consani's archimedean trace domination (closed in print by numerics). Both certificates are pointwise or Schur-averaged gauges and are window-bounded (Wall 13).
5. **A new mechanism must supply one of five things** (walls ledger): square-root cancellation of a prime sum at one modulus with the signs read; equality in Jensen for `log|ζ|`; a Frobenius-type fibration; a Bochner-cone certificate at arbitrary support compatible with node criticality; or a definite spectral realization whose prime part is as large as `S(T)` and whose finite-aperture ground transforms converge to `Ξ`. Any mechanism must fail for Beurling systems and for `ζ(s − a)ζ(s + a)`, survive one character and modulus one, carry information beyond polynomial length at square-root precision, and distinguish `log 4` from `log 6`.
6. **Normalization.** The gauge-free kernel of the odd jump form is `dm(|x − y|) + 2 sinh(x/2) sinh(y/2)` per unordered pair, forced by `Z = J_M + V_μ` with `V_μ` over ordered pairs; the ACT and AIP READMEs and every AIP sign statement use this kernel.

### Classification used in every entry

| Label | Meaning |
|---|---|
| **Established** | Proved, with its scope and tag. |
| **(a) Just work** | Finishable with known methods: **(a1)** Lean closure (commit or wire an [S] module, finish a docstring, repair a conflict); **(a2)** receiver bookkeeping (prove or refute a stated equivalence or identification with known tools); **(a3)** a finite calculation or constant the route itself names, including the next window radius of a certified gauge family. No (a) item supplies the missing sign or bound; "None" means no such item exists. |
| **(b) Open, B-RH** | An unproved statement that implies RH (equivalence stated only where proved). |
| **(b) Open, B-C** | An unconstructed object or transfer whose existence is itself a research question. |
| **Walls** | Numbers from the walls ledger. **Refuted shortcuts** retire a mechanism, not the route. |

## 2. Live routes

### WL — Weil lag function

- **Receiver.** Exact prime data → one-sided bound on the lag function, on prime lags, or on the integrated Chebyshev deficit → RH; `±∫₀ᵀ(eᵗ − ψ(eᵗ))dt ≤ Be^{T/2}` forces RH by Landau [L].
- **Established [L].** Both one-sided bounded-lag criteria are RH-equivalent; power-gap, prime-mesh, progression and thin-exception samplings transfer bounds. Packet laws: every nonzero compact `C²` source has prime-minus-polar packet values `> c` and `< −c` arbitrarily late; eventual one-sided boundedness of every packet is RH-equivalent; a one-sided bound at rate `e^{στ}` on one packet excludes every zero of depth `> σ` it sees; an explicit universal probe `U(u) = e^u(U₁^{*4})(u)` on `[−4, 4]` sees every zero and RH iff its packet is eventually bounded above; the band law `∫_T^L P_f² = O((1 + L)e^{2σL})` iff `f̂` vanishes at every zero deeper than `σ`; the universal probe's linear band is RH-equivalent; the multiplicity ceiling `E_crit(f) ≤ KW_crit(f)` iff all critical multiplicities `≤ K`; pairing-recurrence and translated-pairing envelopes (`B:PacketPersistenceLaw`, `B:PacketOneSidedGrowthLaw`, `B:UniversalProbeLaw`, `B:CubicSplineUniversalProbe`, `B:PacketBandLaw`, `B:MultiplicityCeilingLaw`, `B:TranslatedPairingEnvelopeLaw`). Energy identities: Plancherel `∫|𝓕f|²(1/4 + 4π²ξ²)S_N(ξ)dξ`, band `|ξ| ≤ √(N + 2)` versus full Laplace energy within `O(log(N + 2))`, dyadic renewal and Stirling producers, Halász-type large-value bounds; a linear band `∫₀^L Ẽ² = O(L)` is RH both ways, its slope bounds `Σm_ρ²/|ρ|²`, Cramér's mean square and the band liminf `≥` zero energy hold under RH. Unconditional Chebyshev and sawtooth errors carry Vinogradov–Korobov rates. HF's prime-window ceiling criterion `c(L) ≤ e^{L/2} + O(L)` lands in this deficit receiver (`B:PrimeWindowCeilingRHCriterion`).
- **(a) Just work.** None.
- **(b) Open, B-RH.** A source-derived one-sided bound at every positive exponential slack on the lag function, the deficit primitive or the universal spline packet; equivalently the linear band or the window remainder `O(L)`. Littlewood's `Ω±(√x log log log x)` forbids an `O(√x)` target and either eventual sign; any power saving is a zero-free half-plane. Wall 1 in its original form.
- **Walls** 1, 7, 10. **Refuted shortcuts:** packet convergence to zero; thin lag sampling without a top-depth premise; sub-`√x` Mertens cancellation; the positive high-dilation envelope.

### RW — Restricted Weil ground energy

- **Receiver.** Complete prime−Gamma−polar form → nonnegative constrained ground energy at every aperture → RH; equivalently the sinh-capacity bound at every level, vanishing all-aperture negative index, `μ(A) → 0`, or `μ₀ ≥ 0` at every aperture with no attainment premise [L].
- **Established.** Exact split `W = (Markov jump energy) + ½⟨cosh, g⟩² − ½⟨sinh, g⟩²` and the explicit archimedean functional on real compact `C²` tests [L]. The ground-energy profile of fact 2: floors through `21/200` (`1/30`), `29/200`, `39/200`, `6/25`, `13/50`, `7/25`, `29/100` (`1/1000`) [L] and `3/10` (`1/5000`) [S]; Suzuki's main term as the window floor; `μ₀ ≥ 1/20` through `(log 2 + 1/50)/2` and `μ₀(A) ≥ −(10 + 68e^A)` at every aperture; every contact aperture exceeds `29/100` [L] and `3/10` [S]; the Gaussian upper decay; `RH ⟺ μ(A) → 0` [L]. Grid receivers: on a nonresonant aperture grid RH iff `ZerosApproachLine` plus eventual boundedness below of sampled `μ`; continuous `μ₀` receivers need no zero-side premise [L]. Factorial-tent patterns of unrestricted scales are RH-complete; on each fixed pattern support high translates are coercive while the limiting critical prime channel is negative definite, so fixed-support positivity is nonselective [L]. Low/high multiscale bounds retain `−K_low E_low` [L]. Corrected-factorial, Müntz-repaired and ramp–tent families have eventually positive complete energy without RH [L]. No uniform primitive graph-norm gap and no uniform positive gap at unbounded aperture [L]. The constrained even-polar form has a self-adjoint ground operator with compact resolvent [L]; CCM's finite-stage theta–Sonin isomorphism, Hardy–Titchmarsh square, metaplectic oscillator identification and logarithmic Dirac determinant dichotomy are formalized [L]. Window positivity is selective against large shifts of `ζ(s − a)ζ(s + a)` [L].
- **(a) Just work.** (a1) Commit the ACT umbrella import of `C:ThreeTenthsSharpGaugeWeilPositivity`. (a3) Push the all-profile window from `3/10` to `log 2/2` with the hub–Schur certificate (the Connes–Consani window; the fold cost is confined to inner points `x < 0.0851` and the bulk potential is the binding term). (a2) Decide whether the RW/SZ/CHMD common-core equality extends to completed source norms.
- **(b) Open, B-RH.** `μ(A) ≥ 0` for every `A`: the path must not cross zero between the certified floor at `3/10` and its limit `0`. In every coordinate the unpaid term is the signed prime−polar pairing `ΣΛ(n)n^{−1/2}h(log n) − ∫2cosh(x/2)h`, a Chebyshev-error gauge [L]; past `log 2/2` the folded conductances across the first prime are negative on even tests, so the next regime is the even sector through the first prime window with the atom paid by the potential.
- **Walls** 8, 11, 12, 13. **Refuted shortcuts:** uniform primitive graph-norm gap; uniform ground gap at unbounded aperture; even-ground parity selection (KR-CCP); cofinal Markov ground-state positivity (KR-BD); pointwise positivity as Bochner positivity; restricted-family positivity as selection; nonnegative folded supersolutions.

### FU — CCM-FU signed prime scheduling

- **Receiver.** Signed Möbius/prime scheduling → completed Abel moment `A(M)/M` bounded above → RH; one-sided power bounds give `Θ ≤ 1/2 + max(0, c)` [L].
- **Established [L].** Prescribed prime blocks admit helper cores with positive Boolean energy differences; a prime-exhaustive history decreases complete clock energy at each cutoff; the closed positive clock cone contains every cutoff-fixed target and its negative; distinct deep terminal-prime clocks approximate any source-graph vector with vanishing diagonal cost, with strictly negative off-diagonal pairing for a resolvent eigenvector `μ > 1/2` (a conditional negative certificate); growing-cutoff packets with bounded norm and vanishing diagonal stay pairwise separated.
- **(a) Just work.** None.
- **(b) Open, B-RH.** A uniform upper bound on the completed Abel moment paying seed, inherited action, inter-block covariance and endpoint drift; the decisive premise is nonnegativity of the off-diagonal prime-clock interaction on low-diagonal approximants.
- **Walls** 1, 7, 10, 14, 16. **Refuted shortcuts:** bounded norm plus vanishing diagonal as compactness; coarse Selberg inputs; weighted Suzuki first-moment bound (false under RH).

### RP — Route-P / SP-E history floor

- **Receiver.** Literal matched-quantile prime history → eventual linear defect floor → RH [L].
- **Established [L].** Linear-floor equivalence, signed hyperbola, centroid and square-debt identities, low-LCM payment, exact Abel/RP tails; full signed Cayley tails have noncompact positive and negative parts; the native first clock jet is bounded, noncompact, strongly but not norm differentiable; Burnol damping shells tend strongly to zero while their trace tends to `log(c)/4`.
- **(a) Just work.** None.
- **(b) Open, B-RH.** The complete-history floor with centroid, square debt, high-LCM terms, moving core and singular-domain transport paid together; the cancellation is signed between full LCM fibres.
- **Walls** 1, 10, 14. **Refuted shortcuts:** shell trace-norm vanishing; absolute complete-fibre payment; causal mass compensation.

### PA — Prime–archimedean source passivity

- **Receiver.** Continued exact prime−archimedean trace → high-frequency passivity, a thin Bernstein mismatch envelope, or a signed compact moment completion → RH.
- **Established [L].** On `Re s > 1/2` the continued trace is the weighted WL lag-pole series plus an affine mass term; signed current multiplier positivity on all upper half-strip slices is RH-equivalent; thin exponential envelopes for the coupled-Sonin Bernstein mismatch imply RH with every Hausdorff premise discharged; for each fixed Hausdorff order the calibrated moment differences are nonnegative beyond an order-dependent shift, and any finite block of orders simultaneously, with no order-uniform threshold; a bounded-support signed-measure representation of all normalized moments is RH-equivalent; if RH fails the Bernstein index measures recover the maximal off-line packet (tomography, not exclusion); at the critical Stokes carrier every exact completion must raise infinitely many singleton masses; a positive quadratic saddle band carries half the absolute atom mass with its complement uncontrolled.
- **(a) Just work.** (a3) Finitely many shifts for finitely many orders; the orders are unbounded.
- **(b) Open, B-RH.** The arithmetic sign of the high-frequency current numerator, an order-uniform shift threshold, or the signed complement of the saddle band.
- **Walls** 2, 6, 12, 15. **Refuted shortcuts:** fixed finite passive realization (KR-FPR); ensemble change (KR-TK); termwise Nevanlinna sign (KR-NEV); passive deletion and finite atom repair.

### MC — Möbius cancellation at half power

- **Receiver.** Signed Möbius source → half-power cancellation, subpower energy, or a square-sampled Chebyshev bound → RH; a one-sided subpower bound on the Möbius–divisor quotient head at any cutoff `M^θ` is RH-equivalent; the cumulative square energy of the normalized Abel action has exact exponent `2Θ` [L]; the Liouville receiver at arbitrarily small damping implies RH [L].
- **Established [L].** Hilbert, Liouville, Riesz and square-source receivers; signed bilinear and divisor decompositions; the Vaughan dictionary and five-piece 25-entry Gram; all-horizon unsigned energy `≤ M·invSum(M)³`; VK window rates; Mertens `Ω±(√x)`; on a moving high-dilation cutoff the squared tail is diagonal plus signed covariance, the diagonal prefix `≤ 9N/25`, the covariance RH-equivalent, and the absolute envelope fails. BVI supplies every finite law of the trans-horizon source and the renormalized defect sign at every prefix for large horizons uniformly in damping, with threshold `10N² + 8N`; fixed-damping variance ceilings, non-commuting limits, second-order laws `V(ε) = ε/2 − ε² + o(ε²)`, `R(ε) = ε/2 + o(ε²)`; the Hardy–Littlewood singular series at every fixed lag. Cancellation boundary: finite linear centering cannot remove the Brownian Type-II loss; bounded partial sums give `Q_N(c) ≤ 11B² + 4Σc_n²/n`; the cross-scale Gram is two readouts plus a residue-sensitive Bernoulli term plus a cubic tail; universal dispersion fails on coherent blocks (Wall 17). Möbius and Liouville receivers are equivalent at every `ε`; critical-Wiener convolutions and sparse prime flips preserve boundedness; the receiver is not amplitude-decidable below half damping (Wall 16).
- **(a) Just work.** None; the Type-II rewrite of the interior remainder is done through the third-order cross-scale law and the dual norm [S].
- **(b) Open, B-RH.** The global signed bilinear bound at half-power scale: `M(x) = O_ε(x^{1/2+ε})`, equivalently the signed covariance at cutoff exponent `1/2`, equivalently the single-modulus low-frequency statistics of the Möbius row at `θ = 2` with the signs read.
- **Walls** 1, 7, 10, 11, 16, 17. **Refuted shortcuts:** positive high-dilation envelope; absolute squarefree contraction; periodized uniform-cycle budget; deformation-stable inequalities (KR-DEF); raw pronic energy (limit `1/2`) as a selector; amplitude-only classification.

### TT — Theta-tail and heat–Cassini currents

- **Receiver.** Theta source → directed signed covariance/Wold decay or odd Weil-form sign → RH.
- **Established [L].** Exact seam, tail and odd-four identities; Wold threshold `t < 1/2`; natural-cutoff energy criterion; odd/primitive half-line reflected-prime inequality and Φ-Doob form; translation averages are depth-blind; a periodic Kelvin-chirp profile cannot separate once `e^L > 4 + 2√2`; the enriched clock current is positive in the inner chamber at large action; the abstract Ruelle continuation has no identification with `ζ`.
- **(a) Just work.** (a3) Enlarging the inner-chamber region.
- **(b) Open, B-RH.** Signed nonlocal covariance or Wold decay, or full odd/primitive positivity across all rapidities and scales; the odd positivity is OWU's.
- **Walls** 4, 7, 13, 15. **Refuted shortcuts:** transverse equilibrium (KR-TEQ); pair-heat monotonicity (KR-CAL); translation averaging; compact-open Wold descent.

### LA — Line anchor

- **Receiver.** Literal theta source → all-height Laguerre/Hadamard or Jensen sign → real-rooted `Ξ` → RH; `RH ⟺ Re(ξ'/ξ) ≥ 0` on `Re s > 1/2`; heat-slice Taylor positivity at time `λ` iff `newmanConstant ≤ λ` [L].
- **Established [L].** `newmanConstant ≤ 1/8` and Newman's conjecture `newmanConstant ≥ 0` (`H_t` has a non-real zero at every `t < 0`), so RH is the equality `Λ = 0`; exact negative index of the slice coefficient operator; `S(T)` not integrable and unbounded; the BSY identity; theta moment source with positive normalized fluctuation moments, fixed-degree Jensen–Hermite limits, nonselective hyperbolicity in the saddle regime (KR-JPR); clusters persist under the heat flow.
- **(a) Just work.** None.
- **(b) Open, B-RH.** The all-height arithmetic sign with low-order slices and a separator for near-double off-line pairs; the needed de Bruijn–Newman direction is `Λ ≤ 0` against the unconditional `≤ 1/8`.
- **Walls** 3, 4. **Refuted shortcuts:** KR-JPR, KR-CAL, KR-TEQ; Laguerre–Pólya inverse filters; mass-calibrated score floors.

### TG — Topological sub-unit gate

- **Receiver.** Pre-divisor Euler/Gaussian source → positive-residual cubic transgression and integer trace `< 1` → RH.
- **Established [L].** Boundary winding and index identities; source-sensitive transgression; summable proper-prime-power nuclear assembly against a non-summable linear-prime trace; finite-scale and compactness gates do not orient the reflection-odd source.
- **(a) Just work.** (a3) The final integrality step once a nonnegative integer is shown `< 1`.
- **(b) Open, B-RH.** `E_base = E_residual + Tr T_D` with `E_residual ≥ 0` and the sub-unit trace on every disc, or the source central-gap bound at exponent zero. **B-C:** the source-to-divisor transgression.
- **Walls** 5, 12, 14, 15. **Refuted shortcuts:** anchored chiral-loss passage (KR-R1); discrete escape indicator (KR-DSA).

### HF — Positive Hodge form on arithmetic cohomology

- **Receiver.** Original arithmetic cohomology → positive Hodge-compatible form, or a full-positive weight → RH; equivalently prime-blind positivity (PBAP) [L]; alternate: the window ceiling `c(L) ≤ e^{L/2} + O(L)`, or the floor mirror, into WL's deficit receiver [L].
- **Established [L].** Full-positive weights are rigidly `Λ`; the Meyer quotient has Xi-jet synthesis, Hasse admission, Paugam pairing, compact inverse with determinant `Ξ`, trace-class flow and the complete prime−Gamma−polar trace; the zero-algebra form is circular; odd-sector Farkas, Riesz extensions and the secular counterterm hierarchy give coercivity up to `S/L ≤ 27`, while every nonzero smooth prime-blind even-polar test has `S/L > 27`. Node criticality and its prices (Wall 11): `ZeroPoleBlindPositiveOn N ↔ RH ∧ PP ⊆ N`; single, additive, tower, whole-tower and full-grid deletion prices; window ceilings `λ₂₃`, decoupling length `log 6`; the window ceiling `c(L) ~ e^{L/2}` with RH criterion, width law, Liouville mirror and twist invariance. Bounded-energy all-grid correlations can lose Lévy energy at the origin; the logarithmic modulus and inverse-linear blind tails are sharp; the Nyquist tail, divisor-energy completion, physical dilation and collar allocation theory are exact and archimedean.
- **(a) Just work.** (a1) Wire `B:PrimePowerDeletionPairThreshold`. (a3) Finite-grid collar constants; exact full-grid tower extrema.
- **(b) Open, B-RH.** PBAP on unrestricted prime-blind tests in the `S/L > 27` regime without the `sinh`-moment premise; or the window remainder at the RH-sufficient scale `O(L)`. **B-C:** a source-defined positive Hodge/cup/trace structure on the original cohomology with the correct trace and no simplicity premise; a faithful whole-quotient completion (the unregularized extension is obstructed).
- **Walls** 5, 11–15. **Refuted shortcuts:** zero-algebra invariant form; sparse-node positivity; `S/L ≤ 27` closure; finite global certificates; uniform strict relative gap; additive same-tower prices; window-independent Euler decoupling.

### CHMD — Causal Hyperbolic–Modular Duality

- **Receiver.** Exact Weil source → causal prime wave, Chebyshev-discrepancy derivative pairing `∫₀^∞ ∂_sK_y(s)Δ(s)ds` bounded above (or below), Möbius-rest one-sided bound, or odd bound-state space zero, or the complete odd archimedean-plus-prime-chain Poincaré inequality → RH [L].
- **Established [L].** The arithmetic resolvent has simple eigenvalue `1`; if off-line zeros are finite the bound-state dimensions are `(q, q + 1, 2q + 1)`; RH iff the odd bound-state space is finite-dimensional and `AsymptoticAbscissaLaw`; one-signed odd eigenstates above `1/2` vanish, sign-changing ones are not excluded; the signed radical is `ker(resolvent − ½)`, the polar-constrained quotient nondegenerate; cardinal projections span the primitive bound band; Beurling–Deny nodal contraction, five-term lobe balances, nodal-modulus identities (`RH ⟺ sourceEnergy(absGraph) ≥ 4·sourcePair(pos, neg)` on every odd eigenvector above `1/2`); fixed-coefficient cosh-by-sinh absorption fails on some compact even multiplier at every `0 < a ≤ log 2/2`; the Schur ratio pays finite collar sums by half-line jumps plus a support budget; finite Möbius folds stay uniformly separated from the completed wave; inserted off-line radial modes have nonnegative hyperbolic prime-chain excess (lower bounds, not exclusion); the signed-gauge quadratic law and the two-moment law of ACT apply.
- **(a) Just work.** None.
- **(b) Open, B-RH.** An actual-source inequality excluding sign-changing odd eigenstates with `μ > 1/2`: payment of the primitive `oneL` defect, a sign for the nodal cross-prime term, or the one-sided discrepancy-derivative bound, which is the Chebyshev deficit again.
- **Walls** 1, 12–15. **Refuted shortcuts:** one-signed exclusion as full proof; strict coercivity of the unrestricted quotient; finite folds as uniform approximants; fixed-coefficient absorption; off-line chain excess as exclusion.

### TH — Theta moment positivity

- **Receiver.** Exact theta/prime−Gamma moments → all-degree Hankel/Bezoutian positivity at one positive heat time → RH.
- **Established [L].** Moment and heat-current receivers; fixed-rank positivity is unconditional and rank-`N` tests are blind above height `O(N√log N)` (KR-HFR); the quartic Schur charge is the squared norm of a nonlinear feature, so no linear norm-square receiver exists on degree-one coordinates.
- **(a) Just work.** (a3) Specified finite moment matrices; the inner-chamber region.
- **(b) Open, B-RH.** Positivity at all degrees at one common heat time with the full discrete-prime remainder.
- **Walls** 3, 4, 12. **Refuted shortcuts:** fixed-rank completion (KR-HFR); heat transport as same-time positivity; linear quartic Hilbert receiver.

### RN — Theta renewal and singular comparison

- **Receiver.** Literal theta renewal/connection source → divisor-faithful winding or directed boundary-work sign → RH.
- **Established [L].** Global native Green solver, full-multiplicity Meyer packets, fixed-Gaussian realization; the causal renewal kernel is Hilbert–Schmidt and cone-positive with `det₂(zK) = exp(−dz)D(z)/D(0)`; every resonance is an eigenvalue of matching multiplicity; cone positivity does not confine complex resonances; the reduced theta-ratio slope has positive physical value but negative conjugate value, norm and trace; the Cauchy-pole quartet defect vanishes iff RH (zero-side); no continuous unregularized extension of finite native synthesis exists.
- **(a) Just work.** None.
- **(b) Open, B-RH.** The mixed prime+Gamma ≥ pole inequality with all cusp terms, seam/cusp gluing and the boundary-current orientation. **B-C:** a source-faithful native completion in a changed topology.
- **Walls** 10, 13–15. **Refuted shortcuts:** trace-ideal transport (KR-TRC); dyadic renewal winding (KR-R2); nuclear Ruelle zeta; positive reduced-slope norm.

### WD — Ward orientation and horizontal collision

- **Receiver.** Directed source current → global negative-cross control or collision charge `< 2` → RH; the nonnegative global cap vanishes iff RH [L].
- **Established [L].** Exact Ward and collision receivers, cap integrability, strict-right multiplicity readout; the oriented collision extension vanishes under exchange; the horizontal four-trace has a quadratic mixed-range gain that does not bound the cap; averaged Husimi positivity is Euler-blind (KR-HUS).
- **(a) Just work.** None.
- **(b) Open, B-RH.** Source-derived vanishing of the global cap or a complete signed prime−Gamma contraction with uniform owner/absorber bounds for every zero block.
- **Walls** 3, 12, 15. **Refuted shortcuts:** uniform free-orbit count (KR-UCF); holomorphic collision quantum (KR-R3); averaged Husimi positivity (KR-HUS).

### LI — Paired Li and prime–Gamma balances

- **Receiver.** Literal prime−Gamma history → signed lower floor → Li positivity → RH; RH iff an eventual finite lower bound on the literal primitive [L].
- **Established [L].** Exact paired histories and finite primitive receivers; closed-ideal operators classify RH-equivalent compactness; the actual clock series has `liminf|S| = 0`, both jet signs cofinally, negative low cumulants, no absolute exponential envelope, no convergent fixed-history truncation.
- **(a) Just work.** None.
- **(b) Open, B-RH.** `Re H_N ≥ K_N − C` on `0 < t ≤ c log(2N + 1)` with first-crossing and outside correlations retained.
- **Walls** 1, 10, 12. **Refuted shortcuts:** all-even Euler-jet positivity; absolute history domination; cumulant promotion.

### SZ — Suzuki screw and shifted-kernel limits

- **Receiver.** Complete signed boundary pairing → screw nonnegativity or shifted-`Ξ` confinement → RH.
- **Established [L].** Screw and shifted-`Ξ` receivers (shifted leakage criterion RH-equivalent); the arithmetic Hankel operator is compact self-adjoint at every positive shift; the two-leg Gamma source has exact graph closure and Cesàro admission; Cayley partial sums reconstruct the carrier a.e.; the quadratic-contact residual is `o(N)` with no power saving; finite-contact residuals and formation energy have exact `Θ` exponent laws; on the common compact core the screw quadratic equals the RW restricted form and the CHMD quotient energy, with completed norms unidentified; the primary Beta density has explicit mass and first variation.
- **(a) Just work.** (a2) The common-core equality on completed norms.
- **(b) Open, B-RH.** The source Wronskian law paying the moving infinite head and shell leakage, and a cusp-preserving passage to unshifted `Ξ` as the shift tends to zero.
- **Walls** 2, 4, 12, 14. **Refuted shortcuts:** termwise Nevanlinna sign (KR-NEV); cofinal Markov ground state (KR-BD); eventual one-sign flux.

### PM — Physical-model routes: FZZ-P (live), PW-B (candidate)

- **Receiver (FZZ-P).** Approximation of the dyadic Haar target by the alternating Nyman–Beurling generators in `L²(0, 1]` is RH-equivalent [L]; sufficient: `L²` admission of the power-damped Möbius source at dampings arbitrarily close to `0`, which follows from a horizon-uniform complete pronic energy bound at a cofinal sequence of dampings [L]; for the fixed cofactor row, the Báez-Duarte residual `(1 − energyMean)² + energyVariance` tending to zero along some `(ε, Q)` path [L].
- **Established [L].** Admission and horizon-uniform energies for every `ε ≥ 1/2` including the endpoint; the zero-translation law under admission at fixed `ε ≤ 1/2`; at each fixed `ε > 0` the renormalized defect is nonpositive, variance ceilings vanish with `ε`, compensated remainders are `O_ε(1)`, and the interior bracket tracks the energy within `O_ε(1)`; the five-piece Vaughan Gram with nonsummable logarithmic majorant below half damping; the active-pair drift unbounded at small `ε` with slope `≥ 1/24`, so only the log-renormalized complete energy can be bounded; singular series at every lag; witness germ rigidity, fold-free equivalence, exact first-octave cells, selected-trace inverse loss `(4/π²)(log₂N)²`, dyadic-antichain capacity classification. Parity barrier (Wall 16): for `0 < ε ≤ 1/2` receiver boundedness is not a function of the Ramanujan magnitudes, the Fermi squarefree source and its even flip agree in every translated moment and split the receiver, logarithmic moments are a complete invariant, finite and critical-Wiener kernels repair a positive drift only at the pole; Möbius and Liouville receivers are equivalent at every `ε`; bounded multiplicative weights matching a real character are bounded at every `ε`.
- **(a) Just work.** (a1) Wire `T:APoleOfOrderTwoNeedsAZeroOfOrderTwo`. Nothing else: the `ε = 1/2` endpoint and every fixed-`ε` bookkeeping statement are [L].
- **(b) Open, B-RH (FZZ-P).** Unconditional global Haar approximation; equivalently top-octave domination or the linear origin-mass bound for every witness; sufficient: the horizon-uniform log-renormalized complete pronic budget at arbitrarily small fixed `ε`, paying the active-pair drift, the conditional-head mean, the interior orbit means and the signed prime-clock complement. A bound at one fixed `ε ∈ (0, 1/2)` is not of lesser difficulty (zero-translation law), and by Wall 16 it must read the signs at prime moduli.
- **(b) Open, B-C (PW-B).** A pre-divisor source formulation removing the `XiZeroCopy` indexing; a small-damping complete-energy ceiling; the landing on the optical-magnitude, ordered-cap and all-divisor-extinction receiver. The Eisenstein value at `i` factors through `ζ` and `L(s, χ₋₄)`.
- **Walls** 1, 2, 7, 10, 16, 17. **Refuted shortcuts:** local `(δ, 1]` completeness as global approximation; damping monotonicity; raw positive-divisor cutoff; bounded uncentred active-pair payment; magnitude-only or all-translated-moment classification; automatic even-flip energy transfer; HB and its producer classes.

### JAS — Joint ancestry

- **Receiver.** Arithmetic prime-product Weil form → level-one positivity on sufficiently large-prime tests → RH; or square-shell Riesz sums → subpower bounds on the finite power window for every exponent → RH [L].
- **Established [L].** Level-one full-product and dyadic positivity, cosine-kernel and harmonic Euler positivity on large primes, PSD at infinity at every level `σ > 1` and torus-density nonnegativity are RH-equivalent without side conditions; the synchronized Gamma–theta source is admitted over all finite prime supports with forward creation covariance; the native form is nonnegative on finite prime sets of logarithmic budget `((log y)/(128·10⁸))^{3/2}/(log log y)⁴` while the receiver needs budget `y^{1/2}`.
- **(a) Just work.** (a3) The logarithmic budget constant.
- **(b) Open, B-RH.** The source sign at the power budget, all-amplitude damped-shell positivity, or the subpower Riesz bound on the moving window; typical phases are positive, exceptional vectors are the problem.
- **Walls** 3, 6, 7, 12. **Refuted shortcuts:** closed-flat unit-residue certificate; logarithmic budget as the power budget.

### CTF — Chronological tail and Báez-Duarte approximation

- **Receiver.** Bounded chronological rows or finite Báez-Duarte dilates → vanishing `L²` error → RH; `d_N → 0 ⟺ RH`; bounded rows with vanishing error `⟺` RH [L].
- **Established [L].** The exact Vasyunin Gram; the residual identity `(1 − Λ-readout)² + energy-centred pronic Gram` with floor `κ/log N` and the uncertainty principle `κ·readout² ≤ (log N − κ)·energy`; for `−μ_N` the readout tends to `1` and the centred energy has floor `κ/(4 log N)`; bounded vanishing-error rows must carry the Möbius coefficients; every coefficient budget `exp(ε^{−θ})`, `θ ≤ 2`, fails if RH fails; rows retaining literal `μ` through `N/2` have Selberg diagonal `≥ 1/2359296`; Selberg-row period covariances tend to the singular series minus one.
- **(a) Just work.** None.
- **(b) Open, B-RH.** Rows whose centred pronic energy tends to zero; whether rows attain residual `O(1/log N)` is a quantitative form of RH; the signed LCM/Bézout boundary defect needs a uniform cofinal bound, which is Wall 17's single-modulus statistic with Wall 16's signs.
- **Walls** 1, 2, 7, 10, 16, 17. **Refuted shortcuts:** vanishing Selberg diagonal with a literal prefix; sub-logarithmic `ker P` diagonal; uncorrected Dirichlet mollifiers (ratio `≥ 49/48`).

### HCF — Gaussian heat trace / critical feature variance

- **Receiver.** Exact arch−prime heat trace → one-sided vertical growth or all-degree positivity on two prime-log grids after polar cancellation → RH; two-grid Hankel positivity with spacings `log p`, `log r` is RH-equivalent, `(2, 3)` suffices; RH iff `EventualFilteredCentralGapSubexponential` and `AsymptoticAbscissaLaw` [L].
- **Established [L].** Seven equivalent capstones at any fixed heat time; fixed-rank positivity unconditional; exact negative-index, Toda and escaping-branch laws for singular blocks; a conjugate packet inside the spectral parabola mimics a positive atom on one grid and on any finite family of same-step offsets; two marginal grids do not reconstruct four-atom packets.
- **(a) Just work.** None beyond fixed-rank evaluations.
- **(b) Open, B-RH.** Positivity of both literal grid forms at all polynomial degrees on their polar hyperplanes, or the one-sided vertical bound, or a cofinal entropy-deficit bound.
- **Walls** 3, 4, 7, 12. **Refuted shortcuts:** one-grid or finite-offset aliases; marginal reconstruction; fixed-rank completion (KR-HFR).

### XN — Xi Newton invariant discs

- **Receiver.** Xi first-jet source → line-centred Newton self-map discs covering every zero → RH; disc coverage with nonnegative interior margin is RH-equivalent [L].
- **Established [L].** Inside each disc `ΔQ = 4(r² − |z − c|²)|ξ''(z)|² ≥ 0`, so boundary positivity does not give interior positivity; entire scalar damping makes the Newton map holomorphic iff zero; polynomial pole repairs preserve jets but not self-mapping.
- **(a) Just work.** (a3) A specified finite disc and its Green potential.
- **(b) Open, B-RH.** An arithmetic construction of discs covering every zero with `Q ≥ 0` throughout, paying the interior curvature potential.
- **Walls** 3, 4, 15. **Refuted shortcuts:** global scalar damping.

### BAG — Deterministic zeta self-return

- **Receiver.** Source-derived fixed-base `ζ` recurrence on some closed disc about every `1/2 < Re z < 1` → RH; RH iff every right-half-strip point has a strongly recurrent closed disc, iff cutoff-uniform head-target density on some disc at every point [L].
- **Established [L].** Recurrence is closed on zero-free discs: every locally zero-free right-strip point has a recurrent closed neighbourhood with cutoff-uniform Dirichlet-head target approximation, through the Kronecker–Weyl limit law for phased finite Euler products, the Pechersky prime-vector approximation on Hardy discs, the exp/log bridge, the cutoff-uniform Euler-target density on zero-free discs and the disc-uniform Carlson tail (`R:ZetaDiscRecurrenceOnZeroFreeDiscs`, `R:UniformEulerTargetDensityOnZeroFreeDiscs`, `R:EulerProductDiscUniformCarlsonTail`). Targets with an interior zero are approximated by `ζ` only on density-zero height sets; head self-returns never pay the Abel pole; unadjusted centred tails retain the pole `M^{1−Re z}`; `ζ` is Besicovitch almost periodic on strip lines with Bohr–Fourier coefficients `n^{−σ}` at `log n`.
- **(a) Just work.** None; Voronin's third ingredient is in and the fixed-base equivalence is [L].
- **(b) Open, B-RH.** Recurrence at a point not known to be zero-free: by the local equivalences this is exactly "exclude a zero from the disc", and the route carries no intermediate estimate. Conditioning on a return event of density `κ` costs `1/κ` generically; typical translated-height recurrence is nonselective (Wall 7).
- **Walls** 2, 7. **Refuted shortcuts:** finite Euler recurrence (KR-BAG); independent phase transfer (KR-TOR); mollified Littlewood–Levinson (KR-LLM); unadjusted centred-tail returns; automatic head/tail overlap.

### EWU — Even pole-weight uniqueness

- **Receiver.** Actual even blind minimum nonnegative at every aperture → even positivity → `λ = Λ` → RH [L].
- **Established [L].** Blind minimizers exist at every aperture; the minimum is antitone, `≥ 1/20` for `a ≤ (log 2 + 1/50)/2`, nonnegative everywhere iff RH; node `4` is redundant in the dyadic blind grid but changes the second cosine coefficient, node `6` gives strict blindness gains with zero atom; every nonzero smooth prime-blind even-polar test has `S/L > 27`. The critical factorial family (APT): endpoint-collared and uncollared complete critical forms are positive on every sufficiently high dyadic block and on polynomial windows `[M, M^{1+δ}]`, doubly collared compact truncations keep it uniformly in the truncation, lacunary unions of blocks keep it, and for continuous Lipschitz compact critically filtered sources the energy is the literal full Weil functional; grid-tent approximants inherit a positive source margin; the limiting critical prime channel is negative definite and unrestricted factorial-tent patterns are RH-complete; the coefficient-size boundary separates `ζ` from the shifted pair. Low/high coupling bounds retain `−K_low E_low`.
- **(a) Just work.** (a3) Block threshold `M₀`, slopes and offsets; the range of the cell kernel `R`.
- **(b) Open, B-RH.** The nonnegative even blind minimum at every aperture, which on all even tests is the even sector of the Weil form past `3/10`. **B-C:** a passage from the critical family to the compact tests of the receiver with a margin surviving truncation and no `log M` gain; a multi-block Gram law or asymptotic orthogonality of critical sources on distinct blocks.
- **Walls** 8, 11–13. **Refuted shortcuts:** positivity of the limiting critical prime channel; sub-unit pole-weight periodization; prime-2 blindness as pointwise deficit; supercritical Nyquist residuals; correlation compactness as energy continuity; blind-symbol gain as atom payment.

### GTA — Transverse Schur charge

- **Receiver.** Actual theta-stage positive quartic Schur charge → rank-uniform transverse decay → RH [L].
- **Established [L].** Uniform decay across all late packets is RH-equivalent; finite truncations converge strongly off RH; symmetrizing substitutes do not force decay.
- **(a) Just work.** None.
- **(b) Open, B-RH.** Source-derived rank-uniform transverse-energy decay independent of the divisor.
- **Walls** 7, 12, 15. **Refuted shortcuts:** positive-kernel substitutes; bare conductance-Hankel selector.

### OWU — Odd Weil-weight uniqueness

- **Receiver.** Actual `Λ` odd Weil positivity, or an odd-positive arithmetic weight with all-scale dilation-ray sign → RH [L]; on odd compact tests `W(g) = M_N(g) − sinhPairing(g)²/2`, so odd positivity is the capacity inequality `sinhPairing² ≤ 2M_N` [L].
- **Established [L].** Odd-positive minorants and ray-positive weights are rigidly `Λ`; odd blind fibres, dual attainment and the arithmetic-corrected ground operator exist at every aperture; the coherent price `log 2` is sharp; the finite-filter Schur gain is strict; no scalar bounds odd source energy by coherent price; no finite `θ` absorbs cosh mass by sinh potential on all compact even multipliers below `log 2/2`; canonical odd primitive differences have complete energy `O((n + 1)^{−2})`. The odd window (AIP): `Ẑ(F) ≥ (1/40)∫F²` on `[−7/25, 7/25]` by the folded plateau, `(1/100)` on `[−17/50, 17/50]` by the curved fold, `(1/100)` through `347/1000` and `(1/200)` through `7/20` past the first prime with the atom paid on the strip, `(1/1000)` through `353/1000` with the strip shared by the sharp micro-fold; the micro-fold pays every prime-power shift separately within `log n/2 < r ≤ log n/2 + 1/12` with Harnack constant `λ ≈ 1.88`; the crossing kernel `ω(s) − 2sinh(a/2)sinh((s − a)/2)` has threshold in `(log 5, log 6)`, adverse lattice pairs `{2,2}, {2,3}` and, with atoms, `{2,4}, {3,3}`, nine wholly adverse anti-diagonals `{2,3,4,5,7,8,9,11,13}`, off-collar polar payment and two unpaid axis intervals for `n ≥ 23`. Shifted-pair selectivity at radius `13/125` and past the plastic threshold.
- **(a) Just work.** (a3) The odd window from `353/1000` toward the structural inner-edge limit near `0.355` (the `356/1000` numerator is certified without a capstone) and the archimedean odd ceiling near `0.375`; the collar ratio second-order term; the quarter-point range `14 ≤ n ≤ 22`.
- **(b) Open, B-RH.** Odd positivity for actual `Λ` at arbitrary aperture: the summed prime−polar cross terms on crossing pairs between lattice points, the shared strip surplus across overlapping prime windows, the axial collars, and the negative `sinh` moment; the diagonal potential left by low-prime collar duality and the unpaid `θ·sourcePair`.
- **Walls** 11–15. **Refuted shortcuts:** fixed-coefficient absorption; uniform folded-cell residual; coherent price as universal control; pairwise nonnegative crossing conductance; nonnegative folded supersolutions.

### PBM — Regularized prime / log-ζ abscissa

- **Receiver.** RH iff `Σ_{n≥2}(1_ℙ(n) − 1/log n)n^{−σ}` or `Σ_{n≥2}((Λ(n) − 1)/log n)n^{−σ}` converges at every real `σ > 1/2` [L].
- **Established [L].** Raw prime series diverge at every `Re s < 1`; the regularized shift operators have Calkin gap `1/2`; the gap-weighted prime series continues to `Re s > 71/100` as `1/(s − 1) + G(s)`.
- **(a) Just work.** None.
- **(b) Open, B-RH.** Critical-abscissa cancellation of the fixed regularized coefficients, or a prime-gap second-moment exponent `θ ≤ 1/2` with zero-freeness.
- **Walls** 1, 6, 10. **Refuted shortcuts:** raw positive prime Dirichlet series (KR-RAW).

### RB — Robin/Nicolas divisor-sum criterion

- **Receiver.** Eventual Robin or Nicolas inequality → RH; equivalence proved, and Robin on all integers iff on colossally abundant integers [L].
- **Established [L].** With `N = ⌊log n⌋` and the moving valuation defect `D(n, N)`, `σ(n)/n ≤ e^γ log log n·exp((1 + ε)/log log n − D)` eventually; every large counterexample has `D ≤ (1 + ε)/log log n` and is divisible by every `m ≤ η log log n`; `k`-free and positive exponent-defect classes satisfy partial margins.
- **(a) Just work.** None.
- **(b) Open, B-RH.** The sign on prime-saturated extremal integers at square-root remainder scale; the converse runs through a one-sided bound on `ψ(x) − x` at exponent `1/2`.
- **Walls** 1, 9, 11.

### SRT — Prime-side one-parameter lag localization

- **Receiver (minimal).** For one generic width `0 < w < log 2/2`, RH iff `P_v ≥ 0` for every `v ≥ V`; each test reads `Λ` on one dyadic window `(X/2, 2X)`, `X = e^v` [L]. Alternate: pole-free windows (line-or-poles), all difference two-bump tests, the height-localized `Re Π_f(ξ) ≤ Re A_f(ξ)` (full Weil positivity in localized coordinates), and the grid form needing `ZerosApproachLine` [L].
- **Established [L].** Unconditional envelope `P_v ≥ −|φ(0)| − (W + S₂)e^{v/2−√v/10}` for `v ≥ V₀`; pole-free floor `−2B₂(10 + 68e^A)`; ground-energy bridge `Re P_{w,v} ≥ 2B_w μ(v/2 + w)`, hence `Re P ≥ B_w/15` below `21/200` and the corresponding floors through `3/10` [S]; the negativity rate equals the maximal depth; lag-form values determine the configuration. Visibility: record-potential laws for finite lag windows and grids, Fejér and Fejér-power windows with cubic and order-`k` potentials, lag positivity forces close companions, hiding needs loud twins, twin radius at the uncertainty scale `73(κ_w + π log log(180(Γ + 6)) + 4π)/V`, attained tops visible at a lag logarithmic in the separation, twins exponentially tight unless tripled, near-top clusters collapse beyond the threshold, near-top zeros hide only in collapsed clusters, gap-free near-top visibility below an explicit height for the modulated family and polylogarithmic lag `V_w(γ₀, δ₀) ≍ (log γ₀)² log log γ₀/δ₀`; for the problem's own family `P_v`, near-top zeros are visible at explicit lag `V₀(w, η, δ₀)` with no height condition and no attainment, loud records are visible at `V(a, σ) ≍ log²(1/a)·log log(1/a)/σ`, and the horizon law replaces attainment by a condition on zeros beyond the horizon. Grids lose unattained tops; crystals and rotated patterns have threshold-exact first negative lags; finite-aperture positivity coexists with off-line models; the prime symbol floor coefficient `2` and horizon coefficient `4` are sharp; window incidence inside one lag window is doublings, triplings and consecutive `2`/`3` powers.
- **(a) Just work.** (a1) Complete and wire `Q:OneParameterLagFamilyWideNearTopZone`. (a3) Push the unconditional aperture `1/100` toward Yoshida's constant; explicit constants in `V₀` and the record lag.
- **(b) Open, B-RH.** `P_v ≥ 0` for all `v ≥ V` with an explicit `V`: a one-sided bound at exponent zero on the smoothed `√X`-normalized prime window at every scale, the ordinary-lag floor standing at `−O_w(exp(v/2 − √v/10))`. The visibility laws turn a hypothetical off-line zero into a negative lag depending on its depth `δ₀` and transform amplitude `η`; they cannot bound `P_v` from below because `V₀ → ∞` as `δ₀ → 0`, and the zeros beyond every finite horizon are uncontrolled. In the height-localized receiver the obligation is the off-diagonal prime pairs at bandwidth `λ > 1`, the parity problem, with the density hypothesis giving `λ ≤ 1` exactly.
- **Walls** 1, 3, 7, 13. **Refuted shortcuts:** small-aperture, windowed or fixed-profile eventual positivity as exclusion; frozen-height comparison; sub-`2√X` symbol floor; dilute periodic spectra; crystallization masking; grid signs as continuum signs; eventual bounded `S(T)`.

### ACT — Arithmetic criticality / single-shift variation

- **Receiver.** Fix any `a > 0`. RH iff `markovEnergy(Φω_a u) ≥ 0` for every even compact `C²` profile (origin-vanishing profiles suffice), iff `D_a(u) ≤ 2S_a(u) + V_a(u)`, iff the ground remainder dominates the reflected defect; cone form: RH iff `Lévy_arch(v) + Lévy_prime(v) + 2(∫Φve^{x/2})(∫Φve^{−x/2}) ≥ ∫Φcosh(x/2)v²` for every nonnegative compact profile, the factor `1 + ε` failing; global form: RH iff `μ(A) → 0`; in every smeared gauge RH is the pure jump form `J_M(u) + V_μ(u) ≥ 0` with conductances `M(x)M(y)(dm(|x − y|) + 2sinh(x/2)sinh(y/2))` per unordered pair [L].
- **Established.** The ground-energy profile and the window certificates of Wall 12: plateau gauge `(3/40)` below `e^{−2}/2`, pole conductance `(1/30)` on `[−21/200, 21/200]`, Markov window past the plastic threshold, quadratic and quartic curved gauges, the parity fold with the free even fold ending at `log ρ ≈ 0.2812`, the fold cost past `log ρ` as a function of the outer point, the sharp Lévy moments `u ω = ½ + u/4 − u²/48 − u³/32 + O(u⁴)` and the two-point fold cost with gain `36x²`, reaching `Ẑ(F) ≥ (1/1000)∫F²` on `[−29/100, 29/100]` [L] and `(1/5000)∫F²` on `[−3/10, 3/10]` [S]; hub energy (a Poincaré inequality for the folded jump form) and the Schur step [S]. Short-profile and mean-zero variation: `D_a + (1/30)‖Φω_a u‖² ≤ 2S_a + V_a` on `[−21/200, 21/200]`; smooth even `μ_a`-mean-zero profiles with margins `1/10` through `log 2/2` and `1/20` through `(log 2 + 1/50)/2`; all-aperture mean-zero bound with loss `(4 + ε)e^A` [L]. Two-moment law: no nonnegative folded supersolution, one extra jump repairs infinity iff `e^{−2a} + e^{−2ℓ} < 1` and never the origin, signed superpositions and theta convolutions fail at infinity; the signed-gauge quadratic law with conditional endpoint signs and exact origin jump-moment cancellation [L]. Criticality: no Hardy weight, minimal prime rates, capacity ratio `→ 1`, no uniform variance floor; shift averaging gives the inequality under RH with converse unproved; far-apart two bumps and wide plateaus are positive; the finite Allegretto–Piepenbrink equivalence [L]. Selectivity: even tests of the shifted pair are negative at every radius for large `a` [L].
- **(a) Just work.** (a1) Commit the umbrella import of the three `3/10` modules. (a2) Prove or refute the RH converse of the shift-averaged inequality. (a3) The all-profile window from `3/10` to `log 2/2` by hub–Schur certificates with bulk dips allowed; the rate at which the capacity ratio approaches `1`.
- **(b) Open, B-RH.** The single-shift inequality at one `a > 0` for all even compact profiles of arbitrary support; in jump-form coordinates a prime-side inequality paying each anti-diagonal atom `Λ(n)n^{−1/2}` by same-side atoms and the variance with no slack. The smallest open instance is the even sector through the first prime window, where the conductances across `log 2` turn negative and the atom must be paid by the potential; the odd sector is already past it. **B-C:** a sign-changing folded supersolution with `∫M dm ≤ 0` and `∫₀^∞M cosh ≤ 0`, or a non-pointwise certificate (Schur or Ritz) at arbitrary support; a Harnack inequality for the arithmetic jump kernel across prime shifts, which the sharp micro-fold supplies only within one twelfth past each `log n/2`.
- **Walls** 11, 12, 13, 15. **Refuted shortcuts:** nonnegative pointwise supersolutions of every stated class; coercive Hardy-weight shortcuts; the monotone-cone weight criterion; short-window positivity as selection; uniform ground gap at unbounded aperture.

## 3. Route candidates

Candidate status means the source, the decisive estimate or the source-to-receiver landing is unconstructed. A zero-indexed construction is legitimate once its decisive premise is proved independently; what cannot be assumed is the zero property the construction is meant to produce.

### AIP — Arithmetic incidence positivity
- **Path.** Integer-log prime incidence and archimedean crossing classification → source-valid compensation of the full continuum odd Weil form → OWU/ACT positivity → RH.
- **Established [L].** Prime skeleton: the same-side ratio atom dominates the crossing product atom, `ab` a prime power forces one tower, the finite skeleton is a nonnegative graph Laplacian; dyadic-window incidence. Archimedean kernel `ω(|x − y|) + 2sinh(x/2)sinh(y/2)`, crossing symbol `cosh(s/2) − ω(s)` with threshold in `(log 5, log 6)`, axis collars `< 3e^{−3s/4}`, reflected pair negative iff `a = 2`; adverse lattice pairs `{2,2}, {2,3}`, with atoms `{2,4}, {3,3}`; anti-diagonal classification (`{2,3,4,5,7}` atom-dominated, `{2,…,13}` wholly adverse, first paid modulus `6`, first paid prime `17`), collar sandwich `[2e^{−s}, (256/239)2e^{−s}]`, unpaid axis intervals with inner end `2(n²/(n²−1) + Λ(n))/(n − 1)` for `n ≥ 23`, integrated collar law (atom mass exceeds polar mass at the five moduli for every shifted profile). Odd windows: folded plateau `7/25`, curved fold `17/50`, past the first prime `347/1000` and `7/20` (atom-free strip), sharp micro-fold Harnack at every prime-power shift, second-order surplus kernel and antiderivative, strip-shared window `353/1000`. Selectivity against the shifted pair at `13/125` and past the plastic threshold. [S]: the Schur-absorbed ground state (potential lent from a hub to its inner edge) and the numerator certificate at `356/1000`, both committed files not yet umbrella-imported.
- **(a) Just work.** (a1) Wire `I:SchurAbsorbedGroundState` and `I:SchurFoldWindowNumeratorBounds`. (a3) The `356/1000` capstone from the certified numerator if the inner-edge budget closes; the collar ratio second-order term; the quarter-point set in `14 ≤ n ≤ 22`; the bump bridge normalizing the prime part of `J_M` by the width.
- **(b) Open, B-RH.** Pairs between lattice points: bound the anti-diagonal atom on a crossing pair that is not a lattice pair by the reachable same-side atoms and the variance, for arbitrary compact odd tests; allocate shared strip surplus across overlapping prime windows without double counting; pay the axial collars. **B-C:** the integrated atom-versus-pole law for a given odd gauge beyond the five moduli; a direct AIP-to-OWU/ACT sign transfer; a ground-state representation for forms with negative conductances on an arithmetic set of pairs. Walls 11, 12, 13, 15.

### APF — Arithmetic paired Fredholm
- **Established [L].** Fredholm index and actual cycle-trace Fourier reconstruction.
- **(a)** None.
- **(b) B-C.** A zero-independent exhaustion with vanishing of all trace coefficients; the reconstructed coefficients already carry the off-line terms. Walls 12, 14, 15.

### BSH — Arithmetic mate curvature
- **Established [L].** Framed curvature and compact-ideal diagnostics distinguish fibres by the radial character `n^{2Re s−1}`; finite cutoffs are trace-blind.
- **(a)** None.
- **(b) B-C.** A pre-divisor section and mate identity coupling `s` to `Ξ(s) = 0` without setting the radial character to zero. Walls 12, 15.

### BVI — Bézout–valuation incidence
- **Established [L].** Pronic positivity of the Vasyunin prime kernel, cotangent reciprocity at all moduli, the reciprocity defect as residue-difference energy, nearby-modulus logarithmic defect, the Vasyunin Gram formula; the Báez-Duarte bridge with floor `κ/log N` and the `−μ_N` readout law; finite cones (two-moment, two-lag, primitive-energy, five sharp facets), observability horizons and phase recovery up to the half-period companion; the renormalized defect sign at every prefix uniformly in damping; `O_ε(1)` compensated remainders; the Bézout interior martingale carrying the whole obligation with required slope `≥ 7/24`; the Hardy–Littlewood pair and `k`-tuple singular series as limits; the damped Chebyshev tangent receiver; the cross-scale theory of Wall 17: Brownian floor, coherent-block no-go, exact rank-two law, large-sieve dispersion at `Q ≥ P^{5/3}` for arbitrary coefficients and for bounded rows, Bernoulli second- and third-order kernels with reciprocity and sign laws, Type-I gains to `4/3` and `3/2`, block-equidistribution and twisted-short-interval replacements proved sufficient, residue discrepancy as the exact loss, the sharp constant `π²/72`, parity blindness of the cross-scale Gram, discrete Gallagher window spectrum and numerator split. Dual norm reduction to single-modulus statistics [S].
- **(a)** (a1) Wire `V:DualNormOfTheCrossScaleFunctional`. (a3) Whether the defect sign holds at every horizon `N ≥ 2` below the explicit threshold; the least long-window threshold; the window sandwich constant; the factor two in the log-free large sieve; the Vasyunin error below `O(p + q)`.
- **(b) B-RH.** The complete log-renormalized signed remainder at arbitrarily small fixed `ε`, with drift, shared-start covariance, conditional means, signed prime-clock complement and endpoints; for the cofactor rows centred variance `→ 0` along `ε ↓ 0`, `Q → ∞`; for `−μ_N` centred pronic energy `→ 0`. In Wall 17's units: a bound on `Σ_p|Λ_p(c')|/p` for the actual Möbius or prime row at `θ = 2`, that is, cancellation of the low-frequency exponential sums `Σ_n (c'(n)/n²)e(an/p)` at one modulus, with the signs of Wall 16 read. **B-C:** a direct BVI-to-CHMD sign transfer. Walls 1, 7, 10, 11, 16, 17. **Refuted shortcuts:** universal dispersion after rank-two centering; any `ℓ²` Type-II class at `θ > 1`; separated-modulus negligible reciprocity defect; raw pronic energy as selector; Hölder exponent above `1/3`.

### CDC — Constitutive dagger
- **Established [L].** Calibrated confluence holds at `s` iff `Re s = 1/2`; logistic relative entropy bounds the exchange defect; total exchange work tends to `1/8` along deep diffusive grades.
- **(a)** None.
- **(b) B-C.** One pre-divisor potential descending on all closed error fibres and coupling `s` to `Ξ(s) = 0`. Walls 12, 15.

### DR — Dyadic Xi roots
- **Established [L].** Common zero-free cusp roots, finite monodromy and Kummer data, capped atlas; naive prime-germ and positive-root producers fail; `Ξ` has no entire left factor with finitely many critical values; the regularized log-ζ convergence is PBM's receiver.
- **(a)** None.
- **(b) B-C / B-RH.** Global continuation and a common compatible root on the strict-right domain, or source convergence of the regularized series. Walls 1, 4, 6, 15.

### EGC — Pole-safe contour
- **Established [L].** Admissible cofinal rectangles enclose both poles and any finite zero packet; after mass subtraction the inner contour equals the exterior-copy tail uniformly; the source-ray remainder keeps every `Λ` coefficient and tends to its prime-2 coefficient; the complete correction has the Gamma floor `(m + 1)·correction → −ε²/2`.
- **(a)** (a3) The explicit remainder at a specified cutoff.
- **(b) B-C.** The outer expanding-contour covariance or sign excluding off-line copies. Walls 1, 10, 15.

### EWJ — Euler/Wold jets
- **Established [L].** Exact finite-depth jets and compact-quotient character; fixed-history recovery misses transverse gaps.
- **(a)** None.
- **(b) B-C.** Zero-independent admission and norm exhaustion at unbounded depth. Walls 7, 14, 15.

### FEL — Theta likelihood
- **Established [L].** Exact probability, conditional KL and adaptive reveal accounting; the BSY identity as a convergent zero sum.
- **(a)** None.
- **(b) B-C.** A source-derived cofinal zero-to-contrast balance selecting the line. Walls 7, 12, 15.

### HJ — Hurwitz reflection
- **Established [L].** The two-seed residual `2^{ρ−2} − 2^{−ρ̄−1}` depends on the prime `2` only and vanishes iff `Re ρ = 1/2`; all-divisor vanishing is HCF's two-grid sign; the FE-odd witness moves isometrically to an FE-even vector of the same negative energy; Hurwitz prime-log clocks are ray-Rajchman.
- **(a)** None.
- **(b) B-C / B-RH.** A pre-divisor source making the residual vanish or the even witness nonnegative at actual zeros. Walls 4, 12, 15.

### IRK — Rotation-algebra trace
- **Established [L].** Finite-word traces, local winding, quotient-ideal diagnostics; the completed Xi-jet relation is invertible exactly off the line with logarithmic trace equal to boundary winding; the pre-completion cokernel at every zero is not the Poisson source.
- **(a)** None.
- **(b) B-C.** A global arithmetic Poisson/projective lift with integral count and correct source defect. Walls 5, 12, 14, 15.

### MSC — Möbius−Sonin transport
- **Established [L].** The full squarefree discrepancy gives an unconditional critical logarithmic `L²` source with strict-right evaluation columns; real-power rigging and polynomial or LP transports move or lose the divisor.
- **(a)** None.
- **(b) B-C.** A source-faithful bridge from this Hilbert observation to a nonnegative Sonin/Weil energy retaining the complete signed source. Walls 1, 12, 13.

### PCS — Singular co-shift
- **Established [L].** Explicit wall ground; finite-prime co-shift projections converge strongly with norm and ideal gaps retained; the native shift is non-surjective and the co-shift non-injective while chronological dilation is invertible, so no intertwiner identifies the carriers.
- **(a)** None.
- **(b) B-C.** Source-natural wall-class annihilation preserving the forward mode and the shift defect. Walls 7, 14, 15.

### PTR — Photonic source
- **Established [L].** Finite lossless stacks are real-rooted; RH iff `Ξ` is a locally uniform limit of lossless stack products, the proved converse inserting the zeros into the impedances; the continuum Poisson port stays at norm and Calkin distance `1` from the identity at every positive depth gap; local, shift-average and analytic cosine ports fail.
- **(a)** None.
- **(b) B-C.** A prime-faithful nonlocal continuum port preserving the exact divisor before the divisor is inserted, or an independent zero-loss theorem across the unit Calkin gap. Walls 5, 12–15.

### RFHM — Support grade
- **Established [L].** Exact survival, KL and entropy accounting; reversible sewing is inverse-covariant; the synchronized Gamma–theta source is admitted over every finite support with forward creation covariance.
- **(a)** None.
- **(b) B-C.** A source-defined non-inverse-covariant phase/depth/compound law orienting the wall. Walls 7, 12, 15.

### SC — Stokes/Witt−Krein
- **Established [L].** Rigged fibres are chamber-constant; Fourier reconstruction has a common null set; canonical polarization is wall-singular; big-Witt ghosts have exact Selberg-coordinate realization.
- **(a)** None.
- **(b) B-C.** A source-fixed cross-fibre indefinite restriction or index selecting the critical wall. Walls 12, 14, 15.

### SEC — Adjacent prime seam
- **Established [L].** Essential norm equals the seam jump; compact-ideal cost vanishes at `ρ` iff `Re ρ = 1/2`; large-prime smallness is automatic; at Meixner time `θ = 1` factorial-Fock jet boundedness at every divisor point is RH-equivalent.
- **(a)** None.
- **(b) B-C / B-RH.** Pre-divisor eventual compactness or jet boundedness at actual zeros without divisor indexing. Walls 4, 12, 14, 15.

### W1C — Clifford–Dirac / centred Lee–Yang
- **Established [L].** The bare operator lacks point spectrum and compact resolvent; Lee–Yang holds on finite ferromagnetic graphs and an Ising magnetization limit `Ξ/Ξ(0)` would imply RH; constant normalization never converges, balanced prime trees and harmonic chains fail, unitary Euler factors have modulus one, Hermitian pencils cannot match a local Euler factor at nonreal points.
- **(a)** None.
- **(b) B-C.** Source-defined couplings with a centred slow-field law converging to Riemann's measure, or a faithful arithmetic scattering denominator. Walls 5, 12–15.

### WBF — Source certificates
- **Established [L].** Abstract genealogy Gram and determinant theorems on bounded scalar streams; finite-prefix versus completed Calkin gaps; no primes, `ζ` or `Ξ` appear.
- **(a)** None; the arithmetic stream is undefined.
- **(b) B-C.** An arithmetic certificate stream and a depth-uniform completion landing on `Ξ` or Weil positivity. Walls 6, 12, 14, 15.

### PM–PW-B — Physical cusp forcing (embedded candidate)
See the PM entry. Walls 1, 7, 12–15.

## 4. The walls

The seventeen walls, their mechanisms, evidence and the open unit of each are in the [walls ledger](walls-ledger.md). Walls 1, 2, 11, 12, 16 and 17 are RH-strength targets in disguise; walls 3, 4, 6, 7, 10 and 15 state what a class of evidence cannot do; walls 5, 8, 9, 13 and 14 constrain the shape of any construction. None states that a proof must be nonlinear, singular, noncompact or of any particular architecture.
