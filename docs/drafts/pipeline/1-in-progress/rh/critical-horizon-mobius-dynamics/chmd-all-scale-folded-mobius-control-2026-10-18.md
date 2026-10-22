# All-scale control of the folded Möbius wave

- **ID:** CHMD-FOLD-ALL-SCALE-1810
- **Stage:** 1-in-progress
- **Execution:** PAUSED at user request after closing the started Lean work (2026-10-18).
- **Type:** CONJECTURE
- **Statement:** Derive an unconditional, rapidity-uniform one-sided bound on the complete folded Möbius transport from the actual arithmetic source.

## Exact target

In `RHTower.CHMDChebyshevTransport`, set

`F(y) = mobiusWaveConstant * mobiusWave y + (γ + 1) * mobiusTailPairing y + remainderFoldSeries y`.

Prove `∃ C : ℝ, ∀ y : ℝ, 0 ≤ y → F(y) ≤ C` (or its lower-bound counterpart), with no unproved arithmetic premise. The existing `riemannHypothesis_iff_mobius_pieces_bddAbove` and `_bddBelow` identify this target with RH; neither proves it.

## Plan and gates

1. [done for current candidates] Audit exact source, kernel, prior conjectures, and all-scale receivers using the local research search and actual Lean declarations.
2. [paused] Cancellation candidates and their unresolved proof obligations are recorded below; no further research is authorized by the closeout request.
3. [done for finite-fold spectral classification] Complete a dependency-closed paper proof before formalization; the all-scale arithmetic bound remains open.
4. [done for spectral classification and separation] Seven leaves compile; both final leaves pass direct `lake --old env lean` checks; five theorem axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella wiring and generated indexes updated. The failed-route card records that audit; the additional quantitative-tail audit is recorded below.
5. [paused; open] The requested all-scale arithmetic bound remains unproved. Resume only on a new user instruction.

## Constraints

- No numerical experiments, new axioms, assumed cancellation, full builds, or heartbeat increases.
- One foreground build at a time; reuse unchanged objects with Lake's `--old` option.
- Preserve concurrent work and the existing frontier map.
- Knowledge ledger: `logs/chmd-all-scale-folded-mobius-1810.md`; facts and failures only.
- `update_plan` is unavailable in this session; this checklist tracks the multi-step task.
- Serena's symbol operation rejects the ignored Lean path; use source reads and direct Lean checks for this subtree.

## Current mathematical boundary

For each fixed rapidity, the folded series converges absolutely with shift decay `exp(-(π-1/2)v)` and a rapidity-dependent constant. The available rapidity-uniform remainder bound is only `7 * laplacianBound * exp(-v/2)`. Neither estimate justifies a uniform sum over all Möbius scales. All three pieces and their cross-cancellation must remain visible.

## Proof status

**OPEN CORE:** independent all-scale arithmetic cancellation. No proof claimed.

## Corrected corpus baseline

Local research search and direct source inspection recover stronger existing producers than the first pass recorded:

- `MobiusDivisorPaidPrimeExhaustion`: unconditional exhaustive insertion with every prefix paid at its own proportional clock.
- `MobiusDivisorExhaustiveClockCheckpoints`: nested exhaustive cores, universal full logarithmic energy bound at geometric checkpoints, and fourth-root cutoff collars.
- `MobiusDivisorTerminalClockOrder`: complete terminal insertion orders bounded by the larger actual endpoint; the completed source square remains explicit.
- `MobiusDivisorGrowingDepthCurrentPayment`: unconditional logarithmic-size omitted-prime payment over the initial core.
- `MobiusDivisorWeightedCutoffDiagonal`: exact signed correlation and self-square in cutoff evolution.

Do not rebuild these producers or infer an all-scale bound from their incompatible cutoff/core quantifiers. The unresolved scheduling obligation is signed drift and earlier completed action across changing cutoffs. Generic summable-spectrum Bohr extraction is also already available in `HTGeometry/ExponentialSeriesFiberwise` and `SummableSpectrumScrewBohrCoefficients`; the finite-fold work below only applies that spectral distinction to this specific transport.

## Conjecture: uniform truncation versus atomic completion

**Candidate shortcut:** the finite sums converge uniformly for all nonnegative rapidities. This is stronger than boundedness of the completed sum.

**Proposed obstruction and positive survivor:** every finite linear combination of folds has zero temporal cosine coefficient at every positive frequency other than the explicit pole frequency `sqrt(7/4)`. If the completed wave is bounded, the existing receiver implies RH; its temporal cosine coefficients then recover positive masses at actual zeta-zero frequencies. Therefore finite folded sums cannot approximate the completed wave uniformly on the entire rapidity half-line. The positive result is the exact temporal spectral classification, not merely nonconvergence.

### Paper proof

Use `A_T(f,λ) = ∫₀¹ f(Tt) cos(λTt) dt`. Its operator norm on bounded functions on the forward half-line is at most one for `T≥0`. Product-to-sum and the sine primitive give `A_T(cos(a·),λ) → 1/2` for `a=λ>0`, and zero for distinct positive frequencies. For an integrable spectral density, dominated convergence permits integration of this limit.

The Klein–Gordon frequency is `sqrt(r²+2)`. Each frequency fibre contains at most two real points, hence has Lebesgue measure zero. The explicit Fourier formulas therefore give zero temporal coefficient for `K_y(v)`, its first two spatial derivatives, and their conjugated combination. Their existing uniform bounds permit the same conclusion for every fixed bounded spatial integral and for the exponentially dominated remainder fold.

The pole law rewrites the tail exactly as
`exp(-v) * [P(y) - poleShadow(y) - ∫₀ᵛ K_y(s) exp(s/2) ds]`.
Consequently the only temporal atom of one fold is the pole mode, with coefficient `(γ+1) exp(-v)` times the pole mode's coefficient. In particular every finite fold combination has zero coefficient at every positive `λ ≠ sqrt(7/4)`.

The complete fold has the exact source identity
`F(y) = K_y(0) - poleShadow(y) - chmdArchWave(y)/(2π) + chmdWave(y)`.
The first three terms have zero temporal cosine coefficients. Under RH the last is the absolutely summable cosine series over actual zero frequencies, with strictly positive weights. At any actual zero frequency its coefficient is half the total matching weight, hence positive. Its frequency is at least `sqrt(2)`, distinct from the pole frequency.

If the complete fold has no uniform bound, no uniformly bounded finite fold can uniformly approximate it. If it is bounded, RH follows and the preceding positive coefficient separates it from every finite fold combination by a fixed positive sup-norm distance. The source identifications and analytic exchanges are now checked in Lean.

**Current verdict:** UNIFORM APPROXIMATION SHORTCUT RETIRED; exact positive-frequency atom classification and unconditional uniform separation formalized. See [failed-route card](../../../5-failed/chmd-uniform-fold-approximation-2026-10-18.md) for the exact theorem, positive survivor, paper proof, prior-work audit, and verification limits. This does not refute uniform boundedness of partial sums or of the completed wave. A valid all-scale argument may allow spectral atoms to emerge in a nonuniform limit.

## Next arithmetic candidate: bounded supported Möbius rows

The existing `selbergMobiusCoeff N m` is supported on `1 ≤ m ≤ N`, has absolute value at most one, and tends to `μ(m)` at every fixed index. Test the precise claim

`∃ C : ℝ, ∀ N ≥ 2, ∀ y ≥ 0, |Σ_{m=1}^N selbergMobiusCoeff N m * mobiusFold y (log m)| ≤ C`.

Fixed-rapidity absolute summability makes pointwise passage to the complete fold available. The missing work is the bound itself. Uniform approximation is neither needed nor compatible with the proposed atom classification. Existing Selberg total-energy estimates retain a growing diagonal/remainder; bounded coefficients alone do not pay them. Do not formalize the easy pointwise-limit receiver as an arithmetic advance. First attack the actual signed spectral density or source pairing of these already-defined rows, with pole and all-scale tail retained.

## Existing one-sided source target recovered across routes

The corpus already contains a sharper sufficient signed comparison than an absolute bound on the neutral quadratic work. `ChebyshevDeficitPrimitiveOneSidedRH.lean` proves RH from either envelope `±D(T) ≤ B(1+T) exp(T/2)` for every `T ≥ 0`. The TG audit in `tg-native-covariance-transfer-2026-10-15.md` already checked its application to the short work and the neutral decomposition in Lean. This is recovered existing work, not a new receiver to formalize.

For the literal neutral coefficient vector, retain the exact `D(T) = L(T) - Q(T)`. The sufficient arithmetic comparison is

`∃ B : ℝ, ∀ T ≥ 0, Q(T) ≥ L(T) - B(1+T) exp(T/2)`

(or `Q(T) ≤ L(T) + B(1+T) exp(T/2)`). It includes every unequal-label term and retains the actual linear work. Its existing quadratic-polynomial envelope cannot be silently replaced by a linear envelope. The comparison remains unproved.

The same prior audit records why coefficient-tail redesign and an assumed variational minimum do not pay this comparison. The head-extension action is stationary, but its complete Hessian is signed. Paid linear and diagonal channels do not control the complete quadratic form. Preserve those prior failures when attacking this specific source estimate.

## Applicability attack: terminal cancellation versus all-scale transfer

Candidate mechanism: use the exact child-cofactor cancellations from the Euler-deletion route to control the complete wave. The corpus already proves terminal composite-level vanishing and a high-clock leakage bound `N²/(clock(l)+1)` for arbitrary coefficients of absolute value at most one. Neither fact alone estimates the earlier simultaneous signed tails.

A stronger indexing check is required before using any terminal child theorem: `historyLayer_predictableDrift_eq_reverse_tail` sums only over `l < i < N`. At `N=l+1`, this is empty, so the entire terminal drift layer vanishes at every level, including prime levels. Paper proof: apply the existing reverse-tail identity and use the empty index condition. A scratch `lake --old env lean` applicability audit passed; its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`. This is a consequence of existing work, not a new arithmetic cancellation theorem.

The nonempty target must retain `N > l+1`. For the separate geometric-checkpoint attempt, clock energy only samples cofactors disjoint from the processed core. The existing terminal classification `mobiusDivisorFiniteClockEnergy_terminal` leaves the current head square and omitted-prime singleton squares. Old processed cofactors are absent, so those coordinates cannot directly recover earlier completed cutoffs.

The Euler-deletion corpus already localizes the complete drift to `logClockSourceProjection`, with a bounded martingale and error at most `110/(N+1)` in squared norm. It also gives a cofinal polylogarithmic receiver at the two-logarithm clock. These preserve one complete signed paired-source quotient; they do not bound it. Importing only terminal vanishing or high-clock leakage would discard that exact surviving field.

## Next source question: spatial wave energy

Investigate the actual translated field `H(y,v) = exp(v/2) Σ_m μ(m) mobiusFold y (v + log m)` on `v ≥ 0`. The conjugated kernel suggests `H_yy = H_vv - 2H`. If the needed derivatives and integrals are admitted, its half-line energy has boundary work `-H_y(y,0) H_v(y,0)`. No passive boundary condition or uniform energy estimate has been established. The CHMD energy search recovered the existing local origin maximum, Doob energy localization, nodal identities, and spectral receivers; none of these statements supplies that boundary-work estimate. A uniform energy argument also needs scrutiny against the completed wave's temporal atoms.

## Source multiplier candidate, with prior-work and arithmetic gates

Write `α = γ+1`, `β = log(2π)/2`, `R = ccmPrimeDeficitDilationRemainder`, and

`B(q) = α - β + α/(q-1) + q² ∫₀∞ R(u) exp(-qu) du`, for `Re q > 0`, `q ≠ 1`.

For finite real coefficients supported on positive integers, put `A_a(q)=Σ a_m m^(-q)` and `h_a=Σ a_m/m`. The candidate exact combined spectral formula is

`Σ a_m Φ_y(v+log m) = α exp(-v) h_a P(y)`

`  + exp(-v/2)/π ∫ℝ cos(y sqrt(r²+2)) sech²(r/2) Re(exp(irv) B(1/2-ir) A_a(1/2-ir)) dr`.

Here `P(y)=2 cos(y sqrt(7/4))/cos²(1/4)`. This is a paper derivation, not a Lean-verified new theorem. It retains the pole, constant, and remainder before taking an absolute value. Its derivation uses the existing fold decomposition: split the pole-density tail as its full integral minus the interval `(-∞,v]`; Fourier integration of that latter interval gives `exp((1/2+ir)v)/(1/2+ir)`. The remainder contributes `q²∫R exp(-qu)`. The bound `|R|≤7/2`, exponential decay of `sech²`, and polynomial size of `q²` admit the two Fourier exchanges for each finite row.

The causal-ramp identity in `CCMPrimeDeficitResidualPairing` gives, on `Re q>1`, the paper identity `B(q)=ζ'(q)+q ζ(q)/(q-1)` by termwise Laplace integration. Any use of this identity on the critical line still requires analytic continuation to be established; it is not assumed here. Related existing work is `LSeries_selbergWeightedVonMangoldt`, which identifies the completion's `-M_w ζ'` Dirichlet series, and the finite Weil-symbol representation. The precise CHMD formula above has not been kernel checked.

For `a_m = selbergMobiusCoeff N m`, the explicit pole coefficient is already paid by existing arithmetic. Source proof: use `selbergMobiusCoeff_eq`, factor out `1/log N`, and apply `Sieve.abs_sum_moebius_log_div_le`. Thus

`|h_a| ≤ (5+|γ|)/log N` for `N≥2`.

This is an applicability consequence of existing work. A scratch `lake --old env lean` audit passed; the derived coefficient theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. No new repository wrapper is needed.

One stronger candidate is a uniform bound on `∫ max(-d_N(r),0) dr`, where

`d_N(r) = sech²(r/2) Re(B(1/2-ir) A_N(1/2-ir))/π`.

Why this would suffice: the formula at `y=0`, fixed-rapidity absolute convergence, and the paid pole coefficient bound the signed mass `∫d_N` uniformly. The identity `∫|d_N| = ∫d_N + 2∫max(-d_N,0)` would then give a uniform cosine-transform bound and allow the already admitted pointwise Selberg-row limit. **The negative-mass estimate is unproved.** Do not replace it by pointwise nonnegativity: finite Selberg completions already fail full-cone Weil positivity, with exact rough-integer law `Λ_w(n)=w(1) log n` as the known positive survivor. That exclusion concerns its stated Weil completion, not every folded-wave density.

## Weaker cutoff target and quantitative light-cone tail

The existing `chmdWave_growth_law` and `chmdPrimeWave_growth_law` receive every exponential rate `0 ≤ a < 1/2`. Bounds for all positive rates force every frequency displacement to vanish. Hence a subpower-in-cutoff bound on suitable finite rows can suffice; a cutoff-independent spectral total variation is stronger than needed.

The taper must preserve its head for a quantitative transfer. A linear Selberg row changes every head coefficient by `log m / log N`; fixed-rapidity convergence alone gives no useful moving-cutoff rate. The existing `ChronologicalSelbergTaperEnergy` already expresses the plateau taper as a difference of logarithmic cutoffs. At outer cutoff `N²`, the row `2*selbergMobiusCoeff (N²) - selbergMobiusCoeff N` equals `μ` through `N`, has coefficient magnitude at most one, and vanishes above `N²`. This is existing taper structure, not a new arithmetic producer.

**Dependency-closed paper proof of the analytic tail estimate:** let `P(y)=(1+|y|)(1+y²) exp(π|y|)`. The existing odd Bessel integral gives `|J₁(x)| ≤ |x|/2`: dominate its integrand by `|x| sin² θ` and use `∫₀^(π/2) sin² θ dθ = π/4`. With `besselJ_one_eq` and the value at zero this proves `|lightConeBesselReal(w)| ≤ 1` for `w≥0`. For a spatial kernel bounded by `C(1+|s|) exp(-π|s|)`, the existing `shift_decay_le` bounds either shift inside the light cone by `C(1+|y|) exp(π|y|) exp(-(π-1)|s|)`. Its pair-minus-Bessel-tail therefore has modulus at most `2 C P(y) exp(-(π-1)|s|)`. Apply this to `dAlembertReal`, `dAlembertDeriv`, and `dAlembertDeriv2`, whose spatial bounds are already proved. Their conjugated combination is bounded by `D P(y) exp(-(π-1/2)s)` for `s≥0`, with `D` independent of `y,s`. The existing source bound and the integral calculation in `exists_abs_mobiusFold_le` then give

`∃ C≥0, ∀ y, ∀ v≥0, |mobiusFold y v| ≤ C P(y) exp(-(π-1/2)v)`.

This proof uses the actual source and has no arithmetic cancellation premise. The strengthened rapidity dependence and the complete absolute series-tail estimate are now formalized in `CHMDLightConeFoldTailBound.lean`. The earlier decay proof selects a constant containing `exp(y²/2)`; its quantifiers alone do not establish the displayed estimate. The existing `CHMDLightConeBesselZeroAndIntegrationByParts` already removes that Gaussian cost for the cumulative prime channel, and `BesselJOneRecurrence` already proves the amplitude estimate for its separate integral definition of `J₁`. The new proof identifies the two Bessel definitions and reuses that estimate.

The exact `Sieve.tsum_tail_rpow_neg_le` estimate was already in the corpus. Reusing it proves `∃ C≥0, ∀ y, ∀ N≥1, Σ' j |Φ_y(log(j+N+1))| ≤ C P(y) N^(-(π-3/2))`. The following transfer remains a paper argument: the absolute tail bounds a plateau-row error; for `y≥0`, choose `N=ceil(2 exp(3y))`. Then `2 exp(3y)≤N≤3 exp(3y)`, and the error is bounded by a constant times `(1+y)(1+y²) exp((9/2-2π)y)`, which is bounded since `π>3`. Thus the weaker arithmetic conjecture is

`∀ ε>0, ∃ Cε, ∀ N≥2, ∀ y≥0, |Σ selbergMobiusCoeff N m * mobiusFold y (log m)| ≤ Cε N^ε`.

For the plateau row, this gives `2|S_(N²)(y)|+|S_N(y)|≤3 Cε N^(2ε)`, hence a constant times `exp(6εy)` at that cutoff. The existing source identity differs from `chmdWave` only by uniformly bounded terms. Since `ε` is arbitrary, the existing growth law would force every frequency displacement to vanish. The combined-density negative-mass bound with the same subpower allowance is sufficient for the finite-row conjecture. **Both arithmetic estimates remain open.** The analytic tail estimate and the moving-cutoff transfer are not proofs of either estimate.

The new leaf passes a direct `lake --old env lean` source audit and a separate scratch import/axiom audit. All five public theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`. Its umbrella import appears once; indexes are refreshed and lexical corpus search locates the tail theorem. Global lint reports three unrelated errors in concurrent BVI wiring and package-root placement. Exact statements, commands, and limits: [quantitative-tail card](../../../3-formalized/chmd-quantitative-fold-tail-2026-10-18.md). The requested uniform all-scale bound remains open.

The current CHMD frontier also includes the support-radius collar bridge: `log d+R≤a`, `a≥3R+δ+L`, a support-dependent `supportArchBudget`, and explicit continuum integrability conditions. It does not provide a constant fitting the fixed archimedean coefficient of the complete source form. Preserve these conditions in any cross-route transfer.


## Corpus correction: coherent depths and actual cutoff order (1810e)

The following are existing results, not missing lemmas to recreate:

- `AllDepthHilbertDilationCubeAndHyperCubeGramFactorization.lean`: exact signed Hilbert-vector and Gram factorization over every divisor of a squarefree prime cube; the diagonal is already evaluated. `CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity.lean` already cancels the Euler prefactor's undilated mode and proves prime-shift covariance summability for each fixed base modulus. Eight exact APIs/axiom closures passed `lake --old env lean /tmp/chmd-corpus-reuse-1810e.lean`; only standard axioms.
- `PMRamanujanCompleteAperture.lean:233,257`: for every fixed `0 < ε < 1/2`, canonical completed prime-aperture Fermi-source norms tend to infinity, although their logarithmic coefficient-square mass is uniformly bounded. `PMPowerDampedMobiusPrimeThreshold.lean:32` supplies the complementary absolute bound for `ε > 1/2`. A universal full-prime-cube energy bound is already ruled out; no new obstruction leaf is needed.
- `NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean:386,418`: exact natural-denominator variance decomposition into head energy, forced conditional-mean energy, and centered tail variance. Its uncentered residual includes `-(H+1) * pmPowerDampedRamanujanEnergyMean ε Q`. Keep this term. The fixed-base summability theorem supplies neither a base-uniform constant nor this final conditional-tail estimate.
- `MobiusDivisorFiniteClockCountingCancellation.lean:117` and `MobiusDivisorTerminalClockOrder.lean:143` retain the actual cofactor support. Once square-root primes are processed, clock energy is exactly the head square plus omitted-prime singleton squares. A terminal checkpoint does not contain arbitrary earlier-cutoff source samples.

Deep retrieval produced both complete and partial runs; all returned candidate/source-argument lists were inspected. Exact lexical searches and dependency links located results missed by the broad queries. Search suggestions are not proofs, and absence from ranked hits is not evidence of a missing theorem. Frontier map remains read-only.

## Weaker moving-window arithmetic candidate (1810e; OPEN)

Retain the previously defined natural Selberg row
`S_N(y) = ∑_{m≤N} selbergMobiusCoeff N m * mobiusFold y (log m)`.
It is sufficient to prove

`∀ ε > 0, ∃ Cε ≥ 0, ∀ N ≥ 2, ∀ 0 ≤ y ≤ (log N)/3, |S_N(y)| ≤ Cε * N^ε`.

This weakens the earlier all-rapidity row conjecture. Paper transfer: set
`N = ceil(2 * exp(3*y))`, so `N ≤ 3*exp(3*y)` and the same `y` lies in the admitted windows for both `N` and `N²`. The existing plateau row `2*selbergMobiusCoeff (N²)-selbergMobiusCoeff N` equals the actual Möbius row through `N` and has absolute coefficient at most one. Its wave is at most `3*Cε*N^(2*ε)`. The verified fold-tail theorem bounds the difference from the complete wave by a constant times
`(1+y)*(1+y²)*exp((9/2-2*pi)*y)`, hence uniformly. Therefore the complete wave has growth `Oε(exp(6*ε*y))`; the existing growth-law receivers apply for every positive exponent. No new receiver formalization is warranted while the signed moving-window estimate is unpaid.

A cutoff-independent full prime-cube norm ceiling is refuted by the existing divergence theorem. That qualitative divergence alone does not exclude a subpower cube bound. Any proposed cube transfer must track its growth rate, the actual observation window, and the signed pairing. The new window estimate itself has no proof or Lean producer yet; the all-scale goal stays OPEN.


Corpus-audit evidence: `logs/chmd-corpus-reuse-1810e-verification.json` records 15 searches (4 partial), 14 independently checked API/axiom closures, five fresh imported source artifacts, and the raw search/check archive. Both scratch Lean audits exited 0. No Lean source changed during this correction; the previous fold-tail source hash is unchanged.

Possible rate follow-up, not proved or prioritized over the arithmetic window target: for `0<ε<1/2` and `0≤a<1/2-ε`, conjecture that canonical prime-aperture norms exceed every `C*N^a` infinitely often. Qualitative divergence alone does not prove this. A proposed argument uses dyadic differences of their Mellin transforms: exact stabilization above `1/(N+1)` plus an assumed `O(N^a)` norm bound gives locally summable increments on `Re s>1/2+a`. The existing vanishing real Mellin interval would force the analytic limit to vanish, contradicting its nonzero value at `s=1`. The local-uniform limit and value at one still require a full applicability/novelty audit. The existing first-prime-band identity in `PMPowerDampedMobiusPrimeSlab.lean:106` is another input to inspect before building any new rate theorem.


## Selberg dual pairing audit (1810f; candidate, not established)

Corpus search recovered existing finite Selberg Hilbert isometry and inverse coordinates (`SelbergHilbertCoordinateEquivalence.lean`), the attained sharp absolute-mass constant (`ChronologicalSelbergSharpMass.lean`), and exact prefix discrepancy duality (`ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean`). `Sieve/SquarefreeTotientLogMean.lean` already proves `tendsto_sum_sqfreeTotientInv_div_log_one`, the reciprocal-totient base mean. Source inspection establishes these as existing work; no new Lean applicability audit was run in this final search pass.

For a finite test row `w`, finite multiples inversion gives the proposed dual coordinate
`V_w(e)=sum_{d|e} d*mu(e/d)*w(d)` and dual energy `D_N(w)=sum_{e<=N} V_w(e)^2/phi(e)`.
The small Selberg energy of a logarithmic taper would bound its signed pairing by
`sqrt(Q_N * D_N(w))`. This is useful only after paying the actual dual energy; the finite Hilbert isometry already exists in `SelbergHilbertCoordinateEquivalence.lean`, and the exact sharp absolute-mass inverse norm already exists in `ChronologicalSelbergSharpMass.lean`.

Candidate residue identity, requiring novelty and proof audit: for fixed finite support,
`D_N(w)/log N -> sum_a a * (sum_k mu(k)*w(a*k))^2`.
The candidate limiting matrix is
`H(d,e)=sum_{a|gcd(d,e)} a*mu(d/a)*mu(e/a)`.
At one prime its proposed nonzero entries are `H(p^k,p^k)=p^(k-1)*(p+1)` for `k>=1`, `H(1,1)=1`, and `H(p^(k+1),p^k)=-p^k`; valuation gaps above one give zero. This comes from comparing the finite inverse-totient Möbius Gram's Euler factors, not a verified asymptotic theorem yet.

If applicable to the folded kernel after justified limiting exchanges, the right side contains complete Möbius folds at every dilation. It would expose the cost hidden by the Cauchy step, not provide cancellation. No uniform-in-rapidity bound for this dual energy is assumed, and no new Lean wrapper is planned without a substantive arithmetic result.

## Pause checkpoint (1810f)

The eight started Lean leaves are complete: the seven temporal-spectrum/separation leaves recorded on the [failed shortcut card](../../../5-failed/chmd-uniform-fold-approximation-2026-10-18.md), plus the [quantitative fold-tail leaf](../../../3-formalized/chmd-quantitative-fold-tail-2026-10-18.md). Each has exactly one `RHTower` umbrella import and an existing compiled artifact newer than its source. Their earlier targeted builds, direct source checks, and public-theorem axiom audits remain the verification evidence; no Lean source changed during this closeout.

`logs/chmd-closeout-1810f-verification.json` records all eight source hashes, wiring, artifacts, final lint, and cleanup. Ten final search responses (three partial) are retained in `logs/chmd-duality-search-1810f.tar.gz`; every archive member was hash-checked. The final reciprocal-totient response lists were inspected without starting another proof audit. Search coverage and proposed ingredient sets do not establish the unproved residue candidate.

Final verification: `scripts/formal_tools.py index` exited 0 and refreshed generated API, gap, and overview docs. The subsequent `scripts/formal_tools.py lint --check-generated` exited 1 solely for the unrelated package-root research leaf `TransHorizonIncidenceMechanics.lean`. It reported no stale generated file or finding in the eight owned leaves. All eight source hashes remained unchanged; all eight modules have generated API entries. No global lint pass is claimed.

No owned Lean implementation remains unfinished. The moving-window arithmetic bound, possible prime-aperture rate sharpening, and dual-residue identity remain explicitly unproved. The all-scale card stays in `1-in-progress` because its mathematical target is open; execution is paused.
