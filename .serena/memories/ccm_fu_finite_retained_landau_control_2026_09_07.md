# CCM-FU finite retained-field directional control — CLOSED; cofinal coverage/RH OPEN

## Authoritative goal and validation
Active UNBUDGETED /goal is unconditional kernel-checked proof/falsification of RH via CCM-FU. Full chain: Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH. This goal turn is PROGRESS: 37 new public declarations in four modules close positive carrier, MGF germ, Landau continuation, meromorphic identity/pole contradiction, all finite-field directional separation, finite cutoff families and uniform clipping margins. Do NOT mark complete/blocked. Complete compatible cofinal source coverage, PE4/PE4G/PE4C, SD1 and RH remain OPEN.

All four modules passed scratch and exact-file `lake env lean` checks. Only four needed oleans emitted; imports unique in RHTower, never built umbrella/dependencies. All 37 new public declarations audited ONCE, only propext/Classical.choice/Quot.sound. Global formal lint PASS, existing large-file warnings. Formal index regenerated ONCE (API/gaps/overview/research). Own source/doc whitespace and paper/card links passed. All owned Lean processes finished; /tmp scratch and logs cleaned at end. No numerical experiments/computations, no RunPod job, no computed proof premises. Do NOT recheck or reaudit these 37 or previous 43+28.

Paper: docs/drafts/pipeline/3-formalized/ccm-fu-finite-retained-directional-control.md.
Current bridge/coverage card: docs/drafts/pipeline/1-in-progress/ccm-fu-finite-source-cone-exhaustion.md (rewritten as current closed finite-field theorem + open cofinal costs).
Frontier, adaptive-prime-ceiling, previous spectral/Mellin papers updated. Universal STATUS new MUST-PAY-GROWING-WITNESS-COSTS; previous discrete-sign carrier entry updated.
Previous inputs: mem:ccm_fu_retained_source_mellin_transport_2026_09_07 (43 declarations, exact source Mellin) and mem:ccm_fu_finite_retained_spectral_separation_2026_09_07 (28 declarations, finite numerator, high poles, low balls). Those inputs are fully closed; do not list transport, Landau or finite-field control as open again.

## Four new modules/APIs — RHTower namespace, formal/GaloisForLFunctions/RHTower

### RetainedPrimeLandauCarrier —18 public
Q:Finset Nat.Primes, y:Finset Nat→Real; P=Q.image(fun p:Nat.Primes=>(p:Nat)).
`retainedPrimeLandauPrimitive Q y` := squareRootSummatoryPrimitive(retainedPrimeDivisorConvolution P (funR=>(yR:Complex))). Complex-valued but proved real everywhere.
`RetainedPrimeSourceNonnegative Q y` := ∀M:Nat, 0≤(retainedPrimeSourceMean P (funR=>(yR:Complex)) M).re. This is an explicit one-sided condition USED IN THE CONTRADICTION, not an RH assumption in final existential witnesses.
`retainedPrimeLandauPrimitive_eq_zero_of_le_one Q y hx` for x≤1.
`retainedPrimeLandauPrimitive_im_eq_zero Q y x` for every realx, using exact real coefficient summatory formula, integer source mean and sqrt interpolation.
`retainedPrimeLandauPrimitive_nonneg h x` under one-sided condition, allrealx.
`retainedPrimeLandauDensity Q y x := norm((x:Complex)^(-5:Complex)*primitive Q y x)`.
`retainedPrimeLandauMeasure Q y := (volume.restrict(Ioi0)).withDensity(funx=>ENNReal.ofReal(density Q y x))`. NOTE underlying measure is Ioi0, NOT Ioi1. Density vanishes below1, eliminating an extra Mellin restriction conversion.
`integrable_retainedPrimeLandauDensity Q y`: integrable against restricted volume, from old source HasMellin at4.
`retainedPrimeLandauMeasure_finite Q y`: IsFiniteMeasure, ordinary lemma (not instance).
`log_nonneg_ae_retainedPrimeLandauMeasure Q y`: logx≥0 a.e. under newmeasure, via vanishingdensity below1.
`exp_mul_retainedPrimeLandauDensity_eq_norm Q y t hx`: exp(tlogx)*density=norm(x^((t:Complex)-5)*primitive), x>0.
`integrable_exp_log_retainedPrimeLandauMeasure Q y ht`: t<2 ⇒ Integrable(exp(tlogx)) newmeasure.
`zero_mem_interior_integrableExpSet_retainedPrimeLandauMeasure Q y`.
`ofReal_retainedPrimeLandauDensity_eq h hx`: under onesided, castdensity=x^-5*primitive, x>0. Reality and positivity remove norm.
`complexMGF_retainedPrimeLandauMeasure_eq_mellin h z`: exact ALLz totalized integral identity complexMGF Real.log newmeasure z = mellin primitive (z-4).
`retainedPrimeLandauContinuation Q y z`: finiteDirichletDivisorMellin (retainedPrimeDirichletCoefficients P (casty)) Q (2gamma) (4-z).
`retainedPrimeLandauContinuation_eq_complexMGF h hz`: z.re<2 ⇒ continuation=complexMGF.
`retainedPrimeLandauContinuation_eventuallyEq_complexMGF h`: germ equality at0.

### FiniteDirichletMellinContinuationObstruction —2 public
Imports prior FiniteDirichletDivisorPoleSurvival and mathlib Meromorphic.Order.
`meromorphicAt_finiteDirichletDivisorMellin a ha Q c s`: a:Finsupp Nat Complex, ha:a0=0 ⇒ globally meromorphic full expression, including all denominator factors.
**`no_analytic_finiteDirichletDivisorMellin_continuation a ha hne Q c hb hH hgerm : False`**
- hne:a≠0; b:Real, hb:b<1.
- hH:AnalyticOnNhd Complex H {s|b<s.re}.
- hgerm:H=eventually at nhds(4:Complex) finiteDirichletDivisorMellin a Q c.
Proof: H-M meromorphic on connected half-plane. Germ zero⇒meromorphicOrderAt discrepancy4=top. Mathlib order-ne-top propagates on preconnected domains, so contraposition makes discrepancy ordertop at every point. Thus H andM equal on each punctured neighborhood; meromorphicOrderAt_congr transfers the order. Existing arbitrarily high critical poles at linePt t+1/2 have order−1 and re1, contradicting Hanalytic/nonnegativeorder. No clearing zeta factors or simple-zero derivative proof needed.

### RetainedPrimeLandauSeparation —6 public
`retainedPrimeLandau_integrable_transfer h hR ht0 htR`: R:NNReal,R<7/2;0≤t<R ⇒ exp(tlogx) integrable newmeasure. Uses old continuous Landau theorem and exact new MGF germ/old low-height balls.
`Iio_subset_interior_integrableExpSet_retainedPrimeLandauMeasure h hR`: allrealtilts belowR lie in interior (negative ones already classical).
`analyticOnNhd_retainedPrimeLandauReconstruction h`: s↦complexMGF Real.log newmeasure (4-s) analytic on Re(s)>3/4. Fixed R=13/4<7/2 enough to cross surviving poles at Re1; no need optimize this margin.
**`retainedPrimeSourceNonnegative_coordinates_zero h`**: ∀R:FinsetNat,R⊆P→yR=0. Uses analytic reconstruction, exact germ at4 and new no-continuation endpoint.
**`exists_negative_retainedPrimeSourceMean Q y hy`**: hy:∃R⊆P,yR≠0 ⇒ ∃M,(literal sourceMean P casty M).re<0.
**`exists_positive_retainedPrimeSourceMean Q y hy`** same nonzero premise ⇒∃M,0<mean.re. Apply negative witness to−y, exact source linearity.
These are unconditional actual source witness theorems; no unproved sign condition remains.

### RetainedPrimeFiniteSourceMargin —11 public
Imports new separation and mathlib finite-dimensional normed modules/order lattice.
`retainedPrimeFieldIndex Q := ↥(P.powerset)` (abbrev, finite subtype includesemptylabel).
`retainedPrimeFieldCoordinates Q := retainedPrimeFieldIndex Q→Real` (abbrev), SUP NORM, not Euclidean norm.
`retainedPrimeFieldPairing Q z M := Σd∈Icc1M z⟨pf(d)∩P, membership⟩*mobiusDivisorDilationChannel M d`.
Private extension of z to allFinsetNat is z onP.powerset,0outside. Private fieldPairing_eq_sourceMean identifies complex sourceMean.real with this finite-coordinate pairing.
`continuous_retainedPrimeFieldPairing Q M`.
`retainedPrimeFieldPairing_smul Q z c M`: pairing(c•z)=c*pairing(z).
`exists_positive_retainedPrimeFieldPairing Q z hz`: z≠0 ⇒∃M,0<pairing.
**`exists_retainedPrimeField_finite_uniform_margin Q`**:
∃K:FinsetNat,K.Nonempty ∧∃c:Real,0<c ∧∀z:coordinatesQ,∃M∈K,c*normz≤pairing Q z M.
Proof: positive halfspaces cover compact unit sphere; extract finiteK; continuous finite supremum has positive minimum on sphere; normalize each direction and choose an attainingM. Includesz0 becauseKnonempty. K may contain irrelevant0/1; can filter later if concrete windows requireM≥2. Any strictly positive witness itself necessarilyM≥2.
`abs_retainedPrimeFieldPairing_le Q z M`: abs(pairing)≤normz*Σd≤M abs(C_d(M)), using norm_le_pi_norm.
**`exists_retainedPrimeField_finite_clip_margin Q`**:
∃K,K.Nonempty ∧∃c δ:Real,0<c ∧0<δ ∧δ≤1 ∧
∀clip:Nat→Real,(∀M∈K,0≤clip M∧clip M≤δ)→∀z,∃M∈K,
c*normz≤(1-clip M)*pairing Q z M+clip M*pairing Q z(M+1).
Exact adjacent profiles; independent clips at every chosen cutoff. Proof A(M)=ΣabsCd, L=1+ΣM∈K(A(M+1)+A(M)), δ=min1(c0/(2L)), finalc=c0/2. No computed constants.
`retainedPrimeFieldProfile Q M : coordinatesQ` := vectorR↦Σd≤M if subtypeIndex(pf(d)∩P)=R thenC_d(M)else0.
`retainedPrimeFieldPairing_eq_sum_profile Q z M`: pairing=ΣR zR*profileQMR. This binds witnesses to COMPLETE actual source vectors, not abstract independent directions.

## Current remaining hard gate and next work
Fixed finite-field directional control, finite cutoffs, clipping tolerance and analytic proof chain are CLOSED. The exact Lean format is full directional detection and finite homogeneous/clipping margins; no separate ConvexCone.hull=top syntax theorem was added. This is the source-control form needed by the intended energy descent mechanism.

Need quantify/transport witnesses as retained field changes in an actual complete source schedule. MaxK, c(Q)^{-1}, δ(Q)^{-1}, prime-window capacity and preparation costs have no uniform-in-Q bound. Norm is sup; energy is Euclidean sum of squares, so any norm conversion must retain dimension=2^{cardP} costs. Qualitative fixed-field completeness is NOT SD1 or RH.

Next concrete handoff: identify new profile with old mobiusDivisorSelectionFibre at processed active-prime complement (old label pf(d)\processed, new label pf(d)∩P). The old selection index excludes nonsquarefree d and the terminalM; both actual channels vanish, making equality exact. Then copy arbitrary finite witness families into actual prime windows using old all-cutoff homothety/interpolation, track preparation history and budget. Existing coupled-two prime-window/batch modules are reusable templates. Mere existence of good child cutoffs does NOT give compatible processed sets.

Critical obstruction remains: processing all primes below4N at parent64N² creates superquadratic singletonenergy in(8N,9N], unaffected by terminal scalarreserves. Therefore cannot assume preparation of all primes belowmaxK exceptP is harmless. Need genuinely nonisolated interleavings before inheritedenergy grows. No chosen complete field sequence or quantitative coverage mechanism yet. Arbitrary fixedS margins alone have no control on these costs.

No numerical screening of more finite fields: qualitative result now proved. If experimenting, freeze a genuinely unresolved QUANTITATIVE tradeoff (witness conditioning/preparation budget/capacity) with competing source-derived predictions per docs/meta/scientific-method.md. All mathematical numerical computations only bounded multicore RunPod ssh root@157.157.221.29 -p27094 -i~/.ssh/id_ed25519; download/docresults andclean. No computation of predictable algebra.

## Discipline / API notes
One owned foreground Lean process at a time; lake env lean file, only necessary oleans, no umbrella/full builds. Audit only new declarations once. No subagents unless explicitly requested. Preserve other tasks' edits/commits; other agents continuously update frontier based on our files, so read current text and use narrow substitutions. No own commit/push. Tool update_plan unavailable; Serena manual read, listmemories refreshed without dumping, no relevant architecture/testing docs.

MeromorphicAt.comp_analyticAt can wrongly infer the inner map as HSub s at1/2 from an explicit argument(s-1/2); give hnum an explicit expected MeromorphicAt(fun z=>source(z-1/2))s type and use placeholder `_` in outer theorem application. This avoids inference loops.
`meromorphicOrderAt_eq_top_iff` is global, no meromorphic hypothesis; rhs ∀eventually on nhds[≠]x,fz=0. `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` supplies global continuation by contraposition. `meromorphicOrderAt_congr` uses punctured equality.
`IsCompact.elim_finite_subcover U hU hcover` gives FinsetK; `mem_iUnion₂.mp` extracts M, hM, hzM. `Continuous.finset_sup'_apply hK ...`; `Finset.exists_mem_eq_sup' hK f`; `Finset.le_sup' f hM`. Unit sphere in finite function space nonempty via constant1 and local Nonempty index, simp[S].
`λ` is reserved syntax, not a variable identifier: use clip. New `push Not at hn` replaces deprecated push_neg. Wrap multiline `simpa ... using (norm_le_pi_norm z index)` in parentheses. NNReal fixed R proof: `change (13/4:Real)<7/2; norm_num`, rather than norm_num[R] (did not unfold coercion). Unpack setmembership hs before linarith. Avoid norm_num when retaining realrpow(-5); it changes to integer inverse powers and breaks exp rewrite. For density integrability, change goal to explicit integrand before simp_only; named density function may stay folded.
