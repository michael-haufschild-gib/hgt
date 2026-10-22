# FZZ-P: original marked source after collision subtraction

Status: original continued response, diagonal sign, independent marked-cutoff limit and derivative–limit commutation formalized, 2026-09-11. All eight new public theorems passed scratch, leaf build and complete axiom audit; only `propext`, `Classical.choice`, `Quot.sound` occur. Global formal lint passed. Higher collision subtractions, the complete physical Ward law and RH remain unproved.

## Chain and obstacle

Original complete FZZ source → mixed replica–momentum Ward law in an independently fixed phase frame → balanced delay saturation → passivity → RH. The original position finite part now has a proved Gamma-continuation identity and negative sign. Its scratch, leaf build and four axiom audits passed; global lint has unrelated missing umbrella imports. A source derivative must retain both collision terms and their counterterms before it can enter the complete physical Ward balance.

## Conjecture and proof attack

For `-3<alpha,beta<-2`, write `X=log|z|`, `K=|z|^alpha|z-1|^beta`, `R=1/2`, and retain the original two collision disks and exterior. Conjectured first derivative in alpha is

`D = integral_B0 X*|z|^alpha*(|z-1|^beta-1) + integral_B1 X*K + integral_E X*K + 2*pi*R^(alpha+2)*(log(R)/(alpha+2)-1/(alpha+2)^2)`.

The second collision counterterm is independent of alpha, but its original subtracted integral contributes `integral_B1 X*K`. Its logarithm vanishes linearly at that puncture, giving admission for beta greater than -3. At zero and infinity, the already proved open exponential-moment intervals should admit the logarithmic mark and justify differentiation. Split signed source weights into their positive and negative parts before applying moment-generating-function theorems; prove admission before integral subtraction. The derivative of the explicit local counterterm must be retained.

Then compare this actual integrated derivative with the now matched Gamma family. The predicted normalized response is

`D/FP = (-psi(-alpha/2-beta/2-1)+psi(1+alpha/2)+psi(-alpha/2)-psi(2+alpha/2+beta/2))/2`,

where `psi=Gamma'/Gamma`. No sign, cancellation, or physical parameter identification is assumed. A subsequent original marked-cutoff limit must retain the differentiated cutoff counterterm as well.

## Outstanding obligations

- [x] Original logarithmic admissions and differentiation for both collision pieces and exterior; scratch and leaf build passed.
- [x] Exact counterterm derivative and complete finite-part derivative; scratch and leaf build passed.
- [x] Evaluated normalized Gamma response; scratch and leaf build passed.
- [x] Original independent marked-cutoff limit, finite-cutoff differentiation and derivative–limit commutation; scratch, leaf build and all eight axiom audits passed.
- [ ] Physical replica/momentum transport, compact and nonzero-mode contributions, independent phase frame and full Ward producer.

## Search evidence

Deep/method query `differentiate subtracted integral logarithm counterterm` returned partial generation 823339, incomplete semantic/compiler coverage and local retrieval timeouts. All 20 candidate and 20 method names were inspected; no theorem supplies the actual source derivative. Current mathlib `MGFAnalytic.lean` supplies `hasDerivAt_mgf` with an open exponential-moment domain, and `IntegrableExpMul.lean` supplies moment admission. Existing `LaplaceTransformMomentDerivative.lean` and `CenterMixedTiltDifferentiation.lean` show the original dominated differentiation method, with domain and domination obligations explicit. These are methods, not assumptions discharging this source.

## Diagonal sign conjecture → proved lower bound

Set `alpha=beta=-2-2x`, `0<x<1/2`. Once the actual marked-response formula above is established, twice the normalized alpha derivative is

`B = 1/(2x) + [psi(1-x)-psi(1-2x)] + [psi(1+x)-psi(1+2x)]`.

The recurrence at `-x,-2x` gives this exact reduction. The current corpus contains strict monotonicity of the real digamma path in `TrigammaVertical.lean` and a proved complex unit-shift recurrence. These give a simpler prospective sign proof than the initial concavity idea: the first bracket is positive, while `1+2x<2+x` and the recurrence bound the negative of the second bracket strictly above `-1/(1+x)`. Since `2x<1+x`, `1/(2x)-1/(1+x)>0`, hence `B>0`. The original source/real-Gamma derivative identification and these recurrence applications now pass Lean. The strict quantitative lower bound and actual negative diagonal insertion passed scratch and leaf build; both axiom closures passed with only `propext`, `Classical.choice`, `Quot.sound`.

The displayed first-order position-exponent direction has multiplier `4k/(k-2)` at `x=k-2`, so its predicted response would be `2k/(k-2)*B`. This is one position sector, not a complete finite-deficit CFT family or a mixed external-momentum Ward law. A complete cancellation would still have to account for all omitted physical source components and the phase frame.

Deep/method concavity search returned partial generation 823339 with no proof-idea or ingredient-set closure and unavailable local semantic retrieval; all candidate and method names were inspected. Exact source search found `ReflectionCocycleArchimedean.lean`, whose proof compares the actual trigamma partial sums, and `TrigammaVertical.lean`, whose real digamma path is strictly increasing on the positive axis. The latter plus the unit-shift recurrence is the smaller proposed ingredient set.

## Current scratch checkpoint

`/tmp/fzzp_continued_screening_mark.lean` now contains the original three-region derivative proof and the Gamma-response comparison. The previous complete check accepted the signed exponential-moment derivative, both logarithmic collision admissions, the exterior mark, the local power-counterterm derivative and the dominated regular-factor derivative; its remaining error was unfolding the sum and composition of functions in the final assembly. That rewrite is corrected. The current check additionally tests the real Gamma logarithmic derivative at negative nonpole arguments, the first-strip chart inverse, local continued-source equality and the four-term normalized response. The combined file subsequently passed. It is now `formal/GaloisForLFunctions/RHTower/FZZCigarContinuedScreeningMark.lean`, wired into the RHTower umbrella. Leaf-only build passed (8845 dependency jobs, leaf 80 seconds); all four public axiom closures passed, containing only `propext`, `Classical.choice`, `Quot.sound`. No umbrella build was run.

Exact real/complex transfer for the planned diagonal sign has a current-library basis: `Real.differentiableAt_Gamma` itself restricts the complex Gamma derivative via `HasDerivAt.real_of_complex`; `Complex.div_ofReal_re` transfers the logarithmic quotient; `Complex.digamma_apply_add_one` requires off-pole admission, which the first strip supplies. These obligations must be checked for the actual arguments before using `RHTower.strictMonoOn_re_digamma_ofReal`.

## Closed original response

Four data-only public theorems now establish all three original logarithmic admissions, the complete finite-part derivative, its normalized logarithmic derivative, and equality of that original normalized insertion with the four-term Gamma slope stated above. The proof first differentiates the actual admitted source and its explicit power counterterm. It then proves Gamma nonpole admission for every negative argument used and matches the source logarithm on a whole neighborhood using the inverse continuation chart `log((alpha+3)/(-alpha-2))`. Uniqueness of the derivative gives the response identity. No positivity, stationarity or physical Ward condition is an input.

Scratch: `/tmp/fzzp_continued_screening_mark.lean`; logs `/tmp/fzzp-continued-screening-mark-{scratch,build,axioms,lint}.log`. The next scratch `/tmp/fzzp_continued_screening_sign.lean` has now proved the source diagonal sign and the stronger explicit lower bound `D/FP > (1/(2x)-1/(1+x))/2 > 0`. It was promoted to `formal/GaloisForLFunctions/RHTower/FZZCigarContinuedScreeningSign.lean` and wired into the umbrella. The leaf-only build passed (8939 dependency jobs, leaf 171 seconds); both axiom closures passed with only `propext`, `Classical.choice`, `Quot.sound`. The actual marked-cutoff limit and full physical parameter transport remain separate obligations.

Final original-response audit: four public statements passed `lake env lean` scratch, the leaf-only build, and all axiom closures. Global lint still fails on other active areas: `DeningerGammaSixFixedDilationTailReader`, `EulerDeletionSignatureWordExpansion`, `HTGeometry.WeightedMinimax.Alternation`, and `HTGeometry.WeightedMinimax.Coefficient`; no FZZ module error was reported. The latest log is `/tmp/fzzp-continued-screening-mark-lint.log`. The diagonal sign draft subsequently passed scratch, leaf build and both axiom audits.

## Next original cutoff identity

After the diagonal sign, the next source obligation is a direct marked-cutoff limit, not an assumed interchange of differentiation and a divergent limit. For `q=alpha+2` and `0<epsilon<R`, the radial logarithmic integral should satisfy

`integral_(epsilon<|z|<R) log|z|*|z|^alpha = 2*pi*[R^q*(log R/q-1/q^2)-epsilon^q*(log epsilon/q-1/q^2)]`.

The proposed proof is the actual planar polar formula followed by the positive-radius antiderivative `r^q*(log r/q-1/q^2)`. Add the differentiated power counterterm at epsilon; the remaining zero-collision logarithmic subtraction converges by its now proved L1 admission. At the second collision the logarithm vanishes, so its full marked kernel is already L1; its shrinking-hole limit requires no alpha derivative of the beta-only counterterm. Retaining the fixed exterior then gives the two-independent-cutoff marked limit. This identity and finite-cutoff differentiation are now proved in the complete scratch audited below. A new whole-corpus deep/method search is recorded in `/tmp/fzzp-marked-cutoff-antiderivative-methods.json`.

The next cutoff-antiderivative search returned partial generation 823339 with interrupted source/text retrieval and no proof-idea or ingredient-set closure. All 20 candidate and 20 method names were inspected. `PrimeTailBoundaryAsymptotic.lean` proves a different inverse-logarithm primitive and retains its remainder; `EvenSeamFinitePart.lean` proves unmarked power and inverse-radius integrals. Neither supplies the marked planar annulus identity. The direct scalar primitive and positive-interval FTC are now checked in `/tmp/fzzp_marked_screening_cutoff.lean`, together with the complete limit and derivative proof below.

## Completed diagonal sign audit

`FZZCigarContinuedScreeningSign.lean` proves `fzzScreeningPlaneContinuedMark_diagonal_response_lower` and `fzzScreeningPlaneContinuedMark_diagonal_neg`, both with only the real chart parameter as input. The explicit positive response floor is retained; this is stronger than a nonvanishing statement. Actual negative insertion follows by multiplying the positive normalized response by the proved negative original finite part. No complete CFT cancellation or external-momentum condition is asserted.

Validation: scratch passed; leaf-only build passed (8939 dependency jobs, leaf 171 seconds); both public axiom closures passed with only the three standard core axioms. Logs `/tmp/fzzp-continued-screening-sign-{scratch,build,axioms,lint}.log`. The final shared-tree lint run still fails outside FZZ on `EulerDeletionCoprimeJointProduct`, `EulerDeletionCoprimePolygonSignature`, `HTGeometry.WeightedMinimax.Alternation`, `HTGeometry.WeightedMinimax.Coefficient`, and `HTGeometry.WeightedMinimax.PolyRoots`. No full or umbrella build was run.


## Original marked cutoffs and derivative interchange

The complete `/tmp/fzzp_marked_screening_cutoff.lean` passed with all eight public theorems. It proves the radial marked primitive, original marked annulus identity, retained counterterm, all finite marked admissions, both local shrinking-hole limits, independent whole-plane cutoff limit and synchronized specialization, original finite-cutoff derivative, corrected derivative, and derivative–limit commutation. The proof body has been promoted unchanged to `formal/GaloisForLFunctions/RHTower/FZZCigarMarkedScreeningCutoff.lean` and wired into the RHTower umbrella. Leaf build passed (8846 dependency jobs, new leaf 159 seconds); all eight axiom audits passed with only `propext`, `Classical.choice`, `Quot.sound`. Global formal lint passed. Logs: `/tmp/fzzp-marked-screening-cutoff-{scratch,build,axioms,lint}.log`; axiom scratch `/tmp/fzzp_marked_screening_cutoff_axioms.lean`. No full or umbrella build was run.

For `alpha,beta` in `(-3,-2)`, write `K=|z|^alpha|z-1|^beta`, `X=log|z|`, and `r=exp(-T),s=exp(-U)`. The proved theorem is the genuine independent limit

`integral_(|z|>r,|z-1|>s) X*K + 2*pi*r^(alpha+2)*(log r/(alpha+2)-1/(alpha+2)^2) -> D(alpha,beta)`.

Every finite marked integral is admitted: its zero annulus is compactly away from the singular point; the other disk and exterior use the already proved marked admissions. The zero-collision split is an exact integral identity, not an assumed exchange of derivative and divergent limit. The second puncture contributes its full admitted mark, with no alpha derivative of the beta-only counterterm.

The further original source derivative proof also passes Lean. For each finite pair of cutoffs, use the positive measure `K d^2z` restricted to that domain. Its `X`-moment generating function at delta equals the original cutoff with exponent `alpha+delta`. The explicit first-strip inverse chart admits this shifted cutoff on an open interval around zero. The current library MGF derivative therefore gives the original marked cutoff. Differentiate both actual power counterterms, then combine the just-proved marked limit with the previously proved derivative of the original finite part. This establishes derivative–limit commutation for the fixed original subtraction prescription without assuming it. All statements have only real data parameters; domain, admission, nonzero denominator and neighborhood requirements are discharged inside the proofs.

Search evidence this pass: deep/all-view `integrable shrinking holes marked counterterm derivative` returned 20 candidates and 20 source methods, all inspected, with pending generation 823339 and unavailable/deadline-limited semantic retrieval. The corpus finite-ball-excision proof uses absolute continuity of the integral after L1 admission; the current source admits the same limiting mechanism directly through dominated convergence. Hybrid `counterterm derivative boundary cancellation original integral` had no useful hits and partial coverage; broad deep/all-view `counterterm derivative --any` supplied a proposed ingredient set for derivatives of anchored arithmetic counterterms. Its actual source proofs (`SquarefreeConvolutionHalfAnchoredCountertermNoGo` and `SquarefreeConvolutionHalfFirstJetCountertermNoGo`) were read: they retain the product-rule contributions but do not supply the screening admission or cutoff limit.

Broad arXiv searches used `renormalization`, `sewing`, and `compensation`, preferring June–September 2026. [SMEFT renormalization, June 17](https://arxiv.org/html/2606.19202v1), equations (4)–(13), retains contributions of redundant operators when passing from off-shell to physical coefficients. Its method suggests auditing source terms before claiming a cancellation; its four-dimensional EFT identities do not prove a cigar Ward law. [Compensation Design, July 16–17](https://arxiv.org/abs/2607.14438) concerns submodular payment rules and supplies no applicable analytic identity. Sewing hits concern garment reconstruction, with no applicable theorem identified. The older [Kerr conserved-current paper](https://arxiv.org/html/2210.15935v3), Lemma 2 and section V.2, extends a conserved bilinear form by a complex contour with proved decay. Section VI explicitly distinguishes it from a positive-definite scalar product. Its contour/adjoint method is a possible source-conservation analogy, not a positivity or passivity theorem for this route.

The full mixed source Ward producer and independent physical phase frame remain missing. These cutoff results concern the displayed position sector only; no full FZZ cancellation, source-to-theta identification, or RH proof is claimed.


## Next source-domain attack: the receiver level is outside this strip

The external-leg receiver audit uses `k=4`; substituting this into the displayed unmarked position exponent `2(1-k)` gives `alpha=beta=-6`, outside `(-3,-2)`. The present proofs must not be transported there by silently evaluating totalized Gamma functions at their poles. Higher local subtraction and full source normalization are required. The original paper's (3.30) also retains interactions among all screening positions, so this one-position source is not the full screening amplitude.

A concrete next conjecture follows from the current corpus Poisson-circle identity (`SteinhausTorusJensenFloor.circleAverage_inv_normSq_one_sub_mul`, read and checked as source). Put `Q=1-2r cos(theta)+r^2`, `A_m(r)=average Q^(-m)`. Differentiating the actual compact angular integral for `0<r<1` should give

`r*A_m'(r)=m*((1-r^2)*A_(m+1)(r)-A_m(r))`.

Starting from the proved `A_1=(1-r^2)^(-1)`, this predicts `A_2=(1+r^2)/(1-r^2)^3` and `A_3=(1+4r^2+r^4)/(1-r^2)^5`. In particular, the local radial average of the `beta=-6` factor would have expansion `1+9r^2+36r^4+O(r^6)`. At `alpha=-6`, the three radial divergences are therefore power, power, and logarithm; a single leading counterterm is insufficient. The next proof must derive this angular identity and its remainder from the original source before integrating or differentiating the higher subtraction. This is a paper conjecture, not yet a Lean theorem or a physical Ward cancellation.


The higher-collision deep/all-view query `angular average Taylor singular integral logarithmic subtraction` returned partial generation 823340 with semantic timeouts; all 20 candidate and 20 source-method names were inspected. The actual `ThetaCuspHawkingBMNativeCircleMean.average_hasDerivAt` proof bounds the parameter derivative on a compact parameter–angle rectangle before dominated differentiation. This provides a current-corpus method for the proposed recurrence, but its global smoothness must be localized away from `r=1`. `BarnesDoubleZetaDeepContinuation` retains the exact Taylor polynomial plus an analytic divided-difference remainder before continuing a singular integral. It provides a remainder mechanism, not the original screening coefficients. Neither hit supplies the full Ward producer.


The higher-strip marked problem also changes the second collision. For a general regular exponent `a`, the angular Taylor coefficients predicted from the local product `(1-z)^(a/2)(1-conj z)^(a/2)` are `c0=1`, `c1=a^2/4`, and `c2=a^2*(a-2)^2/64`. Their exponent derivatives at `a=-6` are `0,-3,-21`. Thus the original mark at the second collision should acquire nonzero power and logarithmic corrections there, although the leading constant's derivative remains zero. The first-strip statement that no second-collision mark counterterm is needed must not be extrapolated to this higher strip. These coefficients and their source remainder still require original analytic/Taylor and Lean proofs.
