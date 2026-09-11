# FZZ-P: higher original screening collisions

- **ID:** FZZ-P-HSC
- **Stage:** 1-in-progress
- **Type:** FORMALIZED SOURCE RESULTS; FULL CONTINUATION OPEN
- **Source:** [current frontier](rh-current-frontier-map.md#fzz-p--parity-delay-mellin-orientation), [first-strip cutoff audit](fzz-p-continued-screening-mark.md)
- **Statement:** Derive the original angular Taylor subtraction at exponent `-6`, including both punctures and all differentiated counterterms.

## Goal

Fixed theta/FZZ source → complete mixed Ward law in an independently fixed phase frame → balanced vacuum delay → passivity → RH. Eight first-strip source theorems now close the original marked cutoff and derivative interchange. The external-leg receiver uses `k=4`, whose displayed position exponent `2(1-k)=-6` is outside that strip. This card attacks that missing source domain; it does not assume a full physical cancellation.

## Gates

- [x] Well-posed original source and non-circular angular-average attack.
- [x] Original angular recurrence with parameter differentiation justified.
- [x] Exact cubic inverse-power angular average and local remainder.
- [x] Higher original cutoff counterterms at both punctures, with complete leaf and axiom audits.
- [x] Original logarithmic angular recurrence, both marked remainders and radial cutoff limits.
- [x] Original marked plane cutoff with both distinct local corrections and independent limits.
- [x] Higher original parameter continuation and both exact cubic finite-part values.
- [x] Original marked source extraction, independent cutoff limit and position-log ratio.
- [x] Dependency-closed paper proofs and data-only Lean statements for these source results, targeted leaf builds and formal lint.
- [ ] Fractional screening-count continuation, complete physical normalization and physical replica/momentum identification.

## Approach

For `Q(r,theta)=1-2r*cos(theta)+r^2`, let `A_m(r)` be the original normalized angular integral of `Q^(-m)`. On `0<r<1`, the current corpus proves `A_1=(1-r^2)^(-1)` through the Poisson kernel. A compact parameter–angle rectangle stays away from `Q=0`; continuous parameter derivatives have a common bound, so the proved dominated differentiation gives

`r*A_m'(r)=m*((1-r^2)*A_(m+1)(r)-A_m(r))`.

Two applications give `A_2=(1+r^2)/(1-r^2)^3` and `A_3=(1+4r^2+r^4)/(1-r^2)^5`. The latter gives the exact local expansion derived below, hence two power divergences and a logarithmic divergence at exponent `-6`. The original angular equality and remainder are now transported to the planar cutoff integral.

The other marked puncture has new terms. The original logarithmic angular coefficients at `a=-6` are now proved to be `0,-3,-21`. Their general-exponent source `1,a^2/4,a^2*(a-2)^2/64` is now derived and admitted by the polynomial restoration below. The first-strip absence of a second-collision marked correction does not extend to this depth.

## Evidence and constraints

Read current sources: `SteinhausTorusJensenFloor.circleAverage_inv_normSq_one_sub_mul` (original inverse-square Poisson average); `ThetaCuspHawkingBMNativeCircleMean.average_hasDerivAt` (compact derivative bound before differentiation); `BarnesDoubleZetaDeepContinuation.barnesConeKernelAnalytic_taylor_three` (exact Taylor polynomial plus admitted remainder). They provide methods, not an identified full FZZ source or Ward theorem.

Deep/all-view searches run over the current corpus; coverage and applicability are recorded as results arrive. No numerical experiments, added proof axioms or unproved source identities are permitted. Public source statements use real data charts; all analytic and integrability requirements must be discharged internally.

## Log

- 2026-09-11 — created after the eight first-strip cutoff/derivative theorems passed scratch, leaf build, all axiom audits and global lint. RH, the full mixed Ward producer and the phase frame remain open.


The angular scratch `/tmp/fzzp_higher_screening_angular.lean` passed cleanly with six public theorems, including the exact corrected radial cutoff limit. Its proof body was promoted unchanged to `formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningAngular.lean` and wired into the umbrella. The targeted leaf build passed (138 seconds for the new leaf); all six axiom audits passed with only `propext`, `Classical.choice`, `Quot.sound`. The proof uses a fixed compact parameter–angle rectangle contained in `0<r<1`, bounds the continuous derivative there, and invokes the current parametric-integral theorem. This is local polar integration of the original collision kernel, not Jacobian averaging of the marked torus selector. The original planar source is now proved below.

The deep/all-view recurrence query returned partial generation 823347 with semantic deadline expiry; all 20 candidate and 20 method names were inspected, with no proposed ingredient set. It supplied current circle-average transport and Poisson identities. Broad recent arXiv searches for multipole, resurgence and orthogonality returned older papers; a stricter June–September search for multipole, Laurent and contour returned no hits. Those empty or out-of-range results are not evidence of absence of applicable research.

## Exact angular and radial derivation

Write `d=1-r^2`. Since `Q >= (1-r)^2 > 0`, every inverse power and its parameter derivative is continuous on a compact parameter–angle rectangle around an interior radius. Compactness supplies an integrable constant bound for differentiation. The pointwise identity

`r*d_r(Q^(-m)) = m*((1-r^2)*Q^(-m-1)-Q^(-m))`

then integrates to the recurrence. The admitted Poisson average gives `A_1=1/d`. Differentiating gives `A_1'=2r/d^2`, so the recurrence yields `A_2=(1+r^2)/d^3`. Differentiating again gives `A_2'=4r*(2+r^2)/d^4`, hence `A_3=(1+4r^2+r^4)/d^5`.

The exact remainder, rather than an unspecified asymptotic term, is

`H(r)=(100-275r^2+316r^4-171r^6+36r^8)/(1-r^2)^5`,

with `A_3=1+9r^2+36r^4+r^6*H`. It is continuous through `r=0` and on `[0,1/2]`. Thus `r^(-5)*(A_3-1-9r^2-36r^4)=r*H` is integrable there. This proves integrability after angular integration; it does not assert absolute integrability of a planar integrand after merely radial subtraction.

The singular radial primitive is

`P(r)=-1/(4r^4)-9/(2r^2)+36*log r`.

For `0<epsilon<=1/2`, the fundamental theorem gives

`int_epsilon^(1/2) r^(-5)*A_3(r) dr + P(epsilon)
 = int_epsilon^(1/2) r*H(r) dr + P(1/2)`.

Dominated convergence removes the lower endpoint in the remainder integral. Multiplying by the polar factor gives the counterterm `-(pi/2)*epsilon^(-4)-9*pi*epsilon^(-2)+72*pi*log epsilon`. The planar-annulus transport is now proved below. Both higher marked angular limits and their original planar transports are now closed below.

## Closed original plane cutoff

`formal/GaloisForLFunctions/RHTower/FZZCigarCubicScreeningCutoff.lean` retains the actual `fzzScreeningPlaneKernel (-6) (-6)` and `fzzScreeningPlaneCutoffDomain`. The polar identity is applied to the original annulus indicator. On the compact parameter–angle rectangle, the full polar kernel is continuous and integrable, justifying Fubini before identifying its angular integral with `A_3`. This gives the original planar annulus value `2*pi*int_epsilon^(1/2) r^(-5)*A_3(r)dr`. A compact annulus away from both punctures also proves ordinary integrability directly. Reflection gives the second original puncture.

The fixed exterior is admitted by the existing total-power theorem with `alpha=beta=-6`. At every pair of finite cutoffs the original plane is covered by the two admitted annuli and exterior. For sufficiently small independent radii these three pieces are disjoint and equal the original cutoff domain, so integral addition is justified. The two local limits then give

`K_cutoff(T,U)+2*pi*P(exp(-T))+2*pi*P(exp(-U))
  -> 2*L + int_exterior K(-6,-6)`

as `(T,U)->(atTop,atTop)`, with `L=2*pi*(int_0^(1/2) r*H(r)dr+P(1/2))`. This value defines `fzzScreeningCubicPlaneFinitePart`; it is not assigned a special-function value.

All five public statements passed clean scratch `/tmp/fzzp_higher_screening_plane.lean` and targeted leaf build (80 seconds for the new leaf); the proof body was promoted unchanged and the umbrella is wired. All five axiom audits passed with only `propext`, `Classical.choice`, `Quot.sound`. At that audit, global lint reported two unrelated unwired modules: `RHTower.Sieve.MenonHarmonicWindowPartitionMass` and `HTGeometry.ChronologicalTensor.CubicCuspPresentation`.

The public theorems are `fzzScreeningCubicAnnulus_integrable`, `fzzScreeningCubicZero_cutoff_limit`, `fzzScreeningCubicOne_cutoff_limit`, `fzzScreeningCubicPlaneCutoff_integrable`, and `fzzScreeningCubicPlane_independent_cutoff_limit`. The last theorem retains both local corrections and the unchanged exterior for independently removed original punctures.

## Current method and distant-paper intake

- Deep/all-view query `polar annulus inverse power Taylor remainder integrable`: partial generation 823348; semantic backend timeout and reranking deadline, no ingredient set. All 20 candidate and 20 method names were inspected. The useful methods were original polar-annulus transport in `DaiYoshikawa.AnnulusMonomialIntegral` and compact-product Fubini in `HTGeometry.CauchyPompeiu`.
- Hybrid query `circleAverage annulus integral compact source`: partial generation 823348, semantic coverage incomplete. All 20 candidate and 20 method names were inspected. Current circle-average angle shifts and the same original annulus transport supply the next planar step.
- Broad searches for resonance, locality and holonomy found [Information locality of a quantum locally recoverable code](https://arxiv.org/abs/2608.04403) (5 August 2026) and [Prometheus–Pandora dynamics](https://arxiv.org/abs/2607.02839) (3 July 2026). Abstracts inspected; no applicable analytic source or Ward identity identified, and no computations run.
- [Resurgence of high-energy string amplitudes](https://arxiv.org/html/2604.07444v1) is dated 8 April 2026, outside the preferred window. Sections 3.2.1–3.2.3 retain periodic ambiguity in their difference-system solutions and leave the higher-dimensional connection problem open. It supplies no complete phase normalization for this route.
- [Covariant Berry connection](https://journals.aps.org/prresearch/pdf/10.1103/1369-2jzh) was published 9 July 2026. Equations (3), (6), (15) retain metric evolution and the derivative correction to a Hermitian-frame Hamiltonian. Inference for this route: that construction alone cannot identify the original fixed-frame generator or cancel its mixed response. No transfer theorem or new universal rule is asserted from this intake.

## Next conjecture: exact whole-plane finite value

**Now proved in Lean by the original cutoff extraction below:** with independent circular punctures at zero and one and precisely the preceding local corrections, the whole-plane finite part of `K(-6,-6)` is `-84*pi`. The harmonic-flux argument that first suggested this value remains a separate, unformalized candidate.

This candidate comes from the original source, not a substituted special-function value at a pole. Set `f(z)=1/(z^3*(z-1)^3)`, so `K(-6,-6)=|f|^2` off the punctures. Its partial fractions are

`f(z)=-z^(-3)-3z^(-2)-6z^(-1)
       +(z-1)^(-3)-3(z-1)^(-2)+6(z-1)^(-1)`.

A single-valued real harmonic potential away from the punctures is

`U(z)=Re(1/(2z^2)+3/z-1/(2(z-1)^2)+3/(z-1))
      +6*log|z-1|-6*log|z|`.

Its proposed exact energy identity is `|grad U|^2=K(-6,-6)`. The local expansion at zero has inverse-square coefficient `1/2`, inverse-linear coefficient `3`, logarithmic coefficient `-6`, and regular constant `-7/2`. At one these coefficients are `-1/2,3,6,7/2`. In the inward flux `-int U*(partial_r U)*r dtheta`, the opposite radial powers' cross terms cancel. Each puncture should therefore contribute

`pi/(2*epsilon^4)+9*pi/epsilon^2-72*pi*log epsilon-42*pi+o(1)`.

Green's identity on the finitely punctured disk, together with vanishing outer flux, would independently give the stated `-84*pi`. For this separate harmonic-flux argument, the remaining work is explicit: verify the original energy identity, admit the multiply punctured Green formula, bound both local remainders and outer flux, and compare with the independently removed cutoff definition. The deep/all-view corpus search for the required Dirichlet-energy method is recorded below. No phase-frame or mixed Ward conclusion follows from this candidate alone.

The first Dirichlet-energy query returned partial generation 823349 with interrupted text/source retrieval and no ingredient set; all 20 candidate and 20 method names were inspected. Broadening to `Green boundary circle` returned the same pending generation with semantic backend timeout, but exposed `Bottcher.integral_ball_laplacian_eq_boundary_flux` in `Bottcher/Brolin/RieszFlux.lean:415`. Its current source was read: it proves the disk flux identity for globally `ContDiff` order-two functions, using polar reduction, angular periodicity and FTC. It does not apply directly to the singular potential.

**Replacement mechanism to test:** multiply `U^2/2` by smooth cutoffs that vanish on smaller neighborhoods of both punctures and equal one near and outside their retained boundary circles. The result is globally smooth. Apply the admitted disk flux identity to the outer disk and the two removed disks, then subtract. On the retained region the Laplacian should equal the original `K(-6,-6)`; on each boundary the function and derivative agree with `U^2/2`. This avoids assuming a multiply punctured Green theorem, while retaining every boundary flux. The smooth extension, original energy identity and all limiting estimates remain to be proved.

## Marked-source derivation

The other puncture's marked coefficients can be attacked without assuming a generic hypergeometric continuation. Define `C_m(r)=average_theta(log(Q)*Q^(-m))`, with the same original `Q`. The current Poisson theorem `HarmonicOnNhd.circleAverage_poissonKernel_smul`, applied to the harmonic function `log|1-r*z|`, predicts `C_1=2*log(1-r^2)/(1-r^2)`. Its zero-free harmonic premise can use the current `AnalyticAt.harmonicAt_log_norm` theorem and `r<1`.

Differentiating the original integrand gives the candidate recurrence

`r*C_m' = m*((1-r^2)*C_(m+1)-C_m)
          -((1-r^2)*A_(m+1)-A_m)`.

Writing `x=r^2`, `d=1-x`, `L=log d`, two recurrences predict

`C_2=2*((1+x)*L-x)/d^3`,

`C_3=(2*(1+4x+x^2)*L-4x-3x^2)/d^5`.

The actual regular-factor logarithmic mark is `C_3/2`; its expansion starts `-3r^2-21r^4`. This predicts the second-puncture marked correction `3*pi*epsilon^(-2)-42*pi*log epsilon`. At the zero puncture, marking the already derived radial source instead predicts the primitive

`-epsilon^(-4)*(log epsilon/4+1/16)
 -9*epsilon^(-2)*(log epsilon/2+1/4)+18*(log epsilon)^2`

before the factor `2*pi`. Original logarithmic angular admission, justified differentiation, remainder control and both corrected radial cutoff limits are now closed below. Planar transport is now closed below. Physical parameter differentiation and the chosen singular-parameter continuation remain open.

The `Poisson weighted logarithm circle average` deep/all-view search returned partial generation 823349 with semantic deadline/backend failure and no ingredient set. All 20 candidate and 20 method names were inspected; current harmonic logarithm and Poisson-kernel source statements were read. This supplies a concrete next attack on the missing higher marked source, with no assumed cancellation.

## Complete-source normalization gate

The [source paper](https://arxiv.org/html/2402.00932v3) states below (3.26) that its screening integral initially uses integer `s'=1/(k-2)`; thus `k=4` requires continuation to `s'=1/2`, not merely exponent continuation of one fixed-dimensional factor. Equations (3.27) and (3.34) also retain a reciprocal-Gamma zero and a compensating singular factor. The full response therefore needs a source-derived joint continuation of multiplicity, normalization and replica insertion. Neither the present circular finite part nor its evaluated value supplies that identification.

The deep/all-view `complex Selberg screening integral Gamma product` search returned partial generation 823349 with reranking deadline and semantic-backend timeout. All 20 candidate and 20 method names were inspected. It found the existing single-position beta integral but no applicable full screening identity. An exhaustive `rg` query for Dotsenko/Fateev and complex-Selberg screening phrases in Lean and notes found only unrelated Selberg-class prime pairings; this is limited lexical evidence, not a claim that no full method exists.

## Closed original logarithmic angular source

The scratch `/tmp/fzzp_marked_angular.lean` passed cleanly with eight public theorems for the original mark `M_m=C_m/2`, whose integrand is exactly `log|1-z|*|1-z|^(-2m)`. Its proof body was promoted unchanged to `formal/GaloisForLFunctions/RHTower/FZZCigarHigherMarkedAngular.lean` and wired into the `RHTower` umbrella. Global formal lint passes at this audit. The targeted leaf build passed (124 seconds for the new leaf), and all eight axiom audits passed with only `propext`, `Classical.choice`, `Quot.sound`. No RH assertion follows from these local source theorems.

The paper proof uses the zero-free analytic function `1-r*z` on the closed unit disk, admitted because `r<1`. Harmonic Poisson reproduction evaluates `M_1=log(1-r^2)/(1-r^2)`. A common compact parameter–angle bound justifies differentiating the original logarithmic integrand. The recurrence is

`r*M_m'=m*((1-r^2)*M_(m+1)-M_m)-((1-r^2)*A_(m+1)-A_m)/2`.

The final unmarked term is forced by differentiating the logarithm. The first two recurrences, using the already derived unmarked averages, give

`M_2=((1+r^2)*log(1-r^2)-r^2)/(1-r^2)^3`,

`M_3=((1+4r^2+r^4)*log(1-r^2)-2r^2-3r^4/2)/(1-r^2)^5`.

For a precise integrability proof, let `E=log(1-r^2)+r^2+r^4/2` and `B=-78+(359/2)r^2-195r^4+102r^6-21r^8`. Direct symbolic algebra gives

`r^(-5)*(M_3+3r^2+21r^4)
 = (1+4r^2+r^4)*E/(r^5*(1-r^2)^5)+r*B/(1-r^2)^5`.

The current `Real.abs_log_sub_add_sum_range_le` theorem gives `|E|<=r^6/(1-r^2)`. Thus the absolute radial remainder is bounded by

`r*(1+4r^2+r^4)/(1-r^2)^6+|r*B/(1-r^2)^5|`,

which is continuous on `[0,1/2]`. This admits the original radial remainder before removing the cutoff. Its singular primitive is `3/(2r^2)-21log r`, giving the required correction `3*pi/r^2-42*pi*log r` after the polar factor. The singular-factor mark at zero instead multiplies the already proved unmarked angular source by `log r`; its residual source is `r*log(r)*H(r)`, continuous through zero by the current `Real.continuous_mul_log` theorem. Its primitive is the power-log and squared-log expression stated above. Finite-interval FTC and dominated convergence now prove both corrected radial cutoff limits. The original planar transport is now closed below; full physical normalization remains open.

### Current corpus and distant methods

The deep/all-view `Poisson harmonic logarithm parameter derivative` search returned partial generation 823350 with incomplete source/semantic indexes and source refresh. All 20 candidate and 20 method names were inspected. The returned ingredient proposal mixed Poisson boundary positivity with a zeta log derivative; that combination was not used. Current `HTGeometry.PoissonKernelBound.circleAverage_poissonKernel_log_norm` and Mathlib harmonic Poisson reproduction directly supply the applicable method.

The deep/all-view `method logarithm Taylor remainder integrable radial inverse power` search returned partial generation 823350 with semantic deadline expiry and worker disconnection. All 20 candidate and 20 method names were inspected. The proposed Taylor ingredient was checked against `DQPT.dqpt_log_taylor_remainder`, whose current proof uses the same Mathlib logarithmic remainder bound. Its uniform geometric estimate was replaced here by the needed vanishing `r^6` estimate. The proposed geodesic-polar ingredient concerns an abstract curvature chart; the present source still needs its own Euclidean planar transport.

Broad single-word arXiv searches for balayage, monodromy and renormalization, then date-broadened searches, produced three recent papers whose primary text was inspected:

- [Rank matching in renormalization-group irreversibility](https://arxiv.org/html/2608.02447v1), 3 August 2026: Sections II–III distinguish quadratic positivity from higher connected responses and retain a problem-specific Ward identity in the first-order closure. Applicability here would require identifying the original source response with that signed quadratic form; no such identification has been derived.
- [Dunkl–Riesz endpoint estimates](https://arxiv.org/html/2609.08492v1), 8 September 2026: Section 1.3 derives the obstacle mechanism from a positive symmetric jump-kernel representation. That kernel property is a concrete additional obligation, not a consequence of the present FZZ cutoff theorem.
- [Orlicz potential theory](https://arxiv.org/html/2606.29912v1), 29 June 2026: Section 1.3 states strict monotonicity, coercivity and growth assumptions for its scale-free potential theory. These are not established for the original continued source. No computations or numerical experiments were run from any paper.

### Original marked plane assembly mechanism

The two radial limits have different source meanings. Polar transport of `K(-6,-6)*log|z|` near zero gives `r^(-5)*log(r)*A_3(r)`. Reflection `z=1-w` near one gives `r^(-5)*M_3(r)`. Thus the eventual whole-plane marked value must retain the two different local finite values and the actual exterior integral; reflection does not justify replacing them by twice one local value.

A direct exterior admission avoids assuming a continued marked formula. For `t>0`, the current logarithm inequality gives `|log t|<=t+t^(-1)`. Therefore the absolute original marked kernel is bounded by `K(-5,-6)+K(-7,-6)`. Both shifted kernels satisfy the already proved exterior total-power admission. Compact annuli admit the original logarithmic kernel separately; the original polar indicator and compact Fubini can then identify each local integral. These steps now give the two-cutoff marked plane theorem below, with no prescribed Gamma value.

The later deep/all-view `method original logarithmic plane exterior power decay integrable cutoff` search returned partial generation 823350 with incomplete source/semantic indexes and source refresh, without runtime errors. All 20 candidate and 20 method names were inspected; its cutoff-operator ingredient proposal did not identify the original marked exterior. The broadened hybrid `log norm exponent moments` query had the same partial generation and no runtime errors; all 20 candidate and 20 method names were inspected. The direct two-neighbor-power bound above uses the admitted original source and avoids substituting an unrelated moment family. That candidate is retained in `/tmp/fzzp_cubic_marked_exterior_candidate.lean` and is now included in the full original marked-plane scratch `/tmp/fzzp_cubic_marked_plane.lean`, now passing cleanly. The scratch includes compact polar admission, both angular transports, the distinct local limits, exterior admission, finite-cutoff integrability and independent-cutoff assembly; the completed planar results are recorded below.

## Next pole identification conjecture

**Both original values now proved:** the original circular finite parts satisfy

`fzzScreeningCubicPlaneFinitePart=-84*pi` (proved by the extraction below).

The marked extraction below proves `fzzScreeningCubicMarkedPlaneFinitePart=-141*pi/8`.

The proved normalized position-mark ratio is `47/224`, hence nonzero. The complete physical source still must supply its compensating contribution. Neither value is assigned by definition.

The first candidate already has the independent harmonic-flux derivation above. A second source of both candidates is the current first-strip Gamma formula, using the current `Real.Gamma_add_one` recurrence (Mathlib `Gamma/Basic.lean:409`). Write `u=(alpha+6)/2`, `w=(beta+6)/2`, `v=u+w`, and `R(t)=Gamma(1+t)/Gamma(1-t)`. Away from the poles its symbolic factorization is

`B=pi*(1/u+1/w)*F(u,w)*R(u)*R(w)/R(u+w)`,

`F(u,w)=((1-v)*(2-v)*(3-v)*(4-v))^2/
         ((1-u)^2*(2-u)^2*(1-w)^2*(2-w)^2)`.

The Gamma quotient is one through degree two: the logarithm of `R` is odd, and its linear terms cancel in `log R(u)+log R(w)-log R(u+w)`. The rational jets are

`F(0,0)=36`, `F_u=F_w=-42`, `F_uu=F_ww=73/2`, `F_uw=-107/2`.

Subtract the two complete pole functions `pi*F(0,w)/u` and `pi*F(u,0)/w` before evaluating. The predicted analytic remainder has value `-84*pi` and `u` derivative `-141*pi/4`; the latter becomes `-141*pi/8` for the original `alpha` derivative. The pole coefficient is `F(0,w)=(3-w)^2*(4-w)^2/4`, equal to the proposed general regular angular coefficient `beta^2*(beta-2)^2/64`, whose value at `beta=-6` is the proved coefficient `36`. Its `alpha` derivative at `alpha=-6` is `-21`, matching the logarithmic correction in the marked source.

**Current bridge status:** the higher original parameter family, full six-term restoration, analyticity on `alpha,beta>-8`, `alpha+beta<-2`, and the cleared source/Gamma jets are now closed below. Both original cutoff-to-jet extractions are proved below, with every logarithmic correction and clearing-factor derivative retained. The marked finite part and its ratio follow from that original-source bridge. Fractional number-of-screenings continuation and the physical mixed Ward law remain open.


## Closed original marked plane cutoff

`formal/GaloisForLFunctions/RHTower/FZZCigarCubicMarkedScreeningCutoff.lean` retains the actual `fzzScreeningPlaneMarkedCutoff (-6) (-6) T U`. Compact polar rectangles admit the two marked angular integrals before Fubini. Near zero the original `log|z|` insertion gives the singular radial mark `log(r)*A_3(r)`; reflection at one gives the distinct regular angular mark `M_3(r)`. The fixed exterior is admitted directly by `|log t|<=t+t^(-1)` and the two neighboring original power kernels `K(-5,-6)` and `K(-7,-6)`.

The two compact annuli and admitted exterior cover every original finite cutoff domain. For small independent radii their disjoint union equals that domain, so both local limits assemble without changing either subtraction:

`marked_cutoff(T,U)+2*pi*P_singular(exp(-T))+2*pi*P_regular(exp(-U))
 -> L_singular+L_regular+int_exterior log|z|*K(-6,-6)`.

This defines `fzzScreeningCubicMarkedPlaneFinitePart` by the original integrals. Its Gamma-jet value is derived independently in the closed marked extraction below. Six public statements passed clean scratch `/tmp/fzzp_cubic_marked_plane.lean`; the proof body was promoted unchanged and the umbrella is wired. The targeted leaf build passed (145 seconds for the new leaf), and global formal lint passes. All six axiom audits passed with only `propext`, `Classical.choice`, `Quot.sound`.

Public statements: `fzzScreeningCubicMarkedExterior_integrable`, `fzzScreeningCubicMarkedAnnulus_integrable`, `fzzScreeningCubicZeroMark_cutoff_limit`, `fzzScreeningCubicOneMark_cutoff_limit`, `fzzScreeningCubicMarkedPlaneCutoff_integrable`, `fzzScreeningCubicMarkedPlane_independent_cutoff_limit`.

Higher source-parameter continuation and original position-derivative identification are now closed below. The remaining mathematical chain is full screening-multiplicity/normalization continuation, an independently fixed physical phase frame, and the complete mixed replica–momentum Ward law. RH remains unproved.


### Source-remainder mechanism to test next

A direct pointwise subtraction may supply the missing higher analytic family without first assuming analyticity of a radially subtracted angular average. On `|z|<=1/2`, write `q=|z|^2-2*Re(z)`, so `|1-z|^beta=(1+q)^(beta/2)`, `-3/4<=q<=5/4`, and `|q|<=(5/2)|z|`. Subtract the degree-five Taylor polynomial in `q` at zero. Every intermediate base `1+t*q` stays at least `1/4`, so compact parameter bounds on the sixth derivative should give a uniform pointwise remainder `O(|z|^6)`. The current vector-valued `taylor_mean_remainder_bound` (Mathlib `Analysis/Calculus/Taylor.lean:390`) supplies the norm estimate; negative `q` can be handled by reflection about the expansion point.

Multiplication by `|z|^alpha` would then be absolutely integrable for `alpha>-8` in the original plane. Subtracting the entire Taylor polynomial retains the odd angular terms before integration; their circle averages vanish, while the low even terms give the three collision poles. The polynomial also contains even powers six through ten; these have admitted integrals and must be added back explicitly. They cannot be discarded. Repeat at the other puncture and retain the existing exterior.

For the parameter-analytic step, use `exp((beta/2)*log(1+q))` with a complex parameter on compact neighborhoods. Its sixth base derivative has the same positive-base bound; proving an analytic remainder under the original integral would allow the existing connected identity-theorem method after clearing the three collision poles in each parameter. This attempt is now realized by the higher original analytic family and continuation below. It does not establish full physical normalization.

## Original fifth subtraction and exponential lift

The next attack uses the actual plane position before angular averaging. Scratch
`/tmp/fzzp_higher_taylor.lean` passed cleanly with eight public source statements.
Its proof body was promoted unchanged to `FZZCigarHigherScreeningTaylor.lean`
and wired into the umbrella. The targeted leaf build passed (166 seconds for
the new leaf), and global formal lint passed. All eight axiom audits passed
with only `propext`, `Classical.choice`, and `Quot.sound`.
No new Gamma value or RH conclusion is claimed.

Put `s=beta/2`, `q(z)=|z|^2-2*Re(z)`, and
`a_j(s)=descPochhammer(j,s)/j!`. The subtracted factor is

`R(alpha,beta,z)=|z|^alpha*(|z-1|^beta-sum_(j=0)^5 a_j(beta/2)*q(z)^j)`.

For `|z|<=1/2`, `-3/4<=q<=5/4` and `|q|<=(5/2)|z|`. Expanding
`t ↦ (1+q*t)^s` on the fixed interval `[0,1]` handles both signs of `q`
without moving the Taylor interval. The base stays in `[1/4,9/4]`. Its exact
`n`th derivative is `q^n*descPochhammer(n,s)*(1+q*t)^(s-n)`; the proof uses
local positive-base differentiation, not a false global smoothness assertion
for real powers. Compactness in `(s,base)` bounds the sixth derivative uniformly
near each exponent. Taylor's bound therefore gives `|R|<=C*|z|^(alpha+6)`,
which is locally integrable in the original plane for `alpha>-8`.

The stronger integral-remainder identity is

`integral_B R(alpha,beta,z) = descPochhammer(6,beta/2) * integral_(B×(0,1]) W_alpha(z,t)*exp(beta*X(z,t))`,

where `B=ball(0,1/2)`,
`W_alpha=|z|^alpha*q^6*(1-t)^5/(5!*(1+t*q)^6)` and
`X=log(1+t*q)/2`. The weight is nonnegative on the original product measure;
the descending factorial is retained, including its sign and zeros. The same
sixth-order domination proves joint integrability before Fubini, at every real
`beta` and every `alpha>-8`. The signed exponential-moment theorem then proves
real analyticity in `beta`. Multiplication by `exp(delta*log|z|)` shifts `alpha`
inside its open integrability interval and proves analyticity in the singular
exponent. This avoids the proposed complex-parameter detour for separate real
analyticity. Reflection admits the subtraction at the other puncture.

### Remaining polynomial and pole assembly

The original full finite part is not the remainder alone. The current cosine
integral recurrence (`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`,
`integral_cos_pow`) and the corpus's admitted cosine moments give a direct
proof of the complete angular polynomial, now closed below. Its coefficient list is

`c0=1; c1=a1+2*a2; c2=a2+6*a3+6*a4; c3=a3+12*a4+30*a5; c4=a4+20*a5; c5=a5`,

with `a_j=a_j(beta/2)`. The audited symbolic simplification gives
`c1=beta^2/4` and `c2=beta^2*(beta-2)^2/64`. Restore all six integrated terms
`2*pi*c_k(beta)*(1/2)^(alpha+2*k+2)/(alpha+2*k+2)`, not only the three poles.
The terms `k=3,4,5` have admitted denominators for `alpha>-8` and contribute
finite values. These coefficient and restoration identities are now verified
in Lean; the pole-cleared whole source and its Gamma jets are now closed
below. Both original unmarked and marked extractions are now proved.

Clear `A(alpha)=(alpha+2)*(alpha+4)*(alpha+6)` at both punctures. The existing
`FZZCigarPlaneScreeningGammaContinuation.reciprocal_gamma_analytic` proof uses
the actual entire reciprocal Gamma function; no assumption excluding its zeros
is required. The candidate cleared Gamma family is

`64*pi*Gamma(-alpha/2-beta/2-1)*Gamma(4+alpha/2)*Gamma(4+beta/2)/(Gamma(-alpha/2)*Gamma(-beta/2)*Gamma(2+alpha/2+beta/2))`.

Its numerator arguments are positive on `alpha,beta>-8`, `alpha+beta<-2`.
The complete original polynomial and exterior assembly, followed by two
real analytic identity arguments from the ordinary chamber, is now proved
below.
The original unmarked cutoff is now identified with its cleared jet and has
value `-84*pi`. The marked cutoff-to-jet bridge now gives `-141*pi/8`.
Fractional screening multiplicity, full normalization, independent phase frame,
and the complete Ward producer remain open.

### Current-source search and paper intake

Four current-corpus searches covered the uniform Taylor mechanism, affine-power
derivatives, signed exponential analyticity, and constant-coefficient circle
integration. All returned partial generation `823353`; their candidate and
method lists were inspected. The circle search reported semantic and reranking
deadlines and no ingredient set. Partial hits do not establish absence of a
stronger theorem. The useful verified mechanisms are the current
`BourgainTaylorRemainders` local affine derivative proof, `PolynomialPowerFiniteDifference`
Pochhammer Taylor evaluation, Mathlib's mean and integral Taylor remainders,
and the actual signed-weight proof in `FZZCigarSubtractedScreeningAnalytic`.
The new scratch discharges their source-specific domains and integrability.

Broad recent-paper searches used interpolation, cocycle, and regularity.
[Greedy sampling designs via reduced basis methods](https://arxiv.org/abs/2609.01578),
1 September 2026, works with RKHS kernel and width-decay assumptions; its
abstract does not identify this source remainder or produce the missing Ward
law. [Stability Landscape in Wave-Packet Scattering](https://arxiv.org/html/2607.21578v1),
23 July 2026, retains regularity requirements in its scattering stability
analysis; no source identification was obtained from the inspected introduction.
[Interactions between quantitative rectifiability, singular integrals, and boundary value problems for harmonic functions](https://arxiv.org/abs/2607.16457),
revised 21 July 2026, surveys geometric hypotheses for singular integrals and
harmonic boundary problems. Its abstract supplies no substitute for the
original screening-polynomial restoration. No theorem from these papers is
assumed in the Lean proof.

## Closed original polynomial restoration

Scratch `/tmp/fzzp_higher_taylor_restoration.lean` passed cleanly with seven
public source statements. The proof body was promoted unchanged to
`formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningRestoration.lean`
and wired into the umbrella. Global formal lint and the targeted leaf build
(99 seconds for the new leaf) passed. All seven public theorems passed the
complete axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`.

The current cosine primitive and its recurrence prove the five nonconstant
moments of `q=r^2-2*r*cos(theta)` directly. They give the complete six-term
angular polynomial specified above, with both pole coefficients
`c1=beta^2/4` and `c2=beta^2*(beta-2)^2/64`. Every coefficient is real analytic
in `beta`. These coefficient and angular identities are now Lean-checked.

For `alpha>-2`, the polynomial weighted by `|z|^alpha` is integrable on the
original half-radius disk. In polar coordinates, its density is
`r^(alpha+1)*T_beta(circleMap(0,r,theta))`. The polynomial factor is bounded
on the compact radius-angle rectangle; the radial power is integrable at zero.
This proves product admission before Fubini. Polar change of variables,
the complete angular identity, and the admitted monomial primitives prove

`integral_B |z|^alpha*T_beta(z) = 2*pi*sum_(k=0)^5 c_k(beta)*(1/2)^(alpha+2*k+2)/(alpha+2*k+2)`.

Adding this exact original polynomial integral to the fifth remainder gives
the original local position integral. All finite terms of degrees six, eight,
and ten remain. The displayed quotients at their poles are not asserted to be
finite-part values.

### Next pole-cleared source

The next source uses the admitted higher remainder and an explicitly cleared
counterterm. Set `A(alpha)=(alpha+2)*(alpha+4)*(alpha+6)`. In the first three
terms cancel the appropriate factor algebraically before defining the pole
value: the remaining factors are `(alpha+4)*(alpha+6)`,
`(alpha+2)*(alpha+6)`, and `(alpha+2)*(alpha+4)`. In the last three terms retain
`A(alpha)/(alpha+2*k+2)`; their denominators remain strictly positive for
`alpha>-8`. Multiply this first local cleared term by `A(beta)`, add its
reflection, and add `A(alpha)*A(beta)` times both local remainders and the
original exterior. This construction should retain the actual pole-line values
instead of setting them to zero by totalized division.

The already-read `FZZCigarPlaneScreeningGammaContinuation` uses two real
analytic slices: first fix `-2<beta<0` and continue in `alpha` from a genuine
ordinary neighborhood; then fix `alpha<-2` and continue in `beta` from a
neighborhood of `-1`. Replacing the lower bound `-3` by `-8` is now supported
by the proved higher local remainder. The exact original restoration above
supplies the new ordinary source identity. The pole-cleared source and all its Gamma jets are now proved below.
The identification with the original marked finite-part cutoff is now closed by the extraction below.

### Current restoration search

The deep/all-view cosine query returned partial generation `826581` without
tool errors; all candidate and method names were inspected. Its harmonic-cosine
candidate in `CosinePolynomialPurchaseCap` was read. The present proof uses
the current direct cosine-power primitives, avoiding an additional Chebyshev
conversion. The continuation query returned partial generation `826734`, with
a reranking deadline; its candidate and method names were inspected. The
useful identity method is already instantiated by the original FZZ continuation
module, whose two-slice proof was read.

Broad gluing, renormalization and duality searches did not reliably return the
requested June–September 2026 window, including after date refinements; the
direct sorted arXiv search endpoint returned a cache miss. Primary abstracts
for [rank-one invariant random subgroups](https://arxiv.org/abs/1612.09510)
(2016) and [N=2 dualities](https://arxiv.org/abs/0904.2715) (2009) were read.
The former constructs different rank-one geometric families; the latter
assembles strongly interacting superconformal theories. Neither abstract
identifies this fixed source or its missing complete Ward law. These dates
are outside the preferred window; no recent result or imported proof premise
is inferred from them.

## Closed higher whole-source continuation

The explicit source construction passed scratch in
`/tmp/fzzp_higher_cleared_source.lean` and is now in
`formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningGammaContinuation.lean`.
Ten public data-only statements prove equality with the higher cleared Gamma
family on the full domain `D: alpha,beta>-8, alpha+beta<-2`,
including all three collision lines at each puncture. The proof starts from
the original local restoration and the admitted whole-plane Beta integral.
Three numerator Gamma recurrences on each side give the factor `64*pi`.
The reciprocal Gamma factors remain analytic at their zeros.

The two-slice argument extends farther than the originally proposed negative
square. First fix `-2<beta<0` and continue in `alpha` from an ordinary open
interval. Next fix `alpha<-1` and continue in `beta` from a neighborhood of
`-1` lying below `min(0,-2-alpha)`. Every point in `D` has either `alpha<-1`
or `beta<-1`; reflection covers the other case. The proved positive chart
uses `alpha=-8+14*exp(u)/(1+exp(u)+exp(v))`, with the symmetric formula for
`beta`. Its inverse uses `log((alpha+8)/(-2-alpha-beta))` and its reflection.

Local equality of the cleared functions identifies every mixed iterated
derivative, including every order at `(-6,-6)`. This closes the cleared
source/Gamma jets. The original unmarked finite-part cutoff comparison now closes below, retaining
every finite term and both clearing-factor derivatives. The marked comparison
still requires the original differentiated remainder and pole-residue terms.

The umbrella is wired. The targeted leaf build passed in 331 seconds and
global formal lint passed. The new leaf is clean; the build replayed existing
dependency warnings. The scratch initially reported three unreachable `ring`
tactics, which were removed before the successful leaf build. All ten public
statements passed the complete axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`.

### Closed Gamma-unit factorization and next finite-part extraction

Set `a=alpha+6`, `b=beta+6`, and `v=(a+b)/2` near the cubic collision.
The inspected Gamma recurrences rewrite the remaining transcendental unit as

`U(a,b)=Gamma(1-v)*Gamma(1+a/2)*Gamma(1+b/2)/(Gamma(1+v)*Gamma(1-a/2)*Gamma(1-b/2))`.

All arguments are positive near the origin. The eight public statements in
`FZZCigarHigherScreeningGammaUnit` now pass mathematical scratch: `U(0,0)=1`,
both first axis derivatives, both second axis derivatives and the mixed second
derivative vanish. The exact local factorization `H=Q*U` is proved first for
the cleared Gamma family and then for the actual cleared original source,
including the collision point. The rational mixed jets are `Q_ab(0,0)=-12288*pi` and
`Q_aab(0,0)=16176*pi`; the actual original cleared source has the same values.
The umbrella is wired. The expanded eight-statement targeted final leaf build
and global formal lint passed. The leaf build reports 39 seconds for the changed
module, with tactic-style warnings; its one unused simplifier argument was
removed before promotion. No numerical Gamma evaluation is used.

The separate original-source extraction now closes below. Writing
`A(-6+a)=8*a-6*a^2+a^3`, its proved unmarked relation is

`partial_alpha partial_beta H(-6,-6)=64*FP-6912*pi`.

The proof retains the original local remainder, exterior and every restored
polynomial term, then matches the independently removed cutoff limit. Merely
dividing the cleared identity at the collision point cannot establish it.
The marked extraction retains the derivative of each local residue and
the original logarithmic cutoff corrections; this extraction and its value are now proved below.

The completed proof uses direct parity: set
`L(t)=log Gamma(1+t)-log Gamma(1-t)`. This function is odd by its definition,
and is analytic near zero because both Gamma factors are positive there.
Thus `L''(0)=0`. The logarithm of the unit is
`L(a/2)+L(b/2)-L((a+b)/2)`, whose first derivatives cancel and whose second
derivatives vanish. Exponentiation then gives the required unit jets. The
current corpus's `SlepianKernelScaledFubini.even_prolateSLAction` explicitly
uses `deriv_comp_neg` and differentiation of a reflection identity; its proof
was read as the parity mechanism. The actual Gamma source specialization
is now proved; the original marked finite-part extraction is also closed below.

### Continuation search and paper intake

The deep/all-view continuation query returned partial generation `844002`
without tool errors and a proposed, unverified Gamma-recurrence ingredient
set. All twenty candidate and twenty method names were inspected. The actual
`SeamTwoLatticesArchimedeanResidue.GammaR_recurrence` was read; its shifted
Gamma recurrence has an explicit nonzero argument obligation. The present
source proof instead discharges positivity at each of its three ordinary
Gamma shifts. The hybrid/all-view finite-jet query returned partial generation
`857720`, with background refresh unfinished and no tool errors. Its complete
candidate and method lists were inspected. `GammaDifferentialFE.iteratedDeriv_residue_of_factor`
and `AdS2RenormalizedScalarClockParity.tendsto_simplePoleProduct_sub_principalPart`
were read; both retain the principal factor and differentiated regular term,
and neither by itself identifies the original cubic cutoff.

The deep/all-view reflected-unit query returned partial generation `869214`
with semantic/Qdrant deadlines and unfinished filtering and refresh. Its
candidate and method lists were inspected. The selected direct parity method
comes from the actual derivative-reflection proof cited above. No absence
claim follows from these partial searches.

Broad arXiv searches used resonance, sewing, residue, monodromy, fusion,
coaction, factorization and cocycle, with the preferred June–September 2026
window and date refinements. Many results were empty or older than requested.
[Fundamental Mathematics in the Age of AI](https://arxiv.org/abs/2608.12816),
revised 29 August 2026, is an overview of mathematical understanding and
institutions; its inspected abstract supplies no source or Ward theorem.
[The non-Abelian X-ray transform on surfaces](https://arxiv.org/abs/2006.02257),
revised 26 January 2022, uses loop-group factorization to reduce to a unitary
setting on simple surfaces. Those geometric assumptions do not identify the
present fixed FZZ source or its phase frame. Neither paper supplies a premise
of the Lean proof; the latter lies outside the requested recent window.

The rational factor now proved near the cubic origin is

`Q(a,b)=64*pi*v*((v-1)*(v-2)*(v-3)*(v-4))^2/((1-a/2)*(2-a/2)*(1-b/2)*(2-b/2))`,

with `H(-6+a,-6+b)=Q(a,b)*U(a,b)`. Since `Q(0,0)=0`, unit
flatness through order two isolates the cleared jets through order three
in `Q`. The derivative product-rule transfer is now proved in Lean:
`H_ab=-12288*pi` and `H_aab=16176*pi`. For the original mark in the
first exponent, the corresponding extraction target is

`H_aab=128*markedFP-96*FP+10368*pi`.

The constant corrections in the proposed cutoff extraction come from the
cubic clearing factors and the local residue coefficients. The cleared source
jet values and the original unmarked cutoff-to-jet comparison are proved.
The marked comparison and complete source extraction are now proved below, so the finite-part value follows.

The current Mathlib theorem
`Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one`
(`Analysis/SpecialFunctions/Gamma/Beta.lean:501`) was read. It proves the
reciprocal recurrence at every complex argument, including zero. This supplies
a direct route to the five reciprocal shifts in the proposed rational
factorization while retaining the collision point. All four unit-flatness
and factorization statements passed `/tmp/fzzp_higher_gamma_unit.lean`.
The exact rational second and third mixed derivatives passed
`/tmp/fzzp_higher_rational_jets.lean` cleanly. Their transfer to the original
cleared source then passed `/tmp/fzzp_higher_gamma_source_jets.lean` and is
promoted into the same leaf. This uses the actual local factorization and the
axis derivative `W(a)=(L'(0)-L'(a/2))/2`. Write `X(a)=Q(a,0)`. The correction
to the right derivative is `C(a)=X(a)*W(a)`. Local analyticity admits every
differentiation; `X(0)=W(0)=W'(0)=0` forces `C'(0)=C''(0)=0`. Two explicit
product-rule steps therefore transfer both rational mixed values to the
original source. No finite-part cutoff value is assigned by this argument.


The mixed-product deep query returned partial generation `873258`, with local
semantic/reranking deadlines and no proposed ingredient set. Its complete
candidate and method lists were inspected. The source proof in
`HedenmalmCenterMixedLocalThreePoint` supplies the explicit derivative-product
method; `HedenmalmCenterMixedFourthJetCusp` supplies its iterated version.
The Gamma logarithm uses local analyticity, so the stronger entire-function
premise in `SignedReflectionParity` is not imported.

Broad searches also used transgression and renormalization.
[Renormalization group bounds on Araki relative entropy](https://arxiv.org/html/2609.07277v1),
submitted 7 September 2026, was inspected in the original paper. Its
probabilistic entropy identity assumes a stochastically positive KMS system,
a sharp-time perturbation in `L^(2+epsilon)`, and exponential integrability.
Its entropy bound additionally requires a multiscale curvature criterion.
These are not yet identified for the fixed FZZ source and independently fixed
phase frame; the bound alone does not force Ward saturation. No premise is
imported from this paper.


The original-cutoff deep query returned partial generation `873783`, no tool
errors, and unfinished semantic indexing and source refresh. All twenty
candidate and twenty method names, its proof idea and its proposed ingredient
set were inspected. Reading `LocalExtensionQuadraticRateRigidity` showed that
its poles and residues are finite spectral-gap data; the generated transfer
does not identify the screening cutoff. `SelbergScatteringCuspSubtraction`
retains the original source minus its principal cutoff, but also supplies no
cubic finite-part identity. The original angular cutoff and full-polynomial
restoration already available here remain the applicable starting point.

For the next original local comparison, the full quintic angular polynomial
at exponent `-6` has coefficients `(1,9,36,-460,-405,-21)`. Consequently the
angular average of the integrable fifth remainder differs from the previously
admitted cubic angular remainder by `460+405*r^2+21*r^4`. Integrating this exact
difference on the original half disk gives the now-proved identity

`CubicLocalFP = integral_ball R5(-6,-6) - 10993*pi/64 + 72*pi*log(1/2)`.

This original-integral comparison passed mathematical scratch and is promoted
in `FZZCigarCubicFinitePartExtraction`. It retains all three integrable
polynomial terms. Joint polar admission precedes Fubini and the comparison
with the already proved independent cutoff limit.


A useful refinement of the next unmarked extraction is now explicit. Let
`Rsum` denote both admitted fifth-remainder integrals plus the original exterior
at `(-6,-6)`. Differentiating the complete source definition proves

`H_ab = 64*Rsum + 16*deriv (fun alpha => ClearedCounterterm(alpha,-6)) (-6)`.

The six radial derivatives give the counterterm derivative
`-14449*pi/8 + 576*pi*log(1/2)`. Together with the original half-disk comparison
above, this is exactly `H_ab=64*FP-6912*pi`. This derivation needs only the
already admitted separate analyticity of the two local remainders, the original
exterior and the restored counterterms; no derivative of an unregularized
singular integral is introduced. Both displayed extraction steps passed Lean
scratch and are promoted in the new leaf; its targeted final build and global formal lint passed.


## Closed original cubic cutoff value

`formal/GaloisForLFunctions/RHTower/FZZCigarCubicFinitePartExtraction.lean`
contains six public data-only statements, all passed mathematical scratch:

- `fzzScreeningFifthAngularPolynomial_cubic` retains the complete six-term polynomial.
- `fzzScreeningCubicLocalFinitePart_eq_fifthRemainder` identifies the original half-disk finite part.
- `fzzScreeningCubicPlaneFinitePart_eq_fifthRemainders` retains both punctures and the original exterior.
- `fzzScreeningHigherClearedSource_cubic_second_extraction` proves `H_ab=64*FP-6912*pi`.
- `fzzScreeningCubicPlaneFinitePart_value` proves `FP=-84*pi`.
- `fzzScreeningCubicPlane_independent_cutoff_value` gives this value as the limit of the actual original cutoff with both punctures removed independently.

The proof first admits the polar product using the uniform original sixth
remainder bound. Its finite angular tail integrates to `8177/128` before the
polar factor. The actual exterior has a positive weighted-measure exponential
representation, so neighboring admitted original powers give local parameter
analyticity. Exact differentiation of all six cleared radial primitives gives
`countertermSlope(-6)=-14449*pi/8+576*pi*log(1/2)`. Both clearing factors vanish
with derivative eight; the mixed response is therefore `64*Rsum+16*countertermSlope`.
Combining the original cutoff comparison with the already proved source jet
`H_ab=-12288*pi` fixes the value, with no numerical experiment or assigned
special-function value at a singular endpoint.

The umbrella is wired. The targeted final leaf build passed (232 seconds for
the new leaf), and global formal lint passed. The scratch proof is clean. The marked value is now proved below. Screening-count
continuation, complete physical normalization, independent phase frame and
full mixed Ward producer remain open.

### Next marked extraction

The existing original marked cutoff retains distinct singular-factor and
regular-factor local terms. Differentiating the full binomial recurrence gives
the next exact coefficient targets at `beta=-6`:

`(c0',c1',c2',c3',c4',c5')=(0,-3,-21,788/3,1779/8,459/40)`.

These coefficient derivative values are now proved in the original marked-remainder and marked-source-value leaves below.
The singular local derivative must retain `log(r)` times every finite Taylor
term. The reflected regular local derivative must subtract the differentiated
Taylor polynomial before integration. The existing integral Taylor lift gives
a candidate admission mechanism: differentiate both its parameter prefactor
and exponential weight, retaining the logarithmic lift insertion. Equality
with the original marked cutoff now yields
`H_aab=128*markedFP-96*FP+10368*pi`. This bridge proves the
marked value `-141*pi/8` and normalized position-mark ratio `47/224` below.

### Original-extraction search intake

The deep polar query returned partial generation `874090`, with semantic
indexing and source refresh unfinished and no errors. All twenty candidate
and twenty method names and its generated ingredient set were inspected.
`LebesguePolarIntegral.integral_polar_mul` requires an already separated
radial/angular integrand; this does not describe the original remainder before
angular integration. The original indicator-polar transport in `CauchyPompeiu`
and the existing screening modules supplies the applicable mechanism.
`DeningerRadialKahlerTrace` is radial and does not replace the original source.

The deep cleared-coefficient query returned partial generation `874107`, with
semantic indexing, reranking and refresh unfinished and a reranker deadline.
Its complete candidate/method lists and ingredient set were inspected.
`HadamardFinitePart.cutoffFinitePart_eq` and its Suzuki wrapper preserve the
endpoint logarithm for a Cauchy kernel. They support retaining the finite
boundary contribution but do not identify the cubic screening source. The
current Mathlib explicit finite-product and finite-sum derivative rules were
read and the latter is used in the original counterterm derivative.

Broad recent arXiv searches used defect and resolvent.
[Countable IET Models and Defect Sets for Interval Translation Maps](https://arxiv.org/abs/2609.01670),
submitted 1 September 2026, was inspected at its original abstract. Its finite
or countable models retain a branch defect measure and require invariant
nonatomic probability and finite or null defect-support conditions. These
premises are not identified for the fixed FZZ source; no cutoff or Ward theorem
is imported from the paper. No absence claim follows from either partial search.

## Closed original marked remainder derivatives

The next scratch `/tmp/fzzp_higher_marked_remainder.lean` attacks both
original local parameter derivatives. Write `R5(alpha,beta,z)` for the
admitted fifth subtraction, `T5(beta,z)` for its full polynomial, and
`P(beta)=descPochhammer(6,beta/2)`. The regular insertion is defined before
integration as

`|z|^alpha*(log|z-1|*|z-1|^beta - d_beta T5(beta,z))`.

The singular insertion is `log|z|*R5(alpha,beta,z)`. Neighboring original
powers admit its logarithmic moment. For the regular insertion, differentiate
the exact pointwise Taylor integral remainder on its original interval.
Both `P'(beta)*int W exp(beta X)` and `P(beta)*int W X exp(beta X)` survive.
The existing joint exponential admission gives the marked product integral;
Fubini then identifies its marginal with the original pointwise regular
insertion. This proves admission before exchanging the plane integral and
parameter derivative, without introducing an unregularized divergent integral.
The initial scratch exposed measurability unfolding and function-elaboration
issues; the second exposed an unreachable simplifier and universe annotations
in scratch name checks. All eight expanded statements passed scratch. The
final leaf `FZZCigarHigherMarkedRemainder.lean` passed its targeted build
(21 seconds); the umbrella is wired. An unused scratch simplifier argument was
removed before promotion. Global lint initially found an unrelated concurrent
unwired `ThetaCuspHawkingBMRetardedPulseClock`; after its owner wired that leaf,
the repeated global lint passed.

The exact differentiated cubic Taylor polynomial has coefficients
`(0,1/2,-7/4,47/12,-57/8,459/40)` in powers of
`q=|z|^2-2*Re(z)`. Its proved full angular polynomial is

`-3*r^2-21*r^4+(788/3)*r^6+(1779/8)*r^8+(459/40)*r^10`.

These retain the finite radial powers needed for the marked local comparison.
The actual exterior derivative and the sum of all three original remainder
integrals are closed in the same leaf. The marked finite-part value is derived in the later source-value leaf below.

Public statements: `fzzScreeningFifthSubtracted_singularMark_integrable`,
`fzzScreeningFifthSubtracted_singularMark_hasDerivAt`,
`fzzScreeningFifthRegularMark_integrable`,
`fzzScreeningFifthSubtracted_regularMark_hasDerivAt`,
`fzzScreeningFifthTaylorMark_cubic`,
`fzzScreeningFifthTaylorMark_cubic_circleAverage`,
`fzzScreeningCubicExteriorMark_hasDerivAt`, and
`fzzScreeningCubicOriginalRemainders_hasDerivAt`.

### Marked-derivative search intake

The deep original-remainder query returned partial generation `874218`, no
errors, and a proposed log-Taylor/shift ingredient set. Source inspection of
`HurwitzShiftTaylor.shiftRemainder_eq` shows an exact finite-sum rearrangement,
not a parameter-derivative interchange. The sphere-packing `I4` hit is an
interval-to-set-integral conversion; it does not supply the missing domination.
The admitted signed exponential-moment proof in the existing first-strip
`FZZCigarContinuedScreeningMark` does transfer to the higher original singular
remainder. Its pointwise shift and neighborhood admission are rederived.
The installed parametric-integral and MGF derivative signatures were inspected.

The deep angular-coefficient query returned partial generation `874253`, no
errors; source refresh remained pending. Its proposed average-derivative
transfer requires matching the actual parameter. The BM full-circle proof
uses a common compact bound on the parameter derivative. The Böttcher
`hasDerivAt_circleAverage` instead differentiates the radius, so it cannot be
substituted for exponent differentiation. Exact finite polynomial integration
is used for the differentiated cubic Taylor term.

Broad arXiv searches used `transgression` and `intertwining`.
[Abanov–Cappelli, June 2026, revised July](https://arxiv.org/html/2606.18779v2),
sections 5.5 and 5.5.2, retain transverse constitutive corrections when deriving
a reduced action. Their slow-manifold construction is explicitly schematic
and relies on relaxation assumptions. It suggests checking all terms induced
by restriction before imposing a Ward variation; it supplies no FZZ phase
frame, relaxation theorem or unconditional Ward identity.
[Caputo–Quattropani–Sau, September 2026](https://arxiv.org/html/2609.10450v1),
sections 1.4.1–1.4.3, use an actual stochastic intertwining and a positive
semigroup to turn variance contraction into a spectral bound. The present
positive Taylor auxiliary weight is not such a semigroup or intertwining.
The original negative finite part also prevents transferring its positivity
through the retained boundary terms. No spectral or Ward premise is imported.

### Exact marked extraction targets

Let `R=1/2`, `L=log R`, `J_s=int_disk log|z|*R5(-6,-6,z)`,
`J_r=int_disk |z|^-6*(log|z-1|*|z-1|^-6-d_beta T5(-6,z))`, and
`J_e=int_exterior log|z|*K(-6,-6,z)`. The next original polar comparisons are

`SingularMarkedLocalFP = J_s + pi*(36*L^2-10993*L/64+7811/192)`,

`RegularMarkedLocalFP = J_r + pi*(-42*L+650309/7680)`.

They follow on paper by retaining the exact angular tails, integrating
`r^(2k+1)*log r` with primitive
`r^(2k+2)*(log r/(2k+2)-1/(2k+2)^2)`, and retaining the existing distinct
collision primitives at `R`. Consequently the required whole-plane identity is

`MarkedFP = J_s+J_r+J_e + pi*(36*L^2-13681*L/64+962749/7680)`.

All three equalities now pass clean Lean scratch and are promoted in
`FZZCigarCubicMarkedFinitePartExtraction.lean`. The proof transports original
local L1 admission through the nonnegative polar change of variables before
Fubini, retains the full actual angular subtraction, and evaluates both
original endpoint primitives. The targeted final leaf build (104 seconds) and global lint passed.
No comparison equality is assumed as a premise.

For the explicit cleared radial term at `alpha=-6`, the second derivatives
are `32-64*L`, `8-32*L`, and `2-12*L+8*L^2` in slots zero through two. In
slot `k>=3`, put `d=2*k-4`; the derivative is
`R^d*(-12/d-16/d^2+16*L/d)`. Differentiating the complete original source
therefore gives, before substituting any finite-part value,

`H_aab = 128*(J_s+J_r+J_e)-96*RegularSource
         +8*Counterterm_aa-12*CountertermSlope+16*CountertermSlope_beta`.

The retained local constants cancel every `L` and `L^2` term and give
`H_aab=128*MarkedFP-96*FP+10368*pi`. The complete identity now passes Lean
and connects the original finite part to the already closed cubic Gamma jet.
Its marked value and ratio are proved by the source-value leaf below.


## Closed original marked cutoff-to-remainder comparison

Three public data-only statements passed clean scratch
`/tmp/fzzp_cubic_marked_finite_part_extraction.lean`:
`fzzScreeningCubicRegularMarkedLocalFinitePart_eq_fifthMark`,
`fzzScreeningCubicSingularMarkedLocalFinitePart_eq_fifthMark`, and
`fzzScreeningCubicMarkedPlaneFinitePart_eq_fifthMarks`.
Their proof body is promoted in `FZZCigarCubicMarkedFinitePartExtraction.lean`
and the umbrella is wired. The targeted final leaf build passed (104 seconds),
and global formal lint passed.

The regular finite Taylor tail integrates to `558149/15360`. Its combination
with the retained regular collision primitive produces `-42*L+650309/7680`.
The singular tail integrates to `(8177/128)*L-11651/384`; the logarithmic
primitive is continuous at zero through `r*log r`. Its endpoint combines with
the distinct singular collision primitive to produce
`36*L^2-10993*L/64+7811/192`. The whole plane retains the actual exterior
logarithmic integral and sums both local corrections exactly.

The first scratch required explicit real types for polar set intersections,
actual polar-map rewriting, and scalar continuity annotations. The second
required an associativity rewrite. The regular comparison then passed cleanly.
The expanded three-statement scratch required an explicit angular lambda and
the original volume in the two L1 annotations; the final scratch is clean.

The source-value scratch `/tmp/fzzp_cubic_marked_source_value.lean` now passes cleanly and is promoted as `FZZCigarCubicMarkedSourceValue.lean`. It starts from the actual original
cleared source and locally analytic second-product differentiation. The new
deep source-coefficient query returned partial generation `874732`, with local
retrieval/reranking deadlines and pending refresh; no absence claim follows.
The `NonlinearConstraintHorizon.secondDeriv_mul_eq` hit is a derivation-ring
identity, not a real-parameter integral derivative theorem. Installed
`iteratedDeriv_fun_mul` instead exposes the required local `ContDiffAt` premises,
which the admitted original analytic families can discharge.
The global-analytic factorization lemma has stronger everywhere-analytic
premises and is not substituted for this local source germ.

### Second-source coefficient targets

The next exact coefficient identities, derived from the six retained slots,
are

`CountertermSlope_beta(-6) = pi*(892229/960-336*L)`,

`Counterterm_aa(-6,-6) = pi*(137093/48-(14449/4)*L+576*L^2)`.

Together with the already closed first counterterm slope, they give

`8*Counterterm_aa-12*CountertermSlope+16*CountertermSlope_beta
 = pi*(3563569/60-41186*L+4608*L^2)`.

These identities now pass Lean in the source-value leaf. Substituting the proved original unmarked and marked remainder
comparisons cancels the complete logarithmic polynomial and leaves the exact
`10368*pi` mixed-jet correction. This isolates the remaining coefficient
proofs without dropping any source term.


## Closed original marked source value

Four public data-only statements in
`formal/GaloisForLFunctions/RHTower/FZZCigarCubicMarkedSourceValue.lean`
passed clean scratch and the targeted final leaf build (26 seconds):

- `fzzScreeningHigherClearedSource_cubic_third_extraction` proves the full original source identity.
- `fzzScreeningCubicMarkedPlaneFinitePart_value` proves `MarkedFP=-141*pi/8`.
- `fzzScreeningCubicMarkedPlane_independent_cutoff_value` proves the actual original independent two-cutoff limit has this value.
- `fzzScreeningCubicMarkedPlaneFinitePart_ratio` proves the position-log ratio `47/224`.

Write `R(alpha,beta)` for both admitted local fifth remainders and the original
exterior. The actual right source derivative near `alpha=-6` is
`8*A(alpha)*R(alpha,-6)+8*CT(alpha,-6)+A(alpha)*CountertermSlope(alpha)`.
The clearing factor has value zero, first derivative eight and second derivative
minus twelve. Twice differentiating this complete local analytic identity gives

`H_aab=128*R_alpha-96*R+8*CT_aa-12*CountertermSlope+16*CountertermSlope_beta`.

The proved original marked and unmarked integral comparisons cancel every
logarithmic term, leaving `H_aab=128*MarkedFP-96*FP+10368*pi`.
Substitution of the independently proved source jet `16176*pi` and original
value `FP=-84*pi` determines the marked value. The two distinct collision
primitives remain in the limit theorem. The ratio is a position-log response,
not an identified complete physical replica--momentum response.

The scratch fixes were function-shift beta reduction, explicit iterated-derivative
rewrites and explicit function arguments for the local product/sum rules.
No mathematical premise was added. The umbrella is wired; global formal lint
passed after the successful leaf build. Existing dependency tactic-style
warnings were replayed; the new leaf and final scratch were clean.

## Screening-count continuation: current source tests

The fixed-dimensional marked extraction is closed independently of this
next step. Deep continuation search `874855` inspected all twenty candidates,
twenty methods and its proposed ingredient set; coverage was partial because
semantic indexing and source refresh were unfinished, with no errors.
`BurnolDepthCompletion.ae_eq_zero_of_integer_laplace_moments` determines an
already admitted L1 density from integer Laplace samples. The current screening
integrals change dimension with their count, so no fixed density has yet been
constructed to which that theorem applies. The proposed Sonin ingredient set
requires unrelated even-subspace and constant-core identities. The bounded-jet
ODE methods require an actual differential relation not derived for this source.

The source paper's borrowed [finite-factor derivation](https://arxiv.org/html/2310.02313)
(section 3.3) first integrates an integer number of opposite-charge positions,
then matches residues to a Liouville three-point function and uses its shift
identities. It retains an unfixed phase before imposing reality and a joint
limiting prescription for compensating singularities. These are additional
source identifications; ordinary fixed-dimensional analyticity cannot supply
them. Three-position fixing requires at least two insertions in each family.

A second conjecture was that the neutral position kernel is a free Cauchy
determinant at level four. The current corpus's exact `det_cauchyMatrix` formula
shows the omitted term. On collision-free configurations with n positions of
each charge, write D for the product of all opposite-charge distances and V
for the product of all within-charge distances. The original kernel is
`V^2/D^6`, while the Cauchy determinant has squared norm `V^2/D^2`.
Thus the exact positive survivor is

`K_4 = |det(1/(z_i-w_j))|^2 / D^4`.

The residual depends on every opposite-charge pair. It cannot be silently
replaced by a one-position weight or removed from the source. The next Lean
target is this exact all-integer-count decomposition, including the totalized
collision cases; fractional count and all cutoff passage remain separate.
Under common positive dilation, the full integration density has homogeneity
`2*n*(1-(k-2)*n)`. At level four this is `2*n*(1-2*n)`; neutrality concerns
count one-half, not an integer-size determinant. This homogeneity check is a
paper calculation, not a claimed Lean continuation theorem.

Deep determinant search `874889` was partial (semantic indexing/source refresh),
with no errors. Its twenty candidates, twenty methods and ingredient set were
inspected. The neutral torus coefficients are factorial/power coefficients,
not integrals of this sphere kernel; the suggested fractional-power expansion
requires an independent asymptotic bound. Exhaustive source-text search located
the actual Cauchy determinant formula, which supplies the displayed decomposition.

Broad searches used sewing, descent, neutrality, confluence and localization,
with June–September 2026 preference. Several returned only older or empirical
work, and direct arXiv confluence search failed to fetch. The recent
[Culf–Sebbar replication descent](https://arxiv.org/html/2609.08243v1)
(8 September, theorem 1.1 and proof 4.1) requires replication identities and
modular invariance; no such source law is available here. The recent
[localized conformal prediction proof](https://arxiv.org/html/2608.06206v1)
(6 August, theorem 3 and its proof) separates local bias, calibration and
normalization errors on one common event. Its probability and regularity
hypotheses do not identify the FZZ continuum source. No Ward or continuation
premise is imported from either paper.
