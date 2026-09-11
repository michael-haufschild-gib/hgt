# FZZ-P: higher original screening collisions

- **ID:** FZZ-P-HSC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
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
- [ ] Higher parameter continuation, physical derivative identification and full source normalization.
- [ ] Dependency-closed paper proofs and data-only Lean statements, targeted build and complete axiom audit.

## Approach

For `Q(r,theta)=1-2r*cos(theta)+r^2`, let `A_m(r)` be the original normalized angular integral of `Q^(-m)`. On `0<r<1`, the current corpus proves `A_1=(1-r^2)^(-1)` through the Poisson kernel. A compact parameter–angle rectangle stays away from `Q=0`; continuous parameter derivatives have a common bound, so the proved dominated differentiation gives

`r*A_m'(r)=m*((1-r^2)*A_(m+1)(r)-A_m(r))`.

Two applications give `A_2=(1+r^2)/(1-r^2)^3` and `A_3=(1+4r^2+r^4)/(1-r^2)^5`. The latter gives the exact local expansion derived below, hence two power divergences and a logarithmic divergence at exponent `-6`. The original angular equality and remainder are now transported to the planar cutoff integral.

The other marked puncture has new terms. The original logarithmic angular coefficients at `a=-6` are now proved to be `0,-3,-21`. Their proposed general-exponent source is `1,a^2/4,a^2*(a-2)^2/64`; that whole parameter family remains to be derived and admitted. The first-strip absence of a second-collision marked correction does not extend to this depth.

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

**CONJECTURE, not Lean-proved:** with independent circular punctures at zero and one and precisely the preceding local corrections, the whole-plane finite part of `K(-6,-6)` is `-84*pi`.

This candidate comes from the original source, not a substituted special-function value at a pole. Set `f(z)=1/(z^3*(z-1)^3)`, so `K(-6,-6)=|f|^2` off the punctures. Its partial fractions are

`f(z)=-z^(-3)-3z^(-2)-6z^(-1)
       +(z-1)^(-3)-3(z-1)^(-2)+6(z-1)^(-1)`.

A single-valued real harmonic potential away from the punctures is

`U(z)=Re(1/(2z^2)+3/z-1/(2(z-1)^2)+3/(z-1))
      +6*log|z-1|-6*log|z|`.

Its proposed exact energy identity is `|grad U|^2=K(-6,-6)`. The local expansion at zero has inverse-square coefficient `1/2`, inverse-linear coefficient `3`, logarithmic coefficient `-6`, and regular constant `-7/2`. At one these coefficients are `-1/2,3,6,7/2`. In the inward flux `-int U*(partial_r U)*r dtheta`, the opposite radial powers' cross terms cancel. Each puncture should therefore contribute

`pi/(2*epsilon^4)+9*pi/epsilon^2-72*pi*log epsilon-42*pi+o(1)`.

Green's identity on the finitely punctured disk, together with vanishing outer flux, would give the stated `-84*pi`. The remaining work is explicit: verify the original energy identity, admit the multiply punctured Green formula, bound both local remainders and outer flux, and compare with the independently removed cutoff definition. The deep/all-view corpus search for the required Dirichlet-energy method is recorded below. No phase-frame or mixed Ward conclusion follows from this candidate alone.

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

The [source paper](https://arxiv.org/html/2402.00932v3) states below (3.26) that its screening integral initially uses integer `s'=1/(k-2)`; thus `k=4` requires continuation to `s'=1/2`, not merely exponent continuation of one fixed-dimensional factor. Equations (3.27) and (3.34) also retain a reciprocal-Gamma zero and a compensating singular factor. The full response therefore needs a source-derived joint continuation of multiplicity, normalization and replica insertion. Neither the present circular finite part nor its conjectured value supplies that identification.

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

**CONJECTURED ORIGINAL SOURCE VALUES, not established in Lean:** the circular finite parts should satisfy

`fzzScreeningCubicPlaneFinitePart=-84*pi`,

`fzzScreeningCubicMarkedPlaneFinitePart=-141*pi/8`.

If both identifications hold, their normalized position-mark ratio is `47/224`, hence nonzero. This would still require the complete physical source to supply its compensating contribution. Neither value is assigned by definition.

The first candidate already has the independent harmonic-flux derivation above. A second source of both candidates is the current first-strip Gamma formula, using the current `Real.Gamma_add_one` recurrence (Mathlib `Gamma/Basic.lean:409`). Write `u=(alpha+6)/2`, `w=(beta+6)/2`, `v=u+w`, and `R(t)=Gamma(1+t)/Gamma(1-t)`. Away from the poles its symbolic factorization is

`B=pi*(1/u+1/w)*F(u,w)*R(u)*R(w)/R(u+w)`,

`F(u,w)=((1-v)*(2-v)*(3-v)*(4-v))^2/
         ((1-u)^2*(2-u)^2*(1-w)^2*(2-w)^2)`.

The Gamma quotient is one through degree two: the logarithm of `R` is odd, and its linear terms cancel in `log R(u)+log R(w)-log R(u+w)`. The rational jets are

`F(0,0)=36`, `F_u=F_w=-42`, `F_uu=F_ww=73/2`, `F_uw=-107/2`.

Subtract the two complete pole functions `pi*F(0,w)/u` and `pi*F(u,0)/w` before evaluating. The predicted analytic remainder has value `-84*pi` and `u` derivative `-141*pi/4`; the latter becomes `-141*pi/8` for the original `alpha` derivative. The pole coefficient is `F(0,w)=(3-w)^2*(4-w)^2/4`, equal to the proposed general regular angular coefficient `beta^2*(beta-2)^2/64`, whose value at `beta=-6` is the proved coefficient `36`. Its `alpha` derivative at `alpha=-6` is `-21`, matching the logarithmic correction in the marked source.

**Missing bridge:** prove a higher parameter family directly from the original angular integrals, subtract its three even Taylor coefficients at each puncture, and establish the required parameter analyticity and differentiation. A uniform sixth-order angular remainder would give radial admission for `alpha,beta>-8`, with the existing exterior condition `alpha+beta<-2`. Then continue the already identified first-strip source into this larger connected domain and identify the two original finite parts with the corresponding pole-subtracted jets. The displayed Gamma algebra alone does not establish this bridge or the fractional number-of-screenings continuation. No conjectural source value is added to the universal ledger.


## Closed original marked plane cutoff

`formal/GaloisForLFunctions/RHTower/FZZCigarCubicMarkedScreeningCutoff.lean` retains the actual `fzzScreeningPlaneMarkedCutoff (-6) (-6) T U`. Compact polar rectangles admit the two marked angular integrals before Fubini. Near zero the original `log|z|` insertion gives the singular radial mark `log(r)*A_3(r)`; reflection at one gives the distinct regular angular mark `M_3(r)`. The fixed exterior is admitted directly by `|log t|<=t+t^(-1)` and the two neighboring original power kernels `K(-5,-6)` and `K(-7,-6)`.

The two compact annuli and admitted exterior cover every original finite cutoff domain. For small independent radii their disjoint union equals that domain, so both local limits assemble without changing either subtraction:

`marked_cutoff(T,U)+2*pi*P_singular(exp(-T))+2*pi*P_regular(exp(-U))
 -> L_singular+L_regular+int_exterior log|z|*K(-6,-6)`.

This defines `fzzScreeningCubicMarkedPlaneFinitePart` by the original integrals. It does not impose the conjectured Gamma-jet value. Six public statements passed clean scratch `/tmp/fzzp_cubic_marked_plane.lean`; the proof body was promoted unchanged and the umbrella is wired. The targeted leaf build passed (145 seconds for the new leaf), and global formal lint passes. All six axiom audits passed with only `propext`, `Classical.choice`, `Quot.sound`.

Public statements: `fzzScreeningCubicMarkedExterior_integrable`, `fzzScreeningCubicMarkedAnnulus_integrable`, `fzzScreeningCubicZeroMark_cutoff_limit`, `fzzScreeningCubicOneMark_cutoff_limit`, `fzzScreeningCubicMarkedPlaneCutoff_integrable`, `fzzScreeningCubicMarkedPlane_independent_cutoff_limit`.

The remaining mathematical chain is now higher source-parameter continuation and derivative identification, full screening-multiplicity/normalization continuation, an independently fixed physical phase frame, and the complete mixed replica–momentum Ward law. RH remains unproved.


### Source-remainder mechanism to test next

A direct pointwise subtraction may supply the missing higher analytic family without first assuming analyticity of a radially subtracted angular average. On `|z|<=1/2`, write `q=|z|^2-2*Re(z)`, so `|1-z|^beta=(1+q)^(beta/2)`, `-3/4<=q<=5/4`, and `|q|<=(5/2)|z|`. Subtract the degree-five Taylor polynomial in `q` at zero. Every intermediate base `1+t*q` stays at least `1/4`, so compact parameter bounds on the sixth derivative should give a uniform pointwise remainder `O(|z|^6)`. The current vector-valued `taylor_mean_remainder_bound` (Mathlib `Analysis/Calculus/Taylor.lean:390`) supplies the norm estimate; negative `q` can be handled by reflection about the expansion point.

Multiplication by `|z|^alpha` would then be absolutely integrable for `alpha>-8` in the original plane. Subtracting the entire Taylor polynomial retains the odd angular terms before integration; their circle averages vanish, while the low even terms give the three collision poles. The polynomial also contains even powers six through ten; these have admitted integrals and must be added back explicitly. They cannot be discarded. Repeat at the other puncture and retain the existing exterior.

For the parameter-analytic step, use `exp((beta/2)*log(1+q))` with a complex parameter on compact neighborhoods. Its sixth base derivative has the same positive-base bound; proving an analytic remainder under the original integral would allow the existing connected identity-theorem method after clearing the three collision poles in each parameter. This is a concrete next proof attempt, not a proved higher continuation or physical normalization.

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
below. The original finite-part extraction remains open.

Clear `A(alpha)=(alpha+2)*(alpha+4)*(alpha+6)` at both punctures. The existing
`FZZCigarPlaneScreeningGammaContinuation.reciprocal_gamma_analytic` proof uses
the actual entire reciprocal Gamma function; no assumption excluding its zeros
is required. The candidate cleared Gamma family is

`64*pi*Gamma(-alpha/2-beta/2-1)*Gamma(4+alpha/2)*Gamma(4+beta/2)/(Gamma(-alpha/2)*Gamma(-beta/2)*Gamma(2+alpha/2+beta/2))`.

Its numerator arguments are positive on `alpha,beta>-8`, `alpha+beta<-2`.
The complete original polynomial and exterior assembly, followed by two
real analytic identity arguments from the ordinary chamber, is now proved
below.
Then identify the original unmarked and marked cutoff limits with the
pole-subtracted jets. This bridge, the proposed values `-84*pi` and
`-141*pi/8`, fractional screening multiplicity, full normalization, independent
phase frame, and the complete Ward producer remain open.

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
The identification with the original marked finite-part cutoff remains open.

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
source/Gamma jets. The existing original marked and unmarked finite-part
cutoff limits still require an exact comparison retaining every finite term
and the derivatives of the clearing factors and pole residues.

The umbrella is wired. The targeted leaf build passed in 331 seconds and
global formal lint passed. The new leaf is clean; the build replayed existing
dependency warnings. The scratch initially reported three unreachable `ring`
tactics, which were removed before the successful leaf build. All ten public
statements passed the complete axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`.

### Next finite-part extraction conjecture

Set `a=alpha+6`, `b=beta+6`, and `v=(a+b)/2` near the cubic collision.
The inspected Gamma recurrences rewrite the remaining transcendental unit as

`U(a,b)=Gamma(1-v)*Gamma(1+a/2)*Gamma(1+b/2)/(Gamma(1+v)*Gamma(1-a/2)*Gamma(1-b/2))`.

All arguments are positive near the origin. The next conjecture is that `U`
has value one and vanishing first and second derivatives there. The product
has inverse reflection `U(-a,-b)=1/U(a,b)`; first-derivative cancellation
would then force the second derivatives to vanish. These assertions still
need Lean proof. They would reduce the cleared Gamma jets through degree
three to the remaining rational factors, without numerical Gamma evaluation.

A separate original-source extraction is required. Writing
`A(-6+a)=8*a-6*a^2+a^3`, the expected unmarked relation is

`partial_alpha partial_beta H(-6,-6)=64*FP-6912*pi`.

This relation must be derived from the original local remainder, exterior,
and every restored polynomial term, then matched to the independently removed
cutoff limit already proved. Merely dividing the cleared identity at the
collision point cannot establish it. The marked extraction additionally needs
the derivative of each local residue and the original logarithmic cutoff
corrections. No proposed finite-part value is promoted to a theorem here.

A more direct parity proof is now available as the next attempt: set
`L(t)=log Gamma(1+t)-log Gamma(1-t)`. This function is odd by its definition,
and is analytic near zero because both Gamma factors are positive there.
Thus `L''(0)=0`. The logarithm of the unit is
`L(a/2)+L(b/2)-L((a+b)/2)`, whose first derivatives cancel and whose second
derivatives vanish. Exponentiation then gives the required unit jets. The
current corpus's `SlepianKernelScaledFubini.even_prolateSLAction` explicitly
uses `deriv_comp_neg` and differentiation of a reflection identity; its proof
was read as the parity mechanism. The actual Gamma source specialization
and the original finite-part extraction remain to be checked in Lean.

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

The corresponding rational factor to be verified near the cubic origin is

`Q(a,b)=64*pi*v*((v-1)*(v-2)*(v-3)*(v-4))^2/((1-a/2)*(2-a/2)*(1-b/2)*(2-b/2))`,

with `H(-6+a,-6+b)=Q(a,b)*U(a,b)`. Since `Q(0,0)=0`, the proposed unit
flatness through order two would make the cleared jets through order three
come entirely from `Q`. Symbolic coefficient comparison gives the next Lean
targets `H_ab=-12288*pi` and `H_aab=16176*pi`. For the original mark in the
first exponent, the corresponding extraction target is

`H_aab=128*markedFP-96*FP+10368*pi`.

The constant corrections come from the cubic clearing factors and the local
residue coefficients. These are explicit proof targets, not audited values;
the original cutoff-to-jet comparison remains required before either
finite-part conjecture follows.

The current Mathlib theorem
`Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one`
(`Analysis/SpecialFunctions/Gamma/Beta.lean:501`) was read. It proves the
reciprocal recurrence at every complex argument, including zero. This supplies
a direct route to the five reciprocal shifts in the proposed rational
factorization while retaining the collision point. The two unit-flatness
statements are drafted in `/tmp/fzzp_higher_gamma_unit.lean`; this scratch has
not yet been checked.
