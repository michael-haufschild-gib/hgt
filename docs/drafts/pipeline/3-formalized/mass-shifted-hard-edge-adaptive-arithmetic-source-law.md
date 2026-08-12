# Mass-shifted hard-edge adaptive arithmetic source law

- **ID:** `mass-shifted-hard-edge-adaptive-arithmetic-source`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- **Statement:** Admission-depth reciprocal clearing conjugates the literal adaptive bilinear
  completed source into one cofinal reverse-Euler producer; an admitted affine amplitude proves
  the diagonal producer is pointwise sign-indefinite.

## Goal

Create the arithmetic producer missing between source-first rational--Gamma/von Mangoldt formation
and the hard-edge compactness chart.  Producer must depend on admitted amplitudes and actual degree
before aggregation.  Fixed reporters, divisor orientations, and pointwise-positive kernel
replacements are forbidden.

## Gates

- [x] 0 → 1 in-progress: source-pure, hard-edge coordinate gap isolated
- [x] 1 → 2 fully-proven: complete coefficient proof in report equations (9.3.498)--(9.3.505)
- [x] 2 → 3 formalized: targeted Lean build and axiom audit pass
- [ ] 3 → 4 publication-ready: not yet extracted as standalone paper

## Conjecture loop

1. **C1 — reciprocal clearing turns the source into a fixed hard-edge reporter.** Failed.  Euler
   reversal produces coefficient `M + N + 2`, so operator changes with combined admission depth.
   Positive survivor: exact cofinal reverse-Euler conjugacy.
2. **C2 — diagonal reverse-Euler source is pointwise positive.** Falsified exactly.  For
   `A = 1 - (y+a)X`, `a>0`, depth one clearing is `U-a`, and depth-four source equals
   `-(a+y)^2/2` at `U=(3a+y)/2`.
3. **C3 — clearing is only a coordinate renaming.** Failed hostile audit: bounded-degree reflection
   is multiplicative, removes both marked `X` factors, and conjugates the differentiated shear
   itself before the scalar source is read.  Exact inverse clearing then identifies the original
   literal rational--Gamma-minus-von Mangoldt aggregate with this producer without adding any
   functional or hypothesis.
4. **C4 — exact producer closes RH by sign.** Failed: producer is pointwise sign-indefinite.
   Remaining burden is admitted pairing control on the cofinal `N ≍ sqrt(y)` regime.

## Paper theorem

For `deg A ≤ M`, `deg B ≤ N`, set

\[
 \mathscr C_{y,M}A(U)=(\operatorname{Ref}_M A)(y+U),\qquad
 \mathscr R_{y,d}S=dS-(y+U)S'.
\]

Then

\[
 \mathscr C_{y,M+N+2}\mathfrak A(A,B)
 =\mathscr R_{y,M+N+2}
   ((\mathscr C_{y,M}A)(\mathscr C_{y,N}B)).
\]

On the diagonal, writing `S = C_(y,N) A`,

\[
 \mathscr C_{y,2N+2}\mathfrak A(A,A)
 =2((N+1)S^2-(y+U)SS').
\]

If `U_(y,d)S = Ref_d(S(U-y))`, then `U_(y,d) C_(y,d)Q=Q`; applying this inverse to
the producer gives the exact existing completed arithmetic scalar.  No limiting argument or
positivity input occurs.

## Proof

Put `R=(XA)(XB)` and `d=M+N+2`.  Existing source law gives `A(A,B)=XR'`.  Coefficientwise,

\[
 [U^j]\operatorname{Ref}_d(XR')=(d-j)[X^{d-j}]R
 =[U^j](d\operatorname{Ref}_dR-U(\operatorname{Ref}_dR)').
\]

Degree-bounded multiplicativity gives
`Ref_d R = (Ref_M A)(Ref_N B)` because `Ref_(M+1)(XA)=Ref_M A`.  Translate `U` by `y`.
Inverse clearing follows from composing translations `U+y` and `U-y`, then using involutivity of
`reflect`.  Diagonal formula is the product rule.

For the no-go, depth-one clearing of `1-(y+a)X` is `U-a`.  Direct symbolic evaluation gives

\[
 \mathscr R_{y,4}(U-a)^2\big|_{U=(3a+y)/2}=-(a+y)^2/2<0.
\]

## Theatre audit

Passed.  New theorem changes the finite-to-hard-edge representation of the actual source
polynomial and exposes its cofinal grading coefficient.  It does not classify zeros, orient a
post-aggregation scalar, or assert positivity.  Formal negative example prevents promotion into
the dead fixed-kernel route.

## Literature audit

Broad arXiv searches covered Paley--Wiener spectral gaps, de Branges point evaluation,
hard-edge varying orthogonal polynomials, nonisospectral Toda flows, Julia-normalized Padé
residues, and source-first Weil forms.  Closest external structures are:

- Suzuki, [Weil's quadratic functional and screw functions](https://arxiv.org/abs/2606.09096):
  finite-interval source forms, but no admission-depth reciprocal-clearing conjugacy;
- Connes--van Suijlekom,
  [Fourier positivity and real zeros](https://arxiv.org/abs/2511.23257): isolated ground-state
  criterion, but no adaptive arithmetic source producer;
- Brevig et al., [Point evaluation in Paley--Wiener spaces](https://arxiv.org/abs/2210.13922):
  de Branges/root orthogonality context, but no reverse-Euler completed-source law;
- Poltoratski, [A problem on completeness of exponentials](https://arxiv.org/abs/0908.2079):
  spectral-gap measure structure, but no finite-degree arithmetic conjugacy.

Follow-up searches for moving-endpoint Hausdorff and Christoffel/Toda flows found only static
truncated-Hausdorff interval structure and general continuous transformations of moment forms:

- Fritzsche--Kirstein--Mädler,
  [On the structure of Hausdorff moment sequences of complex matrices](https://arxiv.org/abs/1701.04246):
  intrinsic endpoint intervals and molecular extremals, but no completed-Xi radial connection;
- Álvarez-Fernández et al.,
  [Transformation theory and Christoffel formulas for matrix biorthogonal polynomials](https://arxiv.org/abs/1605.04617):
  Christoffel--Geronimus and Toda deformations of quasidefinite forms, but no one-weight
  complete-diagonal source law;
- Sugawa--Wang,
  [Hausdorff moment sequences and hypergeometric functions](https://arxiv.org/abs/2411.04345):
  static total-monotonicity classification, not admission-first moving reciprocal clearing.

No searched source states the exact law above or its affine sign obstruction.

## Lean artifact

- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeAdaptiveArithmeticSourceLaw.lean`
- umbrella: `formal/GaloisForLFunctions/RHTower.lean`

Principal capstones:

- `reflect_X_mul_derivative_eq_reverseEuler`
- `xiShiftedHardEdgeReciprocalClearing_adaptiveBilinearShear`
- `xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_hardEdgeLanding`
- `xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_hardEdgeLanding`
- `xiShiftedHardEdgeReverseEulerSource_affine_negative`
- `xiShiftedHardEdgeAdaptiveBilinearSource_affine_negative`

## Stronger principle

Reciprocal reflection loss, half-density degree growth, and escaping fixed-degree thresholds are
one grading connection.  Hard-edge compactification preserves source formation only through a
depth-dependent differential producer.  Finite Hankel faces remain observations; cofinal source
dynamics live in the grading coefficient.

## Complete Hausdorff-diagonal landing

A second conjecture loop tested whether reciprocal clearing only renamed the producer.
It does not.  For `j ≤ D`, inverse clearing satisfies

\[
 \mathscr U_{y,D}(U^j)=X^{D-j}(1-yX)^j.
\]

Therefore every depth-bounded source polynomial `T` obeys

\[
 L_m(\mathscr U_{y,D}T)
 =\sum_{j\in\operatorname{supp}T}
  T_j y^j\Delta^{(1/y)}_{D-j,j}(m).
\]

All terms lie on one complete scaled-Hausdorff diagonal of total degree `D`.  Applied to the
actual source, this gives a literal rational--Gamma/von Mangoldt complete-diagonal formula for
both bilinear and mixed `P^sharp` aggregates.

Reverse Euler is information-complete below depth:

\[
 [U^k]\mathscr R_{y,d}S=(d-k)S_k-y(k+1)S_{k+1},\qquad
 \deg S<d\Longrightarrow(\mathscr R_{y,d}S=0\iff S=0).
\]

The producer input has degree at most `M+N=d-2`, so no finite source information is lost.
This connects the mass-shifted producer exactly to the corpus's cofinal Hausdorff-diagonal and
Bernstein-negative-mass RH criteria.

Hostile audit: information completeness does not imply sign.  Coefficients `T_j` are mixed, and
the affine counterexample already proves no nonnegative-weight replacement exists.  Surviving
burden is admitted-cone extinction of complete-diagonal negative mass.

Additional Lean artifact:

- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeHausdorffDiagonalLanding.lean`

Additional capstones:

- `xiShiftedHardEdgeReciprocalUnclearing_X_pow`
- `momentFunctional_hardEdgeUnclearing_eq_completeHausdorffDiagonal`
- `xiShiftedHardEdgeReverseEulerSource_eq_zero_iff_of_natDegree_lt`
- `xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_completeHausdorffDiagonal`
- `xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_completeHausdorffDiagonal`

Current inverse-Hankel admission further gives the exact chamber law

\[
 \sum_j (T_{n,w})_j(w^2)^j
   \Delta^{(1/w^2)}_{2n+2-j,j}(s_{w^2})
 =2h_n(w)E_n(w)>0.
\]

This signs the adaptive aggregate, not its coordinates.  A nonpositive actual aggregate therefore
certifies failure of the `(n+2)` positive-definite Hankel chamber with no admission-mismatch
alternative.

Additional Lean artifact:

- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionHardEdgeSourceLaw.lean`

Additional capstones:

- `xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_hardEdgeLanding`
- `xiShiftedCanonicalAdmissionHardEdgeSource_completeHausdorffDiagonal_eq_jacobiEnergy`
- `xiShiftedCanonicalAdmissionHardEdgeSource_completeHausdorffDiagonal_pos`
- `not_hankelPosDef_of_canonicalAdmissionHardEdgeSource_completeHausdorffDiagonal_nonpos`

## Flat radial source connection

A further hostile loop asked whether the complete-diagonal landing is only static.  It is not.
For

\[
G_{k,r}(y)=L_y\bigl(X^k(1-yX)^r\bigr)
\]

the moving endpoint factor and shifted-moment ODE combine to give

\[
G_{k,r}'=-(k+r+1)G_{k+1,r}.
\]

Thus every channel on total degree `D` carries the same source weight `D+1`.  For fixed admitted
hard-edge polynomial `T`,

\[
F_{D,T}=\sum_jT_jG_{D-j,j}=L_y(U_{y,D}T),\qquad
F_{D,T}'=-(D+1)F_{D+1,T}.
\]

Adding one endpoint factor channelwise gives

\[
F^\partial_{D,T}=F_{D,T}-yF_{D+1,T},\qquad
\frac d{dy}(y^{D+1}F_{D,T})=(D+1)y^DF^\partial_{D,T}.
\]

Canonical inverse-Hankel admission first selects `P^sharp` and its bilinear reverse-Euler `T`.
The actual completed mixed source is exactly `F_(2n+2,T)(w^2)`, and its frozen-admission radial
derivative is `-(2n+3)F_(2n+3,T)(w^2)`.  This requires no positive Hankel chamber, so it is an
unconditional arithmetic producer rather than the chamber-conditional Jacobi sign theorem.

Hostile sign audit: `F^partial` can still carry the super-apex negative channel.  The exact open
burden is cofinal nonnegativity of this endpoint-raised current, or weaker compact boundary-atom
extinction from literal prime--Gamma correlation.

Additional Lean artifact:

- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeRadialSourceConnection.lean`

Additional capstones:

- `hasDerivAt_xiShiftedHardEdgeRadialChannel`
- `hasDerivAt_xiShiftedHardEdgeRadialAggregate`
- `hasDerivAt_xiShiftedHardEdgeRadialPrimitive`
- `xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_radialAggregate`
- `hasDerivAt_xiShiftedCanonicalAdmissionHardEdgeRadialAggregate`
- `hasDerivAt_xiShiftedCanonicalAdmissionHardEdgeRadialPrimitive`

## Actual adaptive arithmetic-source flow

Hostile audit found a necessary correction: the radial theorem freezes the admitted hard-edge
polynomial.  Actual source motion also differentiates reciprocal chart and current inverse-Hankel
admission.  For `K_ij=i+j+2`, define

\[
S_y(a,b)=\sum_{i,j}K_{ij}a_i b_j s_{K_{ij}},\qquad
J_y(a,b)=\sum_{i,j}K_{ij}(K_{ij}+1)a_i b_j s_{K_{ij}+1}.
\]

Exact moving law is

\[
S_y'=-J_y+S_y(\dot a,b)+S_y(a,\dot b).
\]

Both `S` and `J` are source-first polynomial formations.  At square mass they equal literal
rational--Gamma minus von Mangoldt aggregates.  For canonical `P^sharp` admission and its forced
inverse-Hankel velocity `V`, diagonal law is

\[
(A_n^\sharp)'=-J_n^\sharp+2A_y^{\rm bil}(V_n,P_n).
\]

At depth `D`, define radial raise `R_D` and chart drift `C_D` coefficientwise.  Exact identity

\[
J=(D+1)R_D-C_D
\]

gives canonical three-term law

\[
(A_n^\sharp)'=-(2n+3)R_{2n+2}+C_{2n+2}+2A_y^{\rm bil}(V_n,P_n).
\]

This proves frozen radial transport is not full adaptive source differentiation.  Endpoint flux
alone omits chart and admission connections.  At every physical square mass, either leading
admission determinant vanishes or full literal source law holds.  On effective branch,
monotonicity is exactly equivalent to domination of chart plus admission connection by radial
raise.

Additional Lean artifact:

- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow.lean`

Additional capstones:

- `hasDerivAt_xiShiftedAdaptiveBilinearCoefficientSourceMass`
- `xiShiftedAdaptiveBilinearCoefficientSourceMass_sq_eq_arithmetic`
- `xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass_eq_momentFunctional`
- `xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass_eq_radialRaise_sub_chartDrift`
- `hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass`
- `hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_eq_radial_add_chart_add_connection`
- `xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow_sq`
- `xiShiftedCanonicalAdmissionAdaptiveArithmeticSource_singular_or_flow`
- `deriv_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_sq_nonpos_iff_arithmetic`

## Remaining open core

This does not prove RH.  Exact effective-branch burden is

\[
2A_y^{\rm bil}(V_n,P_n)\le J_n^\sharp,
\]

equivalently chart drift plus admission connection is at most `(2n+3)` times radial raise, along
actual cofinal law `n ≍ sqrt(y)`.  Pointwise positivity is false.  Need literal prime--Gamma/null
flag structure to prove this domination, or a weaker integrated estimate excluding compact
boundary mass.  Determinant zero is separate admission-effectivity branch.

## Verification

- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedHardEdgeAdaptiveArithmeticSourceLaw.lean`: passed;
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedHardEdgeAdaptiveArithmeticSourceLaw`:
  passed (`11753/11753`);
- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedHardEdgeHausdorffDiagonalLanding.lean`: passed;
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedHardEdgeHausdorffDiagonalLanding`:
  passed (`11754/11754`);
- both six-capstone axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`;
- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionHardEdgeSourceLaw.lean`: passed;
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeSourceLaw`:
  passed (`11755/11755`);
- four canonical-source capstone axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-declaration scan: clean;
- umbrella import: present;
- `git diff --check`: passed;
- prior scoped formal lint: completed silently with no reported violation;
- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedHardEdgeRadialSourceConnection.lean`:
  passed;
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedHardEdgeRadialSourceConnection`:
  passed (`11756/11756`);
- six radial capstone axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`;
- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow.lean`:
  passed;
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow`:
  passed (`11757/11757`);
- eight adaptive-source-flow capstone axiom audits: only `propext`, `Classical.choice`, and
  `Quot.sound`;
- repository-wide formal lint currently blocked by unrelated concurrent unowned modules missing
  umbrella reachability; target modules have clean direct checks and forbidden-declaration scans.

## Log

- 2026-08-11 — corpus/no-go audit and broad arXiv search
- 2026-08-11 — exact reverse-Euler producer proved on paper
- 2026-08-11 — affine pointwise-positivity conjecture falsified and positive survivor isolated
- 2026-08-11 — unconditional Lean formalization, targeted build, and axiom audit completed
- 2026-08-11 — complete scaled-Hausdorff diagonal landing and source no-kernel theorem formalized
- 2026-08-11 — current-admission complete-diagonal/Jacobi-energy law formalized
- 2026-08-11 — unconditional flat radial connection and endpoint-raised source flux formalized
- 2026-08-12 — fully moving canonical arithmetic-source flow, chart drift, admission connection,
  singular-or-flow classification, and exact monotonicity burden formalized
- 2026-08-12 — fixed-degree actual-source zero recession and eventual positivity combined with
  full covariant flow; exact chamber secant budget and cofinal strict arithmetic domination
  formalized. Remaining obstruction sharpened to degree--mass synchronization.

## Recession-flow survivor

For every fixed `n > 0`, actual canonical adaptive source in squared-mass coordinates tends to
zero and is eventually strictly positive. Therefore strict negative derivative points occur above
every mass threshold. The full moving source law identifies these points exactly with

`admission connection < next completed source layer`.

At square mass, this is literal strict domination of the bilinear inverse-Hankel velocity/current
`P^sharp` formation by the next rational--Gamma-minus-von-Mangoldt completed source. On each
effective compact chamber, one such domination value realizes the complete source secant debt by
the mean-value theorem.

Lean module:
`RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceRecessionFlow`.

Honest residual: cofinal descent is fixed-degree. It does not force degree-changing first-contact
schedules to meet those descent sets and does not prove eventual monotonicity without normalized
`C^1` recession. Exact next target is degree--mass synchronization or uniform logarithmic-time
admission-velocity decay.

Verification:

- direct `lake env lean` check: passed;
- targeted `lake build
  GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceRecessionFlow`:
  passed (`11793/11793`);
- seven capstone axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-declaration scan and `git diff --check`: clean;
- umbrella import: present.

## Neighboring-degree Ward survivor

The difference of two consecutive norm-normalized current arithmetic sources initially contains
three uncontrolled Jacobi beta edges. Substitution of actual nonisospectral alpha flows cancels
all three. Exact remainder is

\[
E_{n+1}-E_n=
\frac12(\alpha_n+\alpha_{n+1})^2+
(\alpha_{n+1}-\alpha_n)
\left(\sum_{j<n}\alpha_j+(n+1)(\alpha_n+\alpha_{n+1})\right)
-\frac12(\alpha_n'+\alpha_{n+1}').
\]

The same equality holds literally for difference of consecutive completed
rational--Gamma-minus-von-Mangoldt sources after current admission and division by twice admitted
norm. Therefore neighboring source monotonicity is exactly one midpoint-velocity versus
gap--trace-load inequality; no beta edge remains.

For amplitude- and coordinate-completed relative sources, consecutive increment tends to exactly
one at fixed degree. Hence every finite source prefix is eventually one strict degree staircase.
This is finite synchronization only: its terminal threshold may escape with prefix length.

Lean module:
`RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceDegreeConnection`.

Capstones:

- `xiShiftedAdaptiveOrthoJacobiEnergy_succ_sub_eq_diagonalConnection`
- `xiShiftedCanonicalArithmeticSource_succ_sub_eq_midpointGap`
- `xiShiftedCanonicalArithmeticSource_succ_ge_iff_midpointConnection`
- `tendsto_relativeArithmeticSource_succ_sub_one`
- `relativeArithmeticSource_eventually_strictMono_forall_le`

Honest residual: prove midpoint-connection inequality uniformly along actual first-contact
degree--mass schedule, or prove uniform convergence of normalized source increment there. Fixed
finite staircases do not imply one global staircase.

Verification:

- direct `lake env lean` check: passed;
- targeted `lake build
  GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceDegreeConnection`:
  passed (`11794/11794`);
- seven capstone axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`;
- umbrella import: present.

## Degree-centered causal-source and trace-coupled survivor

Center Euler transport at admitted degree before forming either rational--Gamma or von Mangoldt
aggregate:

\[
E_n^0A=XA'-nA,
\qquad C_n(A)=(XA)X(E_n^0A).
\]

For monic orthogonal data, its moment is exactly causal in degree:

\[
L(C_n(P_n))
=h_n\sum_{j<n}(\alpha_j^2+\alpha_n\alpha_j+2\beta_j).
\]

Equivalently,

\[
L(C_n(P_n))
=h_n\left(\sum_{j<n}\alpha_j^2+2\sum_{j<n}\beta_j\right)
 +\left(\sum_{j<n}\alpha_j\right)L(P_nXP_n).
\]

Thus degree centering cancels the complete current/future shell
`beta_n`, `beta_(n+1)`, and `alpha_n^2`. At a singular next face it compactifies to

\[
2\mathcal L_w(C_n(P))=-2P.\operatorname{nextCoeff}\,r_n.
\]

This still required a sign for `P.nextCoeff`. The positive survivor is not a reporter or an
orientation map: insert the algebraic trace into the polynomial before arithmetic aggregation,

\[
\mathfrak T_{w,n}(A)
=2\mathcal L_w\bigl(-A.\operatorname{nextCoeff}\,C_n(A)\bigr).
\]

At every flat face,

\[
\mathfrak T_{w,n}(P)
=2(P.\operatorname{nextCoeff})^2r_n.
\]

Therefore every right-hand first crossing forces `T <= 0` with no barycenter or orientation
hypothesis. On canonical shifted-arcsine recession,

\[
\frac{w^{4n+7}}{\log w}\mathfrak T_{w,n}(P_{n,w})
\longrightarrow
\begin{cases}
1/32,&n=1,\\
\operatorname{monicScale}(n)^2\,5n^2/32,&n\ge2.
\end{cases}
\]

Hence the same literal trace-coupled producer is eventually positive at every fixed positive
degree and nonpositive at every first crossing. Relative recession margin is quadratic in degree.

Lean modules:

- `HTGeometry.DegreeCenteredOrthogonalSourceJacobiHistory`;
- `RHTower.XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource`;
- `RHTower.XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSourceRecession`.

Capstones:

- `momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory`;
- `momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_bulk_add_current`;
- `xiShiftedDegreeCenteredCompletedArithmeticSource_eq_monicRemainder`;
- `xiShiftedDegreeCenteredCompletedArithmeticSource_eq_alphaTrace_mul_monicRemainder`;
- `xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource_eq_sq_mul_monicRemainder`;
- `xiShiftedHankelFirstCrossing_traceCoupledDegreeCenteredArithmeticSource_nonpos`;
- `tendsto_scaled_canonicalTraceCoupledDegreeCenteredArithmeticSource`;
- `canonicalTraceCoupledDegreeCenteredArithmeticSource_eventually_pos`.

Honest residual: fixed-degree positivity thresholds may escape along changing-degree first-contact
schedules. Exact remaining theorem is positivity of this literal trace-coupled source along every
admissible cofinal contact schedule. Coefficientwise fixed-degree convergence is insufficient;
need a degree-uniform relative error bound or a contact-adapted compactness law.

Verification:

- direct `lake env lean` checks of all three modules: passed;
- targeted `lake build` of the HTGeometry history module: passed (`8662` jobs);
- targeted `lake build` of the RHTower recession capstone: passed (`11799/11799`);
- eight capstone axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-declaration scan: clean;
- scoped whitespace audit: clean;
- umbrella imports: present;
- repository-wide formal lint reached unrelated concurrent unowned RHTower/Sieve and one
  HTGeometry module missing umbrella reachability; none of the three modules above was reported.

## Riccati-completed trace source

The new cumulative Jacobi-flux corpus removes dependence on source recession for the positive
side. For canonical monic admission write

\[
a_n=P_n.\operatorname{nextCoeff},
\qquad \mathcal F_n=-2a_n+\alpha_n.
\]

Define, before arithmetic aggregation,

\[
\widehat C_n(P)=C_n(P)+2a_n^2P^2,
\qquad
\widehat{\mathfrak T}_{w,n}(P)
=2\mathcal L_w(-a_n\widehat C_n(P)).
\]

Coefficient `2` completes the exact Riccati product:

\[
L(\widehat C_n(P_n))
=h_n\left[
\sum_{j<n}\alpha_j^2+2\sum_{j<n}\beta_j+(-a_n)\mathcal F_n
\right].
\]

The terminal trace law gives `a_n < 0`; degree-free cumulative Riccati contraction gives
`F_n > 0`. Hence the same literal source is strictly positive throughout a complete fixed-degree
terminal ray, without evaluating its source recession.

At a flat null face `L(P^2)=0`, so the completion disappears exactly and

\[
\widehat{\mathfrak T}_{w,n}(P)=2a_n^2r_n.
\]

Every right-hand first crossing therefore still forces this producer to be nonpositive.

New capstones:

- `xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_adaptive_sub_square_add_traceSquare`;
- `riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_flux_below`;
- `momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_pos_below`;
- `xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_pos`;
- `xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_monicRemainder`;
- `xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_eq_sq_mul_monicRemainder`;
- `xiShiftedHankelFirstCrossing_traceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_nonpos`;
- `exists_xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_terminal_pos`.

Honest residual: continuity permits a sign change between first contact and terminal ray. Using
the paper-proved bounded relative terminal-entry theorem, remaining burden is compact-holonomy
zero-exclusion for this producer, not degree-uniform source recession.

Verification:

- direct `lake env lean` checks of all three extended modules: passed;
- targeted `lake build` of the HTGeometry history module: passed (`8662/8662`);
- targeted `lake build` of the RHTower arithmetic-source module: passed (`11797/11797`);
- targeted `lake build` of the RHTower recession capstone: passed (`11799/11799`);
- all nineteen centered-source, Riccati-completed, and component-rigidity capstone axiom audits:
  only `propext`,
  `Classical.choice`, and `Quot.sound`;
- forbidden-declaration scan: clean;
- tracked and untracked scoped whitespace audits: clean;
- umbrella imports: present;
- no stale Lean process remained after the audit.

## Terminal-component rigidity and degree escalation

The first zero-exclusion conjecture was overbroad. A source zero need not be excluded directly;
its location must first be classified relative to higher-block positivity. On every interval where
the shifted-Xi `(n+2)` moment block stays positive definite, corpus connection laws give

```text
canonicalFirstCoeff' > 0,
cumulativeJacobiFlux' < 0.
```

If the right endpoint has terminal signs `canonicalFirstCoeff < 0 < cumulativeJacobiFlux`, both
signs propagate backward through the whole interval. The Riccati-completed history is then
strictly positive, so its trace-coupled arithmetic source is positive throughout the complete
positive component containing the terminal chamber.

Contrapositively, a nonpositive source value cannot occur inside that component. If it occurs at
a point where the `(n+2)` block is positive, a strictly later `(n+2)`-block failure must separate
that point from the terminal component. Thus each interior source zero exports to a higher-face
gap; it is not free scalar holonomy.

New capstones:

- `xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_terminalConnected`;
- `exists_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos`;
- `exists_future_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos`.

Honest residual: iterate this degree-escalation law along the cofinal first-contact schedule and
prove exact compatibility plus local finiteness/properness/closedness of the resulting realization
tower, or isolate an admission/effectivity obstruction. The producer and its internal positive
component are now closed; higher-face staircase compactness is not.

Verification of this extension:

- direct `lake env lean` check: passed;
- targeted build of the extended arithmetic-source module: passed (`11797/11797`);
- direct check and targeted build of the recession module after extension: passed (`11799/11799`);
- all three new capstone axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`.

## Adjacent-trace absorption of cumulative flux

Further hostile loop removed cumulative flux as an independent terminal datum. On one positive
`(n+2)` block, actual inverse-Hankel first coefficients satisfy

\[
\mathcal F_n=-2a_n+\alpha_n=-a_n-a_{n+1}.
\]

Hence completed Jacobi history is

\[
\sum_{j<n}\alpha_j^2+2\sum_{j<n}\beta_j+a_n(a_n+a_{n+1}),
\]

and two negative neighboring traces force strict source positivity. Nonpositive source inside
the positive block conversely forces `a_n >= 0` or `a_(n+1) >= 0`.

### Conjecture loop

1. **Generic positive terminal component from Toda topology.** Failed. Indefinite Toda tau
   functions admit zeros and blow-ups; integrability supplies evolution, not missing sign.
2. **Ordinary Hankel positivity signs every Jacobi alpha.** Failed. This needs a shifted
   localizing Hankel form not present in finite positive-block admission.
3. **Factorial/Gamma carrier supplies sign.** Failed by existing formal no-go: fixed carrier
   reaches same singular face with opposite crossing orientation.
4. **Flux is an independent monotone scalar.** Reinterpreted and eliminated. Exact adjacent-trace
   identity shows it is bilinear admission coupling before aggregation.
5. **Next trace requires an `(n+3)` block.** Failed. Differentiating adjacent identity yields
   `a_(n+1)' = D_n - a_n' > 0` already under `(n+2)` positivity, with exact positive gap

   \[
   \sum_{j<n}\alpha_j^2+\alpha_n^2+2\sum_{j<n}\beta_j
   +2\beta_n+2(n+1)\beta_{n+1}.
   \]

Both adjacent terminal trace signs now propagate backward through one connected positive block.
Future higher-face-gap capstone has been reproved using only these adaptive traces; terminal flux
recession is no longer used.

New capstones:

- `riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_adjacentTrace_below`;
- `momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_pos_of_adjacentTrace_neg_below`;
- `adjacentTraceDissipationGap_pos_below`;
- `xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_adjacentFirstCoeff`;
- `xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_adjacentFirstCoeff_neg`;
- `current_or_nextFirstCoeff_nonneg_of_traceCoupledRiccatiCompletedSource_nonpos`;
- `deriv_xiShiftedCanonicalAdmissionFirstCoeff_succ_pos_of_add_two_posDef`;
- `xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_terminalAdjacentConnected`;
- `exists_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos_of_terminalAdjacent`.

Literature search found nearby Toda and special varying-weight double-scaling laws but no
shifted-Xi inverse-Hankel adjacent-trace theorem. Novelty status: `[NOVELTY UNVERIFIED]`.

Honest residual: prove compatibility plus local finiteness/properness/closedness of iterated
higher-face gaps on cofinal parabolic degree--mass schedule, or identify exact
admission/effectivity obstruction. Arithmetic producer, adjacent source sign, and internal
terminal-component transport are closed; tower compactness remains open.

## Canonical terminal-frontier quotient

Arbitrary higher-gap witnesses are not intrinsic. Define

\[
\mathcal B_n=\{y\ge0:H_{n+2}(y)\not>0\},
\qquad \tau_n=\sup\mathcal B_n.
\]

Far-right fixed-block positivity proves `B_n` bounded above; no rightmost zero or analytic
isolation is needed. Every nonnegative `y > tau_n` has positive `(n+2)` block. Principal-block
nesting proves `tau_n <= tau_(n+1)` whenever `B_n` is occupied. Completed-source nonpositivity
inside a positive current block supplies a later failure witness, hence

```text
w^2 < tau_n <= tau_(n+1).
```

This quotients all escalation branches to one monotone scalar sequence. Infinite branching is no
longer intrinsic. Remaining exact alternatives are frontier nonattainment, simultaneous lower-head
admission loss, or frontier separation too weak to contradict the existing quadratic parabolic
upper envelope.

New Lean capstones:

- `xiShiftedHigherBlockFailureSet`;
- `xiShiftedHigherBlockTerminalFrontier`;
- `bddAbove_xiShiftedHigherBlockFailureSet`;
- `le_xiShiftedHigherBlockTerminalFrontier_of_mem`;
- `xiShiftedHigherBlock_posDef_of_terminalFrontier_lt`;
- `xiShiftedHigherBlockTerminalFrontier_mono_succ`;
- `sq_lt_xiShiftedHigherBlockTerminalFrontier_of_traceCoupledSource_nonpos`;
- `xiShiftedHigherBlockFailureSet_nonempty_of_traceCoupledSource_nonpos`;
- `xiShiftedHigherBlockTerminalFrontier_le_succ_of_traceCoupledSource_nonpos`.

### Frontier attainment and strict-step geometry

Every source-generated frontier is positive. Since `sSup B_n` lies in closure of `B_n` and
positive definiteness persists locally, its frontier cannot be positive definite. Therefore
`tau_n ∈ B_n`; no rightmost zero or closedness premise is added.

If `tau_n < tau_(n+1)`, previous block is already beyond its frontier, hence positive definite at
`tau_(n+1)`. The new block is positive immediately to the right. Determinant analyticity forces
nonnegative boundary determinant, and Schur complement geometry yields

```text
H_(n+2)(tau_(n+1)) > 0,
H_(n+3)(tau_(n+1)) >= 0 but not > 0.
```

Every strict step is thus an admission-effective singular face. Simultaneous admission loss can
occur only on plateau `tau_n = tau_(n+1)`. Remaining route burden is plateau exclusion plus a
quantitative strict-step separation law outrunning quadratic parabolic frontier envelope.

### Odd-contact null-flag landing

Generic plateau exclusion is false: higher odd Padé contact creates an explicit finite PSD flat
plateau. If `P` is the degree-`n` monic null polynomial, defects vanish below
`2*n + (2*m+1)`, and `A = P * X^m`, then the complete visible flag
`P, P*X, ..., P*X^m` is null, `A` is a kernel vector of the size-`n+m+1` block, and the next block
is the first possible indefinite extension.

The new source producer survives this singular compactification without an inverse-Hankel
quotient:

```text
traceCoupledRiccatiCompletedSource(w, n+m, A)
  = 2 * A.nextCoeff^2 * firstOddPadeDefect(w^2, P).
```

All factors are formed before rational--Gamma/von-Mangoldt aggregation. At a genuine two-sided
crossing below `41/2`, the first odd defect is the strictly negative completed prime--Gamma moment
`L(X*A^2)`. Hence the adaptive mixed/completed `P^sharp` aggregate is nonpositive, and strictly
negative whenever `A.nextCoeff != 0`. Parity lift preserves `nextCoeff`, so the sole local
degeneracy is the original null-root barycenter zero.

This identifies, rather than hand-waves, the admission/effectivity branch: contact order, flat
plateau length, first failing extension, and source landing index are one invariant. It does not
exclude equality of global terminal frontiers.

### Nondegenerate adjacent completion

Trace zero is removable. For current and adjacent monic amplitudes `A,B`, put
`a=A.nextCoeff`, `b=B.nextCoeff` and form

```text
Qdagger(n,A,B) = QRiccati(n,A)
  + (1+a) * X*A^2
  + ((a-b)^2 - (a-b) + 1) * A^2.
```

Every term is inserted before completed rational--Gamma/von-Mangoldt aggregation. In a positive
`(n+2)` chamber, `a-b=alpha_n`, and exact orthogonality gives

```text
L(Qdagger) = norm_n *
  (sum_{j<n} alpha_j^2 + 2*sum_{j<n} beta_j + 2*a^2 + alpha_n^2 + 1) > 0.
```

No trace, flux, or terminal sign remains. On an odd-contact null flag `A=P*X^m`, all `A^2`
completion channels vanish; coefficients `-a` and `1+a` on first odd defect sum to one. Therefore

```text
nondegenerateSource(w,n+m,A,B) = 2 * firstOddPadeDefect(w^2,P)
```

for every polynomial `B`. At a genuine crossing this is `2*L_primeGamma(X*A^2) < 0`. Trace zero
and singular adjacent-admission totalization cannot erase it.

Exact residual is admission effectivity: actual adjacent admission yields strict positivity where
its chamber exists, while singular landing is strictly negative independent of missing adjacent
amplitude. Boundary audit below proves nonzero odd contact is surrounded by an open indefinite
moat, so no closed-graph extension through that face exists. Quantitative terminal-frontier
separation is mandatory.

Additional capstones:

- `xiShiftedHigherBlockTerminalFrontier_mem_failureSet`;
- `xiShiftedHigherBlockTerminalFrontier_mem_failureSet_of_traceCoupledSource_nonpos`;
- `xiShiftedHigherBlockTerminalFrontier_strict_step_effective`;
- `xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef`;
- `xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_liftedNull_eq_firstOddDefect`;
- `xiShiftedTraceCoupledRiccatiCompletedSource_liftedNull_eq_sq_mul_firstOddDefect`;
- `exists_liftedNull_traceCoupledRiccatiCompletedSource_landing_of_genuine_crossing`;
- `nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial`;
- `momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_pos_below`;
- `xiShiftedCanonicalAdjacentNondegenerateNullFlagCompletedArithmeticSource_pos`;
- `xiShiftedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect`;
- `exists_liftedNull_nondegenerateNullFlagCompletedSource_strictNeg_of_genuine_crossing`.

### Literal adaptive-bilinear identification

Source-type audit closed a terminology gap.  For every positive odd-contact lift `m`, let
`A=P*X^m` and `C=P*X^(m-1)`.  Then the new nondegenerate producer is exactly the existing literal
adaptive bilinear rational--Gamma-minus-von-Mangoldt source, after forced total-degree scaling:

```text
(2*n + 2*m + 1) * nondegenerateSource(w,n+m,A,B)
  = 2 * adaptiveBilinearCompletedArithmeticSource(w,A,C).
```

This follows because both sides land on the same first odd Padé defect with respective
coefficients `2` and `2*n+2*m+1`.  It is valid for every polynomial `B`; no adjacent inverse or
post-aggregation orientation is used.  Lift `m=0` is intrinsically order one and cannot be
represented by two nonnegative null-lift degrees.

The full producer was also expanded directly as existing adaptive mixed `P^sharp` completed source
plus four polynomial source channels, all inserted before arithmetic aggregation.

Additional capstones:

- `xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_adaptiveMixed`;
- `xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_adaptiveBilinear_of_liftedNull`.

### Deterministic finite extension exit

Every positive flat shifted-Xi face has some strictly larger principal block that is not positive
semidefinite.  Infinite-Xi-divisor exclusion supplies finite first contact.  Odd contact exits by
the lifted hyperbolic plane; even contact can fill one rank but exits in the following block.

Frontier closure proves any non-PSD block lies strictly below its fixed-degree terminal frontier.
Hence every effective flat face forces a strictly larger frontier at finite higher degree, and
every strict frontier step forces another later strict increase.  Eternal PSD plateaus are
impossible; residual obstruction is quantitative sparsity/size of strict frontier increases.

Additional capstones:

- `exists_xiShiftedMomentHankelMatrix_higher_not_posSemidef_of_flatFace`;
- `xiShiftedHigherBlock_posSemidef_of_terminalFrontier_le`;
- `lt_xiShiftedHigherBlockTerminalFrontier_of_not_posSemidef`;
- `exists_later_xiShiftedHigherBlockTerminalFrontier_gt_of_flatFace`;
- `exists_later_strict_xiShiftedHigherBlockTerminalFrontier_of_strict_step`.

### Exact arithmetic admission boundary layer

Actual adjacent inverse-Hankel admission does not extend completed source continuously through a
nonzero odd flat contact. In every positive adjacent chamber,

```text
norm_n * completedSourceMass_n
  = 2 * oddCurrent_n^2 + 2 * norm_n^2 * regularLowerHistory_n.
```

Therefore `2 * oddCurrent_n^2 <= norm_n * completedSourceMass_n` for every genuinely available
positive chamber. Hostile audit shows this cannot be specialized to an actual nonzero odd flat
contact: such a contact has no adjacent positive chamber at all.

If the monic flat relation holds and its first omitted remainder is nonzero, the first omitted
coupling is nonzero by the terminal-coordinate identity. Hankel extension rigidity then makes the
next block non-PSD at the contact. A fixed negative quadratic direction persists on a full
neighborhood by differentiable dependence of shifted-Xi moments. Hence nonzero odd contact creates
an open indefinite admission moat, not a source-mass pole. In particular it lies strictly before
the same-degree terminal frontier. Dually, any flat monic face at or beyond that closed frontier
must have zero first omitted odd remainder. Terminal-frontier admission therefore excludes odd
arithmetic contact exactly, rather than selecting its orientation.

The abstract filter coercivity theorem remains valid, but the removed flat-face specialization had
inconsistent assumptions and was theorem theatre. Source formation must restart beyond the moat on
a later admitted frontier. Remaining burden is quantitative cumulative terminal-frontier growth
plus arithmetic capture of every putative off-line contact; fixed linear reporting and
post-aggregation orientation cannot supply either.

Additional capstones:

- `norm_mul_momentFunctional_nondegenerateSource_eq_odd_sq_add_regular_below`;
- `xiShiftedCanonicalAdmissionNorm_mul_nondegenerateSourceMass_eq_odd_sq_add_regular`;
- `not_eventually_nondegenerateSourceMass_le_of_oddCurrent_survives_norm_collapse`;
- `xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_flatFace_nonzero_monicRemainder`;
- `xiShiftedHankelBoundaryMonicRemainder_eq_zero_of_flatFace_of_succ_posSemidef`;
- `eventually_xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_flatFace_nonzero_monicRemainder`;
- `xiShiftedHankelBoundaryMonicRemainder_eq_zero_of_flatFace_of_terminalFrontier_le`;
- `lt_xiShiftedHigherBlockTerminalFrontier_of_flatFace_nonzero_monicRemainder`.

### Choice-free adaptive source witness and determinant curvature

Existential negative direction has been replaced by source-first producer. For flat monic current
admission `H_(n+1)c=0`, let `gamma` be first omitted coupling, `a=s_(2n+2)`, `u=(c,0)`, and `e`
new terminal basis. Define

```text
x_gamma = u - gamma/(|a|+1) * e.
```

This vector is computed from admitted source before reflection aggregation. Exact laws are

```text
Q_y(u+t*e) = 2*t*gamma + t^2*a,
Q_y(x_gamma) = -gamma^2*(2*(|a|+1)-a)/(|a|+1)^2 < 0  if gamma != 0,
gamma^2/(|a|+1) <= -Q_y(x_gamma).
```

Canonical monic admission gives `gamma=Delta` literally. A determinant-preserving column/row
elimination proves generic two-degree curvature identity

```text
det H_(n+2) = -gamma^2 * det H_n.
```

On effective head, `det H_n>0`, so `det H_(n+2)<0` iff odd monic remainder is nonzero. Odd
Gamma--prime contact, adaptive hyperbolic direction, and signed determinant loss are one invariant
in arithmetic, vector, and scalar coordinates.

### Sharp integral-Lipschitz frontier law

Actual integral estimate now exists in Lean:

```text
|Re m_k(b) - Re m_k(a)| <= (k+1) * C_Xi * (b-a),  0<a<=b.
```

For finite Hankel direction `x`,

```text
|Q_b(x)-Q_a(x)| <= W(x)*(b-a),
W(x) = 2*C_Xi*(sum_i |x_i|)*(sum_i (i+1/2)*|x_i|).
```

Adaptive witness coefficient masses split exactly into current admission coefficients plus
terminal source amplitude `|gamma|/(|a|+1)`. No hidden matrix norm remains.

Scaling audit sharpened initial `2*(W+1)` displacement. Negative energy forces `W>0`; otherwise it
would persist into known far-right positive chamber. Since frontier failure excludes positive
definiteness, transport may land at zero energy. Exact law is

```text
y + (-Q_y(x))/W(x) <= tau_n.
```

For adaptive source witness:

```text
y + Delta^2*(2*(|a|+1)-a)/((|a|+1)^2*W(x_Delta)) <= tau_n,
y + Delta^2/((|a|+1)*W(x_Delta)) <= tau_n.
```

Open burden is now precise: cumulative lower control of this determinant-curvature/source quotient
along source-generated effective frontiers sufficient to outrun parabolic upper envelope. Producer,
orientation, finite observer, compactness, local moat, and matrix-norm questions are closed.

Additional capstones:

- `det_finiteHankelMatrix_add_two_of_monic_kernel`;
- `det_xiShiftedMomentHankelMatrix_add_two_of_flatFace_eq`;
- `det_xiShiftedMomentHankelMatrix_add_two_neg_iff_monicRemainder_ne_zero_of_head_posDef`;
- `xiShiftedOddContactAdaptiveHankelWitness`;
- `xiShiftedMomentHankelQuadratic_padTerminalZero_add_terminal_eq`;
- `xiShiftedMomentHankelQuadratic_oddContactAdaptiveHankelWitness_eq`;
- `xiShiftedCanonicalOddContactAdaptiveHankelWitness_energy_eq`;
- `xiShiftedMomentHankelQuadraticLipschitzWeight_eq_l1_mul_weightedL1`;
- `sum_abs_xiShiftedOddContactAdaptiveHankelWitness`;
- `sum_abs_mul_halfDegree_xiShiftedOddContactAdaptiveHankelWitness`;
- `xiShiftedMomentHankelQuadraticLipschitzWeight_pos_of_neg`;
- `add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier_sharp`;
- `add_oddRemainderAdaptiveEnergy_div_lipschitzWeight_le_terminalFrontier_sharp`;
- `add_oddRemainderSq_div_terminalAbs_div_lipschitzWeight_le_terminalFrontier_sharp`.
