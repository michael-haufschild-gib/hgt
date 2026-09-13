# HB: attacks on the physical selection mechanism

Owner: current core-bridge investigation. Status: **OPEN**.
Companion: [viability assessment](hb-core-bridge-viability.md) and
[source evidence](hb-core-bridge-viability-facts.md).

These attacks concern the complete physical-action bridge. They do not claim RH,
a new physical law, or a completed Lean proof. Existing declarations are identified
by source; new deductions below are explicitly **paper derivations, not formalized**.
No Lean check or build was run for them. A proof written below must not be promoted
to a certified result in the publication manuscript.

## Attack 1: can local variational symmetry select the orbit without a boundary law?

**Conjecture tested.** Source exchange and local action symmetry suffice for the
reflected full cut to vanish, even before the completed boundary pairing is known.

**Result: the proposed deduction fails.** The exact algebra exposes the missing
terms. This is a bookkeeping derivation from the corpus's cut definition, not a
physical identification or a new conservation principle.

Let X,Y be complex vector spaces, P:X x Y -> C bilinear, B:X x X -> Y symmetric
bilinear, and Delta:Y -> X linear. For fixed branches p,m put

```
f = B(p,m),   a = B(p,p)/2,   b = B(m,m)/2,
Omega(s,t) = P(Delta(s),t),
kappa(x,y,z) = P(x,B(y,z)) - P(z,B(x,y)),
R(s,t) = Omega(s,t) + Omega(t,s).
```

The corpus's phase-normalized cut is

```
C(p,m) = P(m,B(p,Delta(f))) + P(m,B(m,Delta(a))).
```

**Paper derivation P1 — not formalized.** Direct substitution gives

```
C(p,m) + C(m,p)
  = R(f,f) + 2*R(a,b)
    + kappa(m,p,Delta(f)) + kappa(p,m,Delta(f))
    + kappa(m,m,Delta(a)) + kappa(p,p,Delta(b)).                 (1)
```

Indeed, the first summand of C(p,m) is Omega(f,f)+kappa(m,p,Delta(f));
its second is 2*Omega(a,b)+kappa(m,m,Delta(a)). Exchange p,m and add.
This uses bilinearity and symmetry of B, with no cyclicity or skewness assumption.
When kappa=0 and R=0, it recovers the existing conditional swap theorem in
`ThetaCuspHawkingCubicPeierlsPolarization.lean`.

The calculation also identifies a weaker sufficient condition than global
cyclicity and global skewness: only the displayed sum must vanish on these actual
sources and their actual response jumps. It need not vanish term by term. This is
a conditional target, not a supplied source theorem.

Here kappa is an algebraic exchange defect. Identifying it with a physical
boundary expression requires the actual varying-weight and source-residual
identities; it is not automatically a pure boundary term.

**Hostile checks on the deduction, on paper only.** Neither family of defects
can be omitted from general algebra. For X=Y=C, P(x,y)=xy, B(x,y)=xy and
Delta=identity, kappa=0 but C(1,1)+C(1,1)=3. Conversely take X=Y=C^2,
P the bilinear dot product, Delta(x1,x2)=(x2,-x1), and
B(x,y)=(0,x1*y1+x1*y2+x2*y1). Then R=0. At p=(1,0),m=(0,1),
C(p,m)=3/2 and C(m,p)=0. These are algebraic counterexamples to dropping
the conditions, not models of the original Einstein equations.

**What does this mean for HB?** The completed boundary/reciprocity budget is
part of the selection problem. It cannot be erased by citing a local cubic
symmetry. Equation (1) tells an actual physical calculation which source-restricted
combination to evaluate. It does not predict its sign or value. If different
harmonic restrictions of the causal operator are used, their cross-reciprocity
terms must be retained rather than assuming the reduced operators are identical.

**Pivot.** Test an actual source-derived transpose and its retained boundary data.

## Attack 2: does a source-derived transpose furnish the physical dual state?

**Conjecture tested.** The opposite-branch density dual can be identified with a
constant-normalized fundamental physical QNM, because it reproduces the original
source coefficients.

`ThetaCuspHawkingBMSourceDensityDual.lean` supplies a precise positive input:
`densityDual_originalForcing` matches the transpose of the common radial source
operator to the original forcing, including the theta half-square and its full
Laplacian. The radial weight is w(u)=(1+u)^5/u^4.

**Result: the proposed identification fails wherever its displayed residue is
nonzero.** The same module's `densityDual_physicalMode_ads_residue` proves, for
independent source and reader copies q,r and every constant normalization c,

```
lim[u -> 0+] u^4*(dualSeed(q) - c*physicalFundamentalMode(r))
  = a^2*timeOnset(2*s,v)*Q(q,z),                              (2)
```

where u is the compact radial coordinate, s is the source branch rate, and
Q is the actual theta half-square. The theorem itself does not assert that
this coefficient is nonzero at every chosen point. The physical fundamental
mode has zero AdS value; it cannot remove a nonzero fourth-order coefficient.

**Positive survivor.** The source transpose is exact, with an explicit boundary
port. A relative pairing may retain that port instead of equating the two states.
No result here identifies the auxiliary transpose with the full physical left
state, including such a port.

**What does this mean for HB?** An algebraic adjoint construction is not enough
to validate the physical connection. The original domain and its boundary trace
are a falsifiable part of the connection. This obstruction concerns the stated
constant-normalized fundamental-state identification; it does not exclude all
augmented pairings.

**Pivot.** Determine whether retaining this port obstructs extinction or can
instead yield a legitimate oriented cancellation.

## Attack 3: does a surviving radial port prevent total boundary cancellation?

**Conjecture tested.** A retained radial port must obstruct the desired zero
of the completed boundary expression.

**Result: that inference fails.** The corpus's `dualRadialFlux_exact` gives

```
F(q,branch;a,b;v,u,z)
  = -a^2*b^2*chi(v)^2*exp(-6*v)*K(q,z)*S2(q,z)/y^2,          (3)
K = ((7*lambda-2)*Q - 2*L(Q))/8,
S2 = -L(L(Q)) + 2*L(Q),    lambda = rho*(rho-1).
```

There is no u or branch on the right. Consequently the two *oriented* radial
endpoint values cancel, F(u2)-F(u1)=0, at every pair of interior endpoints.
This consequence is **paper derivation P2, not separately formalized here**.
It requires neither endpoint value to vanish. No integrability or limiting
claim for additional angular/time variables is made by this deduction.

Using the existing `square_reflect` and lambda(1-rho)=lambda(rho), (3) also
gives F(q*)=F(q) at fixed amplitudes, time and angular point: it is FE-even.
Thus the unsigned reflection sum is 2F whereas the oriented radial difference
is zero. This is **paper derivation P3, not separately formalized here**.
No universal nonvanishing of K*S2 is asserted.

**What does this mean for HB?** Reflection sums, oriented boundary differences,
and individual fluxes are different observables. A nonzero endpoint is not a
whole-route no-go. Equally, an identically zero radial difference is not yet a
selective RH detector. The positive survivor is exact radial transport with its
port retained; identification of the completed physical orbit is still needed.

**Pivot.** Test an actual, fully oriented physical cancellation already in the
corpus against the required radiation-source polarization.

## Attack 4: can horizontal parity supply the missing selection?

**Conjecture tested.** Horizontal reflection of the actual theta source and
causal response kills the needed physical radiative pairing.

**Positive result already in the corpus.**
`ThetaCuspHawkingBMSpatialReflectionCurrent.lean` derives evenness of the full
literal scalar and native causal response under X -> -X. It proves that the
cross-eigenvalue/coexact work is odd, admits the actual physical contraction on
finite slices, and proves its integral zero. All four oriented edges of a
symmetric finite angular rectangle cancel (`rectangle_boundary_flux_zero`).
These declarations supply an actual physical sector cancellation without an
extra extinction premise.

**Failure of the extension to the full target.** The same file separately proves
`causal_coexact_work_reflection`: the coexact/coexact contraction is even. Oddness
therefore cannot be transferred to that channel. Evenness alone proves neither
its vanishing nor its nonvanishing. The complete radiative Peierls pairing has
not been identified with the odd cross-work expression by this investigation.

For comparison, bilinear reflection-invariant pairings satisfy
Omega(Tf,Tg)=Omega(f,g). If both inputs have character -1, bilinearity gives
Omega(-f,-g)=Omega(f,g), not its negative. This elementary **paper check** shows
why a cancellation with one odd factor cannot automatically kill a pairing of
two odd quadratic sources. No physical parity assignment is introduced by this
abstract check.

**What does this mean for HB?** It would be inaccurate to say that the corpus
contains no physical cancellation mechanism. It does. What remains unvalidated
is the connection of a sufficiently selective diagnostic to the complete
physical coefficient, including its even angular channels. This narrows the
next attack to the actual surviving polarization, rather than another proof
of the already-canceling odd current.

## Attack 5: does an admitted physical Green current settle the causal phase?

**Conjecture tested.** The admitted physical Hilbert-space Green identity supplies
the required zero of the phase-normalized action merely by exchanging branches.

The corpus has a stronger physical input than a formal integration by parts.
`ThetaCuspHawkingBMPhysicalPrimitiveCurrent.lean` constructs double time
primitives U and first primitives U' of the actual causal response. Its
`physicalPrimitiveCurrent_balance` proves the complete finite-time source work
equals the final-time current

```
J(U,V) = <U,V'> - <U',V>.                                   (4)
```

Spatial cancellation occurs within the admitted original operator domain. The
source includes its native remainder and all three cutoff-commutator channels.
The theorem retains J(T); it does not set J(T)=0 or identify it with the complete
metric Peierls coefficient.

**Paper derivation P4 — not formalized.** Conjugate symmetry of the existing
Hilbert inner product gives

```
J(V,U) = -conj(J(U,V)),
Re(J(U,V)+J(V,U)) = 0,
Re(-i*(J(U,V)+J(V,U))) = 2*Im(J(U,V)).                       (5)
```

The input is `inner_conj_symm` in the installed mathlib, not an assumption of a
real source. To check that the last expression need not vanish by algebra alone,
take instantaneous scalar data U=1,U'=0,V=0,V'=i. Then J(U,V)=J(V,U)=i.
This is not a claim that those data arise from the HB source.

**Result: exchange alone does not determine the required extinction.** It
selects one real component of an anti-Hermitian current. Multiplication by the
phase -i changes which component it selects. Neither (4) nor (5) permits choosing
that phase to fit the RH receiver. In addition, exchanging two current inputs
must be distinguished from FE transport of the entire original response family.
The source reflection and principal-index reversal provide a concrete route to
that transport, but no new such Lean theorem was produced here.

**Positive survivor and meaning for HB.** There is an admitted physical
source-work balance with a controlled final-time term. It is a viable starting
point for testing selection, not the finished selector. The action-to-current
identification must fix the phase, the time primitive, the cutoff restoration
and the reflected inputs before its vanishing can be used. Proving only the
easy real-part cancellation in (5) would leave the central problem untouched.

## Attack 6: does FE exchange cancel the actual tested quartic radial sector?

**[BRIDGE] tested.** Transport the existing full angular responses, then the
entire incoming SV--SV radial current, before changing its physical reader.
This extends the fixed-reader issue in V09 to an explicit quartic balance;
it is not a conjectured new physical law.

Write q* for FE reflection, s=rho-2, t=-rho-1, and

```
alpha=(2*s+1)*(2*s+2), beta=(2*t+1)*(2*t+2), s+t=-3,
S=scalar(center(q)), Q=S^2/2,
H+=fullAngularField(q,true), H-=fullAngularField(q,false),
J_j=completeCurrent(q,j), W=reducedSourceWork(q),
T_r=scalar(physicalAngularParameter(r)).
```

Q is the actual **half-square**, not S^2. The names refer respectively to
`ThetaCuspHawkingBMSquareSourceDifferential.lean`,
`ThetaCuspHawkingBMFullAngularCovector.lean`,
`ThetaCuspHawkingBMQuarticTestedCurrentCusp.lean`, and
`ThetaCuspHawkingBMQuarticResponseWork.lean`.

**Paper derivation P5 — not formalized.** The constructed responses exchange:
H+(q*)=H-(q), H-(q*)=H+(q). Here is the dependency argument, including the
representative issue that cannot be settled by rewriting a classical choice.

1. `physicalRate_reflect`, `scalar_reflect`, and `weylCoefficient_reflect` in
   `ThetaCuspHawkingBMSourceReflectionTransport.lean` exchange s,t and the two
   original Weyl coefficients and preserve S. Thus alpha and beta exchange.
2. In `cuspPowerResponse` the three terms have exponents 2*rho, 1, 2-2*rho
   and coefficients A^2, 2*A*D, D^2. Replacing rho by 1-rho and exchanging
   A,D reverses the outside terms and preserves the middle term, with exactly
   the same resolvent denominators. The cutoff is independent of q and branch.
   Consequently `cuspResponse`, `cutoffResponse`, and the complete `forcing`
   at (q*,branch) equal their values at (q,!branch).
3. Equality of those forcing functions gives equality of `forcingVector` in
   the same native Hilbert space. The definition of `WeakSolution` now has
   identical parameter and forcing on both sides.
   `full_forcing_weak_response_unique` in
   `ThetaCuspHawkingBMGlobalAngularWeakResponse.lean`, applied to the two
   `weakResponse_spec` statements, gives equality of the actual weak responses.
4. `globalResponse_ae_lift` identifies their smooth global representatives
   almost everywhere in full invariant volume. The continuous-on-open-chart
   argument `chartSmooth_eq_of_ae_eq` in
   `ThetaCuspHawkingBMGlobalSmoothResponse.lean` upgrades this to pointwise
   equality. The chart density is positive on the upper half-plane; equality
   merely on a null or discrete set would not suffice.
5. `globalCuspCutoff` is the same cell-germ extension of the equal cutoff
   functions. Adding it to `globalResponse` gives equality of `fullAngular`,
   and hence of `fullAngularField` after composing with its fixed chart map.

This proof uses uniqueness of the prescribed finite-energy remainder, not
uniqueness of arbitrary non-L2 solutions to the full inhomogeneous equation.
No independent covariance hypothesis is inserted.

Now write w0,w1,w2 for `sourceWorkWeights`. Direct exchange of s,t gives

```
(w0,w1,w2)(q*)=(-w1,-w0,-w2)(q),
angularResponseGreen(q*)=-angularResponseGreen(q),
J(q*)=-J(q),                    W(q*)=-W(q).                (6)
```

For W, its last coefficient is odd: either use
`squareWorkCoefficient_factor`, whose expression is a symmetric polynomial
in s*t times s-t, or use (s+1)(s+2)=(t+1)(t+2). Thus the local contact is
retained in (6), not discarded. Derivatives respect the function equalities.

Put F=div J-W/y^2 and K=4*a^2*b^2/64. The existing
`incoming_radial_mass_reduced_source_work` and `complete_divergence` imply
that the physical radial clock-mass coefficient is K*F for y>0. Consequently
the **diagonal tested orbit**, with the same amplitudes, is

```
T_q*K*F(q)+T_(q*)*K*F(q*) = K*(T_q-T_(q*))*F(q).           (7)
```

Here T_(q*) means the reflected reader, never complex conjugation. Let dT=T_q-T_(q*),
let an overbar denote horizontal cell averaging, and take 0<l,r. The full
finite-cusp identity becomes

```
integral_l^r overbar(diagonal tested orbit) dy
 = K * ( [overbar(dT*J_y)]_l^r
         - integral_l^r overbar(sum_j (partial_j dT)*J_j
                                  + dT*W/y^2) dy ).       (8)
```

The two horizontal edges cancel by the actual periodicity used in
`physical_radial_finite_cusp_balance`. Both vertical endpoints and the entire
reader-derivative/source work remain. The physical translation-clock version
multiplies both sides by h*exp(-6*h), as in `physicalClockDensity_eq`; it does
not change the spectral reader defect. No infinite-height limit is taken.

**Failed deduction and positive survivor.** Untested oddness does not prove
diagonal extinction. `physical_reader_reflect_ne` excludes equality of T_q
and T_(q*) at every Xi occurrence, including known critical occurrences.
This does not prove that their product with F, or its integral, is nonzero.
The survivor is the exact reader-difference balance (7)--(8), not a global
no-go. A critical-line-vanishing diagnostic cannot be identified with this
sector by citing source exchange alone.

**Meaning for the whole route.** This supplies a concrete paper-level location
for an unresolved even orbit contribution, with its boundary and work terms
visible. It still concerns the incoming radial SV--SV sector. Identification
with the complete metric retarded-minus-advanced coefficient, including the
other sectors and all limiting faces, is unproved. The same reader defect was
already present in V09; proving many transport helper lemmas alone would not
settle either core bridge.

## Attack 7: does taking the half-square supply a new conservation mechanism?

**Conjecture tested.** The nonlinear source's positive defect density might
supply a selection principle independent of the scalar source-current law.

**Paper derivation P6 — not formalized.** Set S=scalar(center(q)), Q=S^2/2,
N=S*conj(S)=normSq(S), and write j(S) for the actual `fieldCurrent` and
D(S)=y^2*sum_j partial_j j_j(S). Then

```
j_j(Q) = (N/2)*j_j(S),
squareGradientContact = (y^2/2)*sum_j (partial_j N)*j_j(S),
D(Q)-squareGradientContact = (N/2)*D(S).                    (9)
```

Proof: partial_j Q=S*partial_j S and
partial_j N=conj(S)*partial_j S+S*partial_j conj(S). Expanding the
product of the latter sum with j_j(S) cancels its two mixed products and
leaves conj(S)^2*(partial_j S)^2-S^2*(partial_j conj(S))^2.
Multiplication by y^2/2 and summation gives exactly
conj(Q)*fullGradientEnergy-Q*conj(fullGradientEnergy). Finally apply the
product rule to j(Q). Smoothness of S on y>0 is already supplied by
`cuspLeg_contDiffAt`; no division by S occurs, so its zeros cause no exception.

Substituting the existing `source_divergence` into (9) yields precisely
`square_divergence_sub_gradient_contact`: 8*i*(Re rho-1/2)*Im rho*normSq(Q).
Thus that nonlinear balance is a weighted scalar balance. It is not an
independent reason why either side vanishes. At a point with S nonzero,
D(Q)-squareGradientContact=0 if and only if D(S)=0. On the critical line
both vanish by the spectral coefficient; off the line either vanishes at
a point exactly when S vanishes there, since Im rho is nonzero for Xi copies.
No claim that S is everywhere nonzero is needed or made.

**Result and meaning for HB.** The proposed *independent* selection mechanism
has not been obtained. The positive survivor is a contact-preserving polynomial
identity valid even at zeros of S. It tells us exactly why dropping the
gradient work invents an extra conservation assumption. The action must
independently realize and annihilate the retained flux-minus-work observable;
the positive-square rewriting itself proves neither assertion. A formalization
of (9) would document this dependency, not close the main route.

## Attack 8: is the relative reader merely a normalization error, or a fatal boundary divergence?

**Two conjectures tested.** Equal leading radial normalization could make the
full reflected readers equivalent; conversely, a nonzero relative boundary
coefficient could preclude a finite boundary contribution. Both deductions
fail, for different reasons, in the current corpus.

**Existing Lean-source results, not newly formalized here.** In
`ThetaCuspHawkingBMRelativeReaderHorizon.lean`, fix the unchanged physical
frequency w=`physicalFundamentalFrequency q side` and let z tend to zero at
the horizon. The two Gauss factors both have value 1 at z=0, but

```
G_q'(0)-G_(q*)'(0) = center(q)/(8*(1+w)) != 0.              (10)
```

This is `gauss_first_difference` and `gauss_first_difference_ne_zero`.
The actual derivative current Jrel has

```
Jrel/z^(w+1) -> c(q,w),    c(q,w)=center(q)/(4*(1+w)) != 0,
no finite raw horizon limit,
Jrel-c(q,w)*z^(w+1) -> 0.                                  (11)
```

The declarations are `radialGreen_actual`, `normalized_radialGreen_tendsto`,
`radialGreen_horizon_coefficient_ne_zero`, `radialGreen_no_finite_horizon_limit`,
and `radialGreen_sub_source_counterterm_tendsto_zero`. Moreover,
`radialGreen_finite_subtraction_iff` says that subtracting c*z^(w+1) gives
any finite limit **if and only if** c=c(q,w). This uniqueness is within that
specified family of leading-power subtractions. It is not uniqueness among
all possible finite counterterms or boundary prescriptions.

The source proof uses -2<Re w<-1: the leading power is divergent, while the
remainder after the forced leading subtraction decays. This is an exact
asymptotic theorem about the original radial modes, with no RH premise.

**Paper corollary P7 — not formalized.** No constant rescaling identifies
these two analytic radial factors near z=0. Equality at z=0 forces the
rescaling to be 1; equality of first derivatives then contradicts (10).
This says nothing about changing their differential equations or inserting
a nonconstant dressing, which would be a different identification.

**Positive survivor and meaning for HB.** The radial obstruction has a sharp
repair determined by finiteness: its exact leading subtraction leaves zero.
This provides a concrete boundary contribution that can be made finite with
a source-derived coefficient, including on critical-line copies. It is
evidence against declaring the route dead merely from the raw divergence.
It is not permission to add that subtraction to the physical action by hand.
One must still identify the original action's boundary prescription with it.

There is also an independent angular remainder. The existing
`normalized_stream_difference_tendsto` retains the difference of the two
coexact angular readers as the leading trace of the **full** left streams.
Its statement does not say that difference is nonzero at every point; nor
does it set it to zero. Thus (11) alone cannot establish equality of full
readers or eliminate the work in (8). Source search found the radial module
wired into the umbrella, but no external direct use of its subtraction
theorems in an assembled action coefficient.

**Next discriminating test.** Compare the original relative-reader action
boundary term with the subtraction in (11), at the same frequency, density,
source polarization and angular test. The finite-subtraction theorem is a
candidate physical boundary input; inventing a new action whose finite part
is defined to be zero would not establish the identification bridge.

## Broad recent-paper transfers tested

Searches used broad subject words, not an HB/RH query: reciprocity, gluing,
shadowing, quotient, sewing, index, entropy, transgression, resonance and anomaly.
The following primary texts were opened; dates were checked against arXiv records.
These papers provide methods or rejection tests, not evidence of Lean theorems.

- Niu, Bi and van Wyk, [Reciprocity Separates Gradient Flow from Rotation in
  Conservative Physical Learning](https://arxiv.org/html/2608.30778v1),
  31 August 2026, sections III--V: matched adjoint transport supplies a Gram
  response; conservation alone does not. **Transfer tested:** separate cyclic
  matching and reciprocal response in (1). No network positivity theorem is
  imported into the original complex Einstein pairing.
- Kim et al., [GlueNN](https://arxiv.org/html/2601.05889v1), 9 January 2026,
  introduction and method: local asymptotic matching is checked against the
  original differential residual. **Rejected as a proof mechanism:** learned
  interpolation supplies neither an exact source identity nor the boundary
  domain required by (2). No numerical experiment was run.
- Peng, [Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse
  Limits](https://arxiv.org/html/2606.14435v1), 12 June 2026, Theorem A:
  its stronger inverse-limit representation retains surjective bonding maps.
  **Applicability failure:** no compact shadowing dynamical system or relevant
  bonding maps have been identified for HB. Abstract representation alone is
  not a source selector; this theorem is not used as one.
- Hubisz, Moradipasha and Singh, [Anomalies at the End of the Universe?](https://arxiv.org/html/2609.10459v1),
  9 September 2026, section 6.1, equation (6.47): boundary contributions from a
  bulk term carry opposite endpoint orientations. **Transfer tested:** keep
  orientations in (3), rather than interpreting a surviving port as failed
  conservation. Their five-dimensional quantum anomaly theory is not the
  original four-dimensional HB action; adding a new term to force cancellation
  would change the proposed problem.
- Grassi and Landò, [Intertwiners for D=3 Gauge Theories](https://arxiv.org/html/2601.18490v1),
  26 January 2026, section 2 and outlook: their construction transports BRST
  constraints under specified grading/cohomology conditions. **Transfer test:**
  distinguish transport of a source equation from transport of its observable.
  In (6)--(8), response uniqueness transports the source, while diagonal
  testing still changes the reader. No BRST grading or cohomology premise for
  HB has been established; their intertwiner is not an HB action dictionary.
- Qu and Duan, [Observability and controllability for the Schrödinger equation
  on polyhedra](https://arxiv.org/html/2609.10096v1), 9 September 2026,
  Proposition 3.1: the resolvent observation estimate retains both the measured
  solution and the forcing norm. **Transfer test:** an observation-vanishing
  argument for HB's forced response cannot silently set its residual to zero.
  The polyhedral geometry and observation hypotheses are not the modular
  black-hole problem. This suggests checking observation and forcing together,
  not importing a coercivity or extinction theorem. No such HB estimate is
  claimed here.

## Right-problem assessment

The highest-value remaining calculation is the original **even angular radiation
pairing**, together with the source-restricted boundary/reciprocity budget in (1).
It must use the genuine quadratic sources and actual causal jumps. An auxiliary
density dual, an odd cross-current, and the BM algebraic detector are three
distinct objects until their correspondences are proved.

The two bridges remain open. These attacks establish neither their simultaneous
physical realization nor an impossibility theorem for all HB realizations.
