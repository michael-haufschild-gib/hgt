# HB fixed-clock source translation and extinction

- **ID:** HB-FIXED-CLOCK-SOURCE-TRANSLATION
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Derive the finite physical-time translation defect of the literal switched theta source, retain its contact contribution in the complete nonlinear action, and determine whether its physical left-QNM projection vanishes.

## Proof chain and open core

Literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The existing finite causal reconstruction is closed. Neither complete nonlinear action identification nor source-derived extinction is assumed here. The reduced complete cokernel satisfies K=-Sigma |D|² with Sigma>0. This is an exact receiver; setting D or K to zero would assume the sought conclusion.

## Work plan

1. Audit source equations, corrected mixed action and all physical faces; search existing proof methods and broad recent primary literature.
2. Attack finite translation of the original onset and full scalar source. Prove or reject zero contact, then carry the exact remainder into the extinction interface.
3. Formalize only unconditional source identities; scratch-check, wire the leaf, audit that leaf and run static lint. Record unresolved physical identifications explicitly.

The plan tool is unavailable in this session. Frontier map and unrelated concurrent files are read-only for this work.

## Conjecture loop

**C1: autonomous action symmetry supplies fixed-source covariance. Rejected as an inference.** Simultaneous translation of a field, source, domain and switching surface differs from translating the field while retaining the predeclared source. The actual source contains smoothTransition(u), and the existing complete source decomposition retains its derivative. Ordinary action symmetry supplies a balance including temporal and spatial flux; no individual flux is thereby zero.

**C2: the finite shifted source contact has zero demodulated mass. Rejected; exact replacement proved in Lean.** Put chi=Real.smoothTransition, S_v(u)=chi(u)exp(vu), h≥0 fixed independently of v. The exact replacement is

    integral_{-h}^1 exp(-vu)[S_v(u+h)-exp(vh)S_v(u)]du = h exp(vh).

Proof: cancel exponentials before integration. Translation changes the integral of chi to that over [0,1+h]. Subtract the original integral over [-h,1]. The shared interval cancels; chi=0 on [-h,0] and chi=1 on [1,1+h], leaving h. This uses compact integrals only, including at the source rate. No frequency correction is introduced.

**C3: the retained onset pulse cancels this mass. Rejected at this temporal test; exact wave-image balance proved in Lean.** Its original coefficient is C(x,z)chi'(u)exp(vu), with full response-angular and half-square channels retained. The same weighted translation difference has zero mass, because both translated derivative integrals equal one. Thus its unshifted contact is C (not asserted universally nonzero), but it does not erase the source translation defect at this temporal test. The two wave-image terms retain the difference. Physical left-QNM projection remains a separate calculation.

## Source and action audit

- `ThetaCuspHawkingBMJointSourceTimeField.timeOriginalForcing`: fullSquarePotential and fullGradientEnergy retained, original rate and onset fixed.
- `ThetaCuspHawkingBMFullSourceOnsetReduction`: actual wave decomposition and fullSourceOnsetPulse_transition.
- `hb-mixed-action-source-coefficient.md`: corrected mixed coefficient includes E2_pp and E2_pm against both changing-weight contractions; full quadratic solutions are required to remove them.
- `hb-einstein-action-boundary-current.md`: local action variation only; global boundary evaluation is not implied.
- `hb-complete-mixed-current-common-source.md`: all four mixed current directions and common scalar producer; independent SS/VV complete physical pairing remains outside that theorem.
- `hb-total-cokernel-clock-defect-transduction.md`: canonical reduced receiver is not by itself the two-sided physical nonlinear action.

## Status

2026-09-11: the exact source, pulse and actual wave-image translation moments are formalized in `ThetaCuspHawkingBMFixedClockSourceTranslation` (218 lines, seven public theorems). Scratch check and exact leaf build passed with no warnings; no dependency or umbrella build. The [formal result and proof](../../../3-formalized/hb-fixed-onset-translation-moment.md) give the precise scope. Extinction, complete physical-action identification and RH remain open. No route retired.

The continuation now adds `ThetaCuspHawkingBMIncomingClockTranslation`: 459 lines, ten public source/current theorems, scratch-checked and audited by an exact leaf build (132 seconds, no warnings). It proves the incoming clock moments, two angular divergence/source-work laws, their exact radial mass balance, and the literal pulse factorization. See the [source balance and remaining physical scope](../../../3-formalized/hb-incoming-clock-source-balance.md). The complete extinction goal remains open.

### Direct current attack

**C7: the derivative-clock channels erase the finite translation of the incoming Einstein current.** The current is already identified with the original action and its exterior-to-horizon limit in `ThetaCuspHawkingBMFullIncomingCurrent`. All four horizon components have the exact form

    J_j(u)=exp(-6u)[C_j0 chi(u)^2+C_j1 chi(u)chi'(u)+C_j2 chi'(u)^2].

The rate -6 is common to both physical branches and independent of the Xi occurrence. The C coefficients retain distinct angular trace/normal covectors and both angular Green currents. The source proof establishes

    M_h^{-6}(J_j)=h exp(-6h) C_j0.

The derivative terms are compactly supported and have zero translation integral after the fixed demodulation. The squared onset tends from zero to one and contributes h. This determines an incoming boundary contribution; it does not identify the temporal test with the left-QNM state.

**C8: original-measure late-slab current vanishes from temporal translation.** For T,h≥0, the proved original-measure calculation instead gives

    integral_{1+T}^{1+T+h} J_j(u) du
      = C_j0 exp(-6(1+T))[1-exp(-6h)]/6.

Both derivative channels vanish on this slab; the complete mass coefficient survives. Both C7 and C8 now pass scratch checking, as does the original-measure identity `integral_0^T (J(u+h)-J(u)) = integral_T^(T+h) J - integral_0^h J`. Any complete fixed-clock invariance must cancel these terms against the corresponding pulse-response, cross, cusp and other radial/temporal faces. The exact leaf audit passed.

**C9: the incoming radial mass is a pure angular divergence. Exact residual proved.** Put s=physicalRate(q,true), t=physicalRate(q,false)=-s-3, d_s=s(s-1)/4, d_t=t(t-1)/4, alpha_s=(2s+1)(2s+2), alpha_t=(2t+1)(2t+2). Let H_s,H_t be the actual full angular potentials, Q the literal half-square, U=coexact H_s, V=coexact H_t, W=coexact Q. Dot products below are complex bilinear coordinate contractions. The original forced equations give

    E = U dot (roughDelta+1)V - V dot (roughDelta+1)U
      = (alpha_t-alpha_s) U dot V + alpha_t U dot W - alpha_s V dot W.

For the actual angular density

    G_j = alpha_t partial_j H_s (H_t+Q)
            - alpha_s partial_j H_t (H_s+Q),

product differentiation gives `div G=E`: the second-derivative terms cancel using `Delta H_i=alpha_i(H_i+Q)`. This is the original densitized angular measure: inverse-metric y² and volume y^(-2) cancel in covector dot products. Thus an integral over a finite rectangle retains the two horizontal and two vertical integrals of G with outward signs; any cusp or seam limit still needs its actual admission.

The radial mass coefficient instead has the exact decomposition

    C_10/(4c) = -(st/3) E + r_s U dot W + r_t V dot W + r_Q W dot W,
    c=a²b²/64,
    r_s=-2s d_t[(t+1)²-st]+st alpha_t/3,
    r_t= 2t d_s[(s+1)²-st]-st alpha_s/3,
    r_Q=2d_s d_t(s-t)(1-st).

The displayed division is notation only: the formal theorem multiplies by 4c, including c=0. Proof: expand the original trace/normal covectors `U-d_s W`, `-sU+d_s(s+2)W` and their t partners in `clockCoefficients`. The U dot V coefficient is `2st(t-s)=-(st/3)(alpha_t-alpha_s)`; the other three coefficients are as displayed. No division by tilt, spectral difference or amplitude occurs. This identifies the precise source-response remainder after the angular boundary is extracted. No vanishing of that remainder, or compensation by the actual pulse response, has been derived. The algebraic source identity and its differentiated angular current are now proved in Lean.

**C10: another angular integration by parts removes the remainder. Exact source balance proved in Lean; no extinction.** Write `Z=r_s H_s+r_t H_t+r_Q Q`, `lambda=(s+1)(s+2)`. The actual source equation is `Delta Q=2lambda Q+fullGradientEnergy`. Thus

    R = div(Z grad Q)-y^(-2) Z(2lambda Q+fullGradientEnergy),
    C_10 = 4c div[-st G/3+Z grad Q]
             -4c y^(-2) Z(2lambda Q+fullGradientEnergy).

Proof: differentiate `Z grad Q`; its differentiated-Z term is exactly the three-term remainder R above, because coexact rotation preserves the bilinear dot product. The other term is Z times the Euclidean Laplacian of Q; substitute the literal hyperbolic source equation. This replaces the remainder with work against the literal half-square Laplacian and an explicitly determined boundary current. It does not set the full gradient energy to zero or replace Q by a Laplace eigenfunction. The source-work identity and its combination with the actual radial mass coefficient are now formalized without source-equation premises. Pulse comparison remains open.

For a finite angular rectangle `[x0,x1] x [y0,y1]`, y0>0, the flux of any displayed densitized angular current J is

    integral_y0^y1 [J_0(x1,y)-J_0(x0,y)]dy
      +integral_x0^x1 [J_1(x,y1)-J_1(x,y0)]dx.

The horizon component integrals retain the coordinate-current sign; an outward-oriented lower radial face requires its corresponding minus sign. These formulas must be inserted in the same finite-domain action balance before removing a cutoff. Neither modularity alone nor rapid decay of only the remainder discards the principal cusp terms.

**C11: the source pulse disappears on the horizon and therefore cannot affect the current. Rejected on paper after retaining the original master normalization.** Put `u=1/r=-tanh x`, `A_s(u)=a²(1+u)^(2s)`, `d_s=s(s-1)/4`, and `alpha_s=(2s+1)(2s+2)`. Directly differentiating the literal source seed and lift in the existing pulse formula gives

    Pulse_s=2 alpha_s A_s(u)(1-u)
      [-((2s+1)u+1)H_s+d_s u²((2s+3)u+3)Q] chi'(v)exp(2sv).

The ordinary scalar pulse tends to zero at u=1. But its actual scalar forcing is `Pulse_s/alpha_s`, and conversion to the original master source multiplies by `-r³/f`, with `f=r²-1`. The factor `(1-u)` cancels before the limit. Its resulting horizon expression is

    S_pulse,s|horizon=2 A_s(1)(T_s-N_s) chi'(v)exp(2sv),
    T_s=U_s-d_s W,
    N_s=-s U_s+d_s(s+2)W.

These are precisely the normalized trace and normal covectors already present in `clockCoefficients`. The original normalized exterior equality and horizon limit are now proved in `ThetaCuspHawkingBMPulseHorizonSource.lean`; its exact leaf audit passed. The proof differentiates the actual angular fields, discharges the original denominator nonvanishing, and takes the regular limit after cancellation. It neither evaluates the causal pulse response nor cancels its cross current with the incoming field. No equality of an unevaluated physical projection is asserted.

**C12: that local pulse contact alone cancels the incoming mass. Paper calculation rejects this inference.** Using the source-contact orientation in `hb-mixed-complete-current.md`, insert the C11 drive into `Psi_s,v dot S_pulse,t-Psi_t,v dot S_pulse,s`, with `Psi_s=A_s(1)T_s chi(v)exp(2sv)`. Put `X=T_t dot N_s`, `Y=T_s dot N_t`, `c=a²b²/64`. Direct bilinear expansion gives

    C_pulse(v)=exp(-6v){
      4c[(s-t)T_s dot T_t+tX-sY] chi(v)chi'(v)
        +2c(X-Y)chi'(v)²}.

The derivative-square coefficient matches the incoming radial current's derivative-square coefficient. There is no squared-onset mass in this local contact, so its fixed demodulated translation moment is zero. The C11 transfer, this contact profile, its clock moment and the original static-chart radial contact limit are now proved in Lean and passed the exact leaf audit. The original radial derivative is retained until continuity of both differentiated incoming jets justifies its horizon limit. It does not say that the **response** to the pulse has zero moment: a transition-supported forcing can leave a causal response after the transition. The next necessary cancellation calculation therefore involves that response, its incoming cross terms and the remaining physical faces, rather than discarding the pulse or its late-time tail.

**C13: the retarded action inherits finite clock covariance from a stationary kernel. The finite-domain change of variables retains an initial-history strip.** The literal-pulse specialization, including its finite-domain continuity, is now closed in Lean and passed its exact cached leaf audit (155 seconds, no warnings). The general source-defect linearity formula below remains a paper interface unless its source admission is independently discharged. Let `R[S](p,w)` be the existing `retardedNullAction`, with common physical time step h>=0 and fixed width w. Set `S_h(t,x,z)=S(t+h,x,z)`. Write `K^d_{p,w}[S](a,b)` and `K^i_{p,w}[S](a,b)` for the original direct and image circular integrands, including their factor 1/4. Their exact argument identity is

    K^e_{p+h,w}[S](a+h,b+h)=K^e_{p,w}[S_h](a,b), e=d,i.

Both source and target times shift by h; source and target spatial coordinates stay fixed. Split the outer a integral at h, and translate a,b by h only in the upper piece. The result is

    R[S](p+h,w)=R[S_h](p,w)+H_h[S](p,w),
    H_h[S](p,w)= integral_0^h da integral_a^(p+h+w) db K^d_{p+h,w}[S](a,b)
                 -integral_0^h da integral_a^(p+h) db K^i_{p+h,w}[S](a,b).

Consequently, for the unchanged original rate lambda,

    Delta_h^lambda R[S](p,w)
      = R[S_h-exp(lambda h)S](p,w)+H_h[S](p,w).

This follows from finite integral additivity and substitution, with the original direct and image domains and orientation. It requires no frequency correction. For the actual pulse, source ingoing time is a and its temporal factor is chi'(a)exp(2sa). Its support removes new forcing after a=1, but does not remove H_h or the p-dependence of the old-history kernel. A source-derived annihilation of the completed left-QNM projection of these two terms, together with the quadratic cross currents and other faces, remains to be proved. Calling a finite-history response zero from forcing support is not that proof.

**C14: positive theta heat-kernel squares supply the sign of the completed physical cut. This transfer is not justified.** For positive heat parameters t_i and finitely many coefficients c_i, the ordinary theta series gives the Gram identity

    sum_ij conjugate(c_i)c_j[theta(t_i+t_j)-1]
      =2 sum_{n>=1}|sum_i c_i exp(-pi n² t_i)|² >= 0.

Finite expansion and the positive minimum heat parameter justify the absolutely convergent interchange. This is a heat-parameter pairing. It is not the actual renormalized cusp source, the Lorentzian/complex Einstein cut, or the original physical-clock translation. The missing transfer would have to identify the physical pairing with this positive form while deriving every cusp subtraction, radial weight, nonlinear correction and cross term. That transfer has not been found.

The prior-research check rules out replacing it with a generic all-order reflected-Hankel claim: `completeReflectedHankel_realRootedness_noGo` in `TCDCompleteReflectedHankelRealRootednessNoGo.lean` proves that the positive real entire source `cosh(z)+cosh(2z)` has all reflected polynomial-square moments nonnegative and strict rank-three determinant, yet has a nonreal zero. Its final theorem and explicit zero proof were inspected. The positive Gram survivor is already covered by prior source-positive work; no duplicate no-go or Gram wrapper is being added. HB still needs the signed **identified physical** estimate, not another positive form on a different variable or source.

## Exact nonlinear interface still required

All formulas below describing the completed physical action are **proof obligations**, not new Lean assumptions or established physical identities. Existing local coefficient formulas are identified separately.

Use the literal residual expansion at the original background, with its actual derivatives L, B, C. Write p and m for the two first-order fields. The complete quadratic corrections must satisfy

    L k_pp = -B(p,p)/2,
    L k_pm = -B(p,m),

with the actual causal and endpoint prescription. Defining these symbols by formal inverse notation does not prove they are admitted solutions. The actual mixed cubic source is

    S_ppm = B(p,k_pm) + B(m,k_pp) + C(p,p,m)/2.

The original mixed weighted coefficient is already proved to be

    <W0, L l_ppm + S_ppm>
      + <W1(m), L k_pp+B(p,p)/2>
      + <W1(p), L k_pm+B(p,m)>.

W1 includes volume variation and both raised tensor indices. Only the solved **complete tensor equations** remove the last two terms. The first term L l_ppm may be removed from a left projection only after its full Green boundary form is evaluated.

For the original densitized linearization and an admitted adjoint solution psi, the required Green identity is

    integral_D <psi,L l> - <L^dagger psi,l>
      = sum_{face in boundary(D)} integral_face J(psi,l).

At finite cutoffs every face must be present: initial and final temporal caps, horizon and exterior/AdS radial faces, upper cusp and identified modular seams, characteristic direct/image faces when those coordinates are used, and source-switching/contact terms generated by differentiation. Characteristic and switching faces must be accounted for in one decomposition, without counting an internal interface twice. Pairing normalization and measure must be inherited from the actual action. Only after joint admission and oriented limiting flux are proved does this define the physical left-QNM functional.

The corrected retarded-minus-advanced projection must then be identified with the complete physical Peierls cut, including the same boundary contributions. In a completed cyclic pairing the intended surviving radiative term is

    2 Omega_phys(B(p,p)/2, B(m,m)/2).

The common direct C term cancels in the causal difference only with the same direct source, test and prescription on both sides. Skewness eliminates a self-pairing of B(p,m); it does not eliminate the displayed pairing of two different sources. Local action variation does not yet prove this completed identification.

### Independent scalar and vector channels

Let p=a_s p_s+a_v p_v and m=b_s m_s+b_v m_v, with independent amplitudes. Define

    F_ss=B(p_s,p_s)/2, F_sv=B(p_s,p_v), F_vv=B(p_v,p_v)/2,
    G_ss=B(m_s,m_s)/2, G_sv=B(m_s,m_v), G_vv=B(m_v,m_v)/2.

Then F_pp=a_s² F_ss+a_s a_v F_sv+a_v² F_vv and F_mm=b_s² G_ss+b_s b_v G_sv+b_v² G_vv. The radiative cut contains all nine pairings Omega_phys(F_I,G_J), I,J in {ss,sv,vv}. No SS/SV/VV orthogonality is assumed. The mixed quadratic source has four independent products a_i b_j B(p_i,m_j). Every correction and each boundary functional must preserve those coefficients and the retained traceless angular Hessian/spin-two terms. A calculation of the mixed scalar potential supplies only part of this obligation.

### Sufficient signed estimate and its extinction proof

Let C_phys(q,n) denote the **fully completed, normalized, reflected physical cut** after the preceding construction. The exact interface required to use existing transduction is

    C_phys(q,n) = K(q,n) = -Sigma(q,n) |D(q,n)|²,
    Re C_phys(q,n) >= 0,
    Sigma(q,n) > 0.

The first equality is physical-action identification; the second must be produced by the original source equations and all faces. The third and the second equality in the first line already hold for the reduced receiver. Extinction then follows: 0 <= -Sigma |D|² <= 0 implies |D|²=0, hence D=0, hence every occurrence is critical. This elementary conditional argument is not a source theorem and is not being added to Lean as one.

A quantitative sufficient alternative is an independently derived bound

    -Re C_phys <= epsilon Sigma |D|²,  epsilon<1.

Together with exact identification it gives (1-epsilon)Sigma |D|²<=0, again forcing extinction. An unspecified positive constant, ordinary decay, or a bound with epsilon=1 gives no progress. Nothing audited here supplies either strict estimate.

### Why action translation alone stops short

For a covariant action, translating both fields and integration domain leaves a change-of-variables identity. With a fixed domain, finite translation instead adds the outgoing time slab and subtracts the incoming slab. With an external source J held fixed, even simultaneous translation of the domain and field changes the interaction by the translated difference of J. If J is treated as dynamical, its own variation and current must be included instead. None of these alternatives makes the marked radiative projection zero automatically.

The original onset gives an exact compact test of this issue: its demodulated source translation has mass h exp(vh). Demodulation is multiplication by the inverse of the **unchanged original exponential**; it does not change the clock or renormalize its frequency. This temporal test is not yet a left-QNM state. The result therefore rejects discarding the contact, not the possibility of a complete action cancellation.

For the already constructed scalar source, write F=L U-L V/alpha+P/alpha, with U the actual lift, V the actual full-angular seed and P the retained original pulse. An admitted physical adjoint state would give the exact interface

    alpha <psi,F> = alpha Boundary(psi,U)-Boundary(psi,V)+<psi,P>.

Thus the required scalar projection cancellation is precisely

    alpha Boundary(psi,U)-Boundary(psi,V)+<psi,P> = 0.

This exposes a source-boundary identity to prove, not a freedom to redefine the left state. The new compact temporal calculation instead fixes

    Moment_h(alpha L U-L V) = h exp(vh) alpha A(x,z),
    Moment_h(P) = 0,

where A is the complete original spatial scalar source coefficient, including gradient energy. The two wave images therefore retain the entire finite translation mass at this test. One still must derive the **actual** left state, its full radial/angular weighting and all limiting faces before using the first display. It is not legitimate to identify the demodulated temporal moment with that state by definition.

## Broader method search and attempted transfers

Further broad searches used transgression, virial, polarization, passivity, reciprocity and Noether, prioritizing June–September 2026. The arXiv date-sorted passivity endpoint returned HTTP 429; broader web queries recovered the primary records below. These are method tests, not imported assumptions.

- [Kirchhoff, Port-Hamiltonian formulation of energy-based modeling frameworks, 19 June 2026](https://arxiv.org/html/2606.21544v1), Propositions 4.1–4.2: algebraic variables can be retained as auxiliary covectors or represented through additional states. **Transfer tested:** retain source work as an internal exchange. This gives no HB identification of the auxiliary dynamics or sign of its actual radiative channel.
- [Kirchhoff, Interconnection of port-Hamiltonian systems is not dynamical, 30 August 2026](https://arxiv.org/html/2608.29731v1), Example 5.1 and Section 5: power-preserving interconnection requires explicit paired port relations and regular realization of the connecting variables. **Transfer tested:** pair the incoming and pulse currents. HB still needs its actual paired traces and causal cross terms; geometric skewness alone supplies neither those relations nor extinction. The paper concerns finite-dimensional systems.

A further deep source-work/current query returned partial coverage (pending generation 873253), no proof ideas or ingredient sets, and unrelated source-work classifiers alongside an onset forcing definition. Those classifiers were not adopted as source laws. A broader lexical pulse/current search recovered the actual pulse, all current directions, onset Green transfer, and incoming horizon limit. It supplies no evaluated pulse-response cancellation. No numerical experiment or axiom-print run was used in this continuation.

- [Procopio et al., Backreaction of stimulated Hawking radiation in an optical analogue, July 2026](https://arxiv.org/html/2607.01118v1), Appendix A: a Hermitian interaction gives conservation of total co-moving energy while allowing exchange between pump and probe. **Test:** use nonlinear energy conservation to extinguish one radiative channel. **Failed transfer:** conservation permits nonzero exchange; the optical approximation supplies neither the Einstein boundary identification nor its required sign.
- [Yang–Yang–Liu, Decentralized and Equilibrium-Set-Oriented Stability Analysis and Control for Power Systems, 31 August 2026](https://arxiv.org/html/2609.00497v1), Lemma 4: sum local storage inequalities and cancel the network supply, leaving a strict dissipation term. **Test:** combine all physical channel currents by a source-derived storage identity. **Open obligation:** HB needs the original storage and signed supplies for every channel and face. The paper assumes local differential passivity; adding its controller changes the dynamics. Neither operation can be imported as an HB extinction proof. Its theorem gives asymptotic stability, not exact extinction at one prescribed clock.
- [Osipov–Tretyakov, Huygens' principle and field equivalence relations for cylindrical enclosing surfaces, August 2026](https://arxiv.org/abs/2608.14005): exact boundary representations use complementary field traces. **Transfer tested:** boundary reconstruction preserves the traces; it does not assert their vanishing. The harmonic Maxwell cylinder is not the complete nonlinear theta-source problem.
- [Sugiura, Learning to Agree under Pseudo-Reciprocity, August 2026](https://arxiv.org/abs/2608.22234): the abstract classifies consensus networks under rational-learning assumptions. No source-equation or physical-current identity applicable to HB was found.

Two additional deep/method requests targeted conserved bilinear flux and forced angular Green divergence. The first returned one unverified ingredient group based on finite abelian determinant flux and matrix bilinear invariance; neither identifies the physical current. The second recovered the actual forced angular operator, local Green differentiation and native angular-current methods. Their source arguments were inspected; semantic/compiler coverage and local-model deadlines remained partial. The derivative proof pattern is used for C9, with its literal field smoothness discharged independently. No retrieved covariance or RH-equivalent condition is used as a premise.

Three deep corpus requests inspected candidate lemmas and source proof arguments. All returned partial coverage with pending index generations; deadlines affected reranking or semantic retrieval. Retrieved integration/translation arguments support compact endpoint telescoping, but no returned proof supplies the missing physical sign. In particular, the retrieved divergence-vanishing lemma requires the field to vanish near the boundary; using it here without deriving that premise would discard exactly the unresolved flux. Exact source text was also searched for onset translation and clock conservation.

Broad searches used reciprocity, Noether, hypocoercivity, symplectic, dissipation and observability, prioritizing June–September 2026. Primary-paper checks:

- [Ghosh, Gauge theory and symplectic structures, 2 September 2026](https://arxiv.org/html/2609.02699v1): the square-completion argument around Theorem 1.9 keeps curvature and topological terms; integration by parts uses a closed symplectic manifold. **C4:** transfer a Weitzenbock square completion to orient the HB action. **Not closed:** HB's Lorentzian/complex pairing, radiative boundaries and source contacts do not meet those assumptions. The useful demand is to exhibit the complete compensating curvature and boundary terms, not infer positivity from a formal square.
- [Coppola–Lenarcic, Dissipative framework for subsystem dynamics of noninteracting quantum chains, 21 August 2026](https://arxiv.org/html/2608.21336v1): generator reconstruction assumes a quadratic Hamiltonian, initially uncorrelated states and a Gaussian environment. **C5:** recover a positive reduced dissipation law from complete evolution. **Not applicable as a proof:** nonlinear Einstein assembly and its initial/source correlations do not satisfy that theorem's hypotheses; no fixed-clock extinction follows.
- [Li et al., Sensing-Limited Control Under Non-Designable Observation Mechanisms, 30 June 2026](https://arxiv.org/html/2606.31396v1): the sufficient observation mechanism needs a strict information surplus plus curvature/conditioning assumptions. **C6:** use a source-derived strict deficit bound instead of exact covariance. **Open:** the translated idea is the epsilon<1 estimate above; neither the positive geometry nor the needed source bound has been constructed. The paper's theorem itself does not apply to HB.

No novelty claim beyond the audited corpus comparison is made. These are attempted mathematical transfers, not citations proving extinction.


## Pulse horizon and causal-history continuation (11 September 2026)

The source-level horizon calculation was strengthened before attempting a causal cancellation. The original contact is

    C_r(x,v)=f/r² sum_j[(Psi_static,s,r)_j S_pulse,t,j
                          -(Psi_static,t,r)_j S_pulse,s,j].

In ingoing coordinates its regular expression is

    C_r(x,v)=r^(-2) sum_j[(f Psi_s,r+Psi_s,v)_j S_pulse,t,j
                          -(f Psi_t,r+Psi_t,v)_j S_pulse,s,j].

Thus the radial derivative is retained until regularity at r=1 is established. At every exterior radius write `Psi_i=A_i(r) chi(v)exp(2s_i v)`, `D_i=partial_r A_i`, and `S_pulse,i=P_i(r) chi'(v)exp(2s_i v)`, with A_i,D_i,P_i the actual covector coefficients. The exact finite-radius contact is

    C_r=exp(-6v)[B(r) chi chi'+C(r) chi'^2],
    B(r)=r^(-2) sum_j[((f D_s+2s A_s)_j P_t,j)
                         -((f D_t+2t A_t)_j P_s,j)],
    C(r)=r^(-2) sum_j[A_s,j P_t,j-A_t,j P_s,j].

It has zero fixed-clock translation moment before any horizon limit. The normalized-source and horizon-contact leaf audit passed (202 seconds, no warnings). The stronger finite-radius clock-moment extension also passed scratch checking and its exact cached leaf audit (40 seconds, no warnings), as `ThetaCuspHawkingBMPulseContactClock.lean`. Both leaves are wired into the umbrella. This is the source contact with the explicit incoming field, not the current of its unevaluated causal pulse response. A zero translation-defect moment of a compactly supported source does not assert that its Laplace transform or its propagated projection is zero.

The new deep/method search for cancelling a vanishing radial factor returned partial coverage (generation 874024), twenty candidate lemmas and twenty source arguments. Its one unverified ingredient group still required the metric contraction and radial-limit transfer. The actual coexact derivative and exterior denominator arguments were used instead. A subsequent causal-triangle/history query also returned partial coverage (generation 874200, deadline and filter/judge unfinished), with twenty candidates and twenty source arguments but no proof ideas or ingredient groups. It recovered finite integral splitting, actual angular resolvent bijectivity and the already proved causal reconstruction. None was an extinction producer.

Broad searches used tail, memory, echo, hereditary, transparent, Volterra, renewal, observability and controllability, prioritizing June–September 2026. Most hits concerned unrelated graphs, machine learning or observational astronomy. Primary-paper method checks:

- [Cornuejols–Patil, A Hereditary Property of Cutting Plane Procedures, 2 September 2026](https://arxiv.org/html/2609.02038v1): the closure/face result uses one common family of full-dimensional convex sets. HB has no identified convex closure with these hypotheses; it gives no commutation of a radiative projection with nonlinear evolution.
- [Hager–Harang–Pelizzari–Tindel, The Volterra signature](https://arxiv.org/html/2603.04525v1): initial submission 4 March 2026; displayed manuscript date 24 August 2026. Proposition 3.1 changes both the path and kernel under a smooth increasing reparameterization fixing both endpoints. A finite physical translation does not meet that endpoint condition. The Chen relation retains old history, motivating C13's explicit strip. Neither result erases that strip for the unchanged HB kernel.
- [Neshaei Moghaddam–Chen–Gharesifard, Structural Averaged Controllability for Linear Ensemble Systems: Multi-input Case, 30 July 2026](https://arxiv.org/html/2607.27706v1): the construction chooses a system realization and common control to reach an ensemble average. HB's source, dynamics and clock are fixed, and its target concerns every occurrence. The paper therefore supplies no permitted extinction mechanism.
- [Mukherjee–Fahim–Hausenblas, Sphere Constraints and Harmonic Map Flow: Controllability and Reachability by Low-Mode Forcing, 6 July 2026](https://arxiv.org/abs/2607.05687): abstract inspected; HTML retrieval timed out. The proposed Lie-bracket mechanism generates additional controlled directions. It does not establish an invariant of the fixed theta-source evolution or a common-clock annihilation.

No theorem from these papers is assumed in the Lean source. C13 preserves the history term demanded by the actual causal geometry; its projection is the next unresolved calculation.


The C14 deep source-positivity method query returned partial semantic coverage (generation 874420). All twenty candidate names and twenty source proof arguments were inspected. Its proposed ingredient group supplied determinant reflection symmetry and left the cusp-transfer obligation open; reflection of a determinant is not its sign. The returned strict theta/Gamma Hankel rays and adjoining-cone RH equivalences do not supply the physical estimate and were not adopted as hypotheses. The exact prior reflected-Hankel counterexample was checked in its source.

A further broad arXiv pass used oscillation, Hankel and positivity. The date-sorted arXiv Hankel search page failed with a cache miss. [Martin, Oscillation Classes: An Interpolation Approach, 17 August 2026](https://arxiv.org/html/2608.17066v1), Theorem 13, derives endpoint rigidity from a bounded supremal operator, an admissible concave profile and a matching fundamental-function scale. Its proof retains the endpoint envelope through Fatou and duality. The transfer tested was a strict source norm bound after completing the causal history. HB has no identified rearrangement-invariant physical pairing or proof of that operator bound; the paper therefore supplies no fixed-clock sign or extinction. Its endpoint argument reinforces retaining the full envelope rather than discarding an unresolved boundary contribution.


## Literal retarded-pulse translation continuation (11 September 2026)

C13 now has a closed source specialization in `ThetaCuspHawkingBMRetardedPulseClock.lean`. Write P for the actual `fullSourceOnsetPulse`, P_h(t,x,z)=P(t+h,x,z), and K for its original circular integrand including the factor 1/4. Both kernels use the original source point; only the image kernel reflects the radial source argument in its invariant. For p,w,h>=0,

    R[P](p+h,w)=R[P_h](p,w)+H_h[P](p,w),
    H_h[P](p,w)=integral_a=0..h integral_b=a..p+h+w K^d_{p+h,w}[P](a,b)
               -integral_a=0..h integral_b=a..p+h K^i_{p+h,w}[P](a,b).

The proof establishes continuity of the actual pulse integrand from its full angular circular means, literal differentiated radial coefficients, smooth onset derivative and original kernel radius. Finite interval additivity and translation then apply to these particular source functions. No integrability, covariance or extinction premise is added to the public source theorems.

The stronger positive survivor is an exact restriction to the original ingoing onset interval:

    R[P_{1+h}](p,w)=0,
    H_{1+h}[P](p,w)=H_1[P](p+h,w),
    R[P](p+1+h,w)=H_1[P](p+h,w).

Proof: source ingoing time is a+1+h in the first equation, so the literal pulse vanishes for a>0; the single endpoint has zero integration measure. In the second equation the original source vanishes for a>1, so split the outer integral at 1 and discard only that proved-zero piece. The upper b bounds and both kernels still depend on p+h. Thus support in ingoing time does not imply compact support in spacetime, and no horizon/history tail is discarded. The source cutoff endpoint 1 is fixed once and for all; these translations do not modify the Hawking frequency.

The next physical obligation is to insert these exact history integrals into the original left-QNM pairing, its incoming-response cross currents, and the other SS/SV/VV channels. It remains necessary to prove the complete tensor quadratic equations before removing changing-weight terms, and to retain temporal, horizon, exterior, cusp, characteristic and source-contact contributions with their original orientation. This scalar response identity supplies one literal input to that task, not the completed radiative cut.

**C15: reciprocity or a positive scalar source produces the required sign of the reflected physical cut. Not established; the algebra does not imply that sign.** Even for an admitted real skew Green pairing Omega, conjugation and skewness give

    conjugate(Omega(conjugate(F),F))=-Omega(conjugate(F),F).

Consequently i Omega(conjugate(F),F) is real but changes sign when F is conjugated. For real source vectors U,V, its value at U+iV is -2 Omega(U,V). This is a diagnostic of the proposed inference, not a claim that the HB FE-reflected source is a conjugate pair. A physical sign requires its own source-derived frequency/orientation or positive structure, together with boundary admission. No such structure for the completed HB pairing has been proved. Replacing it with ordinary pointwise positivity of a different theta source would omit the operator and all mixed channel terms.

The exact sufficient estimate remains the one above: after identifying C_phys with -Sigma |D|², prove Re C_phys>=0 (or the strict epsilon<1 bound) from the original source. The verified history law does not supply that estimate. Extinction and RH remain open.

### Current search and transfer audit

Two new deep/method searches used finite translated causal intervals and retarded adjoint source work. They returned partial semantic coverage (generations 874513 and 874576); candidates and source proof arguments were inspected. The interval proposal concerned midpoint/escape-region splitting, not the needed nested integral translation. The adjoint proposal paired general graph-adjoint identities with pointwise positivity of `SelbergThetaNativeSource.positiveSource`. Its actual theorem proves positivity of a modular sum; it does not identify the HB physical pairing. The retrieved `HedenmalmThetaQuantileResolventPortLaw` was checked in source: its metric commutator retains a rank-two boundary flux and source-response cross term. Neither transfer closes the sign obligation. The current Lean proof instead uses verified finite interval substitution and the literal pulse equations.

Broad arXiv searches used cocycle, renewal, memory, unitarity and dissipation, prioritizing June–September 2026. Date-sorted memory search was available; the unitarity endpoint failed. Primary-paper method checks:

- [Tall, Log-Hölder continuity at zero Lyapunov gap for finite-state Markov GL(2)-cocycles, 23 August 2026](https://arxiv.org/html/2608.22157v1), Lemmas 5.1–5.2: centered Markov edge sums split into a martingale plus two endpoint values. Centering and the Markov realization are required; the main theorem assumes zero Lyapunov gap. Test: interpret clock defect as a coboundary. No HB centering law was found, and the endpoint/history terms remain.
- [Tchuiaga, C^0-Analogue of Ismagilov's Theorem, 7 August 2026](https://arxiv.org/html/2608.07802v1), Theorem 4.2 and Remark 5.6: flux-cohomology classification uses volume preservation and zero-mean coefficients on a closed manifold; the stated noncompact extension uses compact support and finite volume. Test: obtain a source clock current from a flux cocycle. These geometric and mean conditions are unproved for the radiative HB domain and changing weights. Classification alone does not erase its faces.
- [Yan, Yang-Lee Criticality as a Dissipative Dynamical Phase Transition, 26 August 2026](https://arxiv.org/html/2608.26082v1), Section II.2 and Appendix B: engineered Lindbladian weak-symmetry sectors realize non-Hermitian observable evolution. Test: use an invariant observable sector to kill the radiative projection. The construction changes dynamics and chooses an observable sector; neither is a source-derived HB identity. Its damped evolution does not establish exact extinction at the original clock.
- [Ansbacher et al., Finite relaxation protocols with minimal dissipation, August 2026](https://arxiv.org/html/2608.25207v1), equation (4) and Proposition E.1: dissipation is a sum of relative entropies for protocols with complete equilibration after each changed Hamiltonian, with a Fisher–Rao large-step asymptotic. Test: turn the clock defect into a nonnegative dissipative supply. The paper requires the equilibration that HB must produce and changes the Hamiltonians. It supplies no identity for the unchanged causal source.

No result from these papers is used as an assumed Lean source law.

The literal retarded-pulse leaf passed its exact cached audit (155 seconds, no warnings), compiling only that leaf against twelve existing cache roots. It is wired into `RHTower.lean`; no umbrella build was run. Source SHA-256: `ba006ed0b56e7b91d1101c535ad7eb464bd29fbe0437c044048fdb7dc0fc581d`.

Static API index refreshed; formal lint passed with existing large-file warnings. The audited canonical `.olean` and `.ilean` are retained.


## FE-adjoint density test (11 September 2026, active)

**C16: the FE partner itself is the radial adjoint source.** At fixed ingoing time write F_s=a² chi(v)exp(2sv)(1+u)^(2s)Q and t=-s-3. The actual common generator is D=(1+u)partial_u+3, with D F_s=delta F_s and D F_t=-delta F_t. Substitution into the original measure transpose gives the normalized mismatch (4u-u²)KQ. Thus the unweighted FE branch does not intertwine P and its transpose by the branch relation alone.

**C17: a source-independent radial density factor repairs this mismatch.** Solving its exact coefficient equation

    (1+u) w'/w=1-4/u

produces w(u)=(1+u)^5/u^4, up to a constant normalization. Then

    D(w F_t)=(-delta+1-4/u)w F_t,
    Pdagger(w F_t)=[a_t(v)(1+u)^(2t)w] (P F_s/[a_s(v)(1+u)^(2s)]).

The quotient display is only notation for equality of their angular coefficient operators; the Lean target is cross-multiplied and never divides by amplitudes or onset. The common angular Laplacian is retained, not replaced by an eigenvalue. This factor changes neither physical time nor frequency. It is an auxiliary adjoint test, not a replacement for the literal source or the admitted physical left-QNM state.

The radial density exposes the cost of this formal repair:

    u^4(1+u) (1+u)^(2s) w(u)(1+u)^(2t)=1.

Thus the corresponding fixed-time radial source flux has equal endpoint values, not zero values. With retained spin-two test RQ, R=-Delta(Delta-2), its coefficient is a²b² chi(v)^2 exp(-6v)(KQ)(RQ), with the original angular density. At the AdS face w has a fourth-order pole: u^4 w F_t tends to a_t(v)Q. The original physical left-state boundary prescription must be checked before this test can be used in the physical pairing. No full action cancellation or zero boundary port follows from the repaired radial intertwiner. The source identity and residue are the current Lean target.

A broad June 2026 paper gives a related but insufficient boundary mechanism: [Ciambelli–He–Klinger–Zurek, Mapping the Infrared Phase Space of Gravity to Finite Subregions](https://arxiv.org/html/2606.12515v1), equations (2.2), (2.9)–(2.13). Its null-boundary symplectic form retains the expansion/area pair even when the clock vector is fixed. Its conformal transverse-metric assumption explicitly sets the spin-two null shear to zero. Importing that reduction would remove the radiative sector HB must control; it is not an extinction proof for the literal source.


**C18: the repaired adjoint seed is the original left-QNM radial mode. Failed boundary test.** The physical left stream uses the original homogeneous radial mode at opposite time frequency. At either fundamental resonance, both original radial normalizations are exactly z^(w0/2) sqrt(1-z), z=1-u²; hence they tend to zero at the AdS face. Multiplying any constant-normalized such mode by u^4 still tends to zero. Therefore

    lim_(x→0-) u^4 [w F_t-c psi_left(x)] = a_t(v)Q.

This exact residue is the positive survivor: no constant normalization of the original fundamental radial mode removes the source-dual pole coefficient. It does not claim that coefficient is nonzero at every source point. It rules out identifying the two fields by the radial transpose calculation alone; a source-derived correction and its complete physical boundary transport would be required. The repaired source transpose is first order in the radial generator, while the physical left mode solves the homogeneous second-order master equation. Neither equation implies the other.


### Current method tests and next correction

The two new deep requests, for physical left-state admission and source/propagator commutation, returned partial semantic coverage (generations 874835 and 874857), with deadlines and final filtering unfinished. All candidate names and retrieved source arguments were inspected. The first recovered the original causal source-adjoint density and its cubic remainder, not an admitted homogeneous dual. The second recovered the actual Dirichlet causal boundary and a general Volterra invariance theorem. The latter requires both invariant seed and compatible kernel; those are exactly the missing source obligations and are not imported as assumptions. Neither request supplied a completed physical sign.

Broad arXiv passes used adjoint, duality, intertwining, factorization and Darboux, prioritizing June–September 2026. The date-sorted adjoint endpoint failed with a cache miss. Primary-paper checks:

- [Brennecken–Rösler, Remarks on a proof of the absolute continuity of the representing measures for Dunkl's intertwining operator, August 2026](https://arxiv.org/html/2608.10821v1), Section 2: a spherical mean can change the singular/absolutely-continuous decomposition, and an interior density statement does not exclude a measure on the omitted sphere. Test: obtain boundary admission from an intertwiner's interior identity. The paper supplies no such implication; our explicit AdS residue must remain.
- [Khan et al., Newtonian Gravitational Curvature-Induced Entanglement Generation, 30 August 2026](https://arxiv.org/html/2608.30075v1), equations (8)–(9): exact oscillator closure follows from a terminating Magnus expansion and a curvature-shifted period. A residual two-qubit phase remains. Test: obtain universal finite-clock extinction from closure. Neither the modified frequency nor dropping the surviving interaction is permitted for HB.
- [Startsev, A new family of Darboux integrable partial differential equations, 27 August 2026](https://arxiv.org/html/2608.27709v1), Theorem 1: differential substitutions preserve characteristic integrals for a specified exponential hyperbolic equation with finite separated coefficient rank and nonzero determinant denominators. Test: repair the source intertwiner by derivative terms. HB has no proved identification with that PDE or its finite-rank condition. Its theorem cannot be transferred by the existence of a finite number of tensor channels.

**C19, next correction test:** write the actual ingoing master operator as M=-partial_x²-2 partial_x partial_v-(1-u²)Delta and the common source operator as P=A(u,Delta)+b(u,Delta)partial_x, with b=-u² K/(u-1). On a smooth interior field, the second-radial-order part of [M,P] is

    -2 b' partial_x²-2 b' partial_x partial_v,
    b'=-u(u-2)(u+1)K/(u-1).

Thus even a repaired formal source transpose does not give commutation with the causal master inverse. Comparing the two principal coefficients also excludes absorbing this whole remainder into a scalar zeroth-order multiple of M unless b'=0. A first-order correction c(u,Delta)partial_v would need c'=b' at this level; its full lower-order equations, literal onset contribution, and physical boundary domain still require derivation. This is an interior principal-coefficient calculation, not a completed intertwiner or a new assumption of covariance. No claim is made that it survives the independent SS/SV/VV assembly.

The subsequent hybrid Darboux/complete-source search returned partial semantic coverage (generation 874889). Candidate statements and source arguments were inspected. The existing `ThetaCuspHawkingTopologicalDarbouxStarobinskySpectralFlow` was read through its scalar/vector factorizations: it supplies a homogeneous potential pair at fixed geometric scale, with its denominator conditions retained. It does not identify the common source producer or its pulse and contact corrections with that intertwiner. Its header explicitly leaves the complete nonlinear remainder unevaluated. That established factorization can guide the coupled correction; it cannot replace its source-level derivation.


C17 and the exact C18 residue are now closed in `ThetaCuspHawkingBMSourceDensityDual.lean` (277 lines, seven public theorems, six public definitions). Scratch checking passed without warnings. The exact leaf audit passed in 134 seconds without warnings against twelve cached roots; the leaf is wired once into `RHTower.lean`, with no umbrella build. The [source-density proof and precise physical scope](../../../3-formalized/hb-source-density-dual-ads-residue.md) retain the full spin-two radial value and its AdS discrepancy from both original fundamental modes. Source SHA-256: `7aaa8794178e8c78a2fd7730ff30aa4f89340a4997cd7ef44a029d81158be629`. Extinction and RH remain open; no route retired.

Static API index refreshed and all thirteen public declarations verified. Formal lint passed with existing large-file warnings. Canonical audited oleans are retained; owned temporary audit and scratch files were cleaned.

## Causal two-source clock cancellation test (11 September 2026, active)

**C20: the FE-paired clock annihilates the full native spin-two operator after the causal delay transpose.** The relevant Rodrigues identity is weighted: with p=Z²−1, the retained operator on the actual circular mean M is −partial_Z²(p² partial_Z² M). After transferring two derivatives, the exact bulk is −F partial_Z²(W/A) in the dZ measure, or −AF partial_Z²(W/A) in the original dh measure, where F=p² partial_Z² M and A=partial_h Z. Thus an unweighted cubic-polynomial argument does not apply. Vanishing of this transferred coefficient requires W/A to be affine in Z. This is a test of one proposed mechanism, not an assumption imposed on the literal source.

The original finite clock can be evaluated on the open late interval 1<h<V−1. Set s=physicalRate(q,branch), t=−s−3, alpha=(2s+1)(2s+2), gamma=(2t+1)(2t+2), and d=t(t−1)w[3+(2t+3)w]/[2(1+w)]. The unchanged onset profile is g_s(u,v)=exp(2sv)[alpha chi(v)−b_s(u)chi'(v)]. Its actual two-source integral satisfies

    W_V(h)=integral_0^(V−h) g_s(u,v+h)g_t(w,v)dv
          =a exp(2sh)−b exp((2s+6)h),
    a=alpha(gamma−6d) tailClock,
    b=alpha gamma exp(−6V)/6.

Proof on paper: the later onset equals one and its derivative equals zero throughout the integration interval. The FE relation combines the two v-exponentials to exp(−6v). The original finite contact identity gives integral_0^c exp(−6v)chi'(v)=exp(−6c)+6 integral_0^c exp(−6v)chi(v), and the latter integral is tailClock−exp(−6c)/6 for c>=1. Substitution gives the displayed identity. No source frequency, onset, or causal endpoint has changed.

For the literal geometry let A=partial_h Z and B=partial_h A. Define

    E_r=r²/A²−3Br/A³+(3B²−A²)/A⁴.

Then the already defined full native `delayBulk` on this interval is exactly

    F [a exp(2sh) E_(2s)−b exp((2s+6)h) E_(2s+6)].

The terminal term is part of the original finite response; the zero terminal boundary current at h=V does not permit dropping it from the bulk. The current bounded target is a closed Lean proof of these identities and the actual first/second clock derivatives. Next, test their direct-minus-image and reversed-branch combination against the other channels. Neither a one-branch weight identity nor its failure to vanish is a value or sign theorem for the complete SS/SV/VV physical action. Extinction remains open.

The same formula supplies two exact differential balances on this late interval:

    (partial_h−2s)W_V(h)=−6b exp((2s+6)h),
    partial_V W_V(h)=6b exp((2s+6)h).

The coefficient b is nonzero for every actual Xi occurrence: both s and t have nonzero imaginary part, so neither factor of alpha or gamma vanishes, and the exponential never vanishes. The second balance is the original observation-cap source flux. Neither balance translates the source frequency. Their sum is a local transport identity for this original two-source integral, not a conservation law for the completed nonlinear action. A proposed complete cancellation must account for this cap along with the other faces and channels.

The observation-cap balance also holds globally, before either onset has ended:

    partial_V W_V(h)=g_s(u,V)g_t(w,V−h).

This follows directly by the fundamental theorem of calculus applied to the original finite integral; both literal profiles are continuous, including the onset derivative. It retains the terminal transition layer rather than extending the late formula across it. For h>1, V>h+1 and any fixed H>0, the exact finite cap translation is

    W_(V+H)(h)−W_V(h)=b_V [1−exp(−6H)] exp((2s+6)h) ≠ 0.

Here H is unchanged physical time in the original normalization. This is a comparison of two observation caps for the same source, not a claim that this cap translation is the complete nonlinear action of a translated spacetime field. It proves that source-correlation stationarity cannot replace the required full action identity; the explicit right side is the compensation the other terms would need to supply. The finite-cap result does not determine the value of the full physical action at either cap.

### Current method and external transfer tests

The source-intertwiner, paired-angular-resolvent, spin-two weight, late-clock and positive-transport searches returned partial coverage (generations 874971, 874982, 874991, 875003 and 875070). Candidate names, statements relevant to the proposed mechanisms, source arguments and proposed ingredient groups were inspected. The wave-correction group left temporal applicability as an obligation and proposed a three-point Suzuki response equation; the actual source of that theorem was checked and does not concern the HB wave operator. The energy-transport hit is a Hilbert norm expansion with a mixed cross term, not its cancellation or sign. The direct source hits recovered the already established finite contact, native spin-two primitive, delay transpose and uniform clock derivatives. No returned theorem supplied the complete physical estimate.

Broad arXiv searches used cohomology, transmutation, balance, coercivity, transgression and rigidity, prioritizing June–September 2026; date-sorted coercivity search was available. Primary-paper method tests:

- [Dwivedi–Singhal, A dd^Phi-Lemma and Bott–Chern-type Cohomology for Spin(7)-Manifolds, 3 September 2026](https://arxiv.org/html/2609.04156v1): Theorem 4.5 and Lemma 4.9 use compact torsion-free Spin(7) geometry and specified form components to derive exactness and a harmonic decomposition. Test: complete source constraints force cokernel orthogonality. The compact elliptic geometry and admissible projection have not been identified for the HB radiative domain.
- [Bader–Glasner–Gorfine–Sauer, On the Unitary Cohomology of Semisimple Groups, 9 September 2026](https://arxiv.org/html/2609.08652v1): the cohomological degree and torsion results require actual unitary representations and specified groups; they do not give general rank-one cohomological vanishing. Test: source translation represents a trivial unitary cocycle. Neither that representation nor its triviality follows from the FE branch relation.
- [Li, Existence and strong-field asymptotics of skyrmions in a fourth-order model of frustrated ferromagnets, 8 September 2026](https://arxiv.org/html/2609.08255v1): Lemma 2.4 derives a forced Helmholtz circle-mean formula and its residual norm from a radial Green identity. Lemma 2.5 obtains a positive residual lower bound using the sphere constraint and nonzero topological degree. Test: force the HB residual by a circular-mean energy identity. The native HB mean is already constructed, but no sphere constraint, degree obstruction or identification of this Hermitian norm with the full physical bilinear cut has been proved. The paper does not supply extinction.
- [Vo, Principal eigenvalues of nonlocal operators with advection: sharp scaling limits and spectral phase transitions, September 2026](https://arxiv.org/html/2609.02416v1): Proposition 6.1 and the proof of Theorem 1.3 retain the inflow transport flux. Symmetric nonnegative kernels give a Fourier energy lower bound and compactness; convergence to the limiting energy then forces the nonnegative boundary flux to zero. Test: derive HB boundary extinction by saturation of a bulk energy bound. HB still needs its own positive physical energy, sharp lower bound and convergent complete supply, including mixed channels. Merely transferring the symmetric operator to a test function proves none of these.
- [Wang–Xie–Yu, Gromov's dihedral rigidity conjecture in dimension three, 29 June 2026](https://arxiv.org/html/2606.30130v1): Lemmas 3.10–3.11 track the boundary-domain and inner-normal comparison needed for essential self-adjointness at corners. Test: infer a physical sign from an interior adjoint identity. HB's null/cusp/radiative faces have no proved identification with those elliptic domains or comparison conditions.

These are mechanism tests, not imported source-law assumptions. The current exact two-source calculation retains the obstruction each proposed transfer must address.

**C21: a helicity or characteristic-class identity supplies the missing complete cancellation. Not established.** The date-sorted broad helicity search led to two useful distinctions. [Huang–Long–Zhao–Zhou, Spacelike reduction of the gravitational topological terms and associated helicity densities, 30 August 2026](https://arxiv.org/html/2608.30154v1), equations (1.2)–(1.3), (3.27), (3.34) and Section 7, distinguish the full characteristic-class descendant, its codimension-two terms, and an on-shell kinetic helicity. The identity dQ3=tr(R wedge R) does not make Q3 closed; the vacuum Ricci equation alone does not erase its Weyl curvature contribution. The paper's separated helicity functionals are quadratic around Minkowski space, with conservation and boundary admission requiring separate equations. They are not identified with HB's completed left-QNM action.

[Xu–Chu, Metric Source Completions and Integrability in Celestial Gravity, September 2026](https://arxiv.org/html/2609.10637v1), Section 5.6 and equations (80)–(85), retain a nonlinear coordinate response after subtracting the complete same-chirality Ward anticommutator. Section 6 retains energy derivatives of the full momentum-conservation distribution; global two-leg completion still requires contact and mixed-pole data. Test: infer HB extinction from local same-chirality Ward integrability. This implication is not supplied by the paper, and HB's original source maps and boundaries remain to be evaluated.

The associated deep self-dual source search returned partial coverage (generation 875160). Its proposed abstract dual-system symmetry has no physical amplitude identification. The retrieved `ThetaCuspHawkingHBSelfDualPlebanskiLocalJacobiNoGo` was checked: the local same-transverse-charge cyclic vertex is an exact graph energy, zero only on the momentum diagonal for nonzero real charge. This already excludes the source-local Jacobi shortcut; no duplicate lemma was added. The positive remaining task is the full causal pairing, with the actual terminal flux now evaluated in C20. HB itself is not retired.

The concurrently added `ThetaCuspHawkingBMPhysicalRadialNorm` was also checked through its actual residue factor and final zero-set theorem. Its original horizon finite part is a nonzero Gamma quotient at each fundamental frequency. It therefore reduces vanishing to the remaining physical residue factor; it does not provide a positive sign or a zero multiplier that could replace source extinction.

C20's exact source identities are now closed in `ThetaCuspHawkingBMLateSourceClock.lean`: the global observation-cap balance, late clock and both delay derivatives, nonzero cap coefficient, exact finite cap-translation difference, and substitution into the original native spin-two bulk on its physical causal domain. The [dependency-closed proof and scope](../../../3-formalized/hb-two-source-clock-cap-balance.md) distinguish this source integral from the complete nonlinear action. Scratch checking and the exact cached leaf audit passed without warnings; the audit took 98 seconds against twelve cache roots. The 352-line leaf has ten public theorems and three public definitions and is wired once into `RHTower.lean`, with no umbrella build. Source SHA-256: `e3e2e9f17106759afcf185d9995cd9af35f3533ab80642c6189e2e88d4967f7d`.

The next extinction obligation is the completed causal/action compensation for this explicitly retained cap, including the onset layers, direct-minus-image integration, reversed branch, independent SS/SV/VV terms and all remaining boundary faces. The new source laws supply neither universal covariance nor the physical sign. The full goal remains active; extinction and RH are not proved.

## Variational reciprocity and source-contact rigidity continuation

**C22: complete variational self-pairing forces the oriented radiative pair to vanish. Failed as an inference.** The complete mixed-action coefficient and four-component Einstein current were checked again. The self-bracket cancels the two opposite orientations of a cross term; it does not annul either orientation separately. This repeats the already identified C15 distinction, so no new generic self-bracket lemma is being added. The positive next test is whether the original source producer itself supplies an admissible differential symmetry.

**C23: the C19 first-order source intertwiner can be repaired by adding a time derivative and a zeroth-order term. Correction, 12 September 2026.** The earlier paper calculation omitted `-2Kb' partial_v²`. The proposed half-density adjustment does not eliminate all derivative coefficients. The corrected [source-contact calculation](hb-source-contact-rigidity.md) retains that term; its AdS coefficient trace remains -3K because b'(0)=0. This invented operator route is deferred. It has not supplied complete-action cancellation, and no nonlinear or RH conclusion follows.

**C24: the surviving contact has an independent source differential law. Closed for the literal angular source.** A complex bilinear Bochner/Cayley-Hamilton derivation gives the stronger fourth-power identity (2) in the same card, involving the actual contact, its gradient and Laplacian, and the full theta scalar gradient energy. Its leading coefficient is independently nonzero at every actual Xi occurrence. The original eigen-equation and actual derivatives discharge all source premises. The [formalized leaf](../../../3-formalized/hb-source-contact-differential-rigidity.md) passed its foreground scratch check and 172-second exact cached audit without final warnings. It is not a physical action sign or a cancellation of the nine independent channel pairings.

**C25: the common Hawking clock supplies stationary-horizon rigidity. Failed as an inference.** A fixed parameter does not make the evolved horizon Killing. The Raychaudhuri balance retains both expansion endpoints; inserting the changing area density also changes its quadratic bulk term. The recent black-hole jet rigidity argument requires actual stationarity and a specific positive null stress. No such premise is added to HB.

**C26: reflection or dual gluing makes the complete action positive. Not established.** The recent cusp-bootstrap and quantum-transport methods require positive Hermitian state pairings. The actual contact and oriented left-current pairings are complex bilinear and retain cusp subtractions. Their positive realization has not been derived. The [new source-contact balance card](hb-source-contact-spin-two-balance.md) records the papers and the failed applicability tests.

**C27: the literal contact controls its retained spin-two face by an angular Green identity. Quartic admission and integrated cusp-remainder decay formalized; full Green transport open.** For c=7lambda-2, J=(cQ-2Delta Q)/8, a=c(c-4)/96 and H=2J²+aQ², the source gives J[-Delta(Delta-2)Q]=Delta H+2(c-4)J²-4Gamma(J,J)-a(13lambda-6)Q². The same card gives its finite-domain flux and all cusp exponents for the constant and actual same-occurrence angular QNM tests. This uses the original characteristic-face density and measure. It does not assume that the bilinear gradient term or finite-part periods have a sign. The existing cusp-jet leaf now admits all six original regulated quartic periods in L²/L¹ and proves that the integrated full-minus-principal Green flux tends to zero. Finite modular Green transport with the explicit native Mellin corrections, then causal/left-current transport, remains open.

Static API index refreshed; all thirteen public entries and the single umbrella import verified. Formal lint passed with existing large-file warnings. Audited canonical oleans are retained; owned temporary files and audit directory were cleaned.
