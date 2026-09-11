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

2026-09-11: the exact source, pulse and actual wave-image translation moments are formalized in `ThetaCuspHawkingBMFixedClockSourceTranslation` (218 lines, seven public theorems). Scratch check and exact leaf build passed with no warnings; no dependency or umbrella build. The [formal result and proof](../3-formalized/hb-fixed-onset-translation-moment.md) give the precise scope. Extinction, complete physical-action identification and RH remain open. No route retired.

### Next direct current attack

**C7: the derivative-clock channels erase the finite translation of the incoming Einstein current.** The current is already identified with the original action and its exterior-to-horizon limit in `ThetaCuspHawkingBMFullIncomingCurrent`. All four horizon components have the exact form

    J_j(u)=exp(-6u)[C_j0 chi(u)^2+C_j1 chi(u)chi'(u)+C_j2 chi'(u)^2].

The rate -6 is common to both physical branches and independent of the Xi occurrence. The C coefficients retain distinct angular trace/normal covectors and both angular Green currents. Direct paper calculation predicts

    M_h^{-6}(J_j)=h exp(-6h) C_j0.

The derivative terms are compactly supported and have zero translation integral after the fixed demodulation. The squared onset tends from zero to one and contributes h. This determines an incoming boundary contribution; it does not identify the temporal test with the left-QNM state.

**C8: original-measure late-slab current vanishes from temporal translation.** For T,h≥0, the direct original-measure calculation instead predicts

    integral_{1+T}^{1+T+h} J_j(u) du
      = C_j0 exp(-6(1+T))[1-exp(-6h)]/6.

Both derivative channels vanish on this slab; the complete mass coefficient survives. Both C7 and C8 now pass scratch checking, as does the original-measure identity `integral_0^T (J(u+h)-J(u)) = integral_T^(T+h) J - integral_0^h J`. Any complete fixed-clock invariance must cancel these terms against the corresponding pulse-response, cross, cusp and other radial/temporal faces. Final module audit is pending.

**C9: the incoming radial mass is a pure angular divergence. Exact residual under test.** Put s=physicalRate(q,true), t=physicalRate(q,false)=-s-3, d_s=s(s-1)/4, d_t=t(t-1)/4, alpha_s=(2s+1)(2s+2), alpha_t=(2t+1)(2t+2). Let H_s,H_t be the actual full angular potentials, Q the literal half-square, U=coexact H_s, V=coexact H_t, W=coexact Q. Dot products below are complex bilinear coordinate contractions. The original forced equations give

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

The displayed division is notation only: the formal theorem multiplies by 4c, including c=0. Proof: expand the original trace/normal covectors `U-d_s W`, `-sU+d_s(s+2)W` and their t partners in `clockCoefficients`. The U dot V coefficient is `2st(t-s)=-(st/3)(alpha_t-alpha_s)`; the other three coefficients are as displayed. No division by tilt, spectral difference or amplitude occurs. This identifies the precise source-response remainder after the angular boundary is extracted. No vanishing of that remainder, or compensation by the actual pulse response, has been derived. The algebraic source identity and its differentiated angular current are being checked in Lean.

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

Three deep corpus requests inspected candidate lemmas and source proof arguments. All returned partial coverage with pending index generations; deadlines affected reranking or semantic retrieval. Retrieved integration/translation arguments support compact endpoint telescoping, but no returned proof supplies the missing physical sign. In particular, the retrieved divergence-vanishing lemma requires the field to vanish near the boundary; using it here without deriving that premise would discard exactly the unresolved flux. Exact source text was also searched for onset translation and clock conservation.

Broad searches used reciprocity, Noether, hypocoercivity, symplectic, dissipation and observability, prioritizing June–September 2026. Primary-paper checks:

- [Ghosh, Gauge theory and symplectic structures, 2 September 2026](https://arxiv.org/html/2609.02699v1): the square-completion argument around Theorem 1.9 keeps curvature and topological terms; integration by parts uses a closed symplectic manifold. **C4:** transfer a Weitzenbock square completion to orient the HB action. **Not closed:** HB's Lorentzian/complex pairing, radiative boundaries and source contacts do not meet those assumptions. The useful demand is to exhibit the complete compensating curvature and boundary terms, not infer positivity from a formal square.
- [Coppola–Lenarcic, Dissipative framework for subsystem dynamics of noninteracting quantum chains, 21 August 2026](https://arxiv.org/html/2608.21336v1): generator reconstruction assumes a quadratic Hamiltonian, initially uncorrelated states and a Gaussian environment. **C5:** recover a positive reduced dissipation law from complete evolution. **Not applicable as a proof:** nonlinear Einstein assembly and its initial/source correlations do not satisfy that theorem's hypotheses; no fixed-clock extinction follows.
- [Li et al., Sensing-Limited Control Under Non-Designable Observation Mechanisms, 30 June 2026](https://arxiv.org/html/2606.31396v1): the sufficient observation mechanism needs a strict information surplus plus curvature/conditioning assumptions. **C6:** use a source-derived strict deficit bound instead of exact covariance. **Open:** the translated idea is the epsilon<1 estimate above; neither the positive geometry nor the needed source bound has been constructed. The paper's theorem itself does not apply to HB.

No novelty claim beyond the audited corpus comparison is made. These are attempted mathematical transfers, not citations proving extinction.
