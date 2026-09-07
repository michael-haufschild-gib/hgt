# CLG/TTF two-atom middle source control — 2026-09-07

RH remains unproved. Goal ACTIVE. Full chain: literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier current sign → Xi Bezoutian orientation → RH.

## Verified result
Eight new modules (1,152 lines) under formal/GaloisForLFunctions/RHTower:
ThetaCuspDeepTailCalibration, ThetaCuspDeepTailCooling, ThetaCuspTwoAtomSourceApproximation, ThetaCuspTwoAtomReflectedApproximation, ThetaCuspTwoAtomReflectedBounds, ThetaCuspTwoAtomScalePolynomials, ThetaCuspMiddleLikelihoodBounds, ThetaCuspMiddleCompensationBounds.
Each checked scratch with lake env lean, one foreground process; identical checked bytes copied, required new oleans retained, umbrella imports wired WITHOUT umbrella build. Ten NEW capstones axiom-audited once: only propext, Classical.choice, Quot.sound. Formal lint passed. No numerical source premises. Scratch and Python venv removed after this turn. Do not rebuild or re-audit old modules.

Paper exact proof and symbol mapping:
docs/drafts/pipeline/3-formalized/clg-ttf-two-atom-middle-source-control.md.
Current card: docs/drafts/pipeline/1-in-progress/clg-ttf-center-integration-compensation.md.
Frontier and route-independent STATUS updated.

## Exact estimates
q=π exp(2x), B=q−3/2, φ=first atom, Φ=full source, T=first+second literal atom.
Full n≥3 deep measure support≥8. Mdeep(19/20,0)≤1e−6 from full positive geometric domination. δ=exp(−8(q−49/20))/1e6.
For m≤10,q≥3.7: Mdeep(B,m)≤8^mδ; E=Mdeep(B,0) has 0≤(−1)^nE^(n)≤(16q)^nδ through n10.
Literal Φ−T=φE; all-order exact derivative Leibniz incidence and finite absolute error bound.
x≥8/95 implies q≥37/10 (checked using exp quadratic, π>3.14).

A=T/φ. Full reflection minus T reflection = reflected φ product times V=A+E−+E+A−+E+E−. All-order jet convolution retains first-atom reflected jets b_i:
j_n−t_n=Σ choose(n,i)b_i V_(n−i).
e_n=(16q)^nδ. Bound |V_n|≤Σ choose(n,i)(|A_i|e_(n−i)+e_i|A_(n−i)|+e_i e_(n−i)).
thetaCuspNativeScaledEvenJet vs thetaCuspTwoAtomScaledEvenJet bound through k≤5 at every x≥8/95.

All atoms derivative polynomial:
P0(q)=4q²−6q, Pnext=P/2+2qP′−2qP.
D^m φ_n=exp(x/2−q_n)P_m(q_n); q2=4q.
z=exp(−3q), U_n=P_n(q)+zP_n(4q).
W_n=Σ choose(n,i)(−1)^(n−i)U_i U_(n−i).
Two signed normalized jet k=(−1)^k W_(2k)/(P0(q)² q^k).
These are exact all-order identities, including unequal-source interference.

Complete higher M1≤1/500 on q≥3.7, M0≤M1, φ≤Φ≤1.01φ.
Exact Φ′=φ′(1+M0)−2qφM1.
Φ′≥−5Φ for q∈[3.7,5]; Φ′≥(4−2q)Φ for q∈[3.7,7].
q≤5 implies x≤1/4.
G=3Φ²+2xΦΦ′≥Φ²/2>0 on q∈[3.7,5].
G/(φ²q5)≥−1/2500 on q∈[3.7,7].
Proof uses 16x≤q and q5+2592(3+q/2−q²/4)=(q−6)²(q³+12q²+108q+216)≥0.

## Still open
H+K*ΔG positivity on x∈(8/95,7/16). Already known compact positivity through8/95 and tail q≥7 hence x≥7/16. New estimates do NOT change determinant positivity endpoints.
Need exact two-atom determinant reserve and cofactor-aware error transfer. Below q5 compensation positive. Aboveq5 use new −1/2500 loss, K*≤3e9 and actual Δ upper bound.
Then global mixed rank-six receiver thetaCuspCenterMixed_oddHankelThree_pos_of_compensatedSource; all-order hierarchy remains beyond it.

## Exploratory guidance ONLY, not proofs
Symbolic/numerical evaluation of exact two-atom W_j produced:
q=3.7 Htwo/(φ6q9)=19.482e9, Δtwo/(φ4q4)=49386; generic full absolute determinant error≤28.05e9 (too coarse), while top entry error≈109500 and its retained cofactor costs≈5.5e9, so cofactor-aware proof may work.
q=3.8 Htwo49.576e9, Δ46543, genericerr13.165e9.
q4 Htwo86.873e9, Δ42155, genericerr2.947e9.
q4.5 Htwo112.283e9, Δ35558, genericerr.0739e9.
q5 Htwo107.576e9, Δ31961, genericerr.001915e9.
q6 Htwo93.626e9, Δ28262, genericerr1.3e−6e9.
q7 Htwo86.680e9, Δ26502.
Exact Htwo rational numerator in (q,z) has100 monomials, degree(16,6), denominator q³(2q−3)^6 after cancellation.
Broad static z≤1/50000 DOES NOT suffice at q3.7..5 (negative guidance examples). Need sharper exp(−3q) dependence, e.g. calibration exp(−11.1)≤1/65000 and rational Taylor decay envelope, or small proved chambers.
Possible targets (NOT proved): Hfullnorm≥10e9 for q3.7..5; Hfullnorm≥80e9, Δnorm≤33000 for q5..7. Aboveq5 these would beat CΔG loss39.6e9. Coarse delta bound adequate with retained top cofactor; do not discard that cancellation.
Earlier exploration of broad static modular energy cones failed to support a simple positivity certificate; NOT a formal no-go.

## Efficiency/API notes
New olean import leaves ready; do not lake build umbrella.
New scratch modules: lake env lean /tmp/own_stage/GaloisForLFunctions/RHTower/Foo.lean --root=/tmp/own_stage -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/Foo.olean -M8192.
open scoped ContDiff required for ∞.
Use absolute paths or correct workdir when copying; formal cwd already ends /formal.
Exact coordinate name thetaCuspSingleAtomScale_likelihoodCoordinate x yields B=q−3/2.
thetaCuspDeepTailMoment_le_errorScale 1 needs (x := x), and numeral cast premise via (by norm_num; linarith).
Native scaled jet defined in ThetaCuspNativeOddSchurFarTail; import it.
General new hasDerivAt_thetaCuspSingleAtomReflectionScale n x is checked.
No processes left running.