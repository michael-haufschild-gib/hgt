# HB: actual circle cancellation and regular source remainder

Goal active: unconditional RH via literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. RH and complete pairing extinction remain unproved. Frontier map read-only; no mathematical computations; one foreground Lean process at a time; exact leaves only; new-only axiom checks.

## Installed positive result
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCausalSourceAdjoint.lean` now 732 lines, existing namespace `RHTower.D4BMCausalSourceKernel`, already imported by RHTower umbrella. Nine added public theorems: legendre_zero, legendre_one, legendre_contDiffAt, sourceKernel_action_circle_cancel, circleRemainder_eq_second, actionRemainderDensity_eq_second, regularActionWeight_eq, actionRemainderDensity_eq_regular, regularActionWeight_continuousAt.

The actual Legendre kernels P0=1, P1=Z supply two exact radial moments in prior sourceKernel_action. They cancel all explicit Gamma terms in the assembled expression:
(lambda−2)K_nu(E)=2K_0(E)[E P_nu'(E)−P_nu(E)]−a² integral_direct a_D R_nu +a² integral_image a_D R_nu,
R_nu(E,Z)=P_nu(Z)−P_nu(E)−(Z−E)P_nu'(E), a_D=(L_D−2)g.
No Gamma=0 hypothesis. Exact integral second remainder: R=(Z−E)^2 J, J=integral_0^1(1−t)P_nu''(E+t(Z−E))dt. Actual positive-chart kernel C∞ including Z1 is proved via hypergeometric power series.

Homogenized source cubic C_reg=c C(s,0,u)+d[C(s,1,u)−C(s,0,u)]. `regularActionWeight` explicitly equals c² a_D and has no slope denominator. Combined integrand =u² regularActionWeight*J. Numerator is jointly continuous in c,d,u for 1+u>0, including c0. Full joint parameter-integral continuity/admission is NOT proved.

Scratch lake env lean passed without warnings. Exact leaf lake build passed 49sec/3jobs, 3972 existing own dependencies frozen and external caches reused. No dependency/umbrella builds. Only nine new theorems axiom checked: standard propext, Classical.choice, Quot.sound. Installed source/olean/ilean byte-matched audited copies. Do not re-audit old 5 or these 9 absent changes. Details card `docs/drafts/pipeline/3-formalized/hb-causal-circle-cancellation.md`.

## Direct attack remaining: regular fixed-clock pairing
`docs/drafts/pipeline/1-in-progress/hb-causal-circle-taylor-cancellation.md` contains complete analytical derivation, including equations13–14. Full-angular circle admission remains analytical.
Let kappa_s(q)=K_(s,0,a)(exp q), J_s(q)=coexact(M_(exp q)Q_s), R_s=signed regular remainder. Then A k_s=2kappa_s(J_s'−J_s)+R_s, A=D−2.
Integrating circle derivatives in original finite clock equation8 yields W_t=−2[kappa_t partial_r B_V+(kappa_t'+kappa_t)B_V], W_s analogous partial_q. Upper-delay edges vanish by original flat-onset clock. Lower edges combine with original contacts into the SAME derived effective contact S_hat_s=S_s+2kappa_s(0)J_s(0). All E_V terminal terms and b_Omega angular Green terms are retained. Equation13 gives exact remaining bulk and edge integrals, NOT vanishing.
kappa_s(0)=−a²[A I1+k B I3], Ij=integral_0^1 u^j(1+u)^(2s)du. kappa_s(q)=−a² integral_b^1 u(1+u)^(2s)[A+kB u²]du. b=(expq−1)/(expq+1); kappa_s'=(a²/2)b(1−b)(1+b)^(2s+1)[A+kB b²].
Hard target remains actual complete pairing 2 Omega(B(p,p)/2,B(m,m)/2)=0, with all independent SS/SV/VV monomials, original physical causal response, onset/horizon/AdS/cusp boundaries. Need prove cancellation of equation13 plus remaining sectors, not another generic obstruction.

## Efficient toolchain lessons
`open scoped ContDiff` needed for ∞; finite n≤∞ prove by `change (↑(2:ℕ∞):WithTop ℕ∞) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top`. `ContDiffAt.restrict_scalars` uses underscore. ofReal C∞ via `Complex.ofRealCLM.contDiff.contDiffAt`; typed inner map or comp_of_eq avoids unification recovering wrong source. `ContDiffAt.derivWithin` yields full deriv. Taylor uses map_add_eq_sum_add_integral_iteratedFDeriv n1 plus iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod; actual second derivative identified by local equality of deriv P and existing P'.

Broad corpus Fokas search: 2831 decls/210 modules; Higgs285/26. Inspected FokasLenellsSecondDecay.uniformizedOffDiagonal_corrected_eq (exact opposite-endpoint leading cancellation) and RawScatteringTaylor.rawScatteringMatrix_cubic_factor (all cross terms retained in exact remainder). These are method analogies only, no claimed BM identification.
