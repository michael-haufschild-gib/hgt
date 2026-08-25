Evaluated exact Birmingham–Mokhtari composite frequency/Jost data and isolated why full nonlinear C,R evaluation is not determined by BM linear modes.

Files:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCausalChannelEvaluation.lean
- docs/drafts/pipeline/1-in-progress/hawking-bm-augmented-einstein-mode-evaluation.md
- import added to formal/GaloisForLFunctions/RHTower.lean
No git; endpoint/frontier ledgers untouched.

For chi angular square root and d_n=2n+3/2:
omega_+=chi-i d_n, omega_-=-chi-i d_k.
Omega_pp=2chi-i(4n+3);
Omega_pm=-i(2n+2k+3);
Omega_ppm=chi-i(4n+2k+9/2).
With BM connection exponents A=3/4-i(omega-chi)/2, B=3/4-i(omega+chi)/2, c=1-i omega:
A_pp=-2n-3/4-i chi/2;
B_pp=-2n-3/4-3i chi/2;
c_pm=-(2n+2k+2);
A_pm=-n-k-3/4+i chi/2;
B_pm=-n-k-3/4-i chi/2;
A_ppm=-2n-k-3/2;
B_ppm=-2n-k-3/2-i chi.
Thus +- is an exact odd Hawking–Matsubara Frobenius resonance. Reciprocal Jost factors remain regular for Re chi !=0, but full causal R_pm requires logarithmic horizon normalization. Fixed-chi Laurent finite part of Gamma(c)Gamma(1/2)/(Gamma(A)Gamma(B)) at c=-N has residue P=Gamma(1/2)/(N!Gamma(A0)Gamma(B0)) (N even) and finite part P[H_N-gamma_E-(digamma A0+digamma B0)/2].
At Omega_ppm, A is a negative half-integer, so same-fibre plus Jost never vanishes; for Re chi !=0 full Jost is nonzero. This excludes coincident source pole, not causal excitation of target QNM: half-line turn-on gives Cauchy transforms and retarded Green tails.

Exact bulk trace-reversed Einstein jets from connection difference:
K(h)=linear connection difference, H_h=gbar^{-1}h,
D(A)=nabla_rho A^rho_(nu mu)-nabla_nu A^rho_(rho mu),
Q(A,B)=A^rho_(rho lambda)B^lambda_(nu mu)-A^rho_(nu lambda)B^lambda_(rho mu).
U=H_pK(m)+H_mK(p), V=H_pK(p),
W=H_pH_pK(m)+H_pH_mK(p)+H_mH_pK(p).
Then B_bulk(p,p)/2=-D(V)+Q(Kp,Kp);
B_bulk(p,m)=-D(U)+Q(Kp,Km)+Q(Km,Kp);
C_bulk(p,p,m)/2=D(W)-Q(Kp,U)-Q(U,Kp)-Q(Km,V)-Q(V,Km).
Cosmological term has no B/C jet. Gauge driver and horizon/AdS boundary residuals add their own jets.

Full causal responses require horizon harmonic product coefficients, KI metric reconstruction, sourced radial kernels, gauge/boundary jets, and exceptional stationary charge closure; BM 2006 supplies only homogeneous linear master/Jost data. Exact one-sided transforms:
uhat_pp=-i sum_lambda G^ret_lambda(omega) S_lambda,pp/(omega-Omega_pp);
uhat_pm=Mhat0-i sum_lambda G^ret_lambda(omega) S_lambda,pm/(omega-Omega_pm).
Total source uses causal frequency convolutions plus i C_aug/[2(omega-Omega_ppm)], then adjoint pairing at target pole. BM data alone cannot yield a scalar value.

Validation: direct Lean source and exact target build passed. All 33 public declarations axiom-audited: only propext, Classical.choice, Quot.sound. Lint has only pre-existing unreachable modules; new module reachable. Custom corpus search indexes declarations. Scratch and target build artifacts removed.