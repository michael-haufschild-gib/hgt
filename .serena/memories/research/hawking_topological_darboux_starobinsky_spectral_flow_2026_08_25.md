New Lean module: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTopologicalDarbouxStarobinskySpectralFlow.lean; imported by formal/GaloisForLFunctions/RHTower.lean.

Source-faithful derivation from Birmingham–Mokhtari d=4 potentials. Along fixed s=u*x^2:
p(s,x)=s-x^2-x^3,
nu(Q)=Q(Q+2)/6,
W(Q,s,x)=nu+3p/(Q+2+3x).
Proved:
p(B_S+B_V)/2=W^2-nu^2,
p B_S=W^2-nu^2+p(B_S-B_V)/2,
p B_V=W^2-nu^2-p(B_S-B_V)/2,
dW/dx=-(B_S-B_V)/2.
This identifies topological curvature -1 Starobinsky angular polynomial Q(Q+2), not guessed Schwarzschild Q(Q-2). Defined C_top(M,Q,omega)=Q(Q+2)+12 i M omega and algebraic bridge C_top(M,Q,omega)=C_Schw(M,Q+2,omega).

For Xi mediator theta reflection, with a=Re rho and delta=a-1/2:
Starobinsky defect = 24 delta (M_*(q)-M),
M_*(q)=a(1-a)/3>0.
Thus every tilted fiber has exactly one positive fake-confluence mass; equality at two distinct masses forces a=1/2.

Exact AIME component K(q)=-3/[Q(q)(Q(q)+2)] is bridged to d4FundamentalQNMChiralSourceKernel at the BM mediator spectral point. Its reflected defect is
24 delta/[a(1-a)(2-a)(3-a)(a+1)(a+2)],
whose denominator is positive in 0<a<1; it is nonzero iff tilted. The two-component invariant (Starobinsky defect/2, AIME defect/2) vanishes iff critical line for every mass. At M_*(q), first component vanishes while second survives for tilt.

Scientific boundary: AIME is an exact evaluated component of the nonlinear chiral source, but full second-order Einstein–Teukolsky remainder remains unevaluated and could cancel it. Remaining producer is a source-faithful phase/optical identity or remainder rigidity excluding that exact tuned cancellation; generic KMS/passivity cannot supply it.

Verification:
- target Lean check passed.
- #print axioms for all 23 new lemmas/theorems: only propext, Classical.choice, Quot.sound.
- formal_tools lint has no forbidden declarations; only unrelated existing unreachable-module errors.
- no umbrella build or git used.
- temporary source PDFs, scratch files, and generated target oleans moved to Trash.