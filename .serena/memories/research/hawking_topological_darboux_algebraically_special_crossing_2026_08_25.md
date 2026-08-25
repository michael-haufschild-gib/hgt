Created formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTopologicalDarbouxAlgebraicallySpecialCrossing.lean and imported it from RHTower.lean.

New source-specific result:
For a = Re rho in (0,1), overtone n, theta mediator Q=(2-a)(a-1), omega=-i(4n+3-a), the forward d=4 topological Teukolsky-Starobinsky factor C_+=Q(Q+2)+12 i M omega has unique positive algebraically-special mass
M_AS(q,n)=a(1-a)(2-a)(3-a)/(12(4n+3-a)).
The reflected sector has
M_AS(Rq,n)=a(1-a)(1+a)(2+a)/(12(4n+2+a)).
Their exact difference is
a(1-a)(1-2a)(16n+(3-a)(2+a)) /
[12(4n+3-a)(4n+2+a)],
so crossings coincide iff a=1/2.

Define paired crossing product C_+(q,M) C_+(Rq,M). It factors into positive slopes times (M-M_AS(q))(M-M_AS(Rq)). Every tilted fibre therefore has a positive midpoint mass where this product is strictly negative; nonnegativity for all real M is equivalent pointwise to critical-line placement.

Exact finite-mass horizon Darboux multiplier S_fwd=C_+/C_-, C_-=Q(Q+2)-12 i M omega. For real physical M,Q,omega it has norm one. At theta QNM continuation and M_AS, C_+=0 while C_-=2Q(Q+2) !=0: forward map has zero, reverse orientation has pole.

AdS obstruction sharpened: Darboux boundary trace map
T(W,nu,omega)(y,y')=(Wy+y',(W^2-nu^2-omega^2)y+Wy')
has det=nu^2+omega^2. At M_AS its kernel is Robin line (1,-W), while nonzero Dirichlet trace (0,d) maps to (d,Wd) and survives. Therefore local horizon algebraically-special zero is not automatically a full Dirichlet Jost zero. Exact remaining PDE producer: nonlinear Einstein/Teukolsky return must rotate physical boundary line into this Robin kernel (or otherwise prove paired crossing-product nonnegativity).

Hostile labels:
- FALSIFIED/CIRCULAR: physical self-adjoint positivity applied directly to complex off-line angular continuation.
- FALSIFIED: local horizon Darboux zero automatically gives full AdS Dirichlet scattering zero.
- PROVED: algebraically-special mass splitting, negative chamber, horizon zero/reverse pole, boundary polarization anomaly.
- NOVELTY UNVERIFIED externally.

Verification:
- Direct targeted Lean check passed.
- All 29 new propositions #print axioms: only propext, Classical.choice, Quot.sound.
- formal_tools lint found only unrelated pre-existing umbrella reachability errors.
- Scratch files and generated target artifacts moved to Trash. No git used.