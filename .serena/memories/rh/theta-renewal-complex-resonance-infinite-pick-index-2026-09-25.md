# Theta renewal feedback: resonance phase and Zeno crossing law (2026-09-25)

Authoritative paper card: docs/drafts/pipeline/2-fully-proven/theta/theta-renewal-complex-resonance-stieltjes-obstruction.md. Routes STC/CSB/U via theta one-port. Paper-only; no RH proof/falsification; Lean formalization and external novelty audit OPEN. User says frontier map read-only, no computations, no #print axioms, no umbrella builds.

Definitions: a=1/4, c=Theta(1), ν(t)=2πΣ_{n≥1}n² exp((a+1)t−πn²e^t)>0, N(z)=∫₀∞e^{−zt}ν(t)dt, D(z)=c−N(z); A(λ)=(a+λ)D(λ), B(λ)=(a−λ)D(−λ), K=B/A, Xi(2iλ)=A(1+K). Existing source card gives q=N(−a)/c<1/6, D zero-free Re z≥−a, A(iy)=icy+H(−2y), B(iy)=−icy+H(2y), Xi(2y)=H(−2y)+H(2y), H one-sided theta Fourier source. Re D(iy),Im D(iy)>0 for y>0, so v(y)=Im A(iy)>0, v(y)=cy+o(1), v'(y)=c+o(1).

Earlier paper theorem in same card: D entire finite order; one real root x*<−a, infinitely many nonreal roots all Re<−a. J(z)=∫t e^{−zt}W(t)dt=1/(z+a)−N'(z)/(c−N(z)) has nonreal D-root poles, excluding a nonnegative or absolutely convergent signed real-rate mixture for positive W=e^{−at}/t+Q. CM W alone would not imply RH. Pick defect P_K has infinite positive and negative index: at positive simple critical y_j, K(iy_j)=−1, boundary Gram offdiagonal 0 and diagonal d_j=−(d/dy Xi(2y))_yj/v(y_j). Opposite signs occur infinitely via corpus half-port theorem. T=diag(d_j) is trace-class (XiC Schwartz and zero count O(Y log Y)), injective with dense nonclosed range. Inverse loop 1/(1+K) residue at iy_j equals 1/d_j; residues grow faster than any power.

NEW sharper growth/product: From gamma upper bound and retaining n=1 theta summand on [log R,log R+1/R], log M_D(R)=R log R+O(R). Thus D order exactly 1, infinite exponential type. Corpus OrderOneHadamardFactorization.lean has generic genus-one factorization; paper specialization:
D(z)=D(0)e^{βz} ∏_{ζ:Dζ=0}(1−z/ζ)e^{z/ζ},
β=D'(0)/D(0)>0, ∑|ζ|^{−2}<∞ (multiplicity counted).

NEW exponential inner-strip flatness: Existing Lean XiHorizontalStripDecay.lean proves XiC horizontal exponential bound. For 0<b<a and 0<κ<π/2, sup_|x|≤b |1+K(x+iy)|=O_{b,κ}(e^{−κ|y|}/(1+|y|)); uniform Riemann–Lebesgue gives D(x+iy)→c and A~cy. This supersedes previous superalgebraic version. Every finite inverse-height expansion of K is −1.

NEW Zeno resonance-phase law: Define θ(y)=arg A(iy)∈(0,π), θ(0)=0, θ∞=π/2, u(y)=Xi(2y)/2, v=Im A. Then
θ−π/2=−arctan(u/v);
θ'=(u v'−v u')/(u²+v²)
   =a/(a²+y²)+β+Σ_ζ Re[1/(iy−ζ)+1/ζ].
The sum absolutely converges for each y via ∑|ζ|^{-2}. XiC exponential strip bound and Cauchy estimate give |u|+|u'|=Oκ(e^{−κy}), so |θ'|=Oκ(e^{−κy}/y), ∫_Y∞|θ'|=Oκ(e^{−κY}) for every κ<π/2. At each positive simple critical zero y_j, θ(y_j)=π/2 and d_j=2θ'(y_j). Unconditional half-port theorem gives infinitely many crossings of each orientation despite vanishing total phase variation tail: 'Zeno' oscillation. Resonance product exhibits exponential cancellation of positive seam Lorentzian and positive drift β against left-half-plane resonance cloud. No fixed sign or net winding excludes off-axis zeros.

Tested attempted weld: corpus GammaSewnMobiusApertureStokesCompletedPrimeGammaSpectralFlowIdentification.lean has source winding −1 and completed flow −8t·xiRealLogDeriv(1/2+2|t|) on zero-free real Euler ray, with one center crossing. Cannot identify via continuous scalar monotone zero-preserving reparametrization with θ−π/2, which has infinitely many zeros. Complex nonlocal information required. Broad recent arxiv search yielded no justified transfer.

Remaining RH gate: source-derived confinement of the *complex continuation* of exponentially small renewal/resonance remainder, i.e. K avoids −1 off critical axis. Current results paper-only and do not prove it. No Lean source changed this turn; no owned Lean process or computation.