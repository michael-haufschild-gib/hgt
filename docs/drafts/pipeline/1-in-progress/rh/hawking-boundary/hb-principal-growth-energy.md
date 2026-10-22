# HB: principal growth from the original complex potential

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Closed convergence target

Establish convergence of the actual three principal responses at a parameter inside 3/2<Re(w)<2. A common rate depending on the Xi zero and strictly below two suffices; a uniform rate below 7/4 is a stronger option. This attacks the gap between causal Laplace admission and the physical Green chamber 3/2<Re(w)<2. The actual principal exponents are m=2ρ,1,2−2ρ. Hence 0<Re(m)<2, while Im(m) need not be bounded. The added (2π)² in `principalWavePotential` cancels the free generator mass; the physical equation is u_tt−u_xx−m(m−1)sech²(x)u=f.

## Analytical energy calculation

For a sufficiently regular solution with zero initial data and justified radial integration by parts, write m=σ+iη, c=σ(σ−1), d=2σ−1 and h=sech²(x). Then c≤2 and |d|≤3. Define

E=∫ [|u_t|²+|u_x|²+(η²−c)h|u|²+2|u|²] dx.

The exact factorization

∫ [|u_x|²−c h|u|²+|u|²] dx
= ∫ |u_x+tanh(x)u|² dx +(2−c)∫ h|u|² dx

gives E≥||u_t||²+M, where M=∫(1+η²h)|u|² dx. It follows by expanding the square and integrating tanh(x)∂_x|u|²; tanh′=h and tanh²=1−h. No restriction on η is used.

Differentiating E with the actual equation cancels its real spatial part and leaves

E′=2 Re ∫ conjugate(u_t)[(2+i dηh)u+f] dx.

Pointwise, |2+i dηh|²=4+d²η²h²≤9(1+η²h), since 0≤h≤1. Thus

E′≤6||u_t||sqrt(M)+2||u_t||||f||
≤(13/4)E+4||f||².

The second inequality uses 2ab≤a²+b² and 2ab≤a²/4+4b². With E(0)=0, integration after multiplication by exp(−13t/4) yields

E(t)≤4 exp(13t/4)∫₀ᵗ exp(−13v/4)||f(v)||² dv.

Consequently, a finite weighted forcing-square integral gives ||u(t)||≤C exp(13t/8), uniformly in the rate with respect to Im(m). Constants may depend on the actual source and exponent. The rate 13/8 is strictly below 7/4.

## Outstanding landing

A frequency-domain version can avoid requiring new time regularity. Put v=w u and b_w(u,u)=||u_x||²+w²||u||²−m(m−1)∫h|u|². With the same energy E=||v||²+||u_x||²+(η²−c)∫h|u|²+2||u||², direct algebra gives

2 Re(w) E = 2 Re(conjugate(w)b_w(u,u)) + 2 Re∫conjugate(v)(2+i dηh)u.

The final term is at most 3E. Therefore Re(conjugate(w)b_w(u,u))≥(Re(w)−3/2)E. The pointwise bound c h≤2 also gives E≥||u_x||²+|w|²||u||². For Re(w)>3/2 this controls the original H¹ graph norm. Applying the form equation to its actual solution yields ||u||≤||f||/((Re(w)−3/2)|w|). The tanh factorization and rotated inverse are proved on the original radial Dirichlet graph. The causal Green-band identification follows the direct native-circle argument below. The completed-domain factorization, rotated coercivity, bounded inverse, unique original form solution and mass estimate are formalized in `ThetaCuspHawkingBMPrincipalDirichletCoercivity`. Scratch checking and exact leaf build passed; the module is installed and wired into its umbrella. See [the formalized result](../../../3-formalized/hb-principal-dirichlet-coercivity.md).

The frequency estimate also has a direct scalar proof. Set a=Re(w), b=Im(w), N=||u||², H=||sech·u||², D=||u_x||². The completed-domain factorization gives 2H≤D+N, while 0≤H≤N. With c=σ(σ−1), d=2σ−1, one has c≤2 and d²≤9. The two square inequalities

2a≤(3/2)(a²+1),  b d η≤(3/2)(b²+η²)

follow respectively from (a−2/3)²≥0 and (η−bd/3)²≥0 together with b²(9−d²)≥0. Multiplying by N and H, using b²H≤b²N and (2−c)H≥0, proves

2aN+b d η H≤(3/2)[D+(a²+b²+2)N+(η²−c)H].

The exact rotated form is aD+a(a²+b²)N+[a(η²−c)−bdη]H. Subtracting the preceding inequality proves the claimed coercivity without differentiating the time response. This scalar coercivity argument has passed the same scratch Lean check. The original completed Dirichlet graph, bounded tanh/sech multipliers and kernel-closure extension of the compact-test integration-by-parts identity are used; no new endpoint condition is introduced.

For causal identification, existing `ThetaCuspHawkingBMJointKernelCoherence` and `ThetaCuspHawkingBMJointCausalRightHalfPlane` provide a concrete method: construct shifted Hardy preimages, identify different damping choices by actual Laplace injectivity, then choose arbitrarily small extra damping. Existing `ThetaCuspHawkingBMJointSourcePrincipalGreenIdentification` identifies the original causal transform with the literal Green correction on its coarse convergence overlap. The full joint source-resolvent product now uses the generic Hilbert damping theorem and actual Laplace injectivity, as described below.

The stronger uniform time-growth rate 13/8 remains a paper derivation for classical solutions with admitted boundary terms. Formalizing that stronger rate would require the actual response energy identity and weighted forcing-square estimate. The proved native-circle rate B(q)<2 already closes the Green-band convergence and actual-response transfer below.

The generic every-positive-damping Hilbert theorem removes the old extra unit shift. The actual full joint response has now passed its original inverse/operator identification and physical projected Green/trace transfer in the smaller chamber. QNM-boundary continuation and current limits remain open.

No experiment is required for these inequalities. Frontier map and universal-law ledger remain unchanged.

## Direct native-kernel bridge

A broader Legendre search and inspection of the actual circle transport found `D4BMNativeCircle.powerCircle_eq_legendre` in `ThetaCuspHawkingBMNativeCircleGauss`: for every complex m, the literal average of height(d,θ)^m equals `legendreKernel (-m) (cosh d)`. This gives a shorter causal-growth route than constructing a new inverse.

For d≥0, denominator(d,θ)=cosh d−sinh d cos θ≥exp(−d), so 0<height(d,θ)≤exp d. If Re(m)≥0, the modulus of height^m is exactly height^Re(m), hence the normalized circle average has modulus at most exp(Re(m)d). No imaginary-part bound is needed. On the actual causal cone, 1≤invariant(h,x,y)≤cosh h. The upper inequality follows from cosh(x−y)≥1 and cosh h≥1. Therefore arcosh(invariant)≤h and the actual Riemann kernel obeys |K_{−m}(h,x,y)|≤exp(Re(m)h).

Let B(q)=max(3/2,Re(m₀),Re(m₁),Re(m₂)). The proved Xi strip gives B(q)<2. Thus the three actual kernels have a common rate B(q), and c(q)=(B(q)+2)/2 satisfies 3/2≤B(q)<c(q)<2. A q-dependent intermediate convergence point suffices to obtain overlap with the original Green band; it does not choose or change the later Hawking clock.

The proved landing uses the existing pointwise source bounds. `timeReducedCoefficient_physical_bound` at c=0 bounds the literal source uniformly (its remaining exp(2x) factor is ≤1 for x<0); zero endpoint and odd extension give a uniform bound for the actual odd source. The fixed-rectangle native retarded formula then gives |R(t,x)|≤C t² exp(B(q)t). Existing finite propagation confines its spatial support to [−t,t], so ||R(t)||₂≤C t² sqrt(2t) exp(B(q)t), bounded by a cubic polynomial times exp(B(q)t). This proves absolute Bochner Laplace admission for every Re(w)>B(q), after transfer through `nativePrincipalResponse_eq_principalTimeResponse`. The circle bound, causal invariant comparison, common three-kernel growth, pointwise retarded-response growth, spatial L² growth and Laplace admission are all formalized in `ThetaCuspHawkingBMNativeGreenBand`.

The bounded angular cutoff maps preserve this rate. The full joint response transfer and original physical projected Green/trace data passed Lean checking. The final physical left-QNM action and fixed-clock extinction remain unproved.


## Actual principal and complete-source identification

The current scratch chain transfers the cubic-exponential L² bound through the proved equality of the literal retarded integral and `principalTimeResponse`. For any r>B(q), the exponential series bounds (t+1)³ by K exp((r−B(q))t). Hence the actual response has pure growth at r, and its Bochner transform converges for every Re(w)>B(q). The existing vector-valued Laplace holomorphy theorem applies after identifying its exponential-kernel normalization explicitly.

The existing second-time-derivative Laplace law can then use r=(B(q)+Re(w))/2. Its original spatial distribution equation gives H² regularity, a continuous odd representative and the derived zero Dirichlet trace. The existing classical radial regularity and negative-ray Wronskian uniqueness proofs identify that representative with the literal principal Green correction. All three comparisons use the actual source and its onset transform. The proposed common point w=(B(q)+2)/2+i lies in the original Green band and has nonzero imaginary part. The complete source assembly applies the three bounded cutoff maps to these same principal transforms. The complete 954-line scratch passed `lake env lean`: kernel growth, actual response growth, absolute Laplace convergence, holomorphy, original H²/trace admission, literal Green identification and the complete-source transform are now checked. The exact `ThetaCuspHawkingBMNativeGreenBand` leaf build passed (only the new leaf compiled); its source and artifacts are installed and the umbrella import is present. See [the formalized Green-band result](../../../3-formalized/hb-native-green-band.md).

## Removing the joint vector inversion shift

`CauchyBoundedHilbertMap.lineVector` already exists at every positive Fourier line, although its exported causal vector uses line one. Let Q_s be the original Hilbert Fourier inverse at line s>0. Scalar Hardy coherence gives every probe the identity exp(−st)Q_1(t)=exp(−t)Q_s(t). Both sides are genuine Bochner L² on the positive ray. The existing L² probe-totality theorem therefore gives the same vector identity. Cancelling the nonzero factor exp(−t) yields exp(−st)causalDatum(t)=Q_s(t) almost everywhere. Consequently every positive damping of the original causal datum is L²; Cauchy–Schwarz then gives absolute Laplace convergence at every Re(w)>0. Its scalar-probe transform identifies the original analytic vector there.

The generic vector statement and full joint-response transfer passed their combined scratch check. A boundary for the actual full source-resolvent product at any c>B(q) is constructed from the new source bound. Both its unshifted causal datum and the already constructed original joint response admit a common large exponential damping in L². Their scalar Laplace transforms coincide with the same original frequency response; scalar Laplace injectivity and Bochner L² probe totality prove actual vector equality almost everywhere on the positive time ray. Choosing B(q)<c<Re(w) transfers absolute convergence, the original joint inverse identity, and original unbounded operator-domain equation to every Re(w)>B(q), including a common nonreal point in the Green band. The full physical angular/trace transfer also passed the combined scratch check. `HilbertHalfPlaneFullCausal` passed its exact build and is installed. `ThetaCuspHawkingBMPhysicalCausalGreenBand` also passed its exact leaf build and is installed and wired. See [the formalized physical transfer](../../../3-formalized/hb-physical-causal-green-band.md).


## Physical projected landing

The checked original joint inverse identity gives equality of the actual causal Laplace vector with the existing complete spatial response in the native half-plane. In the physical band with nonzero imaginary part, the proved continued/original source equality identifies its forcing with `continuedCuspResidualL2`. Existing height admission therefore applies to the actual Bochner transform. Applying the literal physical angular projection to that height-admitted class gives exactly `physicalCuspResponse`. The combined scratch check passed for the complete Green representative, original radial derivatives, zero Dirichlet trace, full projected source equation and denominator-cleared Green identity of this actual causal projection. The gap product is retained; no angular noncollision assumption is introduced.

This identifies the actual causal response in an open physical Green overlap. Continuing that identified object to the QNM boundary, justifying the required boundary jets/current limits and assembling/orienting the complete Einstein/left-current remain separate mathematical tasks. Fixed Hawking-clock extinction and RH remain unproved.
