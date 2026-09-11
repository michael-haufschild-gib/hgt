# HB: principal growth from the original complex potential

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Target

Replace the coarse norm-of-potential growth estimate for the three actual principal responses with a rate below 7/4. This attacks the gap between causal Laplace admission and the physical Green chamber 3/2<Re(w)<2. The actual principal exponents are m=2ρ,1,2−2ρ. Hence 0<Re(m)<2, while Im(m) need not be bounded. The added (2π)² in `principalWavePotential` cancels the free generator mass; the physical equation is u_tt−u_xx−m(m−1)sech²(x)u=f.

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

The final term is at most 3E. Therefore Re(conjugate(w)b_w(u,u))≥(Re(w)−3/2)E. The pointwise bound c h≤2 also gives E≥||u_x||²+|w|²||u||². For Re(w)>3/2 this controls the original H¹ graph norm. Applying the form equation to its actual solution yields ||u||≤||f||/((Re(w)−3/2)|w|). The next formal attempt is to prove the tanh factorization on the original radial Dirichlet graph, build the rotated coercive inverse there, and identify it with the original principal response on the existing overlap. This is presently a paper derivation, not a proved additional inverse.

The energy calculation is a paper derivation for classical solutions with admitted boundary terms; it is not yet a Lean theorem for `principalTimeResponse`. Use the proved native/physical principal-response equality to establish the required time and radial regularity, finite propagation, zero initial data and energy identity for the actual response. Verify the physical normalization against the existing mass-conversion theorem. Prove the weighted forcing-square bound from the literal principal forcing, then transfer the estimate through the three bounded cutoff operators without adding their exponents.

The complete residual also needs a response estimate or a refined Hardy/Laplace construction: replacing the principal source growth alone does not remove the extra unit shift in the currently stated causal Laplace theorem. Only after that transfer is proved may the smaller chamber be used to identify QNM profiles and traces.

No experiment is required for these inequalities. Frontier map and universal-law ledger remain unchanged.
