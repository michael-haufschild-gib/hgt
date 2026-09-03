# Restricted prime--Gamma cubic homotopy defect (2026-09-02)

Cards:
- `docs/drafts/pipeline/1-in-progress/universal-law-field/direct-subunit-anchor/restricted-prime-gamma-toeplitz-polar-defect.md`
- `docs/drafts/pipeline/2-fully-proven/universal-law-field/direct-subunit-anchor/restricted-unitary-cubic-relative-index.md`
- `docs/drafts/pipeline/2-fully-proven/universal-law-field/direct-subunit-anchor/gaussian-euler-continuum-relative-formation.md`

Pre-divisor formation:
`L_x(s)=sum_(n>=2)(Lambda(n)/log n)e^(-pi*x*n^2)n^(-s)`;
`M_x=int_1^infty e^(-pi*x*u^2)u^(-s)du`; `A_x'=M_x,A_x(2)=0`;
`Phi_x=(1/2)s*pi^(-s/2)Gamma(s/2)exp(L_x+A_x)`.
For x>0, Phi_x is zero-free on Re(s)>0; on Re(s)>1 it converges to xi with its log derivative. Strict-strip weak H1/2 convergence remains open.

Main object:
for boundary phase U and Hardy projection P,
`R=U*PU`, `Delta=R-P`, `mathsf T=Delta^3`.
At critical H1/2, Delta is self-adjoint Hilbert--Schmidt and mathsf T is self-adjoint trace class with explicit triple integral kernel. Two-projection decomposition gives
`Tr mathsf T=-index(PUP)=wind(u)=||H_(u*)||_HS^2-||H_u||_HS^2`.
Its +/-1 endpoint spectrum is the old polar kernel/cokernel defect. Prime mixing occurs inside
`(conj(u(z))u(w)-1)K_P(z,w)` before triple convolution.

Cubic grade is forced: linear is not nuclear in S2; quadratic is nuclear but reflection-even; cubic is first nuclear, reflection-odd, integral Chern character.

Exact source clock:
`routePPrimeGammaBaseCubicWeight(n)=Lambda(n)/(4n log(n)^3)`, hence
`B_base=(1/8)int_0^infty t^2[-zeta'/zeta(1+t)]dt
=(1/4)sum Lambda(n)/(n log(n)^3)<1`.
Burnol aperture damping diagonalizes the same prime-log semigroup, and its three-channel colligation preserves full complex matrix pairings.

Gaussian--aperture subordination:
with `Theta_Lambda(x)=J_x(1)` and `Theta_0(x)=M_x(1)`, both `J(t)` and `1/t` are obtained by the
same normalized Gaussian Mellin transform; hence `J(t)-1/t` is exactly the transform of the
atomic-minus-continuum anomaly. Also `B_base=int K_3(x)Theta_Lambda(x)dx` for an explicit positive
Mellin--Gamma kernel. This identifies Gaussian formation, continuum subtraction, prime-log
aperture, and cubic capacity as one source law.

Dynamic action:
take `C_B` as the positive trace-class primitive label Gram and `D_c` with full eigenvalue
`exp(-c*(log n+i*kappa))` (energy multiplier `n^(-2c)`). Matrix-complete Burnol colligation gives
`C_B-D_c* C_B D_c>=0`, retains off-diagonal prime/ordinate pairings, and
`B_base=int_0^infinity d/dc Tr(C_B-D_c* C_B D_c)dc`.

Literature boundary: odd trace of a projection-pair displacement is classical
Avron--Seiler--Simon (1994). Corpus-native content is cubic minimality at the proved `S_2` Hardy
boundary and exact fusion to the Gaussian/Route-P/Burnol source clocks.

Exact open RH edge:
construct before divisor specialization a matrix-complete degree-3 cyclic transgression from Gaussian Euler/Burnol formation to the Hardy pair with
`0<=Tr mathsf T_D<=B_base<1`.
This closes RH since strict-right `Tr mathsf T_D` is enclosed multiplicity. It cannot be a bounded one-particle landing or scalar budget identification; it must preserve cross-prime cyclic chains, possibly as closed-graph/mapping-cone/determinant-line transport.

STATUS F452-F458, CANNOT-216, MUST-138. No Lean written/built during current audit phase.
