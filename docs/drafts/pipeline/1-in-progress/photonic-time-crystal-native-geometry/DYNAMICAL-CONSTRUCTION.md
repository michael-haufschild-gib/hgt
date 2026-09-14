# From a temporal dielectric to an arithmetic scattering problem

Michael Haufschild. Research construction; derived bridges and open physical identifications. Nothing in this note is asserted to be a new unconditional Lean theorem. No zeta values, primes or known zero ordinates are inputs to the proposed drive.

## What is being reframed

The candidate primitive is an optical displacement lattice transported by a temporal dielectric. Riemann zeta would count repeated displacement directions; its zeros would appear in the analytically continued response of the lattice space at a cusp. RH would become a confinement statement for those response resonances.

An ordinary Gaussian photonic time crystal does not by itself select this arithmetic space. The displacement lattice is an explicit additional preparation, for example an optical GKP encoding. Its phase and logical data cannot be discarded without specifying the reader. The point of the construction is to identify exactly where the integer quotient and Riemann factor arise physically, rather than writing a zeta-dependent dielectric profile.

## Native evolution supplies more than a topology

For an ideal transverse mode with k=1, canonical coordinates obey

    qdot = p/epsilon(t),  pdot = -q.

A positive-permittivity quarter-wave segment has matrix

    B_epsilon = [[0,1/sqrt(epsilon)],[-sqrt(epsilon),0]].

Two such segments, with epsilon=1 and epsilon=lambda^2, have monodromy

    F = -diag(lambda^-1,lambda).

Both temporal interfaces are included in this canonical product. Symplectic area is conserved; pump work is not discarded. The model excludes material dispersion and pump backreaction explicitly. The common group of these matrices is G=SL(2,R).

At fixed symplectic cell area, an oriented displacement lattice is represented by g Gamma, Gamma=SL(2,Z): changing an integer basis does not change the lattice. This arithmetic quotient is not obtained from band topology alone. Quantum displacement commutation adds the stabilizer-phase fibre and quantizes the area for a code. The full object is therefore richer than the bare quotient. The GKP lattice and phase-bundle constructions are established in [Conrad–Burchards–Flammia](https://arxiv.org/html/2407.03270v2) and [Burchards–Flammia–Conrad](https://arxiv.org/html/2410.07332v2).

For a positive-trace hyperbolic monodromy M=C a_l C^-1, a_l=diag(exp(l/2),exp(-l/2)), the map

    g Gamma -> Gamma g^-1 C

converts the actual left action by M into right action by a_-l. This is sampled modular geodesic flow. Negative trace introduces a central sign that is harmless on the projective lattice base but can matter for quantum transport. Micromotion between samples remains part of the physical path.

This argument does not use a Fubini–Study, Grassmann or Bures metric. Their measured finite-energy anisotropy therefore does not invalidate the group-action construction. It invalidates an attempted identification of those particular metrics with the standard one.

## A native candidate for the scalar operator

There is also a concrete way to generate the hyperbolic operator, rather than choosing it because its spectrum contains a familiar function. Add phase-randomized squeeze cycles: before and after a two-layer period, rotate the oscillator frame by opposite angles, with angle uniformly distributed. This is a specified stochastic control protocol, not a property of every time crystal.

On scalar lattice-shape observables, inversion identifies the base with Gamma\G/K, K=SO(2). A conjugated squeeze R_theta a_l R_theta^-1 induces the angular mean of geodesic steps. The terminal K rotation disappears only for this explicitly scalar, rotation-insensitive base reader. The corresponding quantum phase/logical transport is not being asserted to disappear from the full state.

Here is the local generator calculation. Set

    X = (1/2)diag(1,-1),
    S = [[0,1],[0,0]],  U = [[0,0],[1,0]],
    V = (S+U)/2,  J = S-U.

These symbols also denote the induced right-flow differential operators. Conjugating X by R_theta gives cos(2 theta)X-sin(2 theta)V. Averaging its first power gives zero; averaging its square gives (X^2+V^2)/2. Consequently, for a smooth scalar observable supported away from the cusp boundary, one short-step averaging operator has expansion

    T_l f = f + (l^2/4)(X^2+V^2)f + O(l^4).

The Lie-algebra Casimir identity is

    Omega = -X^2-(SU+US)/2
          = -X^2-V^2+J^2/4.

On K-invariant functions Jf=0, and Omega is the positive hyperbolic Laplacian. Thus the local diffusion generator is a fixed multiple of

    -Delta_H = y^2(partial_x^2+partial_y^2).

This is a derived local bridge, not a completed stochastic-limit theorem on the noncompact quotient. It identifies the mathematical operator selected by an isotropic ensemble of native squeezes. Tightness at the cusp, operator domains, the physical measurement of scalar lattice observables, and convergence with finite energy remain open. They cannot be supplied by the local Taylor expansion.

The limiting clock is diffusive cycle time, proportional to the number of cycles times l^2. At a fixed physical cycle duration, the diffusion rate tends to zero as l tends to zero; no infinite modulation rate is assumed. These small stochastic steps need not individually close a lattice. The integer-trace condition in the closed-loop experiment serves a different purpose: selecting a periodic lattice trajectory for a transport audit.

The group/Casimir formulas can be checked against Sections2.2–2.3 of [Faure, May2026](https://arxiv.org/html/2605.28243v1). That paper's global geodesic-to-wave theorem assumes a compact quotient. Only local Lie algebra is used here; no compact spectral theorem is transferred to the modular cusp. [Arnoux–Schmidt, May2026](https://arxiv.org/html/2605.09230v1) also explains why a discrete continued-fraction return map needs its return-time function before it describes geodesic time.

Computing this known second-order expansion on a large grid would be a predictable identity check, not a discovery experiment. The discriminating computation must concern its missing physical reader or cusp boundary.

## Why this construction produces Riemann zeta

Write tau=x+iy for a lattice shape. A nonzero lattice direction (c,d) has squared norm proportional to |c tau+d|^2/y. Its Mellin-weighted sum separates uniquely into a primitive direction and an integer multiple. Initially for Re(u)>1,

    E(tau,u) = (1/2) sum_gcd(c,d)=1 y^u/|c tau+d|^(2u),
    sum_(c,d)!=0 y^u/|c tau+d|^(2u) = 2 zeta(2u) E(tau,u).

The Riemann factor counts all positive integer repetitions of each primitive vector. An arbitrary spectral zeta was not selected by resemblance. However, a physical reader of all displacements has not automatically measured the primitive-normalized response E.

Average E over one horizontal lattice-basis period. The vertical primitive pair gives y^u. For each c>=1 there are Euler-phi(c) primitive residue classes of d modulo c. The remaining integral separates into

    integral_R y^u/(r^2+y^2)^u dr
      = sqrt(pi) Gamma(u-1/2)/Gamma(u) * y^(1-u),

and the repetition count

    sum_(c>=1) Euler-phi(c)/c^(2u) = zeta(2u-1)/zeta(2u).

Therefore the standard scalar cusp response is

    E_constant(y,u) = y^u + phi(u)y^(1-u),
    phi(u) = sqrt(pi) Gamma(u-1/2) zeta(2u-1)
             / (Gamma(u) zeta(2u)).

These are established arithmetic scattering formulas, not new experimental findings. A source for the actual scattering interpretation is [Dyatlov, lecture24](https://math.mit.edu/~dyatlov/18.156/lecture24.pdf); see also Example2 of [Zworski, Scattering resonances as viscosity limits](https://math.berkeley.edu/~zworski/resvis.pdf). An optical experiment must still identify its incoming/outgoing normalization with this object. Measuring a standing-wave constant term is a different operation; the current Lean corpus already contains a nonvanishing obstruction to treating that constant term as a zero receiver at half-zeta-zeros.

## Where the critical line and zeros live

The variable tau labels optical lattice shape. The variable u is a complex scaling/spectral parameter of the response on the space of shapes. They are different planes. Neither u nor a Riemann zero is a dielectric constant or a programmed drive frequency.

For this scalar modular response, a nontrivial Riemann zero rho gives a resonance at u=rho/2. Thus RH is equivalent, within the established arithmetic receiver, to requiring these resonances to have Re(u)=1/4. The scattering unitarity axis is Re(u)=1/2. Conservation of flux on that axis does not prove the desired resonance confinement.

The distinction has a structural explanation. The lattice-shape scattering problem has two-dimensional scaling, while the multiple-cover factor counts a one-dimensional integer repetition. The Riemann functional-equation reflection s->1-s becomes u->1/2-u for s=2u, with centre1/4. Modular scattering pairs u with1-u, with centre1/2. Confusing those two dualities would create a false proof. Symmetry about either line alone also does not require zeros to lie on it.

An exact physical realization of phi would therefore establish identification, not selection. The remaining question would still be: what additional native law rules out the paired off-axis resonances while retaining the known on-axis ones? No such law is presently supplied by this construction.

## Current experimental consequences

The finite-energy geometry experiments rule against automatically assigning the standard hyperbolic metric to their particular state readers. Phase-correct variations show why the stabilizer fibre must be retained. Neither observation is a no-go for ideal lattice dynamics or the local phase-averaged generator above.

The active transport experiment instead starts from a two-layer physical monodromy and chooses its closed integral lattice. It compares unmonitored evolution, moving code measurements, and their interleaving. Each map retains its rejection probabilities and all logical channels. The first numerical maps show that high survival and correct ideal logical transport are distinct properties; independent precision and monitoring-step challenges are required before a validated conclusion.

The scientifically relevant next objects are therefore the physical matrix-valued transport over the lattice base and its scalar ensemble readers. Replacing that matrix data by an abstract scalar Laplacian is exactly the correspondence that must be established. This is the unresolved middle of the reframing, not a small constant to optimize and not a theorem already implied by naming the modular surface.

## Positive residue of the transport experiment

The observed improvement from driven monitoring has a candidate Gaussian explanation. If the dense-lattice limit makes a one-step projected amplitude scalar with factor a(D)=2/sqrt(det(I+D^T D)), then for the second quarter-wave segment of the trace-m cycle its survival factor is

    a(D)^2 = [1+(m^2-4)sin^2(pi/n)/4]^-1,

where n is the total even number of monitoring steps. The first, orthogonal segment commutes with the energy envelope. The resulting candidate whole-period survival is

    p_candidate = [1+(m^2-4)sin^2(pi/n)/4]^(-n/2).

The determinant identity is elementary; identifying a(D) with the actual infinite-energy code amplitude is an unproved limiting bridge. The already-computed delta=.05data agree with this candidate at roughly1e-6to4e-4relative error across d2/3, m3/6, n64/128. This is a post-result explanation, not a preregistered prediction or a proven universal law. It should not be advertised as a fresh numerical discovery merely by computing more agreement.

The decisive positive possibility is qualitative: the actual temporal pump may cancel the divergent motion of sharp code states that makes purely geometric monitoring ineffective. At the independently checked d2,m3,n64points, changing delta from.2to.05 reduces geometric survival from.134058to9.7387e-11, while driven survival remains.908159/.908319. The driven logical response also approaches its ideal counterpart at those two finite points, but is not exactly equal. The uniformity of such a scalar limit over cusp excursions is unproved. The phase-sensitive metric failures warn specifically against assuming this uniformity from fixed-lattice asymptotics.

A useful next test must attack the full response or its scalarization across a cusp, with all phase and logical channels retained. Another scan that only confirms the determinant survival factor would optimize an already visible mechanism and is not admitted as a discovery experiment.
