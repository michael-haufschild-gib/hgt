# Native optical lattice geometry: first experimental result

This is a physical-geometry feasibility test, not a computation of Riemann zeros. No zeta values, zero ordinates, primes or theta-cusp source are used in the experiment. The optical GKP lattice is an explicit non-Gaussian state preparation added to a photonic time crystal; it is not generated from vacuum by a quadratic dielectric modulation.

## Question and objects

Does the distinguishability geometry of finite-energy quantum optical lattice codes select the hyperbolic metric needed by the proposed modular cusp-scattering construction? Let [q,p]=i, H0=(q^2+p^2)/2. The ideal dim-d code columns are comb_j(q)=sum_n delta(q-sqrt(2*pi*d)*(n+j/d)). Deform the lattice by M(x,y)=[[1/sqrt(y),x/sqrt(y)],[0,sqrt(y)]], apply a physical rotation R(theta), then the canonical finite-energy envelope exp(-delta H0). All logical columns are retained. Their column operator Psi defines Gram G=Psi^*Psi and support projector P=Psi G^-1 Psi^*.

The metric is g_ij=Tr(partial_i P partial_j P)/2 for(x,y,theta). Raw3Dmetric is retained. The separately reported rotation-insensitive shape tensor is its Schur complement Q_ij=g_ij-g_i,theta*g_theta,j/g_theta,theta. This is an explicit extra reader; no global modular descent or elimination of stabilizer-phase fibres is claimed. A hyperbolic metric in(x,y) requires Qxx/Qyy=1, Qxy=0, and shape-independent y^2 sqrt(det Q). Pure squeezed-vacuum hyperbolicity does not establish this code-projector statement.

## Outcome

All40production cases completed at50working digits. Eight structural configurations were challenged at100/160digits with an independent Jacobi inner-comb sum, twice the outer truncation and finite-difference steps reduced from1e-5 to1e-7 and1e-9. All16challenge tasks passed. The largest full-matrix component difference between100/160runs, scaled by max(component magnitude,1e-9), was4.18e-12. These are finite numerical checks, not interval enclosures or100accurate derivative digits.

| Code dimension d | x | y | Envelope delta | Validated Qxx/Qyy |
|---|---:|---:|---:|---:|
|2|0|1|.2|0.922062653303|
|2|0|1|.05|0.999999999913|
|2|0|4|.2|0.00804266061766|
|2|0|4|.05|0.95187110674|
|1|0|1|.2|1.07961484258|
|1|0|4|.2|4.38190401287|
|1|.3|8|.2|11.2251752796|
|2|.3|8|.2|7.9717601757e-07|

Near the square shape, decreasing delta yields close agreement with the hyperbolic shape ratio. Toward the cusp, the same finite-energy prescription has strong directional anisotropy: at x=.3,y=8,delta=.2 the ratio is11.22517528 for d=1 and7.971760176e-7 for d=2. The disparity is not a rounding or inner-sum artifact at these points. The first metric family alone does not test an actual delta-to-zero,cusp-to-infinity limit, so it does not disprove a compact-region or limiting theorem.

## What this changes

An arithmetic lattice quotient does not automatically supply the physical hyperbolic metric at finite energy. Thus one cannot import the standard modular scattering operator merely from the topology of the photonic state space. The opposite encoding responses make probability preparation and retained logical channels relevant to the construction, not secondary numerical details.

Positive salvage: compact-shape data support investigating a local hyperbolic limit, while the cusp must be studied with its actual regulator and physical reader. The next frozen experiment compares this support-projector geometry against the Bures geometry of rho=Psi Psi^*/Tr(G), retaining actual canonical mixture weights, along coupled delta*y paths and dimensions1–4. A support projector can normalize weak logical channels differently from that density; that algebraic distinction is known, while the resulting end geometry remains the experiment's question.

## Consequence for RH and limitations

The proposed native construction is: PTC symplectic transport -> integral optical displacement lattice -> modular shape geometry -> a physically identified cusp-scattering response. On the standard modular hyperbolic surface, Riemann zeros rho correspond to resonances u=rho/2, so RH asks for Re(u)=1/4. This is different from the unitary scattering axis Re(u)=1/2. Neither measured local hyperbolicity nor conservation of flux would prove RH.

The full physical response generator, global stabilizer phases and metaplectic/rotation channels, primitive incoming normalization, finite-energy cusp boundary law and RH-independent confinement remain open. The first family uses a fixed local phase section; comparisons of odd/even code dimensions cannot by themselves establish descent to the same scalar modular quotient. No full Maxwell/material/pump simulation or HB SS/SV/VV/contact/remainder identification was performed. These missing structures are not zeroed.

The conceptual ingredients are established literature: PTC SU(1,1) geometry (arXiv2511.17317), optical lattice/modular geometry (arXiv2407.03270 and2410.07332), finite-energy GKP encoding (arXiv2605.28784). Current cached corpus searches were partial/source-only; source inspection distinguished arithmetic Floquet identities and Eisenstein constant-term blindness from a photonic realization. No Lean builds, formalization or historical-priority claim. Frozen protocols, all24method expansions, all raw tensors, code, parameters, environments and original download checksums are retained.

## Dynamical survivor after the reader comparison

The subsequent reader/cusp family confirms finite anisotropy, but a physical distinguishability metric need not generate native lattice dynamics. For ideal lattices g Gamma, a hyperbolic Floquet action g->M g is conjugate under g Gamma->Gamma g^-1 C to a time sample of modular geodesic flow when M=C a_l C^-1. Thus failure of this metric proposal does not kill that dynamical construction. The missing physical bridge is a reader/intertwiner that retains phase and envelope data and exposes the relevant cusp response. These preparation states use E_delta U(g), while actual evolution uses U(F) E_delta U(g); the two orders must not be identified. More metric refinements cannot resolve that transport issue.
