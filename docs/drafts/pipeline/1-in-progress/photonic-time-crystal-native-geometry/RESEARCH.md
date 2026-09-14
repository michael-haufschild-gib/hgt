# Native photonic geometry and the Riemann problem

Author: Michael Haufschild. Status: research construction and falsification programme; no new Lean proof, no claim of a photonic proof of RH. No Lean builds. Computations use only pod 213.173.105.94:47180.

## What the physical objects are

A photonic time crystal (PTC) is an externally driven medium, spatially homogeneous in the elementary model, with periodic electromagnetic constitutive parameters. It is not automatically a spontaneously formed time crystal. For a lossless, dispersion-free model with positive permittivity, fixed permeability and a transverse mode, choose canonical coordinates q=A and p=epsilon*dA/dt. In units c=1,

    dq/dt = p/epsilon(t),     dp/dt = -k^2 q.

Both canonical variables are continuous at ideal temporal jumps without impulsive sources. In a constant segment of duration t,

    M_epsilon(t) = [[cos(wt), sin(wt)/(epsilon*w)],
                    [-epsilon*w*sin(wt), cos(wt)]], w=k/sqrt(epsilon).

This follows directly from the two equations; it retains interface matching in the canonical frame. The conserved object is symplectic area, not electromagnetic energy: dH/dt=-dot(epsilon)*p^2/(2 epsilon^2). The modulator exchanges work with the field. Dispersion, loss, material dynamics and quantization of the pump require additional fields; they are not set to zero in a purported complete physical theory.

The full-period matrix lies in Sp(2,R)=SL(2,R). In travelling-wave coordinates it is SU(1,1), acting by Mobius transformations on a hyperbolic disk. Absolute trace below/above two gives elliptic/hyperbolic motion; at trace plus or minus two distinguish a genuine parabolic matrix from the central matrices plus or minus I. The latter distinction prevents calling every degeneracy an exceptional point. Quantum counter-propagating photon pairs give infinite-dimensional representations of the same group. Their representation label is not a Riemann spectral parameter.

Three different geometries must remain separate:

* The temporal circle and its Floquet harmonics.
* Hyperbolic geometry of a mode's canonical evolution or Gaussian coherent states.
* Topology of bands and temporal interfaces, including Berry/Zak data with their required symmetries and normalization.

None of these statements identifies the Riemann zeros with band edges. The hyperbolic disk is simply connected. A modular quotient is additional structure, not a consequence of writing SU(1,1).

Primary sources: [PTC topology](https://arxiv.org/abs/1803.08731); [quantum geometry, equations 4–8 and Appendix A](https://arxiv.org/html/2511.17317v1); [quantum PTC Hamiltonian and photon/Floquet lattice, equations 1–4](https://www.nature.com/articles/s41467-025-67572-0); [complex permittivity/conductivity modulation](https://arxiv.org/html/2609.08181v1). These are literature results, not claims of new unconditional corpus formalization. Some displayed equations in the geometry preprint contain apparent normalization/sign inconsistencies; the canonical evolution and work law above are derived from its Lagrangian, not copied indiscriminately.

## Two constructions, with different explanatory power

### Temporal circle: a native but insufficient zeta

For the native periodic coordinate theta, D=-i d/dtheta has integer eigenvalues. Omitting its zero mode, Tr|D|^{-s}=2 sum_{n>=1} n^{-s}=2 zeta(s), initially Re(s)>1. This is an elementary spectral construction: no zeta was inserted in a dielectric profile. It is also shared by every such circle, so it does not explain RH or identify the spectrum of the full modulated Maxwell operator with the integers. A quasiperiodic boundary twist changes this object to sums over shifted integers. The Mellin parameter s is a scaling dimension, not quasifrequency.

This is a [BRIDGE] calculation, not an experimental discovery or the research headline. Computing its known zeros would add no information. The functional-equation centre is an analytic duality statement about the completed spectral object; it is not supplied by the existence of a circle alone.

### Phase-space lattice PTC: a physically motivated arithmetic topology

The stronger construction equips the optical oscillator with a lattice state of commuting displacement operators, as in a Gottesman–Kitaev–Preskill (GKP) code. This is a substantial physical extension of an ordinary Gaussian PTC. It requires a non-Gaussian preparation; modulation of a vacuum by a quadratic Hamiltonian alone does not create it.

Commutation of quantum displacements quantizes their symplectic cell area. After fixing that area, bases of the same oriented lattice differ by SL(2,Z). Thus the lattice space is SL(2,R)/SL(2,Z), up to left/right convention. Rotations, stabilizer phases, logical labels and the metaplectic lift must still be accounted for. Removing a rotation with a specified rotation-insensitive reader gives the modular shape orbifold PSL(2,Z)\H. It is not legitimate to erase those fibres merely because a two-dimensional picture is convenient.

This integer quotient has a physical origin: it relabels the same displacement group. No prime locations, zeta values, zero ordinates, or theta-source profile are inserted in the drive. A PTC transports the lattice through its actual symplectic evolution. A simple positive-permittivity, two-segment example at k=1 uses quarter-wave phases: epsilon=1 for pi/2, followed by epsilon=4 for pi. Its matrix is diag(-1/2,-2). Up to a central rotation, repeated periods squeeze the lattice toward a cusp. This is an exact kinematic bridge; it does not yet generate a Laplace operator on the space of lattices.

The full lattice sum decomposes into primitive directions and their integer multiples. For tau=x+iy and Re(u)>1,

    E(tau,u) = (1/2) sum_{gcd(c,d)=1} y^u/|c*tau+d|^(2u),
    sum_{(c,d) != (0,0)} y^u/|c*tau+d|^(2u) = 2 zeta(2u) E(tau,u).

Here Riemann zeta counts multiple covers of primitive lattice vectors. This explains specifically the Riemann factor, rather than choosing an arbitrary spectral zeta by resemblance. However, a physical sum over all displacements is not automatically a primitive sum, and the primitive normalization is not automatically a measured scattering amplitude.

For the standard hyperbolic Laplacian on the modular surface the cusp coefficient is

    phi(u) = sqrt(pi) Gamma(u-1/2) zeta(2u-1) / (Gamma(u) zeta(2u)).

Nontrivial Riemann zeros rho give scattering resonances u=rho/2. Hence RH places these resonances on Re(u)=1/4. The unitary scattering axis is Re(u)=1/2. THEY ARE DIFFERENT LINES. Self-adjointness or conservation of scattering flux on the latter is not a proof of confinement to the former. Embedded cusp-form eigenvalues are a separate part of the spectrum.

Sources: [lattice geometry and modular geodesics](https://arxiv.org/html/2407.03270v2), [full GKP space and phase fibres](https://arxiv.org/html/2410.07332v2), [finite-energy encoding, Theorem 5.2](https://arxiv.org/html/2605.28784v1), [modular scattering derivation](https://math.mit.edu/~dyatlov/18.156/lecture24.pdf), [scattering resonances and regularization, Example 2](https://math.berkeley.edu/~zworski/resvis.pdf). This assembly is a proposed photonic research programme; it does not claim priority for these established mathematical connections.

## The change of viewpoint

Public statement: investigate whether Riemann zeros can be physical leakage resonances of the space of quantum optical lattices transported by a time crystal.

The new candidate object is the physical response operator on the space of lattice encodings, including its cusp and all relevant fibres. A zero would be an obstruction to a decaying response, rather than a frequency programmed into a dielectric. The critical line would become a resonance confinement law, not a line drawn through a numerical zero plot.

This remains a research direction, not a frozen universal RH law: no physical law has yet been found that forces the required resonance confinement. The universal-shadow gate explicitly forbids presenting a combination of established frameworks as such a law.

| Established ingredient or obstruction | Meaning in this programme |
|---|---|
| Symplectic PTC dynamics | Actual transport of optical displacement lattices |
| GKP lattice relabeling and phase fibres | Source of arithmetic quotient, with channels that cannot be discarded |
| Modular cusp scattering | Candidate native zero receiver, conditional on physical operator identification |
| Source representation changes preserve spectral zeros but alter complex source nodes | Geometry assigned to an arbitrary representation cannot be treated as intrinsic |
| Corpus Eisenstein constant-term blindness | Zeros of a standing-wave constant term are not Riemann resonances |
| HB identification remains separate from selection | A photonic realization, even if exact, still needs an independent confinement mechanism |

## First frozen physical hunch and its falsifiers

Hunch H1: after accounting for rotation and logical basis, the distinguishability geometry of finite-energy optical lattice codes has a universal hyperbolic shape limit; the cusp remains a genuine scattering end in the physical limiting problem.

Motivation before proof search: hyperbolic mode geometry, arithmetic lattice moduli, and fixed-lattice asymptotic isometry of finite-energy encodings are independently established. They do not imply H1. The unoccupied question is whether the physically regularized code subspaces select the metric and end structure required by the proposed receiver.

Freeze H1 without weakening it to a fixed-lattice statement. Test subclaims separately: local metric, rotation fibre, logical dimension, and the coupled finite-energy/cusp limit. A metric ratio or nonzero cross term surviving refinement can falsify the local hyperbolic identification. A collapse or qualitatively different end in coupled limits can falsify the uniform cusp part. No finite scan proves H1.

Competing explanations: hyperbolic geometry genuinely emerges; it emerges only on compact shape sets and fails at the cusp; or a different physical geometry survives even locally. Isotropic Gaussian envelopes alone do not decide this: the measured object is the derivative of the whole code projector, with projection back onto the logical subspace subtracted.

The first computation uses no zeta or zeta zeros. It measures the Grassmann metric of finite-energy GKP code subspaces under symplectic deformation, retaining the physical rotation direction and separately reporting a proposed rotation-insensitive quotient. It tests one proposed construction; it is not a prerequisite for every physical realization of modular dynamics.

## Surviving construction: dynamics before distinguishability

The finite-energy metric experiments do not justify treating optical distinguishability as the standard modular metric. At finite coupled cusp points, both the support-projector and preparation-weighted Bures readers have strong, independently validated anisotropy. Correcting the odd-code stabilizer phases changes that anisotropy substantially. No infinite cusp limit or global curvature classification has been established.

The stronger positive survivor starts with the actual group action. Write G=SL(2,R), Gamma=SL(2,Z), and an ideal lattice as g Gamma. A hyperbolic Floquet matrix M=C a_l C^-1, where a_l=diag(exp(l/2),exp(-l/2)), acts by left multiplication. The map

    g Gamma -> Gamma g^-1 C

sends M g Gamma to Gamma g^-1 C a_-l. Right multiplication by a_-l is a time sample of modular geodesic flow, with reversed time in this convention. A negative-trace monodromy also has a central sign; it disappears on the projective base but must be retained in a quantum lift. This is a derived kinematic bridge, not a new Lean theorem. It uses the native PTC squeeze, not a fitted information metric.

The full Floquet micromotion need not follow the geodesic between samples. Replacing a first-return map by a Gauss map also requires the return-time function and past/future data. These distinctions matter to any frequency or resonance claim. [Arnoux–Schmidt, May2026](https://arxiv.org/html/2605.09230v1) explains that suspension structure. [Faure, May2026](https://arxiv.org/html/2605.28243v1) develops a geodesic-to-wave construction on compact quotients; its stated assumptions do not cover the modular cusp.

Three physical spaces are now explicit: the ideal lattice quotient carrying the native flow; the full optical encoding with stabilizer phases and logical/metaplectic data; and ensembles or readers of those encodings. A resemblance between spectra on these spaces is insufficient. An actual intertwining response map is needed. In particular, a finite logical gate on one closed orbit is not the automorphic spectrum of the entire lattice space.

Finite energy introduces an additional distinction. The studied preparation is E_delta U(g) comb, E_delta=exp(-delta H0). Actual pump evolution produces U(F) E_delta U(g) comb. It does not automatically produce E_delta U(Fg) comb. The moving energy envelope is physical memory, not an ignorable normalization. A monitored preparation can choose a different response; its measurement/rejection terms must be included.

The next experiment therefore follows actual positive-permittivity temporal cycles whose endpoint closes an integral optical lattice. It compares free evolution, products of moving finite-energy code projectors, and their interleaving. Its target is whether their logical operator transport agrees, not whether a numerical metric ratio approaches one. A failure exposes the matrix-valued transport that the scalar cusp theory would have to justify removing.

## Exact unresolved bridges

1. Preparation and finite-energy transport of a lattice state by the specified PTC, including material/pump corrections when claiming physical completeness.
2. A physical response or controlled ensemble whose generator is the modular hyperbolic operator, not merely a space homeomorphic to its domain.
3. Correct handling of orientation, stabilizer phase, logical and metaplectic channels; scalar versus vector-valued scattering.
4. Cusp boundary conditions selected by finite-energy physics and a controlled limit to the ideal scattering problem.
5. Identification of the actual reader with primitive incoming/outgoing normalization, including all contact and boundary terms.
6. A reason independent of RH that forbids the relevant resonances off Re(u)=1/4 while admitting them on it.

These are not hidden premises of a claimed theorem. The computations should decide which bridge survives, changes, or fails. A failure of H1 does not disprove RH and does not rule out all PTC constructions; it removes one claimed natural identification and should expose the true metric or missing fibre as positive salvage.

## Corpus reality check

Cached deep/source-method searches on 2026-09-13 were partial, with pending index coverage and source-only candidates. Source inspection confirms that DeningerFloquetPoissonSample.lean defines the critical-line sample and factors an arithmetic Poisson source through zeta; it does not identify a PTC Hamiltonian. ZeroLedgerPairParity.lean contains a direct proof that the completed Eisenstein constant term is nonzero at half-zeros of completed zeta in Re(u)<1/2. GKP searches produced mainly discrete Pauli/stabilizer and unrelated symplectic-current hits, not a checked continuum GKP/PTC bridge. No absence theorem or fresh kernel/axiom audit is claimed. No Lean file was changed.

Rejected experiments: zeta-dependent dielectric profiles; prescribed zeta mass terms; checking the integer-circle identity by large zero scans; computing known modular scattering zeros and calling them new photon data; generic loss of invariance under arbitrary perturbations. These are encodings, established identities, or predictable effects.

## Working construction and research record

The expanded dynamics-first derivation is in DYNAMICAL-CONSTRUCTION.md. It includes the local phase-averaged Floquet generator, the primitive/multiple lattice count producing the Riemann factor, the two distinct spectral reflections, and the missing physical scalar reader. FACTS.md retains this agent's concise findings and no-gos. These research notes are not a publication-ready proof paper.
