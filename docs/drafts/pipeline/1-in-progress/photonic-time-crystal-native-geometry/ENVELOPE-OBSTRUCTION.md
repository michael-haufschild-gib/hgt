# Why a closed optical lattice need not be a returning photon state

Status: elementary derived obstruction, supported by established squeeze-operator theory; not a new unconditional Lean theorem. This is an audit of the physical interpretation, not a proposed RH proof.

## The exact distinction

A hyperbolic temporal-crystal period can return an ideal displacement lattice to itself through an integer basis change. It cannot return a nonzero finite-dimensional subspace of normalizable oscillator states exactly to itself under that same unmodified unitary evolution. The energy envelope is therefore essential physical data, not a gauge choice that can silently follow the closed lattice base.

To see the obstruction directly, consider the normalized dilation

    (D_r psi)(q) = exp(-r/2) psi(exp(-r) q),  r != 0.

This formula is also equation2.15 of [Chruściński, Spectral properties of the squeeze operator](https://arxiv.org/pdf/quant-ph/0403106). The paper distinguishes its continuous Hilbert-space spectrum from generalized resonance states. We use the ordinary dilation action, not a claim that its generalized equally spaced levels are Riemann zeros.

Suppose a normal oscillator density operator rho were invariant under D_r. Its position probability measure is absolutely continuous, since rho is a positive trace-class sum of normalizable pure states. Invariance would make that probability measure invariant under q->exp(r)q.

Take r>0, replacing the dilation by its inverse if necessary. All disjoint intervals (exp(nr),exp((n+1)r)], n in Z, would then have the same probability. Finiteness forces that common probability to be zero. Their union is the positive half-line. The negative half-line has the same argument, and absolute continuity assigns zero probability to q=0. Total probability would be zero, contradicting normalization.

Thus a nontrivial dilation has no invariant normal density state. In particular, a finite-dimensional invariant oscillator subspace would give one through its normalized orthogonal projector, which is impossible. The conclusion also applies after a metaplectic conjugacy. A negative hyperbolic monodromy can be squared first, retaining the same obstruction.

The paper argument is elementary, but a dependency-closed Lean formalization has not been produced or checked here. Current cached deep search is partial with pending coverage; no absence theorem about the corpus is claimed. No Lean build was run.

Source inspection found the related declaration `finitePrimeCommutingDilationHamiltonian_has_no_eigenvector` in `formal/GaloisForLFunctions/RHTower/FinitePrimeCommutingDilationNoPointSpectrum.lean`. It concerns a derivative plus finite paired translations on scalar L2(R), defined by Fourier conjugacy of a multiplier. Its source proof does not directly instantiate the normal-density or finite-code monodromy statement above. A Hamiltonian and its time-one unitary must also be distinguished. The search snapshot reports extensive pending compiler metadata, so this note does not present a fresh axiom audit.

## What fails and what survives

This rules out one interpretation: an exactly equivariant finite-dimensional normalizable code bundle whose hyperbolic lattice loops close under free photonic evolution. It does not rule out a finite-energy family of code projectors indexed by the modular lattice space. Such a family can be prepared by E_delta U(g), but its physical evolution U(F)E_delta U(g) need not stay in that family. The monitored-loop experiment measures precisely this distinction.

It also does not rule out a classical quotient of ideal lattice labels, a distributional encoding, scattering states, a controlled measurement protocol, or a limiting physical response. Each must be defined honestly. Monitoring adds its own logical transport and rejected probability; the envelope can instead be retained as an additional noncompact coordinate.

The strongest positive residue is a change of primitive: study transport over the lattice space with its escaping envelope and logical/phase fibres. A topological return of the lattice is then a scattering event in the full optical state space, rather than a normalizable eigenstate. That is compatible with looking for Riemann zeros as resonances, but does not identify those resonances or constrain their real parts.

The RH task remains two separate problems: derive the actual primitive-normalized scalar or matrix cusp response of this full object; then find a law independent of RH that confines the relevant resonances. Neither follows from ideal modular topology, unitarity, a half-integer oscillator shift, or high probability of code recovery.
