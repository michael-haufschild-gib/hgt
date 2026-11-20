# One reduced Hamiltonian for a finite observation window

**Stage** 3-formalized. **Parent** [Static-Hamiltonian spectator problem](../1-in-progress/quantum-spectator-recurrence.md).

For a Hermitian Hamiltonian on D = km levels with spectrum in [a,b], there is one choice of tensor coordinates and one diagonal k-level Hamiltonian K such that

$$
\frac1D\left\|e^{-itH}-W(e^{-itK}\otimes I_m)W^*\right\|_{\mathrm{HS}}^2
\le \frac{2|t|(b-a)}{k}.
$$

The same W and K work at every real time. Each retained level has multiplicity m. For a window of half-width T the bound is at most ε² whenever k ≥ 2T(b−a)/ε² and k divides D. The encoding W may be nonlocal.

**Proof.** Sort energies in increasing order and divide them into k blocks of size m. Retain the lowest energy of each block. If a block has width w, each squared phase error is at most min(4,t²w²) ≤ 2|t|w. The sum of the block widths is at most b−a. Conjugation by the energy eigenbasis preserves the Hilbert–Schmidt norm.

**Lean.** [SpectralBlockHamiltonian.lean](../../../../formal/GaloisForLFunctions/HTGeometry/Quantum/SpectralBlockHamiltonian.lean) proves the interval-width bound in energy coordinates, its exact matrix-error identity, and the matrix capstone `exists_equalMultiplicity_hamiltonianSimulation` with the enclosure [−max|E|,max|E|]. Direct source check passed. The capstone uses only `propext`, `Classical.choice`, and `Quot.sound`.

**Priority and scope.** Time–bandwidth compression for quantum dynamics was derived by Kosut, Ho and Rabitz. The result above specifies an autonomous tensor-factor simulator with predetermined equal multiplicities and a uniform-in-time error estimate. Gate complexity in the original tensor coordinates remains open. [Physical Review A](https://doi.org/10.1103/PhysRevA.103.012406)
