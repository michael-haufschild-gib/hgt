# How much of a quantum echo can a few frequencies explain?

For almost every static nearest-neighbour qubit Hamiltonian in the coefficient-shell ensemble on n ≥ 3 sites, let D = 2ⁿ. Compare the source with any autonomous Hamiltonian having k distinct energy levels, in any eigenbasis. Any q chosen frequencies in the normalized trace echo carry total weight at most

$$
\min\left(1,\frac{k+q-1}{D}\right),\qquad k,q\ge1.
$$

One conull source event works for every comparison. In particular the competitor's basis, energies and selected frequencies may depend on the Hamiltonian. The measure here is the discrete frequency measure of the trace amplitude.

**Proof.** Write Eᵢ for the source energies and Fₐ for the model energies. A selected detuning vᵦ can receive weight from source level i only if Eᵢ = Fₐ + vᵦ. The affine span over the rationals of these sums has dimension at most (k−1)+(q−1). The generic source energies are affinely independent over the rationals. Hence at most k+q−1 source levels contribute. Unitarity of the basis change gives each source level total trace weight 1/D.

**Sharpness mechanism.** In the source basis, partition the energies into k nonempty sectors. Retain one representative energy per sector. The representatives produce the same zero detuning. Every other detuning occurs once because the nonzero ordered source gaps are distinct. Thus the normalized echo-frequency weights are k/D followed by D−k weights of 1/D. Lean verifies the exact equality criterion for these detunings.

**Declarations.** [SpectralDetuningCoverage.lean](../../../../formal/GaloisForLFunctions/HTGeometry/Quantum/SpectralDetuningCoverage.lean) contains `chainShell_detuningCoverage_ae`, `chainShell_selectedEchoWeight_ae`, and `representativeEcho_detuning_eq_iff`. The local-chain capstone uses only `propext`, `Classical.choice`, and `Quot.sound`.

**Application boundary.** An arbitrary short circuit can have exponentially many distinct eigenvalues. A bound on model energies alone supplies no lower bound on its gate count.
