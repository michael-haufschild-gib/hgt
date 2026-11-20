# Exact best completed-time fidelity of a k-energy Hamiltonian

Fix n ≥ 3 qubits and take a uniform direction in the full traceless onsite and nearest-neighbour Pauli coefficient space. Write D = 2ⁿ. Almost surely, for every 1 ≤ k ≤ D, the maximum long-time mean of |tr(exp(−itH)exp(itK))/D|² over all autonomous K with at most k energies is

$$
\frac{D+k(k-1)}{D^2}.
$$

K may be chosen after H. The [frequency coverage bound](local-chain-echo-frequency-coverage.md) gives a budget k−1 for the sum of the excesses above one of the unnormalized frequency weights. Each weight is at most k and their sum is D. Thus their squared sum is at most D+k(k−1). The time mean equals this squared sum divided by D². Retain any k source energies and map all remaining levels onto one retained energy. The zero detuning has mass k and the D−k remaining atoms have unit mass.

[AutonomousEchoModelOrder.lean](../../../../formal/GaloisForLFunctions/HTGeometry/Quantum/AutonomousEchoModelOrder.lean) proves the physical trace expansion, the conull upper bound `chainShell_modelEchoMean_ceiling_ae` and attainment `retainedModel_echoMean`. The latter holds for every simple spectrum. Both source audits use only `propext`, `Classical.choice` and `Quot.sound`. Lean averages from 1 to T. Starting at zero alters the normalized integral by a fixed bounded integral divided by T.
