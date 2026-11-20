# A Fourier clock tests a simulator with freely adjustable phases

At the D Fourier ticks of the equally spaced D-level clock, compare its evolution with any fixed spectral decomposition into k sectors. Each sector phase may be chosen separately at every tick. For any subset S of ticks the sum of normalized squared trace fidelities is at most k. Thus fidelity at least f > 0 on all chosen ticks requires |S|f ≤ k.

In the source basis, let pₐ(x) be the diagonal of sector projector a. The trace is a sum of k finite Fourier transforms of these weights, each multiplied by a unit phase. Cauchy–Schwarz costs a factor k. Parseval sums each squared transform to D times the squared mass of its row. Summing over sectors costs at most one per source index since their diagonal values form a probability vector. Dividing by D² gives the bound. The cases k = 1 and k = D attain equality on the complete clock.

[FourierClockModelOrder.lean](../../../../formal/GaloisForLFunctions/HTGeometry/Quantum/FourierClockModelOrder.lean) proves `fourierClock_sectorTrace_energy_le` for arbitrary eigenbases and tick-dependent sector phases. Direct source check and axiom audit passed with `propext`, `Classical.choice` and `Quot.sound`.
