# The initial trace of heat depth energy

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacles:** B13, B112; initial data for global heat-depth dissipation.
- **Objects:** `H_t = riemannHeat t`, `u(q) = max (Im xiSpectralPoint(q)) 0`, and `E⁺(t) = Σ_z mult(H_t,z) max(Im z,0)²` for `t>0`.
- **Statement:** For every real `K`, all finite sums `Σ_q u(q)²` are at most `K` iff `E⁺(t)≤K` for every `t>0`. Consequently `E⁺` is bounded near zero iff `Σ_q u(q)²` converges. In the convergent case `E⁺(t)→Σ_q u(q)²`; otherwise `E⁺(t)→∞` as `t→0⁺`.
- **Significance:** Identifies the exact initial value required by heat-depth dissipation, including infinite energy. Positive-time finiteness alone supplies no bound at zero. This does not assert that the initial energy is finite, nor close B13 or B112.
- **Novelty audit:** `TheGlobalHeatDepthIsContinuous` proves continuity only at positive times. `HeatZeroSumContinuity` includes zero only for bounded support. `DeBruijnNewmanEnergyUnitTime` supplies upper majorization, but no initial trace or equivalence with square summability. Corpus searches for initial heat energy, bounded heat energy and squared-depth summability found these inputs and no matching trace theorem.

## Paper proof

For `0<t≤1`, the existing polynomial-to-entire majorization bounds each finite upper heat-zero energy by any upper bound for the initial finite sums, since `(u²−2t)_+≤u²`. Positive-time nonreal finiteness lets the finite sum cover all nonzero contributions. For `t≥1`, all heat zeros are real. This proves the forward bound with the same constant.

Conversely fix finitely many initial multiplicity copies. Choose a continuous radial cutoff, equal to one at their spectral points, between zero and one everywhere, and zero outside a bounded ball. Its weighted zero sum is continuous at heat time zero. At positive times it is bounded by `E⁺(t)`. At zero it dominates the chosen finite copy sum, by grouping copies at each spectral point and using their exact analytic multiplicities. Passing to zero proves the reverse bound without any uniform confinement assumption.

For a finite initial sum, choose finite partial sums arbitrarily close to it. Their cutoff sums give the required lower limit; majorization gives the upper limit. If the nonnegative initial series diverges, choose finite partial sums above any prescribed level and use the same cutoff continuity. This gives divergence to infinity. Boundedness on any punctured neighbourhood of zero already suffices in the reverse argument.

Lean formalization pending; uncounted.
