# arXiv:2608.28506 corpus formalization (2026-09-01)

Paper: Marc Cuenca-Laràs et al., "Langevin Theory of Non-Markovian Quantum Dynamics: Application to Delayed Coherent Feedback and the Laser Linewidth", arXiv:2608.28506v1.

## Added modules
- HTGeometry/NonMarkovianLangevinKernel.lean: finite bath kernels; Hermitian symmetry; peak bound; positive definiteness; KMS/Gibbs forms; packet Cauchy and Gram PSD; feedback balance; equilibrium circle; linewidth algebra.
- HTGeometry/NonMarkovianLangevinVolterra.lean: nonresonant detunings encoded by Real units; exact Fourier antiderivative; continuous all-time Volterra solution; integrated memory equation; vacuum/zero-coupling cases.
- HTGeometry/NonMarkovianLangevinFeedback.lean: below/above threshold narrowing inequalities and exact delayed transfer-denominator norm-square decomposition.
- HTGeometry/NonMarkovianLangevinProbabilityMemory.lean: every ProbabilityMeasure characteristic function as a normalized positive-definite memory kernel; compound-Poisson closure.
- RHTower/NonMarkovianLangevinCorpusApplications.lean: Schwarzschild/FZZ Bose memory covariance; unit finite-bath dressing preserves constant-coefficient differential transcendence for Gamma, digamma, zeta, Xi, and Xi logarithmic derivative.
- RHTower/NonMarkovianLangevinCharacteristicApplications.lean: critical prime-tail, Gamma cyclic, Cauchy half-exponential, and Julia-defect characteristic functions as Hermitian positive-definite memory kernels.

All modules wired into HTGeometry.lean or RHTower.lean.

## Validation
Each of six modules passed direct `lake env lean <file>` and targeted `lake build <module>`. Axiom audit of representative core/application theorems reports only `propext`, `Classical.choice`, `Quot.sound`; no project axioms or `sorryAx`. Token scan found no sorry/admit/axiom/opaque/unsafe. `git diff --check` passed. Repository formal lint recognizes all six as umbrella-reachable but currently fails on unrelated pre-existing/concurrent unwired modules.

## Hostile audit / exclusions
- Paper's global Lambert-W stability boundary depends on numerical study; not promoted to unconditional theorem.
- Dirac-delta "peak order" is distributional, not pointwise; not faked in Lean.
- Laser linewidth expression is approximate physics; only exact algebra and order consequences were formalized.

## Main positive survivor
Finite spectral memory kernels are positive-definite, stronger than the paper's pointwise |K(t)| ≤ K(0). This bridges finite Gibbs/KMS spectra, packet Gram positivity, general characteristic-function probability kernels, compound-Poisson closure, Schwarzschild/FZZ Bose spectra, prime-tail laws, and existing corpus characteristic functions.