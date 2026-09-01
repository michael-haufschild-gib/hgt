# Cai–Chen–Fang–Guo Rajchman corpus transfer (2026-09-01)

Main module: `formal/GaloisForLFunctions/HTGeometry/CaiChenFangGuoRajchman.lean` (6890 lines after this work).
Umbrella import: `formal/GaloisForLFunctions/HTGeometry.lean`, import at line 1841.

Source: Cai–Chen–Fang–Guo, “Critical Gaussian Multiplicative Chaos on the Circle Is Rajchman”, arXiv:2608.28328.
Mechanisms transferred mechanically, without claiming Gaussian-chaos formalization:
- Rajchman Fourier decay and atomlessness
- continuous/L1 multiplier stability (paper Lemma 6.4 pattern)
- conditional independence / two-color factorization
- torus and clock consequences

Formalized application families include Haar/Poisson/summable densities, finite and infinite tori, real and general L1 clocks, Möbius/Gamma/Meixner/Sonin/logistic/Connes/Wigner-Smith/Julia/theta/Suzuki/prolate/Fermi-Mellin/beta/recurrence/unit-Riesz and energy-profile constructions.

Key infrastructure/results added:
- global unit-Riesz Markov clock with cell telescoping and total mass one
- off-line conjugate Cauchy pair: signed first mass vanishes while squared energy is strictly positive and Rajchman after normalization
- radial PSWF leading arclength energy positivity
- field-one compact logarithmic Schwartz energy
- outgoing reciprocal-Gamma quantile chi-square strict positivity for N≥3, using prime 2 boundary mismatch
- arbitrary finite-window oscillator energy and general one-sided Sonin bump
- positive theta-square log atoms with exponential upper bound; raw mass fades while normalized clocks remain Rajchman
- arbitrary AnnulusAmplitude spectral energy via nonzero Fourier zero mode and Plancherel, requiring no smoothness beyond existing infrastructure

Verification:
- `lake env lean GaloisForLFunctions/HTGeometry/CaiChenFangGuoRajchman.lean` passes
- `lake build GaloisForLFunctions.HTGeometry.CaiChenFangGuoRajchman` passes (targeted module only)
- representative `#print axioms` audit reports only `propext`, `Classical.choice`, `Quot.sound`
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` tokens in target
- no stale task Lean processes
- global `scripts/formal_tools.py lint` remains nonzero only for pre-existing unrelated umbrella-reachability errors (17 RHTower modules and 2 HTGeometry ramification modules); target itself has only large-file warning.

Do not re-run full builds. Preserve concurrent dirty-worktree changes outside main module.