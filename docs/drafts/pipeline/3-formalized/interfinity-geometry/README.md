# Interfinity geometry — formalized units

- **Stage:** 3-formalized
- **Parent program:** `../../1-in-progress/interfinity-geometry/interfinity-geometry-program.md`
- **Lean status:** all six cards formalized unconditionally

Each card has a dependency-closed paper theorem and proof, and a companion `-formalized.md` card
listing the Lean modules, the audited declarations, and the build command.  Every audited
declaration reports exactly `propext`, `Classical.choice`, `Quot.sound` under `#print axioms`.

## Cards

| Paper card | Companion | Umbrella |
|---|---|---|
| `stable-primitive-exactness-topology.md` | `stable-primitive-exactness-topology-formalized.md` | `GaloisForLFunctions.HTGeometry` |
| `spectral-terminal-horizon-model.md` | `spectral-terminal-horizon-model-formalized.md` | `GaloisForLFunctions.HTGeometry` |
| `multi-time-polyhedral-horizon.md` | `multi-time-polyhedral-horizon-formalized.md` | `GaloisForLFunctions.HTGeometry` |
| `terminal-nerve-and-coherent-source-functor.md` | `terminal-nerve-and-coherent-source-functor-formalized.md` | `GaloisForLFunctions.HTGeometry` |
| `terminal-transgression-curvature-flux.md` | `terminal-transgression-curvature-flux-formalized.md` | `GaloisForLFunctions.HTGeometry` |
| `arithmetic-three-chart-stable-boundary.md` | `arithmetic-three-chart-stable-boundary-formalized.md` | `GaloisForLFunctions.RHTower` |

## Lean surface

Thirty modules under `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/`, imported by the
sub-umbrella `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry.lean`, plus two modules
under `formal/GaloisForLFunctions/RHTower/`.

Three pieces of infrastructure had to be built because mathlib has none:

- Hadamard's lemma for `C^∞` functions of one real variable (`HadamardDivision.lean`);
- smoothness of every finite order for parametric averages (`ParametricSmoothness.lean`);
- the rotated Gamma integrals `∫₀^∞ (e^{-wt} − 1) t^{a-1} dt = Γ(a) w^{-a}` and
  `∫₀^∞ e^{-wt} t^{a-1} dt = Γ(a) w^{-a}` on the right half-plane, together with the
  exponential-integral constant `∫₀¹(e^{-t}−1)/t + ∫₁^∞ e^{-t}/t = −γ` and its rotation
  `−γ − Log w` (`SpectralComplexGamma.lean`, `SpectralEulerConstant.lean`,
  `SpectralComplexLogConstant.lean`).

## Remaining gates

Each card's `3 → 4` gate is an external priority and novelty audit at program level; it is not a
formalization obligation.
