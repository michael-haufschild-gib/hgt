# RBH / PW-B full Goursat finite weak transposition — Lean certificate

- **Paper card:** `rbh-pw-b-full-goursat-finite-transposition.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularGoursat`,
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularGoursatTransposition`; input
  `HTGeometry.VolterraRectangleTransposition`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** `lake --old env lean` clean; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| Goursat identity `K(u,v) = H + ∫₀ᵘ∫₀ᵛ G` for `u, v ≥ 0` | `fullAngularRiemannKernel_goursat` |
| weak form `∫∫ K φ'ψ' = Hφ(0)ψ(0) + ∫∫ Gφψ` for `C¹` tests vanishing at the upper endpoints, `G` with `K + N` and `4cosh²` weight | `fullAngularRiemannKernel_transposition` |
| (nonseparable continuous tests) | `fullAngularRiemannKernel_continuous_test_transposition` |
