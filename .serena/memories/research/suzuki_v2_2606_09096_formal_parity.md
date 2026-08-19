# Suzuki v2 literature parity (2026-08-19)

Masatoshi Suzuki arXiv:2606.09096v2 has 11 labeled results (5 theorems, 2 corollaries, 3 lemmas, 1 proposition); all now have exact Lean landings.

New exact modules:
- `GaloisForLFunctions.HTGeometry.VonNeumannDeficiency`
- `GaloisForLFunctions.RHTower.SuzukiTaSymmetry`
- `GaloisForLFunctions.RHTower.SuzukiTaCharacteristicRealization`
- `GaloisForLFunctions.RHTower.SuzukiTaSpectralEigenspace`
- `GaloisForLFunctions.RHTower.SuzukiTaCharacteristicZeros`
- `GaloisForLFunctions.RHTower.SuzukiTaCharacteristicEntire`
- `GaloisForLFunctions.RHTower.SuzukiV2CharacteristicTarget`

Theorem 1.5 capstone: `suzukiTaCharacteristic_eq_zero_iff_extensionEigenvalue`, `differentiable_suzukiTaCharacteristic`, self-adjoint extension and real-zero theorems. Hidden converse gap closed by exact complex shifted-range closure and `suzukiTa_adjoint_eigenspace_span`.

Novel correction: v2 target `XiC/(XiC+i XiC')` has an unconditional genuine pole at a negative-imaginary point, proved via xi log-derivative IVT. Thus the literal all-plane compact-open convergence premise is false (`not_suzukiV2CharacteristicLimitWall`). Correct survivor is pole-free meromorphic/spherical convergence; `suzukiV2MeromorphicCharacteristicLimitWall_implies_riemannHypothesis` proves it remains RH-bearing.

Research card: `docs/drafts/pipeline/1-in-progress/suzuki-v2-literature-parity-and-cofinal-correction.md`. Route map is read-only.

Verification: all seven `.olean`s exist and targeted builds passed; representative and paper-wide `#print axioms` report only `propext`, `Classical.choice`, `Quot.sound`. Umbrella imports added but umbrellas not built. Whole-tree lint scan failed only on unrelated concurrent unreachable modules, not Suzuki modules.