# Xi centered affine residue requires a Real polarization

- **ID:** RH-REAL-RESIDUE-POLARIZATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** whole-corpus synthesis: Xi source normal cone, modular residue transgression, transverse quasi-unipotence
- **Statement:** Every actual centered Xi affine residue is nonzero; critical-line placement is exactly landing in `ker Re = iℝ`; any nonzero real-linear scalar detector with this kernel is a scalar multiple of `Re`, while any complex-linear detector killing an actual residue is zero.

## Goal

Prove local RH selector is necessarily Real/Hermitian polarization of a surviving complex residue, not complex-holomorphic annihilation. Global landing remains equivalent to RH; no source-side landing premise is assumed.

## Gates

- [x] 0 → 1 in-progress: source-pure statement; exact off-line falsifier
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: focused Lean module, exact target build, axiom audit
- [ ] 3 → 4 publication-ready

## Paper proof

Let `m > 0` be Xi multiplicity at divisor point `ρ` and set `Rρ = -((ρ-1/2)m)`. Existing source-normal-cone conservation identifies `Rρ` as residue of `-(s-1/2) ξ′(s)/ξ(s)`. Coordinate calculation gives
`Re Rρ = -m(Re ρ-1/2)` and `Im Rρ = -m Im ρ`. Xi divisor points have nonzero imaginary part, so `Rρ ≠ 0`; positivity of `m` gives `Re Rρ = 0 ↔ Re ρ = 1/2`. Hence RH is exactly `Rρ ∈ ker Re` for every divisor point, with no residue erased.

For a real-linear scalar map `L : ℂ →ℝ` vanishing on `iℝ`, write `z = Re(z)·1 + Im(z)·i`; then `L(z)=L(1)Re(z)`, so `L=L(1)Re`. If `L ≠ 0`, `L(1) ≠ 0`, hence `ker L=iℝ`. For a complex-linear map `T : ℂ→W`, any nonzero `Rρ` spans the one-dimensional complex domain; therefore `T(Rρ)=0` implies `T=0`. This proves existence, uniqueness, and complex-linear no-go.

## Falsifier

An off-line Xi divisor has `Re Rρ ≠ 0`, so it fails Real-polarized landing and transverse quasi-unipotence while `Rρ` remains nonzero. Conversely a critical-line residue with zero imaginary component would falsify protected height, but corpus proves this impossible.

## Novelty boundary

Irregular Riemann–Hilbert theory supplies enhanced ind-sheaf/Stokes language for holonomic `D`-modules. This theorem is a corpus-derived constraint on the Xi current: local placement selection cannot be complex-linear and is uniquely real-polarized. No external novelty claim made.

## Log

- 2026-08-25 — paper proof closed; Lean scratch compiled
- 2026-08-25 — `XiCenteredAffineResidueRealPolarization.lean` exact target build passed; all new theorems use only `propext`, `Classical.choice`, `Quot.sound`
