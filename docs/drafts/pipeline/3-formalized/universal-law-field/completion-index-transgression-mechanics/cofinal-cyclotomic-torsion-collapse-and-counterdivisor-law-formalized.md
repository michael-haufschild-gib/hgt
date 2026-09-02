# Cofinal cyclotomic torsion collapse and counterdivisor law — Lean certification

- **ID:** `ULF-CIT-2`
- **Stage:** 3-formalized
- **Paper card:** `completion-index-transgression-mechanics/cofinal-cyclotomic-torsion-collapse-and-counterdivisor-law.md`
- **Lean module:** `GaloisForLFunctions.RHTower.CofinalCyclotomicTorsionCollapse`

## Certified declarations

- `cofinalCyclotomicRoot_ne_one`: retained points are nontrivial roots.
- `tendsto_cofinalCyclotomicRoot_of_strictMono`: strict cofinal depth accumulates at one.
- `cofinalCyclotomicTorsionCollapse`: persistent retained zeros plus locally uniform convergence
  force the holomorphic limit to be identically zero.

## Verification

Direct `lake env lean` check and targeted `lake build` passed. Targeted axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean` and
`HTGeometry.UniversalLawField`; no umbrella build was run.
