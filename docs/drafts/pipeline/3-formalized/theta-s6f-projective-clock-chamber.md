# Theta S6F projective clock chamber

- **ID:** S6F-PD-CLOCK
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL SOURCE-ORBIT BOUND
- **Parent:** `../1-in-progress/theta-rank-three-projective-drift.md`

## Theorem

For actual theta modular trajectory and every `0 < x < 137/2000`,

```text
-(thetaCuspModularODEState Z x).re < 3/10.
```

Proof sharpens self-dual theta mass by geometric tail bound, obtains
`thetaCuspSelfDualModularScale^2 < 360000/18769`, bounds absolute modular-lambda derivative by
`600/137` on positive half-line using decreasing discriminant gap, and applies mean-value theorem.

## Lean

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthProjectiveClockChamber`
- Main theorem: `neg_thetaCuspModularODEState_Z_re_lt_three_tenths`
- Supporting theorems:
  - `thetaCuspSelfDualThetaMass_lt_2173_div_2000`
  - `thetaCuspSelfDualModularScale_sq_lt_projectiveClockThreshold`
  - `norm_deriv_thetaCuspModularODEState_Z_re_le_600_div_137`
- API exposure: `thetaCuspModularODEState_Z_zero`
- Umbrella: `GaloisForLFunctions.RHTower`

Direct `lake env lean`, exact module `lake build`, and `#print axioms` pass. Dependencies are only
`propext`, `Classical.choice`, and `Quot.sound`.

## Research consequence

This discharges first physical trajectory localization suggested by S6F chamber search. It does
not prove projective drift positivity or RH. Subsequent computation-free thin-cone theorem sharpens
actual orbit to `2/5<y=v/z<1/2`. Diagnostics suggest positivity on scale half-ray
`X>=191/10`, so previous upper localization `X<20` is no longer expected to be necessary. No
computed coefficient enters either Lean module.
