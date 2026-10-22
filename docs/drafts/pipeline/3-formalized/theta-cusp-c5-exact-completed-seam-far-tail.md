# Theta-Cusp Exact Completed C5 Seam Far Tail

- **ID:** CLG-TTF-C5-exact-completed-far-tail
- **Stage:** 3-formalized
- **Type:** SIGNIFICANT PREMISE DISCHARGE
- **Lean:** `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspExactCompletedC5SeamFarTail`

## Result

For exact physical orientation

`Ω = A²G - 3ACE - 2ABF + 4B²E - 18A³F + 36A²BE`,

with `A=-L₂`, `B=-L₄`, `C=-L₆`, `E=-L₃`, `F=-L₅`, `G=-L₇`, Lean proves

`Ω(x) / thetaCuspSingleAtomReflectionScale 1 x ^ 4 → 36864`

as `x → +∞`. Consequently:

`∃ X, ∀ x ≥ X, 0 < Ω(x)`.

No cutoff value or computation enters proof.

## Proof mechanism

1. Fixed higher-likelihood spectral measure has support at least `3`, giving exponential decay of
   every tilted moment after every fixed polynomial weight.
2. Exact moment-cumulant formulas transport this to scaled cumulant extinction through order seven.
3. Hence every higher-likelihood source log jet used by C5 is `o(scale)`.
4. Normalized first-atom log jets tend exactly to `4, 8, 16, 32, 64, 128`.
5. Cubic C5 terms lose one scale. Quartic residue is
   `-18*4^3*32 + 36*4^2*16*8 = 36864`.

## RH proof-chain consequence

Entire noncompact physical C5 orientation burden is closed. Remaining
`C5-ORBIT-FIRST-CONTACT` problem is compact actual-orbit incidence only:

`compact physical C5 incidence`
→ `global exact C5 orientation`
→ `direct local Jacobian orientation`
→ `reflection-odd rank-four/Ptolemy wall`
→ `cofinal no-escape`
→ `CLG/TTF or Weil polarization positivity`
→ `RH`.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspExactCompletedC5SeamFarTail.lean`: pass.
- Targeted `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspExactCompletedC5SeamFarTail`: pass.
- Final theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, hypothesis, or computation.
- Wired into `GaloisForLFunctions.RHTower` umbrella.

