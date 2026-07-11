# Thue--Morse Mellin carrier supplies Perron flank L2 energy

- **ID:** thue-morse-perron-l2-energy
- **Stage:** 3-formalized
- **Type:** NOT-NEW / INTERFACE DISCHARGE
- **Source:** RHTower `ThueMorseMellinFlatness` + `L2FourierIntegralBridge`
- **Statement:** `[PROVED]` The entire Mellin transform of the concrete Thue--Morse infinite-product kernel has an `L²` trace on every negative integer vertical line, unconditionally inhabits both Perron flank-energy and horizontal-mass interfaces, and consequently has an all-depth canonical cross-line Mellin defect against the concrete nonzero positive theta source.

## Goal

Supply the only pointwise Perron interface with consumers but no provider, using a nonzero concrete
carrier.  A bounded finite Dirichlet polynomial cannot work: its vertical trace is almost periodic,
not square-integrable on the whole line.  Mellin flatness instead makes the weighted logarithmic
source integrable at every real exponent; its uniform kernel bound promotes the relevant source to
`L²`, and Plancherel transports this to the vertical Mellin trace.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `thueMorseMellinCarrier_hasPerronCarrierFlankL2Energy`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

1. At depth `M`, write the Mellin trace at `-M+iy` as the Fourier transform of
   `u ↦ exp(Mu) K(exp(-u))`, evaluated at `y/(2π)`.
2. Mellin convergence at `-M` gives `L¹` of this logarithmic source.  Mellin convergence at
   `-2M`, together with `norm K ≤ 1`, gives integrability of its squared norm and hence `L²`.
3. Use the existing `L¹`/`L²` Fourier bridge and Plancherel to put the classical Fourier transform
   in `L²`; nonzero frequency dilation preserves `L²`.
4. Transfer along the exact Mellin--Fourier identity and package the square-root line energy as the
   Perron budget at every depth.

## Proof

Fix `M : ℕ` and put
`g_M(u) = exp(Mu) K(exp(-u))`, where `K` is the Thue--Morse Mellin kernel.  Mellin
convergence of `K` at `-M` is precisely integrability of `g_M`.  Mellin convergence at `-2M`
gives integrability of `exp(2Mu) ‖K(exp(-u))‖`.  Since `0 ≤ ‖K(t)‖ ≤ 1`,
`exp(2Mu) ‖K(exp(-u))‖²` is dominated by that integrable function, so `g_M ∈ L²`.

The Mellin--Fourier change of variables gives
`mellin K (-M+iy) = Fourier(g_M)(y/(2π))`.  The existing compatibility theorem between the
classical `L¹` Fourier integral and the unitary `L²` transform, followed by Plancherel, puts
`Fourier(g_M)` in `L²`.  Composition with the nonzero dilation `y ↦ y/(2π)` preserves
`L²`.  Hence the negative vertical trace is square-integrable.  Taking the square root of its
exact squared integral gives the budget required by `HasPerronCarrierFlankL2EnergyAt`; universal
quantification over `M` gives `HasPerronCarrierFlankL2Energy`.

Canonical subtraction then closes the next interface without another analytic hypothesis.  The
positive theta source is a concrete nonzero `SoninL2` element with lower support at zero.  At each
depth, subtracting its normalized trace from the Thue--Morse negative line gives the canonical
`SoninL2` defect.  The pointwise construction proves `HasCrossLineMellinDefectAt`; quantifying over
all depths proves `HasCrossLineMellinDefect`, hence also its eventual weakening.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ThueMorseFlankEnergyDischarge.lean`
- Pointwise theorem: `thueMorseMellinCarrier_hasPerronCarrierFlankL2EnergyAt`
- Eventual theorem: `thueMorseMellinCarrier_hasPerronCarrierFlankL2Energy`
- Horizontal-mass theorem: `thueMorseMellinCarrier_hasPerronCarrierHorizontalMass`
- Completed coefficient theorem: `thueMorseMellinCarrier_perronThirdCharge`
- Pointwise seam theorem: `thueMorseMellinCarrier_hasCrossLineMellinDefectAt`
- All-depth seam theorem: `thueMorseMellinCarrier_hasCrossLineMellinDefect`
- Eventual seam theorem: `thueMorseMellinCarrier_hasEventuallyCrossLineMellinDefect`
- Build: `lake build GaloisForLFunctions.RHTower.ThueMorseFlankEnergyDischarge` PASS
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`

## Log

- 2026-07-10 — created in 1-in-progress after rejecting the vacuous zero-carrier and false uniform-bound shortcut.
- 2026-07-10 — proved and formalized the nonzero Thue--Morse provider; moved to 3-formalized/not-new because this closes an underbuilt interface by composition rather than asserting new mathematical knowledge.
- 2026-07-10 — composed the all-depth energy with the concrete positive theta source to discharge all three cross-line defect interfaces.
- 2026-07-11 — proved the Mellin carrier's Gamma-times-`LSeries` identity and composed it with the
  balanced third-order Perron charge. Reciprocal Gamma now extracts every shifted Thue--Morse
  coefficient directly from the concrete carrier without a caller-supplied representation Prop.
