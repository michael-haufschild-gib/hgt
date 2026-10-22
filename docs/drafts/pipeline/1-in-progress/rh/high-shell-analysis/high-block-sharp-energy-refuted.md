# High-block sharp-energy input refuted at head length one

- **ID:** HB-SE-001
- **Stage:** 1-in-progress
- **Type:** FALSIFIED (with positive survivor)
- **Source:** MUST-215 in `universal-law-field/STATUS.md`; `RHTower.SharpEnergyInput` in `formal/GaloisForLFunctions/RHTower/HighBlockParameters.lean`
- **Statement:** No constant `C` satisfies `RHTower.SharpEnergyInput C`.

## Goal

`SharpEnergyInput C` was recorded as the single arithmetic input of the high-block law:
`RHTower.exists_zetaDyadicMeanSquareLaw_of_sharpEnergyInput` turns it into
`ZetaDyadicMeanSquareLaw R c` with an explicit `c`, and hence into the `ζΨ` gate of the single-input
`(L)` constant. Deciding it therefore decides whether the whole high-block lane can produce an
unconditional dyadic mean-square law.

## No-go closure

- **Exact killing theorem/mechanism.** `RHTower.not_sharpEnergyInput (C : ℝ) : ¬ SharpEnergyInput C`
  in [`HighBlockSharpEnergyRefutation`](../../../../../../formal/GaloisForLFunctions/RHTower/HighBlockSharpEnergyRefutation.lean).

  The definition quantifies over every head length `u ∈ range (hbL a)`, including `u = 0`. At `u = 0`
  the sharp head is the single coefficient `1`, so the Dirichlet convolution collapses onto the
  mollifier and the energy is exactly the mollifier's own displaced coefficient energy
  (`sharpEnergy_head_one_eq`):

  ```text
  E(0,d) = Σ_{m ≤ N} (μ(m) log(N/m) / log N)² · m^{2d-1},   N = hbN U = ⌊U^{1/20}⌋.
  ```

  For a prime `p` with `p² ≤ N` the Barban–Vehov ratio `log(N/p)/log N` is at least `1/2`, and
  `p^{2d-1} ≥ 1/p` for every `d > 0`, so `E(0,d) ≥ ¼ Σ_{p ≤ √N} 1/p`
  (`quarter_primeSum_le_headOneEnergy`). The prime reciprocal series diverges, `N → ∞` with `U`, and
  the input demands one constant for all large `U`; so no `C` works. Taking `a = 1` keeps
  `hbL a = 1`, but the argument needs only `1 ≤ hbL a`.

  This is elementary: no Selberg diagonalisation and no Dress–Iwaniec–Tenenbaum constant is used.
  The earlier ledger entry CANNOT-320 located the same `log N` defect in the *full* mollified half of
  the approximate functional equation; the refutation above shows the defect is already present at
  the trivial head, so it cannot be avoided by any choice of head cutoff.

- **Strongest positive survivor.** The head-one energy is pinned from both sides:

  - `RHTower.sharpEnergy_head_one_eq` — the identity `E(0,d) = Σ_{m ≤ N} (μ(m)log(N/m)/log N)² m^{2d-1}`
    for every head length bound `L ≥ 1` and every displacement `d`;
  - `RHTower.quarter_primeSum_le_headOneEnergy` — `¼ Σ_{p ≤ √N} 1/p ≤ E(0,d)` for `d > 0`;
  - `RHTower.headOneEnergy_le` — `E(0,d) ≤ N^{2d} Σ_{m ≤ N} 1/m` for `d ≥ 0`, `N ≥ 2`.

  So `E(0,d)` is a harmonic sum of the mollifier length, inflated by the displacement factor `N^{2d}`,
  and nothing smaller. The displacement factor is harmless at the displacement the consumer actually
  uses — `ZetaDyadicMeanSquareLaw` supplies `R ≤ (1/2 - σ₀) log U` and `(1/2 - σ₀) log(U-1) ≤ R`, so
  `d ≍ R/log U` and `N^{2d} = exp(2d log N) ≍ e^{R/10}` — while the harmonic factor is not: it is
  `≍ log N ≍ (1/20) log U` and enters `exists_highBlock_bound` linearly, through `9 e^{4R} C`.

- **New insight.** The failure is not a property of the Barban–Vehov mollifier and is not removed by
  restricting the displacement range. It is produced by the smooth-to-sharp telescoping
  (`smooth_head_eq_sum_sharp`), which forces a uniform bound on *every* sharp head, including the one
  that has deleted the entire `ζ` factor. Any repaired input must either (i) keep the smooth cutoff,
  where the `ζ`–`Ψ` cancellation survives, or (ii) accept the normalisation
  `E(u,d) ≤ C · N^{2d} · (1 + log N)` and absorb the logarithm downstream — which the present
  `ZetaDyadicMeanSquareLaw`, whose constant `c` is a fixed real, cannot do.

- **Status.** Lean, dependency-closed, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
  Module `formal/GaloisForLFunctions/RHTower/HighBlockSharpEnergyRefutation.lean`, wired into
  `GaloisForLFunctions.RHTower`.

## Open successor

State and attack the smooth-head input: a bound on the coefficient energy of the *smooth* displaced
head against the displaced mollifier, uniform in the block base, without passing through sharp heads.
That is the only formulation of the high-block arithmetic input not refuted by the above.

## Log
- 2026-09-24 — created; `SharpEnergyInput` refuted in Lean; two-sided head-one bounds formalized.
