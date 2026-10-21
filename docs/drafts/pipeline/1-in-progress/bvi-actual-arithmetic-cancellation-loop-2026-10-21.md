# BVI: the missing actual arithmetic cancellation — conjecture loop

- **ID:** BVI-AAC-2026-10-21
- **Stage:** 1-in-progress
- **Type:** CONJECTURE loop (research → derive → formalize)
- **Source:** `formal/GaloisForLFunctions/BezoutValuationIncidence/README.md` §5 (receiver, interior
  martingale "signed sum over moduli", single-modulus statistics of the actual Möbius row);
  `docs/reports/review-2110/hard-obstacles-summary.md` Q5.
- **Statement:** produce unconditional, Lean-verified cancellation of the *actual* Möbius / damped
  Möbius row in BVI coordinates, measured in the README units (damping, exponent θ), and locate exactly
  where each mechanism stops.

## Goal

The receiver `E_T(ε) = Σ_{n≤T} A_ε(n)²/(n(n+1))` of `c_ε(d) = μ(d)d^{-ε}` is bounded for `ε ≥ 1/2`
and unknown below; a bound at one fixed `ε < 1/2` is a zero-free half-plane. The actual arithmetic
cancellation that the corpus does not yet use inside BVI is the zero-free region itself. Each cycle
attacks one concrete missing statement; failures are recorded with their positive survivor.

## Gates
- [x] 0 → 1  in-progress: frontier read (README §5, review-2110 Q5, WP4 ledger, THIM parity pair).
- [ ] 1 → 2  per-cycle paper proofs (below).
- [ ] 2 → 3  per-cycle Lean modules, wired into `BezoutValuationIncidence.lean`.

## Corpus inputs used (verified by search)
- VK Mertens: `RHTower.Sieve.exists_abs_sum_moebius_le_vk_rate`, eventual
  `2√(log N) ≤ log vkHeight N` (`eventually_vk_conditions`), so `|M(N)| ≤ B N e^{-√(log N)/12}`.
- THIM receiver objects: `weightCenteredPrefix`, `weightPronicEnergy`, `dampedSignWeight`,
  `weightPronicEnergy_pmPowerDamped`, hyperbola template `abs_weightCenteredPrefix_dampedSign_le`.
- BVI interior/complete energy comparison:
  `pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half` (and converse).
- `HTGeometry.summable_exp_neg_sqrt_log_div`, `RHTower.sum_rpow_neg_head_le`,
  `HTGeometry.sum_shift_rpow_tail_le`.

## Cycle ledger

### C1 — the receiver is bounded in the zero-free band below half damping (DONE, Lean)
**Conjecture.** There is `E` such that for every horizon `T` and every damping
`ε ∈ [1/2 − 1/(80√(log T)), 1/2]` (and `ε ≥ 1/4`), `E_T(ε) ≤ E`; consequently the Bézout interior
energy is bounded on the same band.

**Paper proof.**
1. *Abel with linear partial sums.* If `|Σ_{d≤x}s(d)| ≤ Lx` for `D ≤ x ≤ X` and `w ≥ 0` is antitone
   on `(D, ∞)`, then `|Σ_{D<d≤X}s(d)w(d)| ≤ L(2D·w(D+1) + Σ_{D<d≤X}w(d))`
   (summation by parts; the weight `d ↦ d` telescopes against `w`).
2. *Blocks and tail.* With `L = Cρ(D)`: `|Σ_{D<d≤X}μ(d)d^{-α}| ≤ 5LX^{1−α}` (`0 ≤ α ≤ 1/2`),
   `|Σ_{d>D}μ(d)d^{-1-ε}| ≤ (2+1/ε)LD^{-ε}`.
3. *Hyperbola split at D.* `A_ε(n) = [short d ≤ D] + [long, along the cofactor k] − n·[tail]`,
   giving `|A_ε(n)| ≤ 3D^{1−ε} + 31·L·n·D^{−ε}` for `1 ≤ D ≤ n`, `ε ∈ [1/4,1/2]`.
4. *Choice of D.* `u = √(log n)`, `D = ⌊n e^{−u/20}⌋`; then `D ≥ √n`, `ρ(D) ≤ e^{−u/18}`, and
   `|A_ε(n)| ≤ K n^{1−ε} e^{−u/40}` uniformly in `ε ∈ [1/4, 1/2]`.
5. *Band.* For `n ≤ T` and `ε ≥ 1/2 − 1/(80√(log T))`: `n^{−2ε} ≤ n^{−1} e^{u/40}`, so each term is
   `≤ K² e^{−u/40}/n`, summable; small `n` use the trivial bound (`D = 1`, `L = 1`).

**Meaning.** First unconditional receiver bound below half damping: the damping unit moves from `1/2`
to `1/2 − c/√(log T)` at horizon `T`, paid by the zero-free region (VK ⟹ dVP rate). A fixed-width band
would be a zero-free strip (README §5), so the band profile is the zero-free profile.

**Lean.** `BezoutValuationIncidence/ReceiverBoundedInTheZeroFreeBandBelowHalfDamping.lean`:
`exists_receiver_le_on_zeroFreeBand`, `exists_interiorEnergy_le_on_zeroFreeBand`, tools
`abs_sum_Ioc_mul_le_of_linear`, `abs_weightCenteredPrefix_dampedSign_le_of_linear`,
`exists_abs_sum_moebiusReal_le_sqrtLog`, `exists_abs_weightCenteredPrefix_pmPowerDamped_le`.
`lake env lean` clean; axioms `propext, Classical.choice, Quot.sound`; wired.

### C2 — the Vinogradov–Korobov band (DONE, Lean)
**Statement.** `E_T(ε) ≤ E` for `1/4 ≤ ε ≤ 1/2`, `ε ≥ 1/2 − κσ(T)/(480 log T)`,
`σ = (log)^{3/5}(log log)^{-5/3}`; same for the interior energy.
**Proof.** As C1 with rate `g = κσ/24`, split `D = ⌊n e^{-g(n)/5}⌋`; shape lemmas: `σ` nondecreasing
from `exp(exp(25/9))` (via `log t/t^{9/25}` antitone), `σ/log` decreasing from `exp(e)`,
`σ(z) ≥ (4/9)σ(x)` when `log z ∈ [(4/9)log x, log x]`.
**Selectivity.** Width `(log T)^{-2/5}(log log T)^{-5/3}` exceeds the dVP width `(log T)^{-1/2}`; dVP
is the best possible zero-free region for Beurling systems (Diamond–Montgomery–Vorhauer), so the
extra width is paid by Vinogradov's mean value theorem, i.e. by the additive structure of ℕ.
**Lean.** `BezoutValuationIncidence/ReceiverBoundedInTheVinogradovKorobovBand.lean`:
`exists_receiver_le_on_vinogradovKorobovBand`, `exists_interiorEnergy_le_on_vinogradovKorobovBand`,
`exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk`, `vkScale_le_vkScale`, `vkScale_div_log_le`,
`four_ninths_mul_vkScale_le`. Clean, standard axioms, wired.

## Log
- 2026-10-21 — card created; C1 paper proof written; Lean module
  `BezoutValuationIncidence/ReceiverBoundedInTheZeroFreeBandBelowHalfDamping.lean` started.
- 2026-10-21 — C1 formalized and wired; C2 (VK band) formalized and wired.
