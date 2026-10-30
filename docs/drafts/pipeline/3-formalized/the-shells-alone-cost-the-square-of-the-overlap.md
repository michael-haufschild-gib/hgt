# The shells alone cost the square of the overlap

- **ID:** ssh-separate-payment-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (no-go for separate payment)
- **Statement:** Let `φ ≥ 0` be continuous, supported in `[0,1]`, `M = ∫φ² > 0`, `q = (∫φ)²/M`,
  `c, ε > 0`. If eventually in `N`, for every `x`,
  `NR_{c/N}(x) ≤ G(εD_N(x) + C Σx_n²)` with `G = ∫(atom)² = (c/N)M`, then
  `C ≥ max(A, 0)²/(2ε)`, `A = cq/(4 log 2) − 1/2`. With `ε = a c⁻⁷`: `C ≥ max(A,0)² c⁷/(2a)`.

## Paper proof

Top band `T = {n ≤ N : N e^w < 2n}`, `w = c/N`. A base `m ∈ T` has no partner: `k ≥ 2` gives
`km > Ne^w ≥ ne^w`. So for `x` equal to `b = n^{−1/2}` on all bases, regrouping the lag terms by the
product `ℓ = km` and `Σ_{d∣ℓ}Λ(d) = log ℓ` give `NR(x) = 2Σ_n x_n R(n)`,
`R(n) = Σ_{ℓ≠n} b_ℓ Λ_N(ℓ) β(log ℓ − log n)`, and `Λ_N(ℓ) = log ℓ` for `ℓ ≤ 2N + 1`.

Witness `x_η = b + η b1_T`, `η ≥ 0`:

- `NR(x_η) = NR(b) + 2ηΣ_T b_nR(n) ≥ 2ηΣ_T b_nR(n)` (`β ≥ 0`).
- For `n, ℓ ∈ T`: `b ≥ N^{−1/2}`, `log ℓ ≥ log(N/2)`, so
  `Σ_T b_nR(n) ≥ (log(N/2)/N)(Σ_{n,ℓ∈T} β(log ℓ − log n) − |T|G)`.
- The atoms of `T` lie in `[log N + w − log 2, log N + w]`; Cauchy–Schwarz on this window gives
  `Σ_{n,ℓ∈T} β = ∫(Σ_T g(· − log n))² ≥ (|T| w∫φ)²/log 2`.
- `D(x_η) = η²D(b1_T)` (the pole vector satisfies every pole relation), and only edges into `T` from
  bases outside `T` survive: `D(b1_T) = Σ_n (b1_T)_n² Σ_{t∣n}Λ(t) ≤ log N Σ_T 1/n ≤ 2 log N`.
- `Σ(x_η)_n² = H_N + (2η + η²)Σ_T 1/n`, `log N ≤ H_N ≤ 1 + log N`.

Divide by `G log N`: `2η(log(N/2)/log N)((|T|/N)²cq/log 2 − |T|/N) ≤ 2εη² + C·H_N/log N + o(1)`.
With `N(1 − e^w/2) ≤ |T| ≤ N/2 + 1`, `|T|/N → 1/2`; letting `N → ∞`, `2ηA ≤ 2εη² + C`, and
`η = max(A,0)/(2ε)` gives the bound.

## No-go closure

- **Exact killing mechanism:** a perturbation of the pole vector on the top band costs defect
  `≍ η² log N` but moves the shells by `≍ ηcq log N`; any separate payment therefore needs
  `C ≳ c²/ε`, and `c⁹` at the reserve fraction `c⁻⁷`. Separate payment of the shells cannot lower
  the confinement exponent `16`.
- **Strongest positive survivor:** (a) on the pole vector and its top-band perturbations the shells are
  prime-free (`shellPoleRow_eq_log`), so the obstruction is a statement about the integers; (b) the
  continuum average of the shells is exactly the pole charge (`continuumShellSum_eq`), so in a joint
  payment with the pole the `c`-linear parts cancel and the remainder is the lattice part, which
  repays (`latticeGain_eq`). Both are formalized
  (`3-formalized/the-integrality-of-the-shift-repays-the-logarithm.md`).
- **New insight:** the reserve cost is controlled by the joint block shells + pole + archimedean
  shells; Q1 of the programme is stated for that block.
- **Status:** floor formalized. The witness-level joint statement (the `η`-coefficient of
  `2·Pole − NR` is `O(G(log N + c))`) is a paper heuristic; it needs a first-order Euler–Maclaurin
  bound for the `C²` profile and is open.

## Lean proof

`SuccessorShellArithmetic/TheShellsAloneCostTheSquareOfTheOverlap.lean`:

- `horizonDivisorMangoldt_eq_log_of_le`, `shellPoleRow_eq_log`, `nonRatioForm_eq_of_pole_on_bases`
- `nonRatioForm_topWitnessVector`, `nonRatioForm_poleVector_nonneg`, `sum_topBand_shellPoleRow_ge`
- `sum_topBand_bumpCorr_ge`, `poleDefect_topWitnessVector`, `poleDefect_topWitness_le`,
  `sum_topWitnessVector_sq`, `sum_topBand_inv_le_two`, `card_topBand_ge`, `card_topBand_le`
- `le_of_nonRatioForm_payment`, `le_of_nonRatioForm_payment_at_reserve`

`lake --old env lean` passes; axioms `propext`, `Classical.choice`, `Quot.sound`.
