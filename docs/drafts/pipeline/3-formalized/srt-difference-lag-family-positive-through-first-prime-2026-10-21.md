# The difference lag family is positive through the first prime

- **ID:** srt-lag-family-first-prime
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2110/hard-obstacles-summary.md §2.2 (O1 prime-side receiver `P_v`, O2 odd sector past the first prime); walls 1 and 13
- **Statement:** For `0 < w`, `2w < v`, `v/2 + w ≤ 353/1000`: `Re P_{w,v} ≥ (1/500)∫‖κ_w‖²`. For `w < 1/12`, `|v − log 2| ≤ 2w` the window read by the test is `{2}` and the inequality reads `(log 2/√2)·Re(k(log 2) + k(−log 2)) + (1/500)∫‖κ_w‖² ≤ Re(polar + archimedean)`.

## Goal
Connect three lanes that were not joined: the difference two-bump test `f_{w,v}(t) = κ_w(t + v/2) − κ_w(t − v/2)`
of the one-parameter lag family (SquareRootThreshold) is an odd function; the odd sector of the
Weil form of `ζ` is positive through `353/1000 > log 2/2` (ArithmeticIncidencePositivity,
`fullZeroForm_ge_of_odd_support_le_threeHundredFiftyThreeThousandths`); the zero-side form splits
as `Ẑ(Re f) + Ẑ(Im f)` (arithmetic-positivity-theory, `zeta_W_re_eq_fullZeroForm_re_add_im`).
Composed, the certified lag range of the problem's own family moves from `v/2 + w ≤ 3/10`
(all-profile floor through the Rayleigh bridge `Re P ≥ 2‖κ_w‖² μ(v/2 + w)`) to `v/2 + w ≤ 353/1000`,
i.e. lags `v ≤ 706/1000 − 2w > log 2`, without passing through `μ(A)`. The dyadic windows containing
the prime `2` are included: at `|v − log 2| ≤ 2w` the prime side of `P_v` is the single atom
`Λ(2)/√2 · (k(log 2) + k(−log 2))` and it is paid by the polar and archimedean terms with margin.

What this changes in the review: the SRT "Established" line (lag floors "through `3/10`") now reads
through `353/1000` on the family; the first lag range in which a prime enters the window is certified.
Units: the certified initial lag segment is `[2w, 706/1000 − 2w]`; the open unit (a late lag `V`
beyond which `P_v ≥ 0`) is unchanged. Selectivity is inherited from the AIP odd window (selective
against the shifted pair). Non-circular: no RH input; standard axioms.

## Gates
- [x] 0 → 1  well-posed, source-pure (composition of unconditional corpus theorems)
- [x] 1 → 2  paper proof: parity of the test + odd window + re/im split + norm identity + literature RHS rewrite
- [x] 2 → 3  Lean: `formal/GaloisForLFunctions/SquareRootThreshold/DifferenceLagFamilyPositiveThroughTheFirstPrime.lean`; `lake env lean` green; `#print axioms` = `propext, Classical.choice, Quot.sound`; wired into `GaloisForLFunctions/SquareRootThreshold.lean`
- [ ] 3 → 4  not pursued

## Approach
1. `modScaledBump_neg`: `κ_{w,γ}(−u) = conj κ_{w,γ}(u)`; `twoBump_modScaledBump_neg`: `f(−t) = −conj f(t)`
   (real part odd, imaginary part even); at `γ = 0` the test is real, hence odd
   (`twoBump_modScaledBump_zero_neg`).
2. `zetaZeroConfig_re_W_ge_of_odd_aperture_le_threeHundredFiftyThreeThousandths`: every odd complex `C²`
   test supported in `[−353/1000, 353/1000]` has `Re W_ζ(f, f) ≥ (1/1000)∫|f|²` (both parts of an odd test
   are odd; the AIP odd window applies to each). No abstract window premise: the statement is specialized
   to the proven window, so every declaration of the module is unconditional.
3. `one_div_1000_mul_le_re_W_twoBump_of_le` (aperture `v/2 + w ≤ 353/1000`), then the disjoint-bump norm
   identity `∫|f|² = 2∫‖κ_w‖²` and the explicit-formula rewrite `W_ζ = literatureRHS = lagPrimeWindowRHS`
   give `one_div_500_mul_le_re_lagPrimeWindowRHS_of_le`.
4. `lagPrimeWindow_eq_singleton_two`: `|log n − log 2| ≤ 4w < 1/3 ≤ log(3/2)` excludes `n ≥ 3`; `n ≤ 1` has
   `log n = 0`; `2 ≤ ⌊e^{v+2w}⌋` since `log 2 ≤ v + 2w`. Then `firstPrime_atom_paid_on_lagFamily` by
   `Finset.sum_singleton` and `Λ(2) = log 2`.
5. `one_div_500_mul_le_re_lagPrimeWindowRHS_of_near_log_two` (`w ≤ 3/1000` covers the whole prime-2
   window of lags); `lt_of_re_lagPrimeWindowRHS_neg` (a negative lag has `v/2 + w > 353/1000`).

## What it does not give
The second prime window `log 3/2 ≈ 0.549` lies beyond the archimedean odd ceiling (`≈ 0.375`), so this
mechanism stops before the prime `3`; nothing about late lags; the modulated family (`γ ≠ 0`) has odd real
part and even imaginary part, so past `3/10` only the unmodulated family is covered.

## Log
- 2026-10-21 — generic transfer lemma with an abstract window premise replaced by its specialization to the proven AIP window (user rule: no unproven premises); recompiled, olean rebuilt, axioms standard.
- 2026-10-21 — created directly in 3-formalized; module compiled (`lake env lean`), olean built single-threaded, umbrella import added; lint shows no issue for this module (other errors in the working tree belong to other agents' unwired modules).
