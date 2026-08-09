# Constitutive-jet factorization and withheld-observer prediction — formalized

- **ID:** `cfr-constitutive-jet-factorization-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `constitutive-jet-factorization-and-withheld-observer-prediction-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ConstitutiveJetFactorization` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellVerticalMode` | new |
| `GaloisForLFunctions.RHTower.HighExponentShellClockMeasure` | reused parent |

Both wired into `GaloisForLFunctions.HTGeometry`.

## Reused, not rebuilt

The shell Gibbs law and its normalisation are the existing `RHTower.shellProbability`,
`RHTower.shellMellin_pos`, `RHTower.hasSum_shellProbability`, `RHTower.shellIndicator_two_pow`;
the card's scope note asks for the existing shell-support and normalised-response files.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 2.1 — the withheld response criterion, card `(CJ.1)`–`(CJ.4)`:

1. `constant_on_fibres_iff` — items 1 and 2 of the theorem: `B` is constant on the fibres of `A`
   iff `ker A ≤ ker B`.
2. `factorQuot`, `factorRange`, `factorRange_apply` — item 3: the canonical factor with
   `B = B̄ ∘ A`.
3. `factorRange_unique` — uniqueness of the factor on `range A`.
4. `ker_le_ker_iff_range_dualMap_le` — item 4, the dual form `(CJ.3)`, in finite dimension.
5. `exists_vertical_mode` — the exact counter-intervention `(CJ.4)`.

Corollary 2.2 — presentation covariance:

6. `factorRange_equivariant` — any symmetry preserving `A` and `B` is preserved by the canonical
   factor.

Section 3 — the quantitative and cofinal form, card `(CJ.5)`:

7. `ker_le_ker_of_response` — a uniform response bound forces kernel containment.
8. `norm_factorRange_le` — the factor is bounded by the response constant.
9. `response_of_factor` — conversely a bounded factor yields the response bound; items 7–9 are the
   two directions of `(CJ.5)`.

Countertheorem 3.1 — finite prediction need not survive aperture:

10. `no_uniform_response` — if some sequence has `‖B eₙ‖ = 1` while `‖A eₙ‖ → 0`, no uniform
    constant exists.  Together with `constant_on_fibres_iff` (which still supplies the algebraic
    factor whenever `ker A = 0`) this is exactly the countertheorem: finite factorization and
    global injectivity do not give a bounded factor.

Theorem 4.1 — the literal Euler-shell vertical mode, card `(CJ.7)`/`(CJ.8)`:

11. `two_pow_mul_three_ne_prime_pow` — the mixed atom `2^m · 3` is not a prime power, so the
    pure-prime skeleton reporter `(CJ.7)` annihilates it.
12. `shellProbability_pos` — an occupied shell atom has positive Gibbs mass.
13. `summable_shellPhase`, `shellCharFun`, `hasSum_shellCharFun`, `normalizedResponse` — the
    normalised Mellin phase response `(CJ.8)` of a single atom.
14. `log_eq_of_response_zero` — if the response of an occupied atom vanished at every time, every
    occupied atom would have the same logarithm.
15. `shell_vertical_mode` — the theorem: the mixed atom is invisible to the prime skeleton yet its
    normalised phase response is nonzero at some time, because `2^m` and `2^m · 3` are two
    distinct occupied atoms.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ConstitutiveJetFactorization.lean  # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellVerticalMode.lean             # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
