# Local Speiser theorem: zeros of ζ′ left of the line lie in off-line disks

- **ID:** SPEISER-LOCAL-DISK
- **Stage:** 3-formalized
- **Type:** THEOREM (pointwise, all heights ≥ 100; structural companion of MUST-593)
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 66
- **STATUS:** MUST-595

## Theorems [L]

Module `formal/GaloisForLFunctions/RHTower/SpeiserLocalDisk.lean` (wired, clean, standard axioms).

For a zero `ρ` of `ξ`, the Speiser disk `D(ρ)` is the closed disk with centre `1/2 + i Im ρ` and
radius `|Re ρ − 1/2|`.

1. `exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero` (and `…_of_abs` for `|Im s| ≥ 100`). If
   `ζ'(s) = 0`, `0 < Re s < 1/2` and `Im s ≥ 100`, then `s ∈ D(ρ)` for some zero `ρ` of `ξ` in the
   strip: `(Re s − 1/2)² + (Im s − Im ρ)² ≤ (Re ρ − 1/2)²`.
2. `deriv_riemannZeta_ne_zero_of_re_zeros`. If every zero of `ξ` has `Re = 1/2`, then `ζ' ≠ 0` on
   `0 < Re s < 1/2`, `Im s ≥ 100`. This is Speiser's direction, now local.
3. `deriv_riemannZeta_ne_zero_of_re_lt`. `ζ'(s) ≠ 0` for `0 < Re s < 1/(58 log(Im s + 1/2))`,
   `Im s ≥ 100`. This is a zero-free region for `ζ'` next to the imaginary axis, obtained from the
   corpus zero-free region for `ζ`.

Supporting lemmas:
- `abs_re_digamma_sub_log_norm_le`: `|Re ψ(z) − log‖z‖| ≤ 3/‖z‖` for `Re z > 0`, `‖z‖ ≥ 2`.
- `re_logDeriv_zetaChi_le`: `Re χ'/χ(s) ≤ −log(t/2π) + 3/50` on the whole strip.
- `re_logDeriv_archFactor_le`: `Re archFactor'/archFactor ≤ ½log(t/2π) + 1/25`.
- `logDeriv_xi_eq_archFactor_add_of_strip`: the split `ξ'/ξ = archFactor'/archFactor + ζ'/ζ`. It is
  now shared with MUST-594.

## Proof

- **Case `ζ(s) = 0`.** Take `ρ = s`, which lies on the boundary of its own disk.
- **Case `ζ(s) ≠ 0`.** Put `w = 1 − s̄`, so `Re w > 1/2` and `Im w = Im s`.
  - Reflection and conjugation turn `ζ'(s) = 0` into `Re ζ'/ζ(w) = Re χ'/χ(s) ≤ −log(t/2π) + 3/50`.
  - Adding the archimedean part gives `Re ξ'/ξ(w) ≤ −½log(t/2π) + 1/10 < 0`.
  - The disk criterion (`re_logDeriv_xi_nonneg_of_disk_bound`) then puts `w` in the off-line disk
    `(Re ρ − ½)² ≥ (Re w − ½)² + (Im w − Im ρ)²` of some zero. That is the statement for `s`.

## What it says

- **The left zeros of ζ′ are shadows of the off-line zeros of ζ.**
  - Each such zero sits within `|Re ρ − 1/2|` of the centre `1/2 + iγ` of an off-line zero, where
    `|Re ρ − 1/2| ≥ 1/2 − Re s`.
  - This holds at every height ≥ 100, not on average.
- **Speiser failures ⊆ reflected Hadamard failures.** `s` fails Speiser only if `1 − s̄` fails the
  Hadamard sign, and the Hadamard failures are exactly the off-line disks. The "Speiser ⇒ RH"
  direction (Levinson–Montgomery, via the argument principle) is not formalized here.
- **Consequence for density.** MUST-593's exceptional heights near left zeros of ζ′ at distance
  `≥ κ/log T` lie within `1/2` in ordinate of off-line zeros with `|β − 1/2| ≥ κ/log T`.

## Limits

- The height threshold 100 is where `−½log(t/2π) + 1/10 < 0` holds with room. Lower heights need
  only finite verification, which is not done.
- No count comparison: several zeros of `ζ'` can share one disk. The Levinson–Montgomery equality
  `N₁⁻(T) = N⁻(T) + O(log T)` needs the argument principle and is open in Lean.

## Addendum (cycle 67, MUST-596): horizontal monotonicity off the Speiser disks [L]

- `re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk`. Let `0 < Re s < 1/2` and `Im s ≥ 100`. If `s`
  lies outside the Speiser disk of every strip zero of `ξ`, then `ζ(s) ≠ 0` and
  `Re ζ'/ζ(s) ≤ −½ log(Im s/2π) + 1/10`. The main theorem is now derived from this bound.
- `strictAntiOn_normSq_riemannZeta_horizontal`. On every horizontal segment `[a, b] + iτ` with
  `0 < a`, `b < 1/2`, `τ ≥ 100`, avoiding all Speiser disks, `σ ↦ |ζ(σ + iτ)|²` is strictly
  decreasing.
- `strictAntiOn_normSq_riemannZeta_horizontal_of_re_zeros`. Under RH this holds on every
  `[a, b] ⊂ (0, 1/2)`, `τ ≥ 100`. That is the horizontal-monotonicity reformulation of RH (the
  "RH ⇒" direction, `|t| ≥ 8` in the literature), here at height ≥ 100.
- **Meaning.** Unconditionally, `|ζ|` decreases towards the critical line from the left, except
  inside the disks `D(½ + iγ, |β − ½|)` of off-line zeros. The failure set is thus explicitly the
  union of those disks.

## Addendum (cycle 71): zeros of ξ′ [L]

`R:XiDerivSpeiserDisk`.
- `exists_xi_zero_disk_of_deriv_xi_eq_zero`: every zero `s` of `ξ'` with `Re s ≠ ½` lies in the
  Speiser disk of a zero of `ξ`. The proof applies the strict disk criterion to the right half,
  using the corpus `re_logDeriv_xi_pos_of_disk_bound`, and reflects through `ξ(1−s) = ξ(s)` for
  the left half.
- `deriv_xi_zero_re_eq_half_of_re_zeros`: RH ⇒ every zero of `ξ'` lies on the critical line.

So the zeros of both `ζ'` (left of the line, MUST-595) and `ξ'` (off the line) are pinned to the
same Speiser disks.

## Addendum (cycle 77): Littlewood-width strip for ζ′ [L]

`R:SpeiserLittlewoodStrip`, `exists_deriv_riemannZeta_ne_zero_littlewood_strip`: there are `c, T₀ > 0` with `ζ'(s) ≠ 0` for `Im s ≥ T₀` and `0 < Re s < c · log log(Im s)/log(Im s)`.
- Proof: local Speiser disk plus the corpus Littlewood zero-free region (`Sieve.exists_littlewood_zero_free_region_abs`).
- Any wider zero-free region for `ζ` (e.g. Vinogradov–Korobov) transfers to `ζ'` the same way.
