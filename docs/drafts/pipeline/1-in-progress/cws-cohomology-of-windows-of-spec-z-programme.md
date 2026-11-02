# Cohomology of Windows of Spec ℤ (CWS) — programme card

- **ID:** CWS
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.7
- **Statement:** attach to each window length `A` the arithmetic object whose `h¹` is Weil's window
  form; determine the window datum exactly; decide which carriers (count, capacity, placement) can
  realize `h¹`; calibrate (curves, prime-free windows, first prime); locate selection.

## Goal
Develop the field of §2.7: answer its questions by Lean theorems, build its tools. Folder
`formal/GaloisForLFunctions/CohomologyOfWindowsOfSpecZ/`, umbrella `CohomologyOfWindowsOfSpecZ.lean`,
README there.

## Lean modules
TheWindowDatum, TheCanonicalClassOfAWindow, TheFirstPrimeFold, TheArchimedeanObstructionAtTheFirstPrime,
ShortWindowsCarryAtMostOneNegativeSquare, TheCanonicalDegreeBoundsTheWindowForm,
TheFrobeniusAtInfinityOfAWindow, WindowRealizations, TheWindowIndex, TheWindowGenusIsAYoungConjugate,
WindowNaiveHeights, TheWindowCohomologyOfACurve, TheSelectionBatteryOfWindows.

## Status [L]
- Window datum: locality in the level and in the Euler factors; window involution an isometry; window criterion.
- Canonical class: fold identity; `k_A(u) = ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})`; degree `2∫_0^A ψ_{1/2}(e^t)dt`.
- Signed folds: each prime power contributes antisymmetric count − symmetric mass; arithmetic `≤ ∫k_A H²`;
  prime-free windows archimedean; first prime = one fold of `T₂`.
- Fold capacity criterion: RH ⇔ `|Ω(0)|‖H‖² + Σ w sym + ½s² ≤ J_∞ + Σ w anti + ½c²` on every window.
- Archimedean obstruction: for `log 2 ≤ A < 2log 2`, `Q − J_∞ = Ω(0)‖H‖² < 0` on an infinite-dimensional
  space of fold-free, pole-free tests; no identity "jump count + fold data + finitely many squares".
- At most one negative square on smooth windows `< log 2 + 1/50` (from LST cosh-hyperplane coercivity).
- Semiboundedness `Q ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²`; second-order pencil nonnegative at bounded `K`.
- Window involution on transforms: multiplier `e^{−(s−½)A}`, unitary exactly on `Re s = ½`.
- Realizations ⇔ RH (zero map); none finite-dimensional. Window index: monotone, finite, `0` to `3/5`,
  exhausts right zeros (even); RH ⇔ `ι < 2`.
- Window genus `≥ (2−η)e^A`, Young conjugate of the zero density, theta count of `Spec ℤ`.
- Windowed Tate law; curve windows (`ℂ^{2g}` realization ⇔ unitary; golden fake has none);
  flip twins of every bounded window.

## Open
README §7: the fold capacity inequality at the first prime (a Poincaré inequality, not an identity); whole prime-free window from the jump count;
window capacity uniform in `A`; window naive heights; admissible dilation constant as `A → ∞`;
window Frobenius at infinity placing the poles of `Λ(s)/Λ(s+1)`.
