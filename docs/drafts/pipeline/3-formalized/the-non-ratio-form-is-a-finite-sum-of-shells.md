# The non-ratio form is a finite sum of successor shells

- **ID:** ssh-shell-decomposition
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For a bump `g` supported in `[0, w]`, the non-ratio prime form of the atomic test is
  `NR(x) = Σ_{0<|h|≤H} Sh_h(x)`, `H = ⌊N(e^w − 1)⌋`, where
  `Sh_h(x) = 2Σ_k Λ(k)k^{−1/2} Σ_{n = km + h} x_m x_n β(log k − log(n/m))`. At `w = c/N`, `H ≤ c e^{c/N}`
  and `H = ⌊c⌋` for all large `N`. The shift `h` reads only partners `n ≥ |h|/(e^w − 1)`. If
  `N(e^w − 1) < 1`, `NR = 0`.

## Paper proof

The two orientations of a non-ratio lag carry the same pairs after exchanging `m, n` (the atom
autocorrelation `β` is even), so `nonRatioLag_k = 2Σ_{n ≠ km} x_m x_n β(log k − log(n/m))`. A term with
`β ≠ 0` has `|log(km/n)| ≤ w`; hence `n ≤ km e^w`, `km ≤ n e^w` and `|n − km| ≤ min(n, km)(e^w − 1)`.
So `h = n − km` is a nonzero integer with `|h| ≤ N(e^w − 1)`, unique for the pair; summing first over
`h` gives the decomposition prime power by prime power, and `k ≤ N e^w` makes every series finite.
For the count, `x ≤ e^x − 1 ≤ x e^x` gives `c ≤ N(e^{c/N} − 1) ≤ c e^{c/N} → c < ⌊c⌋ + 1`. The band
condition is `|h| ≤ n(e^w − 1)`; at `w = c/N`, `e^w − 1 ≤ (c/N)e^{c/N}`.

## Lean proof

`SuccessorShellArithmetic/TheNonRatioFormIsAFiniteSumOfShells.lean`
(namespace `GaloisForLFunctions.SuccessorShellArithmetic`):

- `nonRatioLag_eq_two_mul_upward`, `abs_shift_le_of_bumpCorr_ne_zero`, `upward_eq_sum_shellLag`
- `nonRatioForm_eq_sum_shellForm`
- `card_shellShifts`, `shellRange_le`, `card_shellShifts_le`, `eventually_shellRange_eq_floor`
- `shellLag_eq_zero_of_vanish_on_band`, `shellForm_eq_zero_of_vanish_on_top_band`
- `nonRatioForm_eq_zero_of_shellRange_eq_zero`

`lake --old env lean` passes; axioms `propext`, `Classical.choice`, `Quot.sound`. Wired into
`SuccessorShellArithmetic.lean`.
