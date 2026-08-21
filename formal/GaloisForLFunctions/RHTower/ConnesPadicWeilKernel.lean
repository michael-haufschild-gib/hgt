import Mathlib

/-!
# The non-archimedean local Weil kernel `|1 - u|^{-1}`

Formalization of the shell structure behind Appendix II (9)-(10) and §VIII (10)-(11) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

At a non-archimedean place the local Weil term is
`Pfw ∫_{k_v^*} f(u)|1-u|^{-1} d^*u`, and Connes' normalization (9) makes the *unit* shell
`|u| = 1` contribute zero.  All other shells contribute an explicit constant, because the
ultrametric inequality is an *equality* off the unit sphere:

  `|1 - u| = max(1, |u|)`   whenever `|u| ≠ 1`,

so the kernel is identically `min(1, |u|^{-1})` on the shell `|u| = q^{-m}`, `m ≠ 0`:

  `|1 - u|^{-1} = 1`      for `m > 0`  (i.e. `|u| < 1`),
  `|1 - u|^{-1} = |u|^{-1}` for `m < 0`  (i.e. `|u| > 1`).

This is what turns Weil's local integral into the sum over prime powers of the explicit formula.
Everything here is unconditional; the corpus already owns the multiplicative-Haar shell
decomposition of `ℚ_p^*` (`FieldOnePadicMultiplicativeHaarDecomposition`,
`FieldOnePadicMultiplicativeHaarShellIntegral`).
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- **The ultrametric equality off the unit sphere.**  `|1 - u| = max(1, |u|)` for `|u| ≠ 1`. -/
theorem connes_padic_norm_one_sub {u : ℚ_[p]} (hu : ‖u‖ ≠ 1) :
    ‖1 - u‖ = max 1 ‖u‖ := by
  have hne : ‖(1 : ℚ_[p])‖ ≠ ‖-u‖ := by
    rw [norm_one, norm_neg]
    exact fun h => hu h.symm
  have h := Padic.add_eq_max_of_ne hne
  rw [sub_eq_add_neg, h, norm_one, norm_neg]

/-- **The local Weil kernel below the unit sphere.**  For `|u| < 1` the kernel is `1`. -/
theorem connes_padic_weilKernel_of_lt_one {u : ℚ_[p]} (hu : ‖u‖ < 1) :
    ‖1 - u‖ = 1 := by
  rw [connes_padic_norm_one_sub (ne_of_lt hu), max_eq_left (le_of_lt hu)]

/-- **The local Weil kernel above the unit sphere.**  For `|u| > 1` the kernel is `|u|`. -/
theorem connes_padic_weilKernel_of_one_lt {u : ℚ_[p]} (hu : 1 < ‖u‖) :
    ‖1 - u‖ = ‖u‖ := by
  rw [connes_padic_norm_one_sub (ne_of_gt hu), max_eq_right (le_of_lt hu)]

/-- **Appendix II (9)/(10), shell form.**  On the valuation shell `‖u‖ = p^{-m}` with `m ≠ 0`, the
local Weil kernel `|1-u|^{-1}` is the constant `min(1, p^m)`. -/
theorem connes_padic_weilKernel_shell {m : ℤ} (hm : m ≠ 0) {u : ℚ_[p]}
    (hval : ‖u‖ = (p : ℝ) ^ (-m)) :
    ‖1 - u‖⁻¹ = min 1 ((p : ℝ) ^ m) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp1
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · -- m < 0 : ‖u‖ = p^{-m} > 1
    have hgt : 1 < ‖u‖ := by
      rw [hval]
      exact one_lt_zpow₀ hp1 (by omega)
    rw [connes_padic_weilKernel_of_one_lt hgt, hval, ← zpow_neg, neg_neg]
    have hlt : (p : ℝ) ^ m < 1 := (zpow_lt_one_iff_right₀ hp1).mpr hneg
    rw [min_eq_right (le_of_lt hlt)]
  · -- m > 0 : ‖u‖ = p^{-m} < 1
    have hlt : ‖u‖ < 1 := by
      rw [hval]
      exact (zpow_lt_one_iff_right₀ hp1).mpr (by omega)
    rw [connes_padic_weilKernel_of_lt_one hlt, inv_one]
    have hge : (1 : ℝ) ≤ (p : ℝ) ^ m := one_le_zpow₀ (le_of_lt hp1) (by omega)
    rw [min_eq_left hge]

end

end GaloisForLFunctions.RHTower
