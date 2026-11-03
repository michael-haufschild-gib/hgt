import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# The archimedean Tate family

At a prime `p` the Tate family of `ζ` is the ratio of Euler factors `ζ_p(s − k)/ζ_p(s)`; its values at
`k = β + 1` are the point counts of `ℙ^β` over `ℤ/p^a` (WTZ). The archimedean place has the same
construction with the Gamma factor `Γ_ℝ(s) = π^{−s/2}Γ(s/2)`:

`𝒢_k(s) = Γ_ℝ(s − k)/Γ_ℝ(s)` (`archTate`).

* **It is a Tate cocycle** (`archTate_zero`, `archTate_add`): `𝒢_0 = 1` and
  `𝒢_{k+l}(s) = 𝒢_l(s − k)𝒢_k(s)`, the cocycle law of the Tate flow (WTZ `tateFamily_add`).
* **One Hensel step** (`Gammaℝ_eq_mul_Gammaℝ_sub_two`): `Γ_ℝ(s) = π^{−1}(s/2 − 1)Γ_ℝ(s − 2)`, so
  `𝒢_2(s) = π/(s/2 − 1)` (`archTate_two`).
* **In even dimension the archimedean place is finite** (`archTate_two_mul`):
  `𝒢_{2j}(s) = π^j / ∏_{i<j}(s/2 − 1 − i)`, the reciprocal of a polynomial with the `j` roots
  `s = 2, 4, …, 2j`. Where the arithmetic place counts the points of `𝔸^{2j}∖0` over residue rings,
  the archimedean place has `j` points, at the even integers `2, …, 2j`; adding two dimensions adds one
  point, as adding one dimension multiplies a count at `p` by `p` along a Hensel tower.

Weil's archimedean term is the derivative of this family at `k = 0` (the digamma function), exactly
as Weil's arithmetic term is the derivative of the Jordan family. The completed family
`Λ(s − k)/Λ(s) = 𝒢_k(s)·ζ(s − k)/ζ(s)` is the Tate family of the completed zeta function; a structured
archimedean family for the domination question (DZG §7.3) is a functional of `𝒢_k`.
-/

noncomputable section

open Complex
open scoped Real

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

/-- The **archimedean Tate family** `𝒢_k(s) = Γ_ℝ(s − k)/Γ_ℝ(s)`. -/
def archTate (k s : ℂ) : ℂ := Gammaℝ (s - k) / Gammaℝ s

theorem archTate_zero {s : ℂ} (hs : Gammaℝ s ≠ 0) : archTate 0 s = 1 := by
  rw [archTate, sub_zero, div_self hs]

/-- **The Tate cocycle at the archimedean place**: `𝒢_{k+l}(s) = 𝒢_l(s − k)𝒢_k(s)`. -/
theorem archTate_add (k l s : ℂ) (h : Gammaℝ (s - k) ≠ 0) :
    archTate (k + l) s = archTate l (s - k) * archTate k s := by
  rw [archTate, archTate, archTate, sub_add_eq_sub_sub, div_mul_div_comm, mul_comm (Gammaℝ (s - k)),
    mul_div_mul_right _ _ h]

/-- **One Hensel step of the Gamma factor**: `Γ_ℝ(s) = π^{−1}(s/2 − 1)Γ_ℝ(s − 2)` for `s ≠ 2`. -/
theorem Gammaℝ_eq_mul_Gammaℝ_sub_two {s : ℂ} (hs : s ≠ 2) :
    Gammaℝ s = (s / 2 - 1) / (π : ℂ) * Gammaℝ (s - 2) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : s / 2 - 1 ≠ 0 := fun h => hs (by linear_combination 2 * h)
  have hG : Gamma (s / 2) = (s / 2 - 1) * Gamma (s / 2 - 1) := by
    rw [← Complex.Gamma_add_one _ h1, sub_add_cancel]
  have hcpow : (π : ℂ) ^ (-(s - 2) / 2) = (π : ℂ) ^ (-s / 2) * π := by
    rw [show -(s - 2) / 2 = -s / 2 + 1 by ring, cpow_add _ _ hπ, cpow_one]
  rw [Gammaℝ, Gammaℝ, hG, hcpow, show (s - 2) / 2 = s / 2 - 1 by ring]
  field_simp

/-- `𝒢_2(s) = π/(s/2 − 1)`. -/
theorem archTate_two {s : ℂ} (hs : s ≠ 2) (hG : Gammaℝ (s - 2) ≠ 0) :
    archTate 2 s = (π : ℂ) / (s / 2 - 1) := by
  have h1 : s / 2 - 1 ≠ 0 := fun h => hs (by linear_combination 2 * h)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [archTate, Gammaℝ_eq_mul_Gammaℝ_sub_two hs]
  field_simp

/-- The Gamma factor does not vanish off the even integers. -/
theorem Gammaℝ_ne_zero_of_not_even {s : ℂ} (hs : ∀ m : ℤ, s ≠ 2 * m) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  exact hs (-n) (by rw [hn]; push_cast; ring)

/-- **In even dimension the archimedean place is finite**: off the even integers,
`𝒢_{2j}(s) = π^j / ∏_{i<j}(s/2 − 1 − i)`. -/
theorem archTate_two_mul {s : ℂ} (hs : ∀ m : ℤ, s ≠ 2 * m) (j : ℕ) :
    archTate (2 * j) s = (π : ℂ) ^ j / ∏ i ∈ Finset.range j, (s / 2 - 1 - i) := by
  induction j with
  | zero => simp [archTate_zero (Gammaℝ_ne_zero_of_not_even hs)]
  | succ j ih =>
    have hshift : ∀ m : ℤ, s - 2 * j ≠ 2 * m := fun m h => hs (m + j) (by
      rw [show s = (s - 2 * j) + 2 * j by ring, h]; push_cast; ring)
    have hne2 : s - 2 * j ≠ 2 := fun h => hs (j + 1) (by
      rw [show s = (s - 2 * j) + 2 * j by ring, h]; push_cast; ring)
    have hG1 : Gammaℝ (s - 2 * j) ≠ 0 := Gammaℝ_ne_zero_of_not_even hshift
    have hG2 : Gammaℝ (s - 2 * j - 2) ≠ 0 := Gammaℝ_ne_zero_of_not_even fun m h => hs (m + j + 1) (by
      rw [show s = (s - 2 * j - 2) + 2 * j + 2 by ring, h]; push_cast; ring)
    have hfac : s / 2 - 1 - (j : ℂ) ≠ 0 := fun h => hne2 (by linear_combination 2 * h)
    have hprod : ∏ i ∈ Finset.range j, (s / 2 - 1 - (i : ℂ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i hi h
      have hi' := Finset.mem_range.mp hi
      exact hs (i + 1) (by rw [show s = 2 * (s / 2 - 1 - i) + 2 * i + 2 by ring, h]; push_cast; ring)
    rw [show (2 : ℂ) * ((j + 1 : ℕ) : ℂ) = 2 * j + 2 by push_cast; ring, archTate_add _ _ _ hG1,
      archTate_two hne2 hG2, ih, Finset.prod_range_succ, pow_succ]
    rw [show (s - 2 * j) / 2 - 1 = s / 2 - 1 - j by ring]
    field_simp

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
