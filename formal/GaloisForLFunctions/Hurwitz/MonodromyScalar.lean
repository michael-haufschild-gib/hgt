/-
# The Hurwitz monodromy scalar `q = exp(-2πi s)` and its orbit

A loop around the singular point `a = -n` multiplies the singular vector `H(x) = (x^{-s-k})_k` by the
**diagonal** scalar `q = exp(-2πi s)` (same factor for every `k`, since `x^{-s-k}` picks up
`exp(-2πi(s+k)) = exp(-2πi s)`). This file pins the orbit structure of `q` purely from arithmetic of
`s`, feeding the abstract `OrbitObstruction` engine:

* `q = 1 ⟺ s ∈ ℤ`, `q² = 1 ⟺ 2s ∈ ℤ`  (`monoScalar_eq_one_iff`, `monoScalar_sq_eq_one_iff`);
* if `s ∉ ℤ` and `2s ∉ ℤ` then `1, q, q²` are pairwise distinct — the **≥3 distinct points** branch of
  the orbit obstruction (`monoScalar_three_distinct`);
* if `s ∉ ℤ` but `2s ∈ ℤ` (i.e. `s ∈ ½ + ℤ`) then `q = -1` — the **order-two** branch
  (`monoScalar_eq_neg_one`).

So the dichotomy of the card's quadratic descent (orbit kills `p` outright, vs. orbit-of-order-two
kills only the odd coefficient and the filtration supplies the rest) is governed exactly by whether
`2s ∈ ℤ`. No Hurwitz zeta yet — pure `exp`/root-of-unity arithmetic.
-/
import GaloisForLFunctions.Hurwitz.OrbitObstruction
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Complex

namespace HurwitzOrbit

/-- The diagonal monodromy scalar `q = exp(-2πi s)` of the Hurwitz singular ladder. -/
noncomputable def monoScalar (s : ℂ) : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * s))

theorem monoScalar_ne_zero (s : ℂ) : monoScalar s ≠ 0 := Complex.exp_ne_zero _

/-- `2π i ≠ 0` in `ℂ`. -/
private theorem twoPiI_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [hpi, Complex.I_ne_zero]

/-- **`q = 1 ⟺ s ∈ ℤ`.** -/
theorem monoScalar_eq_one_iff (s : ℂ) : monoScalar s = 1 ↔ ∃ m : ℤ, s = (m : ℂ) := by
  rw [monoScalar, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have : (2 * (Real.pi : ℂ) * Complex.I) * (-s) = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
      ring_nf; ring_nf at hn; linear_combination hn
    have hcancel := mul_left_cancel₀ twoPiI_ne_zero this
    push_cast
    linear_combination -hcancel
  · rintro ⟨m, rfl⟩
    exact ⟨-m, by push_cast; ring⟩

/-- **`q² = 1 ⟺ 2s ∈ ℤ`.** -/
theorem monoScalar_sq_eq_one_iff (s : ℂ) : (monoScalar s) ^ 2 = 1 ↔ ∃ m : ℤ, 2 * s = (m : ℂ) := by
  rw [monoScalar, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    push_cast at hn ⊢
    have hcancel : (2 * (Real.pi : ℂ) * Complex.I) * (-(2 * s)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by linear_combination hn
    have h2 := mul_left_cancel₀ twoPiI_ne_zero hcancel
    linear_combination -h2
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * hm

/-- **The order-≥3 branch: `1, q, q²` are pairwise distinct** when `s ∉ ℤ` and `2s ∉ ℤ`. Feeds
`orbit_eq_zero_of_three_distinct` to kill a degree-≤2 orbit polynomial outright. -/
theorem monoScalar_three_distinct {s : ℂ} (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (h2s : ∀ m : ℤ, 2 * s ≠ (m : ℂ)) :
    (1 : ℂ) ≠ monoScalar s ∧ (1 : ℂ) ≠ (monoScalar s) ^ 2 ∧
      monoScalar s ≠ (monoScalar s) ^ 2 := by
  have hq1 : monoScalar s ≠ 1 := fun h => by obtain ⟨m, hm⟩ := (monoScalar_eq_one_iff s).mp h; exact hs m hm
  have hq21 : (monoScalar s) ^ 2 ≠ 1 := fun h => by
    obtain ⟨m, hm⟩ := (monoScalar_sq_eq_one_iff s).mp h; exact h2s m hm
  refine ⟨fun h => hq1 h.symm, fun h => hq21 h.symm, ?_⟩
  intro h
  -- q = q² ⟹ q(q-1)=0 ⟹ q=1 (q≠0), contradiction
  have : monoScalar s * (monoScalar s - 1) = 0 := by linear_combination -h + (by ring : (monoScalar s)^2 - monoScalar s = monoScalar s * (monoScalar s - 1))
  rcases mul_eq_zero.mp this with h0 | h1
  · exact monoScalar_ne_zero s h0
  · exact hq1 (by linear_combination h1)

/-- **The order-two branch: `q = -1`** when `s ∉ ℤ` but `2s ∈ ℤ` (`s ∈ ½ + ℤ`). Feeds the
`coeff_one_eq_zero_of_pm_one` order-two obstruction. -/
theorem monoScalar_eq_neg_one {s : ℂ} (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (h2s : ∃ m : ℤ, 2 * s = (m : ℂ)) : monoScalar s = -1 := by
  have hq1 : monoScalar s ≠ 1 := fun h => by obtain ⟨m, hm⟩ := (monoScalar_eq_one_iff s).mp h; exact hs m hm
  have hq2 : (monoScalar s) ^ 2 = 1 := (monoScalar_sq_eq_one_iff s).mpr h2s
  -- (q-1)(q+1)=0, q≠1 ⟹ q=-1
  have : (monoScalar s - 1) * (monoScalar s + 1) = 0 := by linear_combination hq2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (by linear_combination h) hq1
  · linear_combination h

end HurwitzOrbit
