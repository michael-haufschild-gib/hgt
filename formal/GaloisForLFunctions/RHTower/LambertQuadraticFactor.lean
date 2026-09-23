import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The quadratic factor of a Lambert term

The denominator of the Lambert form of a moment-Borel transform factors over the unit circle:

`1 + 2u cos α + u² = (1 + u e^{iα})(1 + u e^{-iα})`.

Two consequences.  Its zeros are exactly the two points `-e^{∓iα}`, which is why the poles of the
transform lie on two multiplicative lattices; and away from the unit circle it is bounded below by
`(1 - ‖u‖)²`, which is what makes the Lambert series converge normally once the finitely many terms
with `‖u‖` near one are removed.

* `GaloisForLFunctions.RHTower.lambertQuadratic_factor`;
* `GaloisForLFunctions.RHTower.lambertQuadratic_eq_zero_iff`;
* `GaloisForLFunctions.RHTower.norm_lambertQuadratic_ge`;
* `GaloisForLFunctions.RHTower.tsum_alternating_sine_geometric_complex`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

/-- **The quadratic factors over the unit circle.** -/
theorem lambertQuadratic_factor (α : ℝ) (u : ℂ) :
    1 + 2 * u * (Real.cos α : ℂ) + u ^ (2 : ℕ)
      = (1 + u * Complex.exp ((α : ℝ) * Complex.I))
        * (1 + u * Complex.exp (-((α : ℝ) * Complex.I))) := by
  have hsum : Complex.exp ((α : ℝ) * Complex.I) + Complex.exp (-((α : ℝ) * Complex.I))
      = 2 * (Real.cos α : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    ring
  have hprod : Complex.exp ((α : ℝ) * Complex.I) * Complex.exp (-((α : ℝ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc 1 + 2 * u * (Real.cos α : ℂ) + u ^ (2 : ℕ)
      = 1 + u * (Complex.exp ((α : ℝ) * Complex.I) + Complex.exp (-((α : ℝ) * Complex.I)))
        + u ^ (2 : ℕ) * (Complex.exp ((α : ℝ) * Complex.I)
          * Complex.exp (-((α : ℝ) * Complex.I))) := by
        rw [hsum, hprod]
        ring
    _ = (1 + u * Complex.exp ((α : ℝ) * Complex.I))
        * (1 + u * Complex.exp (-((α : ℝ) * Complex.I))) := by ring

/-- **The zeros of the quadratic are the two points of the unit circle it factors through.** -/
theorem lambertQuadratic_eq_zero_iff (α : ℝ) (u : ℂ) :
    1 + 2 * u * (Real.cos α : ℂ) + u ^ (2 : ℕ) = 0 ↔
      u = -Complex.exp (-((α : ℝ) * Complex.I)) ∨ u = -Complex.exp ((α : ℝ) * Complex.I) := by
  rw [lambertQuadratic_factor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left
      have hE : Complex.exp ((α : ℝ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have hu : u * Complex.exp ((α : ℝ) * Complex.I) = -1 := by linear_combination h
      have : u = -1 / Complex.exp ((α : ℝ) * Complex.I) := by
        field_simp at hu ⊢
        linear_combination hu
      rw [this]
      rw [neg_div, one_div, ← Complex.exp_neg]
    · right
      have hE : Complex.exp (-((α : ℝ) * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
      have hu : u * Complex.exp (-((α : ℝ) * Complex.I)) = -1 := by linear_combination h
      have : u = -1 / Complex.exp (-((α : ℝ) * Complex.I)) := by
        field_simp at hu ⊢
        linear_combination hu
      rw [this]
      rw [neg_div, one_div, ← Complex.exp_neg, neg_neg]
  · rintro (rfl | rfl)
    · left
      rw [neg_mul, ← Complex.exp_add]
      simp
    · right
      rw [neg_mul, ← Complex.exp_add]
      simp

/-- **The quadratic is bounded below away from the unit circle.** -/
theorem norm_lambertQuadratic_ge (α : ℝ) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    (1 - ‖u‖) ^ (2 : ℕ) ≤ ‖1 + 2 * u * (Real.cos α : ℂ) + u ^ (2 : ℕ)‖ := by
  have hnn : (0 : ℝ) ≤ 1 - ‖u‖ := by linarith
  have hfac : ∀ w : ℂ, ‖w‖ = 1 → 1 - ‖u‖ ≤ ‖1 + u * w‖ := by
    intro w hw
    have hnormuw : ‖u * w‖ = ‖u‖ := by rw [norm_mul, hw, mul_one]
    have hbase : ‖(1 : ℂ)‖ - ‖-(u * w)‖ ≤ ‖(1 : ℂ) - -(u * w)‖ := norm_sub_norm_le _ _
    rw [norm_one, norm_neg, hnormuw, sub_neg_eq_add] at hbase
    exact hbase
  have h1 : ‖Complex.exp ((α : ℝ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I α
  have h2 : ‖Complex.exp (-((α : ℝ) * Complex.I))‖ = 1 := by
    have harg : -((α : ℝ) * Complex.I) = ((-α : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
    exact Complex.norm_exp_ofReal_mul_I (-α)
  rw [lambertQuadratic_factor, norm_mul]
  have hle1 := hfac _ h1
  have hle2 := hfac _ h2
  calc (1 - ‖u‖) ^ (2 : ℕ) = (1 - ‖u‖) * (1 - ‖u‖) := by ring
    _ ≤ ‖1 + u * Complex.exp ((α : ℝ) * Complex.I)‖
        * ‖1 + u * Complex.exp (-((α : ℝ) * Complex.I))‖ :=
        mul_le_mul hle1 hle2 hnn (le_trans hnn hle1)

/-- **The alternating sine geometric sum, for a complex ratio.**  The same closed form holds off the
unit disc boundary with `u` complex: the sum splits into two geometric series with ratios
`-u e^{±iα}`, and their difference is the quadratic factor. -/
theorem tsum_alternating_sine_geometric_complex (α : ℝ) {u : ℂ} (hu : ‖u‖ < 1) :
    ∑' k : ℕ, ((-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * u ^ (k + 1))
      = u * (Real.sin α : ℂ) / (1 + 2 * u * (Real.cos α : ℂ) + u ^ (2 : ℕ)) := by
  set E : ℂ := Complex.exp ((α : ℝ) * Complex.I) with hEdef
  set F : ℂ := Complex.exp (-((α : ℝ) * Complex.I)) with hFdef
  have hE : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I α
  have hF : ‖F‖ = 1 := by
    have harg : -((α : ℝ) * Complex.I) = ((-α : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hFdef, harg]
    exact Complex.norm_exp_ofReal_mul_I (-α)
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  -- the sine of a multiple angle in terms of the two exponentials
  have hsin : ∀ k : ℕ, ((Real.sin ((k + 1) * α) : ℝ) : ℂ) * (2 * Complex.I)
      = E ^ (k + 1) - F ^ (k + 1) := by
    intro k
    have hEk : E ^ (k + 1) = Complex.exp ((((k + 1) * α : ℝ) : ℂ) * Complex.I) := by
      rw [hEdef, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hFk : F ^ (k + 1) = Complex.exp (-((((k + 1) * α : ℝ) : ℂ) * Complex.I)) := by
      rw [hFdef, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hEk, hFk, Complex.ofReal_sin, Complex.sin]
    ring_nf
    rw [Complex.I_sq]
    ring
  -- the two geometric series
  have hpnorm : ‖-u * E‖ < 1 := by
    rw [norm_mul, norm_neg, hE, mul_one]
    exact hu
  have hqnorm : ‖-u * F‖ < 1 := by
    rw [norm_mul, norm_neg, hF, mul_one]
    exact hu
  have hgeo : ∀ v : ℂ, ‖v‖ < 1 → Summable (fun k : ℕ => v ^ (k + 1)) ∧
      ∑' k : ℕ, v ^ (k + 1) = (1 - v)⁻¹ - 1 := by
    intro v hv
    have hgs : Summable fun n : ℕ => v ^ n := summable_geometric_of_norm_lt_one hv
    refine ⟨hgs.comp_injective (add_left_injective 1), ?_⟩
    have h0 := Summable.tsum_eq_zero_add hgs
    rw [tsum_geometric_of_norm_lt_one hv] at h0
    simp only [pow_zero] at h0
    rw [h0]
    ring
  obtain ⟨hps, hpsum⟩ := hgeo _ hpnorm
  obtain ⟨hqs, hqsum⟩ := hgeo _ hqnorm
  -- the termwise identity after clearing `2i`
  have hterm : ∀ k : ℕ,
      ((-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * u ^ (k + 1)) * (2 * Complex.I)
        = -((-u * E) ^ (k + 1)) + (-u * F) ^ (k + 1) := by
    intro k
    have hexp : ((-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * u ^ (k + 1)) * (2 * Complex.I)
        = (-1 : ℂ) ^ k * u ^ (k + 1) *
          (((Real.sin ((k + 1) * α) : ℝ) : ℂ) * (2 * Complex.I)) := by ring
    rw [hexp, hsin k, mul_pow, mul_pow, neg_pow, neg_pow]
    ring
  have hsummable : Summable fun k : ℕ =>
      (-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * u ^ (k + 1) := by
    have hcomb : Summable fun k : ℕ => (-((-u * E) ^ (k + 1)) + (-u * F) ^ (k + 1)) :=
      (hps.neg).add hqs
    have hscaled : Summable fun k : ℕ =>
        ((-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * u ^ (k + 1)) * (2 * Complex.I) :=
      hcomb.congr fun k => (hterm k).symm
    have := hscaled.mul_right (2 * Complex.I)⁻¹
    refine this.congr fun k => ?_
    field_simp
  have hmain : (∑' k : ℕ, ((-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * u ^ (k + 1)))
      * (2 * Complex.I)
      = -((1 - (-u * E))⁻¹ - 1) + ((1 - (-u * F))⁻¹ - 1) := by
    rw [← tsum_mul_right, tsum_congr hterm, Summable.tsum_add hps.neg hqs, tsum_neg, hpsum, hqsum]
  -- evaluate the right-hand side
  have hEne : (1 : ℂ) + u * E ≠ 0 := by
    intro hcon
    have : ‖(1 : ℂ)‖ - ‖-(u * E)‖ ≤ ‖(1 : ℂ) - -(u * E)‖ := norm_sub_norm_le _ _
    rw [norm_one, norm_neg, norm_mul, hE, mul_one, sub_neg_eq_add, hcon, norm_zero] at this
    linarith
  have hFne : (1 : ℂ) + u * F ≠ 0 := by
    intro hcon
    have : ‖(1 : ℂ)‖ - ‖-(u * F)‖ ≤ ‖(1 : ℂ) - -(u * F)‖ := norm_sub_norm_le _ _
    rw [norm_one, norm_neg, norm_mul, hF, mul_one, sub_neg_eq_add, hcon, norm_zero] at this
    linarith
  have hEmF : E - F = 2 * Complex.I * (Real.sin α : ℂ) := by
    rw [hEdef, hFdef, Complex.ofReal_sin, Complex.sin]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hrhs : -((1 - (-u * E))⁻¹ - 1) + ((1 - (-u * F))⁻¹ - 1)
      = (u * (Real.sin α : ℂ) / (1 + 2 * u * (Real.cos α : ℂ) + u ^ (2 : ℕ))) * (2 * Complex.I) := by
    have hquad : (1 : ℂ) + 2 * u * (Real.cos α : ℂ) + u ^ (2 : ℕ) = (1 + u * E) * (1 + u * F) :=
      lambertQuadratic_factor α u
    rw [hquad]
    have hone : (1 : ℂ) - (-u * E) = 1 + u * E := by ring
    have htwo : (1 : ℂ) - (-u * F) = 1 + u * F := by ring
    rw [hone, htwo]
    field_simp
    linear_combination u * hEmF
  rw [hrhs] at hmain
  exact mul_right_cancel₀ hI hmain

end GaloisForLFunctions.RHTower
