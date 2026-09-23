import Mathlib

/-!
# Energy bound from bounded Satake parameters

A sum of `d` complex numbers of modulus at most one has modulus at most `d`, with equality only when
every summand has modulus exactly one.  Squaring and weighting gives, for a coefficient sequence of
the form `a p = ∑_{j<d} α j p` with `‖α j p‖ ≤ 1`,

```text
∑_{p ∈ s} ‖a p‖² w p ≤ d² ∑_{p ∈ s} w p     for any nonnegative weight w .
```

For an element of the Selberg class possessing a polynomial Euler product of local degree at most `d`
with Satake parameters bounded by one, this reads `∑_{p ≤ x}|a_F(p)|²/p ≤ d² ∑_{p≤x} 1/p`, so the
prime energy density is at most `d²`; equality would force all Satake parameters at a prime to
coincide and be unimodular, which happens only for a `d`-th power of a degree-one element.
-/

open Finset

namespace HTGeometry

/-- A sum of `card ι` complex numbers of modulus at most one has modulus at most `card ι`. -/
theorem norm_sum_le_card {ι : Type*} [Fintype ι] (v : ι → ℂ) (hle : ∀ i, ‖v i‖ ≤ 1) :
    ‖∑ i, v i‖ ≤ (Fintype.card ι : ℝ) := by
  calc ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
    _ = (Fintype.card ι : ℝ) := by simp [Finset.card_univ]

/-- **Rigidity of the equality case.**  If the modulus of the sum attains `card ι`, every summand has
modulus exactly one. -/
theorem norm_eq_one_of_norm_sum_eq_card {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (hle : ∀ i, ‖v i‖ ≤ 1) (h : ‖∑ i, v i‖ = (Fintype.card ι : ℝ)) :
    ∀ i, ‖v i‖ = 1 := by
  have h1 : ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
  have h2 : ∑ i, ‖v i‖ ≤ (Fintype.card ι : ℝ) := by
    calc ∑ i, ‖v i‖ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
      _ = (Fintype.card ι : ℝ) := by simp [Finset.card_univ]
  have hsum : ∑ i, ‖v i‖ = (Fintype.card ι : ℝ) := le_antisymm h2 (by rw [← h]; exact h1)
  have hzero : ∑ i, (1 - ‖v i‖) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp [Finset.card_univ]
  intro i
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ 1 - ‖v j‖ := fun j _ => by
    linarith [hle j]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
  linarith

/-- Two unit vectors on a common ray coincide. -/
theorem eq_of_sameRay_of_norm_one {x y : ℂ} (h : SameRay ℝ x y) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    x = y := by
  rcases h with h | h | ⟨r, s, hr, hs, hrs⟩
  · simp [h] at hx
  · simp [h] at hy
  · have hxr : ‖r • x‖ = r * ‖x‖ := by
      rw [norm_smul]; simp [abs_of_pos hr]
    have hys : ‖s • y‖ = s * ‖y‖ := by
      rw [norm_smul]; simp [abs_of_pos hs]
    have hrs' : r = s := by
      have hn := congrArg norm hrs
      rw [hxr, hys, hx, hy] at hn
      linarith
    subst hrs'
    exact smul_right_injective ℂ (ne_of_gt hr) hrs

/-- **Extremal Satake configuration at a prime.**  If two Satake parameters of modulus at most one
have `‖α₁ + α₂‖ = 2`, then both are unimodular **and equal**: the local factor is the square of a
degree-one factor.  This is the equality case of `norm_sum_le_card` for two summands, sharpened from
"both unimodular" to "both equal". -/
theorem satake_eq_of_norm_add_eq_two {α₁ α₂ : ℂ} (h₁ : ‖α₁‖ ≤ 1) (h₂ : ‖α₂‖ ≤ 1)
    (h : ‖α₁ + α₂‖ = 2) : α₁ = α₂ ∧ ‖α₁‖ = 1 := by
  have hle : ‖α₁ + α₂‖ ≤ ‖α₁‖ + ‖α₂‖ := norm_add_le _ _
  have hsum : ‖α₁‖ + ‖α₂‖ = 2 := by
    have := h ▸ hle
    linarith
  have hn₁ : ‖α₁‖ = 1 := by linarith
  have hn₂ : ‖α₂‖ = 1 := by linarith
  have hray : SameRay ℝ α₁ α₂ := sameRay_iff_norm_add.mpr (by rw [h, hn₁, hn₂]; norm_num)
  exact ⟨eq_of_sameRay_of_norm_one hray hn₁ hn₂, hn₁⟩

/-- **The determinant is the square of the trace, corrected by the Satake gap.**  Exactly, with no
error term: `α₁α₂ = (α₁+α₂)²/4 − (α₁−α₂)²/4`. -/
theorem satake_det_eq (α₁ α₂ : ℂ) :
    α₁ * α₂ = (α₁ + α₂) ^ (2 : ℕ) / 4 - (α₁ - α₂) ^ (2 : ℕ) / 4 := by ring

/-- **The Satake gap is controlled by the energy defect.**  With both parameters of modulus at most
one, `‖α₁−α₂‖² ≤ 4 − ‖α₁+α₂‖²`.  So a local trace close to its maximum forces the two parameters
together, quantitatively and with no exceptional set. -/
theorem norm_sub_sq_le_four_sub {α₁ α₂ : ℂ} (h₁ : ‖α₁‖ ≤ 1) (h₂ : ‖α₂‖ ≤ 1) :
    ‖α₁ - α₂‖ ^ (2 : ℕ) ≤ 4 - ‖α₁ + α₂‖ ^ (2 : ℕ) := by
  have hpar := parallelogram_law_with_norm ℝ α₁ α₂
  have hs₁ : ‖α₁‖ ^ (2 : ℕ) ≤ 1 := by nlinarith [norm_nonneg α₁]
  have hs₂ : ‖α₂‖ ^ (2 : ℕ) ≤ 1 := by nlinarith [norm_nonneg α₂]
  nlinarith [hpar]

/-- **Extremal energy forces a vanishing defect.**  If a bounded nonnegative quantity attains, up to
`ε`, its maximal weighted total, then the total weighted defect is at most `ε`.  Applied with
`f p = |a_F(p)|²`, `M = d²` and `w p = 1/p`, an energy density equal to the maximum `d²` forces
`|a_F(p)| = d` outside a set of zero `1/p`-density. -/
theorem weighted_defect_le {ι : Type*} (s : Finset ι) (f w : ι → ℝ) (M ε : ℝ)
    (hlow : M * ∑ i ∈ s, w i - ε ≤ ∑ i ∈ s, f i * w i) :
    ∑ i ∈ s, (M - f i) * w i ≤ ε := by
  have hsplit : ∑ i ∈ s, (M - f i) * w i = M * ∑ i ∈ s, w i - ∑ i ∈ s, f i * w i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  linarith

/-- **Weighted energy bound.**  With `‖a p‖ ≤ D` on the index set and a nonnegative weight, the
weighted square sum is at most `D²` times the weight total. -/
theorem weighted_sq_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, ‖a i‖ ≤ D) :
    ∑ i ∈ s, ‖a i‖ ^ (2 : ℕ) * w i ≤ D ^ (2 : ℕ) * ∑ i ∈ s, w i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h1 : ‖a i‖ ^ (2 : ℕ) ≤ D ^ (2 : ℕ) := by
    have := ha i hi
    nlinarith [norm_nonneg (a i), hD]
  exact mul_le_mul_of_nonneg_right h1 (hw i hi)

end HTGeometry
