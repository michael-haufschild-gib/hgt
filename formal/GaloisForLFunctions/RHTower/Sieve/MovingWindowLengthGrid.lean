import GaloisForLFunctions.RHTower.Sieve.VariableWindowFinitePartition

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Round a variable natural-number length down to a multiple of `q`. -/
def lengthGridQuantizer (q : ℕ) (L : ℕ → ℕ) (y : ℕ) : ℕ :=
  q * (L y / q)

theorem lengthGridQuantizer_le (q : ℕ) (L : ℕ → ℕ) (y : ℕ) :
    lengthGridQuantizer q L y ≤ L y := by
  exact Nat.mul_div_le (L y) q

theorem abs_length_sub_lengthGridQuantizer_lt (q : ℕ) (hq : 0 < q)
    (L : ℕ → ℕ) (y : ℕ) :
    |(L y : ℝ) - (lengthGridQuantizer q L y : ℝ)| < q := by
  have hle := lengthGridQuantizer_le q L y
  have hrem : L y - lengthGridQuantizer q L y = L y % q := by
    have hdiv := Nat.div_add_mod (L y) q
    simp only [lengthGridQuantizer] at hle ⊢
    omega
  rw [abs_of_nonneg]
  · rw [← Nat.cast_sub hle, hrem]
    exact_mod_cast Nat.mod_lt (L y) hq
  · exact sub_nonneg.mpr (by exact_mod_cast hle)

theorem card_image_lengthGridQuantizer_le (q : ℕ) (L : ℕ → ℕ)
    (S : Finset ℕ) (M : ℕ) (hLM : ∀ y ∈ S, L y ≤ M) :
    (S.image (lengthGridQuantizer q L)).card ≤ M / q + 1 := by
  classical
  have hfactor : S.image (lengthGridQuantizer q L) =
      (S.image (fun y => L y / q)).image (fun n => q * n) := by
    ext n
    simp [lengthGridQuantizer]
  rw [hfactor]
  refine (Finset.card_image_le).trans ?_
  have hsubset : S.image (fun y => L y / q) ⊆ Finset.range (M / q + 1) := by
    intro n hn
    rcases Finset.mem_image.1 hn with ⟨y, hy, rfl⟩
    rw [Finset.mem_range]
    have hdiv : L y / q ≤ M / q := Nat.div_le_div_right (c := q) (hLM y hy)
    omega
  simpa using Finset.card_le_card hsubset

theorem sum_lengthGridQuantizationError_le (q : ℕ) (hq : 0 < q)
    (L : ℕ → ℕ) (S : Finset ℕ) :
    (∑ y ∈ S, |(L y : ℝ) - (lengthGridQuantizer q L y : ℝ)| ^ 2)
      ≤ (S.card : ℝ) * (q : ℝ) ^ 2 := by
  have hpoint : ∀ y ∈ S,
      |(L y : ℝ) - (lengthGridQuantizer q L y : ℝ)| ^ 2 ≤ (q : ℝ) ^ 2 := by
    intro y _
    have hlt := abs_length_sub_lengthGridQuantizer_lt q hq L y
    have habs := abs_nonneg ((L y : ℝ) - (lengthGridQuantizer q L y : ℝ))
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  calc
    (∑ y ∈ S, |(L y : ℝ) - (lengthGridQuantizer q L y : ℝ)| ^ 2)
        ≤ ∑ y ∈ S, (q : ℝ) ^ 2 := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (q : ℝ) ^ 2 := by simp

theorem movingFibreWindowLength_le_ceil (x h : ℝ) (hx : 0 < x) (hh : 0 ≤ h)
    {y : ℕ} (hy : y ≤ ⌈Real.sqrt x⌉₊) :
    movingFibreWindowLength x h y ≤ ⌈h⌉₊ := by
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hceilpos : 0 < ⌈Real.sqrt x⌉₊ := Nat.ceil_pos.2 hsqrt
  have hpred_lt_ceil : y - 1 < ⌈Real.sqrt x⌉₊ := by omega
  have hpred_lt : ((y - 1 : ℕ) : ℝ) < Real.sqrt x := Nat.lt_ceil.1 hpred_lt_ceil
  have hratio : ((y - 1 : ℕ) : ℝ) / Real.sqrt x ≤ 1 :=
    (div_le_one hsqrt).2 hpred_lt.le
  have hlocal_nonneg : 0 ≤ h * (y - 1 : ℕ) / Real.sqrt x := by positivity
  have hlocal_le : h * (y - 1 : ℕ) / Real.sqrt x ≤ h := by
    rw [mul_div_assoc]
    nlinarith
  have hfloor : (movingFibreWindowLength x h y : ℝ)
      ≤ h * (y - 1 : ℕ) / Real.sqrt x := by
    exact Nat.floor_le hlocal_nonneg
  have hceil : h ≤ (⌈h⌉₊ : ℝ) := Nat.le_ceil h
  exact_mod_cast hfloor.trans (hlocal_le.trans hceil)

theorem card_movingLengthGrid_le (x h : ℝ) (hx : 0 < x) (hh : 0 ≤ h)
    (q : ℕ) :
    ((Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).image
      (lengthGridQuantizer q (movingFibreWindowLength x h))).card
      ≤ ⌈h⌉₊ / q + 1 := by
  apply card_image_lengthGridQuantizer_le
  intro y hy
  exact movingFibreWindowLength_le_ceil x h hx hh (Finset.mem_Icc.1 hy).2

/-- Terminal normalization through an explicit length grid of mesh `q`. -/
theorem sum_innerFibre_sq_le_lengthGridPartition (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 < x) (hh : 0 ≤ h)
    (q : ℕ) (hq : 0 < q) :
    (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2)
      ≤ 16 * ∑ ℓ ∈
          (Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).image
            (lengthGridQuantizer q (movingFibreWindowLength x h)),
            dyadicMeanSquare f ℓ (⌈Real.sqrt x / 2⌉₊ - 1) (⌈Real.sqrt x⌉₊ - 1)
        + 16 * ((Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).card : ℝ) * (q : ℝ) ^ 2
        + 2 * ((outerBlock x h).card : ℝ) * (h / Real.sqrt x + 2) ^ 2 := by
  have hbase := sum_innerFibre_sq_le_finitePartition f hf hx hh
    (lengthGridQuantizer q (movingFibreWindowLength x h))
  have herr := sum_lengthGridQuantizationError_le q hq
    (movingFibreWindowLength x h)
    (Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊)
  nlinarith

end

end RHTower.Sieve
