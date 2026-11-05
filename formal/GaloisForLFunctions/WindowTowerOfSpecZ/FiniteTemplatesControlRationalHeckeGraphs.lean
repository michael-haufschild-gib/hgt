import GaloisForLFunctions.WindowTowerOfSpecZ.RationalHeckeGraphsDetermineWindowPositivity

/-!
# Finite templates for rational Hecke graphs

A finite template closed under every active ratio within a prescribed spread
controls every rational graph of that spread. Remove the scaled template at
the least remaining vertex; closure makes its quadratic form a separate block.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- Restricting the vertex set is the same as extending its amplitudes by zero. -/
theorem rationalHeckeForm_restrict (N : ℕ) (c : ℕ → ℝ)
    (S T : Finset ℚ) (y : ℚ → ℝ) :
    rationalHeckeForm N c (S.filter fun r => r ∈ T) y =
      rationalHeckeForm N c S (fun r => if r ∈ T then y r else 0) := by
  classical
  unfold rationalHeckeForm
  congr 1
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r ∈ T <;> simp only [hr, if_true, if_false, zero_pow two_ne_zero]
  · apply Finset.sum_congr rfl
    intro n _
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r ∈ T
    · simp only [hr, if_true]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : s ∈ T <;> simp only [hs, if_true, if_false, mul_zero, ite_self]
    · simp only [hr, if_false, zero_mul, ite_self, Finset.sum_const_zero]

/-- A common rational scaling preserves every Hecke edge and its quadratic form. -/
theorem rationalHeckeForm_scale (N : ℕ) (c : ℕ → ℝ)
    (T : Finset ℚ) {r : ℚ} (hr : r ≠ 0) (y : ℚ → ℝ) :
    rationalHeckeForm N c (T.image fun q => r * q) y =
      rationalHeckeForm N c T (fun q => y (r * q)) := by
  classical
  have hinj : Set.InjOn (fun q : ℚ => r * q) T :=
    fun _ _ _ _ h => mul_left_cancel₀ hr h
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  unfold rationalHeckeForm
  congr 1
  · rw [Finset.sum_image hinj]
  · apply Finset.sum_congr rfl
    intro n _
    congr 1
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro s _
    have he : ((r * s : ℚ) : ℝ) = n * ((r * q : ℚ) : ℝ) ↔
        (s : ℝ) = n * q := by
      push_cast
      constructor
      · intro h
        apply mul_left_cancel₀ hr'
        calc (r : ℝ) * s = n * (r * q) := h
          _ = r * (n * q) := by ring
      · intro h
        rw [h]
        ring
    simp only [he]

/-- A set closed under the active Hecke neighbours separates the quadratic form. -/
theorem rationalHeckeForm_split_closed (N : ℕ) (c : ℕ → ℝ)
    (S B : Finset ℚ) (y : ℚ → ℝ)
    (hclosed : ∀ n ∈ Finset.Icc 2 N, ∀ r ∈ S, r ∈ B → ∀ s ∈ S,
      s = n * r ∨ r = n * s → s ∈ B) :
    rationalHeckeForm N c S y =
      rationalHeckeForm N c (S.filter fun r => r ∈ B) y +
      rationalHeckeForm N c (S.filter fun r => r ∉ B) y := by
  classical
  have hdiag : (∑ r ∈ S, y r ^ 2) =
      (∑ r ∈ S.filter (fun r => r ∈ B), y r ^ 2) +
      ∑ r ∈ S.filter (fun r => r ∉ B), y r ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r ∈ B <;> simp only [hr, not_true_eq_false, not_false_eq_true,
      if_true, if_false, add_zero, zero_add]
  have hedge : ∀ n ∈ Finset.Icc 2 N,
      (∑ r ∈ S, ∑ s ∈ S, if (s : ℝ) = n * r then y r * y s else 0) =
      (∑ r ∈ S.filter (fun r => r ∈ B), ∑ s ∈ S.filter (fun r => r ∈ B),
        if (s : ℝ) = n * r then y r * y s else 0) +
      ∑ r ∈ S.filter (fun r => r ∉ B), ∑ s ∈ S.filter (fun r => r ∉ B),
        if (s : ℝ) = n * r then y r * y s else 0 := by
    intro n hn
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrB : r ∈ B
    · simp only [hrB, not_true_eq_false, if_true, if_false, add_zero]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsB : s ∈ B
      · simp only [hsB, if_true]
      · have he : (s : ℝ) ≠ n * r := by
          intro he
          have he' : s = n * r := by exact_mod_cast he
          exact hsB (hclosed n hn r hr hrB s hs (Or.inl he'))
        simp only [hsB, he, if_false]
    · simp only [hrB, not_false_eq_true, if_true, if_false, zero_add]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsB : s ∈ B
      · have he : (s : ℝ) ≠ n * r := by
          intro he
          have he' : s = n * r := by exact_mod_cast he
          exact hrB (hclosed n hn s hs hsB r hr (Or.inr he'))
        simp only [hsB, he, not_true_eq_false, if_false]
      · simp only [hsB, not_false_eq_true, if_true]
  unfold rationalHeckeForm
  have hsum := Finset.sum_congr (s₁ := Finset.Icc 2 N) (s₂ := Finset.Icc 2 N) rfl
    (fun n hn => congrArg (fun z : ℝ => c n * z) (hedge n hn))
  rw [hdiag, hsum]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

/-- A finite template closed under all neighbours below a fixed ratio controls
every finite rational graph of that spread. Peel off the block at the least vertex. -/
theorem rationalHeckeForm_nonneg_of_closed_template
    (N : ℕ) (c : ℕ → ℝ) (T : Finset ℚ) (R : ℚ) (h1 : 1 ∈ T)
    (hT : ∀ n ∈ Finset.Icc 2 N, ∀ q ∈ T, ∀ s : ℚ,
      1 ≤ s → s < R → s = n * q ∨ q = n * s → s ∈ T)
    (hposT : ∀ y : ℚ → ℝ, 0 ≤ rationalHeckeForm N c T y)
    (S : Finset ℚ) (hpos : ∀ r ∈ S, 0 < r)
    (hspread : ∀ r ∈ S, ∀ s ∈ S, s < R * r) (y : ℚ → ℝ) :
    0 ≤ rationalHeckeForm N c S y := by
  classical
  revert hpos hspread y
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hpos hspread y
    by_cases hS : S.Nonempty
    · let r := S.min' hS
      have hrS : r ∈ S := S.min'_mem hS
      have hrpos : 0 < r := hpos r hrS
      let B := T.image fun q => r * q
      have hrB : r ∈ B := Finset.mem_image.mpr ⟨1, h1, mul_one r⟩
      have hclosed : ∀ n ∈ Finset.Icc 2 N, ∀ u ∈ S, u ∈ B → ∀ v ∈ S,
          v = n * u ∨ u = n * v → v ∈ B := by
        intro n hn u _ huB v hv hrel
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp huB
        have hvlo : 1 ≤ v / r := (le_div_iff₀ hrpos).mpr (by
          simpa only [one_mul] using S.min'_le v hv)
        have hvhi : v / r < R := (div_lt_iff₀ hrpos).mpr (hspread r hrS v hv)
        have hvrel : v / r = n * q ∨ q = n * (v / r) := by
          rcases hrel with he | he
          · left
            apply (div_eq_iff hrpos.ne').mpr
            calc v = n * (r * q) := he
              _ = n * q * r := by ring
          · right
            rw [← mul_div_assoc]
            apply (eq_div_iff hrpos.ne').mpr
            nlinarith only [he]
        have hmem := hT n hn q hq (v / r) hvlo hvhi hvrel
        exact Finset.mem_image.mpr ⟨v / r, hmem, by field_simp⟩
      have hfirst : 0 ≤ rationalHeckeForm N c (S.filter fun u => u ∈ B) y := by
        have hset : S.filter (fun u => u ∈ B) = B.filter (fun u => u ∈ S) := by
          ext u
          simp only [Finset.mem_filter, and_comm]
        rw [hset, rationalHeckeForm_restrict, rationalHeckeForm_scale N c T hrpos.ne']
        exact hposT _
      have hsub : (S.filter fun u => u ∉ B) ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
        intro he
        have hm : r ∈ S.filter fun u => u ∉ B := he.symm ▸ hrS
        exact (Finset.mem_filter.mp hm).2 hrB
      have hsecond := ih (S.filter fun u => u ∉ B) hsub
        (fun u hu => hpos u (Finset.mem_filter.mp hu).1)
        (fun u hu v hv => hspread u (Finset.mem_filter.mp hu).1
          v (Finset.mem_filter.mp hv).1) y
      rw [rationalHeckeForm_split_closed N c S B y hclosed]
      exact add_nonneg hfirst hsecond
    · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp only [rationalHeckeForm, Finset.sum_empty, mul_zero, Finset.sum_const_zero,
        add_zero, le_refl]

#print axioms rationalHeckeForm_nonneg_of_closed_template

end GaloisForLFunctions.WindowTowerOfSpecZ
