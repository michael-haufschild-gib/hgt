import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TwoCoupledWindowsHoldAtMostTheBoundStatesOfTheProductModelWithLoweredPotentials
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnANarrowWindowThePotentialIsShallowAndTheCountOfBoundStatesIsOne
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFirstBlockMatricesOfRatioFourAndSevenHaveAMargin
import GaloisForLFunctions.HeckeKreinToeplitz.IntegerFamiliesCarryTheWholeIndex

/-!
# The two halves of a window of ratio four do not glue through a product of charges

The neutral part of the window `(R, 4R]` is the neutral parts of `(R, 2R]` and `(2R, 4R]`
coupled by the weights `K` between their blocks: jets and the contacts of the floor maps. For
charges `u`, `v` with `u_i v_j ≤ K_ij` the union holds at most the bound states of the product
model: the two halves with potentials lowered by the excess `K − u ⊗ v`, glued through `u ⊗ v`.
That model would count one bound state if the lowered halves were nonnegative where their
charge vanishes and their susceptibilities multiplied to at least one.

**For no pair of charges it does.** For `R = 2H`, `H ≥ 64`, and every `u`, `v` below the
couplings, the lowered lower half has two negative squares
(`two_le_hermNegIndex_lowered_lower_half`), it is negative on a vector without charge
(`exists_chargeless_negative_lowered_lower_half`), and the product model has at least two
negative squares (`two_le_hermNegIndex_glued_lowered_ratio_four`).

* **A product of charges carries no contacts.** Let `K ≥ 0` have row sums at most `ρ`, and let
  every block `i` of the first form reserve a set `cont i` of blocks of the second, disjoint
  for different `i`. If `u_i v_j ≤ K_ij` everywhere, then for every set `S` of blocks

    `Σ_{i ∈ S} (excess of i) ≥ Σ_{i ∈ S} Σ_{j ∈ cont i} K_ij − ρ`

  (`sum_contacts_sub_le_sum_excessLeft`). With `P` the sum of the positive parts of `v` and
  `p_i` its part on `cont i`: a positive `u_i` is at most `ρ/P`, so `u_i` times the charge of
  the second form is at most the couplings of `i` outside `cont i` plus `ρ p_i/P`, and the
  `p_i` add up to at most `P`.
* **The contacts of the floor map of `2`.** The block `a` of `(R, 2R]` meets the blocks `2a`,
  `2a + 1` of `(2R, 4R]` with the weight `Λ(2)/2` each: the reserved couplings are at least
  `log 2` per block, while a row of `K` adds up to at most `½ log(12 H) + 1 + log 6`
  (`sum_range_blockWeight_le`).
* **The two quarters.** On the constant packets of `(2H, 3H]` and `(3H, 4H]` the neutral part
  of the lower half takes the values `H (5 log 5 − 9 log 2 − c₀)`,
  `H (7 log 7 − 7 log 2 − 6 log 3 − c₀)` and the pairing
  `(H/2)(12 log 3 + 10 log 2 − 5 log 5 − 7 log 7)`, with `c₀ = γ + log 2π`
  (`sum_neutralBlock_lower_quarter`, `sum_neutralBlock_upper_quarter`,
  `sum_neutralBlock_cross_quarters`). Lowered by `H log 2 − ρ` the two diagonal values are below
  `−1.02 H` and `−0.65 H`, and their product exceeds the square `0.604 H²` of the pairing.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### A product of charges carries no contacts -/

section Contacts

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]

omit [Fintype ι₁] in
/-- The excess over a product of charges is at least the reserved couplings minus one row sum,
when the second charge has a nonnegative sum. -/
theorem sum_contacts_sub_le_sum_excessLeft_of_nonneg {K : ι₁ → ι₂ → ℝ} {u : ι₁ → ℝ}
    {v : ι₂ → ℝ} (hK : ∀ i j, u i * v j ≤ K i j) (hK0 : ∀ i j, 0 ≤ K i j)
    (cont : ι₁ → Finset ι₂) {S : Finset ι₁} (hcont : (S : Set ι₁).PairwiseDisjoint cont)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ i ∈ S, ∑ j, K i j ≤ ρ) (hV : 0 ≤ ∑ j, v j) :
    ∑ i ∈ S, ∑ j ∈ cont i, K i j - ρ ≤ ∑ i ∈ S, excessLeft K u v i := by
  -- `P`: the sum of the positive parts of `v`
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ j, max (v j) 0 := ⟨_, rfl⟩
  have hp0 : ∀ j, 0 ≤ max (v j) 0 := fun j => le_max_right _ _
  have hP0 : 0 ≤ P := hP ▸ Finset.sum_nonneg fun j _ => hp0 j
  have hVP : ∑ j, v j ≤ P := hP ▸ Finset.sum_le_sum fun j _ => le_max_left _ _
  have hup : ∀ i, 0 < u i → ∀ j, u i * max (v j) 0 ≤ K i j := by
    intro i _ j
    rcases le_total (v j) 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact hK0 i j
    · rw [max_eq_left h]
      exact hK i j
  have hρP : 0 ≤ ρ / P := div_nonneg hρ0 hP0
  -- the charge of a block against the whole second form
  have hrow : ∀ i ∈ S, u i * ∑ j, v j ≤
      ∑ j, K i j - ∑ j ∈ cont i, K i j + ρ / P * ∑ j ∈ cont i, max (v j) 0 := by
    intro i hi
    have hsK : ∑ j ∈ Finset.univ \ cont i, K i j + ∑ j ∈ cont i, K i j = ∑ j, K i j :=
      Finset.sum_sdiff (Finset.subset_univ _)
    have hsP : ∑ j ∈ Finset.univ \ cont i, max (v j) 0 + ∑ j ∈ cont i, max (v j) 0 = P := by
      rw [hP]
      exact Finset.sum_sdiff (Finset.subset_univ _)
    have hJ0 : 0 ≤ ∑ j ∈ Finset.univ \ cont i, K i j := Finset.sum_nonneg fun j _ => hK0 i j
    have hp : 0 ≤ ∑ j ∈ cont i, max (v j) 0 := Finset.sum_nonneg fun j _ => hp0 j
    have hmass := mul_nonneg hρP hp
    by_cases hui : 0 < u i
    · have h1 : u i * ∑ j, v j ≤ u i * P := mul_le_mul_of_nonneg_left hVP hui.le
      -- outside the reserved blocks the charges are below the couplings
      have h3 : u i * ∑ j ∈ Finset.univ \ cont i, max (v j) 0 ≤
          ∑ j ∈ Finset.univ \ cont i, K i j := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => hup i hui j
      have h4 : u i * P ≤ ρ := by
        rw [hP, Finset.mul_sum]
        exact (Finset.sum_le_sum fun j _ => hup i hui j).trans (hρ i hi)
      rcases hP0.eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero] at h1
        linarith
      · -- on the reserved blocks the charge `u i` is at most `ρ / P`
        have h5 : u i ≤ ρ / P := (le_div_iff₀ hpos).mpr h4
        have h6 := mul_le_mul_of_nonneg_right h5 hp
        have h7 : u i * P = u i * ∑ j ∈ Finset.univ \ cont i, max (v j) 0 +
            u i * ∑ j ∈ cont i, max (v j) 0 := by rw [← hsP, mul_add]
        linarith
    · have h1 : u i * ∑ j, v j ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hui) hV
      linarith
  -- the reserved parts of the positive mass add up to at most `P`
  have hbi : ∑ i ∈ S, ∑ j ∈ cont i, max (v j) 0 ≤ P := by
    rw [← Finset.sum_biUnion hcont, hP]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hp0 j
  have hmass : ρ / P * ∑ i ∈ S, ∑ j ∈ cont i, max (v j) 0 ≤ ρ := by
    rcases hP0.eq_or_lt with h0 | hpos
    · rw [← h0, div_zero, zero_mul]
      exact hρ0
    · calc ρ / P * ∑ i ∈ S, ∑ j ∈ cont i, max (v j) 0 ≤ ρ / P * P :=
          mul_le_mul_of_nonneg_left hbi hρP
        _ = ρ := div_mul_cancel₀ ρ hpos.ne'
  have hsum := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hex : ∑ i ∈ S, excessLeft K u v i =
      ∑ i ∈ S, ∑ j, K i j - ∑ i ∈ S, u i * ∑ j, v j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [excessLeft, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hex]
  linarith

omit [Fintype ι₁] in
/-- **A product of charges carries no contacts.** If `u_i v_j ≤ K_ij`, the couplings `K ≥ 0`
have row sums at most `ρ`, and the blocks of `S` reserve disjoint sets `cont i` of blocks of the
second form, then the excess of `S` over the product of the charges is at least the reserved
couplings minus `ρ`. -/
theorem sum_contacts_sub_le_sum_excessLeft {K : ι₁ → ι₂ → ℝ} {u : ι₁ → ℝ} {v : ι₂ → ℝ}
    (hK : ∀ i j, u i * v j ≤ K i j) (hK0 : ∀ i j, 0 ≤ K i j) (cont : ι₁ → Finset ι₂)
    {S : Finset ι₁} (hcont : (S : Set ι₁).PairwiseDisjoint cont) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ i ∈ S, ∑ j, K i j ≤ ρ) :
    ∑ i ∈ S, ∑ j ∈ cont i, K i j - ρ ≤ ∑ i ∈ S, excessLeft K u v i := by
  rcases le_total 0 (∑ j, v j) with hV | hV
  · exact sum_contacts_sub_le_sum_excessLeft_of_nonneg hK hK0 cont hcont hρ0 hρ hV
  · -- the product of the charges does not change under a common change of sign
    have h := sum_contacts_sub_le_sum_excessLeft_of_nonneg (u := fun i => -u i)
      (v := fun j => -v j) (fun i j => by rw [neg_mul_neg]; exact hK i j) hK0 cont hcont hρ0 hρ
      (by rw [Finset.sum_neg_distrib]; linarith)
    have e : ∀ i, excessLeft K (fun i => -u i) (fun j => -v j) i = excessLeft K u v i :=
      fun i => by simp only [excessLeft, neg_mul_neg]
    simpa only [e] using h

end Contacts

/-! ### Two negative squares on the plane of two vectors -/

section Plane

variable {ι : Type*} [Fintype ι]

/-- A real form below a binary form with negative leading coefficient and positive
discriminant on the plane of two vectors has two negative squares. -/
theorem two_le_hermNegIndex_of_two_vectors (G : Matrix ι ι ℝ) (w₁ w₂ : ι → ℝ) {α γ c : ℝ}
    (h : ∀ s t : ℝ, bilin G (fun i => s * w₁ i + t * w₂ i) (fun i => s * w₁ i + t * w₂ i) ≤
      α * s ^ 2 + 2 * c * s * t + γ * t ^ 2)
    (hα : α < 0) (hdisc : c ^ 2 < α * γ) :
    2 ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ) := by
  have hcard := card_le_hermNegIndex_of_real_neg (κ := Fin 2) G ![w₁, w₂] (by
    intro g hg
    have e : (fun m : ι => ∑ j : Fin 2, g j * ((![w₁, w₂] : Fin 2 → ι → ℝ) j m)) =
        fun i => g 0 * w₁ i + g 1 * w₂ i := by
      funext m
      rw [Fin.sum_univ_two]
      rfl
    rw [e]
    refine lt_of_le_of_lt (h (g 0) (g 1)) (quad_neg_of_disc hα (by linarith) ?_)
    by_contra hcon
    push Not at hcon
    refine hg (funext fun i => ?_)
    fin_cases i
    · exact hcon.1
    · exact hcon.2)
  rwa [Fintype.card_fin] at hcard

theorem chargeOf_add_smul (u w₁ w₂ : ι → ℝ) (s t : ℝ) :
    chargeOf u (fun i => s * w₁ i + t * w₂ i) = s * chargeOf u w₁ + t * chargeOf u w₂ := by
  simp only [chargeOf, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A real form that is negative on a plane is negative on a vector of the plane without
charge. -/
theorem exists_chargeOf_eq_zero_and_bilin_neg (G : Matrix ι ι ℝ) (u w₁ w₂ : ι → ℝ)
    {α γ c : ℝ}
    (h : ∀ s t : ℝ, bilin G (fun i => s * w₁ i + t * w₂ i) (fun i => s * w₁ i + t * w₂ i) ≤
      α * s ^ 2 + 2 * c * s * t + γ * t ^ 2)
    (hα : α < 0) (hdisc : c ^ 2 < α * γ) :
    ∃ x : ι → ℝ, chargeOf u x = 0 ∧ bilin G x x < 0 := by
  by_cases h0 : chargeOf u w₁ = 0 ∧ chargeOf u w₂ = 0
  · refine ⟨fun i => 1 * w₁ i + 0 * w₂ i, ?_,
      lt_of_le_of_lt (h 1 0) (quad_neg_of_disc hα (by linarith) (Or.inl one_ne_zero))⟩
    rw [chargeOf_add_smul, h0.1]
    ring
  · refine ⟨fun i => chargeOf u w₂ * w₁ i + -chargeOf u w₁ * w₂ i, ?_,
      lt_of_le_of_lt (h _ _) (quad_neg_of_disc hα (by linarith) ?_)⟩
    · rw [chargeOf_add_smul]
      ring
    · by_contra hcon
      push Not at hcon
      exact h0 ⟨by linarith [hcon.2], hcon.1⟩

/-- The form of a symmetric kernel on a step function with two steps of equal length. -/
theorem sum_two_steps (m : ℕ → ℕ → ℝ) (hm : ∀ j l, m j l = m l j) (H : ℕ) (s t : ℝ) :
    ∑ j ∈ range (H + H), ∑ l ∈ range (H + H),
        (if j < H then s else t) * (if l < H then s else t) * m j l =
      (∑ j ∈ range H, ∑ l ∈ range H, m j l) * s ^ 2 +
        2 * (∑ j ∈ range H, ∑ l ∈ range H, m j (H + l)) * s * t +
          (∑ j ∈ range H, ∑ l ∈ range H, m (H + j) (H + l)) * t ^ 2 := by
  have hin : ∀ (c : ℝ) (j : ℕ), ∑ l ∈ range (H + H), c * (if l < H then s else t) * m j l =
      c * s * ∑ l ∈ range H, m j l + c * t * ∑ l ∈ range H, m j (H + l) := by
    intro c j
    rw [Finset.sum_range_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun l hl => by rw [if_pos (Finset.mem_range.mp hl)]
    · exact Finset.sum_congr rfl fun l _ => by
        rw [if_neg (show ¬H + l < H by omega)]
  have h1 : ∀ j ∈ range H, ∑ l ∈ range (H + H),
      (if j < H then s else t) * (if l < H then s else t) * m j l =
        s * s * ∑ l ∈ range H, m j l + s * t * ∑ l ∈ range H, m j (H + l) := fun j hj => by
    rw [if_pos (Finset.mem_range.mp hj)]
    exact hin s j
  have h2 : ∀ j ∈ range H, ∑ l ∈ range (H + H),
      (if H + j < H then s else t) * (if l < H then s else t) * m (H + j) l =
        t * s * ∑ l ∈ range H, m (H + j) l + t * t * ∑ l ∈ range H, m (H + j) (H + l) :=
    fun j _ => by
      rw [if_neg (show ¬H + j < H by omega)]
      exact hin t (H + j)
  have hsym : ∑ j ∈ range H, ∑ l ∈ range H, m (H + j) l =
      ∑ j ∈ range H, ∑ l ∈ range H, m j (H + l) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => hm _ _
  rw [Finset.sum_range_add, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hsym]
  ring

end Plane

/-! ### The glued form contains its first form -/

section Glued

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- A glued form has at least the negative squares of its first form. -/
theorem hermNegIndex_le_hermNegIndex_glued (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (u : ι₁ → ℝ) (v : ι₂ → ℝ) :
    hermNegIndex (A.map (↑) : Matrix ι₁ ι₁ ℂ) ≤
      hermNegIndex ((glued A B u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_submatrix_le
    ((glued A B u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) Sum.inl

end Glued

/-! ### The neutral part on the constant packet of a window without contacts -/

theorem xLogXStep_nonneg (n : ℕ) : 0 ≤ xLogXStep n := by
  rw [xLogXStep, xLogX, xLogX, sub_nonneg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    exact mul_le_mul (by push_cast; linarith) h2 (Real.log_nonneg h1) (by positivity)

/-- The steps of `n log n` telescope. -/
theorem sum_range_xLogXStep (m K : ℕ) :
    ∑ j ∈ range K, xLogXStep (m + j) = xLogX (m + K) - xLogX m := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, xLogXStep, ← add_assoc]
    ring

/-- **The neutral part on the constant packet of a window `(R, R + J]` with `J ≤ R`**: the
density, the jets to the sums and the jets to the differences. -/
theorem sum_neutralBlock_window {Q R J : ℕ} (hJ : J ≤ R) :
    ∑ j ∈ range J, ∑ l ∈ range J, neutralBlock Q (R + j) (R + l) =
      xLogX (R + J) - xLogX R -
          J * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) -
        (xLogX (R + R + J + J) - 2 * xLogX (R + R + J) + xLogX (R + R)) / 2 - xLogX J := by
  have hrow : ∀ j ∈ range J, ∑ l ∈ range J, neutralBlock Q (R + j) (R + l) =
      xLogXStep (R + j) - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) -
        (xLogXStep (R + R + J + j) - xLogXStep (R + R + j)) / 2 -
          (xLogXStep j + xLogXStep (J - 1 - j)) / 2 := by
    intro j hj
    have h := blockPotential_eq_of_window (Q := Q) hJ (Finset.mem_range.mp hj)
    rw [blockPotential] at h
    rw [h, show R + j + R + J = R + R + J + j by omega, show R + j + R = R + R + j by omega]
    rfl
  have h1 : ∑ j ∈ range J, xLogXStep (R + j) = xLogX (R + J) - xLogX R :=
    sum_range_xLogXStep R J
  have h2 : ∑ j ∈ range J, xLogXStep (R + R + J + j) =
      xLogX (R + R + J + J) - xLogX (R + R + J) := sum_range_xLogXStep _ J
  have h3 : ∑ j ∈ range J, xLogXStep (R + R + j) = xLogX (R + R + J) - xLogX (R + R) :=
    sum_range_xLogXStep _ J
  have h4 : ∑ j ∈ range J, xLogXStep j = xLogX J := by
    have h := sum_range_xLogXStep 0 J
    simp only [zero_add] at h
    rw [h]
    simp [xLogX]
  have h5 : ∑ j ∈ range J, xLogXStep (J - 1 - j) = xLogX J := by
    rw [Finset.sum_range_reflect (fun j => xLogXStep j) J]
    exact h4
  rw [Finset.sum_congr rfl hrow]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, h1, h2, h3, h4, h5]
  ring

theorem xLogX_mul {c H : ℕ} (hc : 1 ≤ c) (hH : 1 ≤ H) :
    xLogX (c * H) = c * H * (Real.log c + Real.log H) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast (by omega : H ≠ 0)
  rw [xLogX, Nat.cast_mul, Real.log_mul hc' hH']

/-! ### The two quarters of the window `(2H, 4H]` -/

/-- The neutral part on the constant packet of `(2H, 3H]`. -/
theorem sum_neutralBlock_lower_quarter (Q : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    ∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (H + H + j) (H + H + l) =
      H * (5 * Real.log 5 - 9 * Real.log 2 -
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) := by
  rw [sum_neutralBlock_window (Q := Q) (R := H + H) (J := H) (by omega),
    show H + H + (H + H) + H + H = 6 * H by ring, show H + H + (H + H) + H = 5 * H by ring,
    show H + H + (H + H) = 4 * H by ring, show H + H + H = 3 * H by ring,
    show H + H = 2 * H by ring,
    xLogX_mul (c := 6) (by norm_num) hH, xLogX_mul (c := 5) (by norm_num) hH,
    xLogX_mul (c := 4) (by norm_num) hH, xLogX_mul (c := 3) (by norm_num) hH,
    xLogX_mul (c := 2) (by norm_num) hH, xLogX]
  push_cast
  rw [log_six, log_four]
  ring

/-- The neutral part on the constant packet of `(3H, 4H]`. -/
theorem sum_neutralBlock_upper_quarter (Q : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    ∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (H + H + (H + j)) (H + H + (H + l)) =
      H * (7 * Real.log 7 - 7 * Real.log 2 - 6 * Real.log 3 -
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) := by
  simp only [← add_assoc]
  rw [sum_neutralBlock_window (Q := Q) (R := H + H + H) (J := H) (by omega),
    show H + H + H + (H + H + H) + H + H = 8 * H by ring,
    show H + H + H + (H + H + H) + H = 7 * H by ring,
    show H + H + H + (H + H + H) = 6 * H by ring, show H + H + H + H = 4 * H by ring,
    show H + H + H = 3 * H by ring,
    xLogX_mul (c := 8) (by norm_num) hH, xLogX_mul (c := 7) (by norm_num) hH,
    xLogX_mul (c := 6) (by norm_num) hH, xLogX_mul (c := 4) (by norm_num) hH,
    xLogX_mul (c := 3) (by norm_num) hH, xLogX]
  push_cast
  rw [log_eight, log_six, log_four]
  ring

/-- The neutral part on the constant packet of `(2H, 4H]`. -/
theorem sum_neutralBlock_ratio_two (Q : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    ∑ j ∈ range (H + H), ∑ l ∈ range (H + H), neutralBlock Q (H + H + j) (H + H + l) =
      H * (6 * Real.log 3 - 6 * Real.log 2 -
        2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) := by
  rw [sum_neutralBlock_window (Q := Q) (R := H + H) (J := H + H) le_rfl,
    show H + H + (H + H) + (H + H) + (H + H) = 8 * H by ring,
    show H + H + (H + H) + (H + H) = 6 * H by ring, show H + H + (H + H) = 4 * H by ring,
    show H + H = 2 * H by ring,
    xLogX_mul (c := 8) (by norm_num) hH, xLogX_mul (c := 6) (by norm_num) hH,
    xLogX_mul (c := 4) (by norm_num) hH, xLogX_mul (c := 2) (by norm_num) hH]
  push_cast
  rw [log_eight, log_six, log_four]
  ring

/-- The pairing of the constant packets of `(2H, 3H]` and `(3H, 4H]`. -/
theorem sum_neutralBlock_cross_quarters (Q : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    ∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (H + H + j) (H + H + (H + l)) =
      H * ((12 * Real.log 3 + 10 * Real.log 2 - 5 * Real.log 5 - 7 * Real.log 7) / 2) := by
  have h := sum_two_steps (fun j l => neutralBlock Q (H + H + j) (H + H + l))
    (fun j l => neutralBlock_comm Q _ _) H 1 1
  simp only [ite_self, one_mul, mul_one, one_pow] at h
  rw [sum_neutralBlock_ratio_two Q hH, sum_neutralBlock_lower_quarter Q hH,
    sum_neutralBlock_upper_quarter Q hH] at h
  linarith

/-! ### The couplings of a block of the lower half with the upper half -/

theorem max_sub_max_mem (y x : ℝ) :
    0 ≤ max (y - x) 0 - max (y - (x + 1)) 0 ∧ max (y - x) 0 - max (y - (x + 1)) 0 ≤ 1 := by
  rcases max_cases (y - x) 0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases max_cases (y - (x + 1)) 0 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    constructor <;> linarith

/-- **Only the floor maps of `2` and `3` reach the blocks below `4a` from the block `a`**, each
at most `k` times: the contacts add up to at most `log 2 + log 3`. -/
theorem sum_Ico_floorContact_le {Q a L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) (h4 : L₂ ≤ 4 * a) :
    ∑ l ∈ Ico L₁ L₂, floorContact Q a l ≤ Real.log 2 + Real.log 3 := by
  have hk : ∀ k ∈ Icc 2 Q, ∑ l ∈ Ico L₁ L₂, (if l / k = a then (Λ k : ℝ) / k else 0) ≤
      (if k = 2 then Real.log 2 else 0) + (if k = 3 then Real.log 3 else 0) := by
    intro k hk
    have hk2 := (Finset.mem_Icc.mp hk).1
    by_cases h3 : k ≤ 3
    · have hterm : ∀ l ∈ Ico L₁ L₂, (if l / k = a then (Λ k : ℝ) / k else 0) =
          (Λ k : ℝ) * (if l / k = a then 1 / (k : ℝ) else 0) := fun l _ => by
        split_ifs <;> ring
      have hb1 := (max_sub_max_mem ((L₂ : ℝ) / k) a).2
      have hb2 := (max_sub_max_mem ((L₁ : ℝ) / k) a).1
      have hle : ∑ l ∈ Ico L₁ L₂, (if l / k = a then (Λ k : ℝ) / k else 0) ≤ (Λ k : ℝ) := by
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
          sum_Ico_floor_indicator (by omega) a hL]
        calc (Λ k : ℝ) * _ ≤ (Λ k : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left (by linarith) ArithmeticFunction.vonMangoldt_nonneg
          _ = (Λ k : ℝ) := mul_one _
      refine hle.trans ?_
      interval_cases k
      · rw [vonMangoldt_two]
        simp
      · rw [vonMangoldt_three]
        simp
    · -- a floor map of `k ≥ 4` sends no block below `4a` to `a`
      rw [if_neg (by omega), if_neg (by omega), add_zero]
      refine le_of_eq (Finset.sum_eq_zero fun l hl => if_neg fun hdiv => ?_)
      have h1 : a * k ≤ l := by
        rw [← hdiv]
        exact Nat.div_mul_le_self l k
      have h2 : a * 4 ≤ a * k := Nat.mul_le_mul_left a (by omega)
      have h5 := (Finset.mem_Ico.mp hl).2
      omega
  unfold floorContact
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum hk).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have h3 := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
  split_ifs <;> linarith

/-- The jets between a block `a` and the `K` blocks above `L` telescope. -/
theorem sum_range_blockJet_eq {a L : ℕ} (haL : a < L) (K : ℕ) :
    ∑ j ∈ range K, blockJet a (L + j) =
      (xLogXStep (a + L + K) - xLogXStep (a + L) +
        (xLogXStep (L - a - 1 + K) - xLogXStep (L - a - 1))) / 2 := by
  have h1 : ∑ j ∈ range K, xLogXDiff (a + (L + j) + 1) =
      xLogXStep (a + L + K) - xLogXStep (a + L) := by
    rw [← sum_range_xLogXDiff_add (a + L) K]
    exact Finset.sum_congr rfl fun j _ => by rw [← add_assoc]
  have h2 : ∑ j ∈ range K, xLogXDiff (L + j - a) =
      xLogXStep (L - a - 1 + K) - xLogXStep (L - a - 1) := by
    rw [← sum_range_xLogXDiff_add (L - a - 1) K]
    exact Finset.sum_congr rfl fun j _ => by
      congr 1
      omega
  simp only [blockJet]
  rw [← Finset.sum_div, Finset.sum_add_distrib, h1, h2]

/-- **The couplings of a block `a` with `K` blocks above `L`**, when `K ≤ a + L + 1` and the
blocks stay below `4a`: the jets are at most `½ (log 2 + log(L − a + K)) + 1`, the contacts at
most `log 2 + log 3`. -/
theorem sum_range_blockWeight_le {Q a L K : ℕ} (haL : a < L) (hK : K ≤ a + L + 1)
    (h4 : L + K ≤ 4 * a) :
    ∑ j ∈ range K, blockWeight Q a (L + j) ≤
      (Real.log 2 + Real.log ((L - a + K : ℕ) : ℝ)) / 2 + 1 + (Real.log 2 + Real.log 3) := by
  have hterm : ∀ j ∈ range K, blockWeight Q a (L + j) =
      blockJet a (L + j) + floorContact Q a (L + j) := fun j _ => by
    rw [blockWeight, neutralBlock_of_lt (show a < L + j by omega)]
    ring
  have hC : ∑ j ∈ range K, floorContact Q a (L + j) ≤ Real.log 2 + Real.log 3 := by
    have h := sum_Ico_floorContact_le (Q := Q) (a := a) (Nat.le_add_right L K) h4
    rwa [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at h
  -- the jets to the sums: `log((a + L + K + 1)/(a + L + 1)) ≤ log 2`
  have hb1 := xLogXStep_le (a + L + K)
  have hb2 := le_xLogXStep (show 1 ≤ a + L by omega)
  have hpos : (0 : ℝ) < ((a + L : ℕ) : ℝ) + 1 := by positivity
  have hlog : Real.log (((a + L + K : ℕ) : ℝ) + 1) ≤
      Real.log 2 + Real.log (((a + L : ℕ) : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) hpos.ne']
    refine Real.log_le_log (by positivity) ?_
    have hK' : ((a + L + K : ℕ) : ℝ) ≤ ((a + L + (a + L + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : a + L + K ≤ a + L + (a + L + 1))
    push_cast at hK' ⊢
    linarith
  have hinv : 1 / (((a + L : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hpos]
    have : (0 : ℝ) ≤ ((a + L : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  -- the jets to the differences
  have hb3 := xLogXStep_le (L - a - 1 + K)
  have hb4 := xLogXStep_nonneg (L - a - 1)
  have hcast : (((L - a - 1 + K : ℕ) : ℝ) + 1) = ((L - a + K : ℕ) : ℝ) := by
    exact_mod_cast (by omega : L - a - 1 + K + 1 = L - a + K)
  rw [hcast] at hb3
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, sum_range_blockJet_eq haL]
  linarith

/-- A block is coupled to each of its two preimages under the floor map of `2` by at least
`Λ(2)/2`. -/
theorem log_two_div_two_le_blockWeight {Q a b : ℕ} (hQ : 2 ≤ Q) (ha : 1 ≤ a)
    (hb : b / 2 = a) : Real.log 2 / 2 ≤ blockWeight Q a b := by
  have hab : a < b := by omega
  have hJ := blockJet_nonneg_of_lt hab
  have hC : Real.log 2 / 2 ≤ floorContact Q a b := by
    have h := Finset.single_le_sum (f := fun k => if b / k = a then (Λ k : ℝ) / k else 0)
      (fun k _ => by
        split_ifs
        · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
        · exact le_rfl)
      (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩ : 2 ∈ Icc 2 Q)
    simp only [if_pos hb, vonMangoldt_two] at h
    exact_mod_cast h
  rw [blockWeight, neutralBlock_of_lt hab]
  linarith

/-! ### The lowered lower half on the plane of its two quarters -/

/-- **The lowered lower half on the plane of its two quarters.** For charges below the
couplings of `(2H, 4H]` and `(4H, 8H]`, the lower half with the potential lowered by the excess
is, on the packets constant on `(2H, 3H]` and on `(3H, 4H]`, below a binary form with negative
leading coefficient and positive discriminant. -/
theorem lowered_lower_half_plane {H Q : ℕ} (hH : 64 ≤ H) (hQ : 2 ≤ Q) (u : Fin (H + H) → ℝ)
    (v : Fin (4 * H) → ℝ)
    (huv : ∀ i j, u i * v j ≤ blockWeight Q (H + H + i) (H + H + (H + H) + j)) :
    ∃ α γ c : ℝ, α < 0 ∧ c ^ 2 < α * γ ∧ ∀ s t : ℝ,
      bilin (neutralWindow Q (H + H) (H + H) - diagonal (excessLeft
          (fun (i : Fin (H + H)) (j : Fin (4 * H)) =>
            blockWeight Q (H + H + i) (H + H + (H + H) + j)) u v))
        (fun i => s * (if (i : ℕ) < H then 1 else 0) + t * (if (i : ℕ) < H then 0 else 1))
        (fun i => s * (if (i : ℕ) < H then 1 else 0) + t * (if (i : ℕ) < H then 0 else 1)) ≤
        α * s ^ 2 + 2 * c * s * t + γ * t ^ 2 := by
  obtain ⟨K, hKdef⟩ : ∃ K : Fin (H + H) → Fin (4 * H) → ℝ,
      K = fun (i : Fin (H + H)) (j : Fin (4 * H)) =>
        blockWeight Q (H + H + i) (H + H + (H + H) + j) := ⟨_, rfl⟩
  rw [← hKdef]
  have hKapp : ∀ i j, K i j = blockWeight Q (H + H + i) (H + H + (H + H) + j) := fun i j => by
    rw [hKdef]
  have hH1 : 1 ≤ H := by omega
  have hHr : (64 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => by
    have hi := i.2
    rw [hKapp]
    exact (blockWeight_pos (show H + H + (i : ℕ) ≠ H + H + (H + H) + (j : ℕ) by omega) Q).le
  have hKle : ∀ i j, u i * v j ≤ K i j := fun i j => by
    rw [hKapp]
    exact huv i j
  -- the logarithms
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l3 := log_three_mem
  have l5 := log_five_mem
  have l7 := log_seven_mem
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hπ : Real.log 3 < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) Real.pi_gt_three
  have hlogH : Real.log H ≤ 6 * Real.log 2 + H / 64 - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hHpos (by norm_num : (0 : ℝ) < 64))
    have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [Real.log_div hHpos.ne' (by norm_num), h64] at h
    linarith
  -- the row sums of the couplings
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ,
      ρ = (Real.log 2 + Real.log ((6 * H : ℕ) : ℝ)) / 2 + 1 + (Real.log 2 + Real.log 3) :=
    ⟨_, rfl⟩
  have hlog6H : Real.log ((6 * H : ℕ) : ℝ) = Real.log 2 + Real.log 3 + Real.log H := by
    have h6 : ((6 * H : ℕ) : ℝ) = 6 * (H : ℝ) := by push_cast; ring
    rw [h6, Real.log_mul (by norm_num) hHpos.ne', log_six]
  have hlogH0 : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef, hlog6H]
    linarith [l3.1]
  have hρH : ρ ≤ 3 / 20 * H := by
    rw [hρdef, hlog6H]
    linarith [l3.2]
  have hρ : ∀ i, ∑ j, K i j ≤ ρ := by
    intro i
    have hi := i.2
    have h := sum_range_blockWeight_le (Q := Q) (a := H + H + i) (L := H + H + (H + H))
      (K := 4 * H) (by omega) (by omega) (by omega)
    have hmono : Real.log ((H + H + (H + H) - (H + H + (i : ℕ)) + 4 * H : ℕ) : ℝ) ≤
        Real.log ((6 * H : ℕ) : ℝ) :=
      Real.log_le_log
        (by exact_mod_cast (by omega : 0 < H + H + (H + H) - (H + H + (i : ℕ)) + 4 * H))
        (by exact_mod_cast (by omega : H + H + (H + H) - (H + H + (i : ℕ)) + 4 * H ≤ 6 * H))
    have hfin : ∑ j, K i j =
        ∑ j ∈ range (4 * H), blockWeight Q (H + H + i) (H + H + (H + H) + j) := by
      simp only [hKapp]
      exact Fin.sum_univ_eq_sum_range
        (fun j => blockWeight Q (H + H + i) (H + H + (H + H) + j)) (4 * H)
    rw [hfin, hρdef]
    linarith
  -- the reserved blocks: the two preimages under the floor map of `2`
  obtain ⟨cont, hcont⟩ : ∃ cont : Fin (H + H) → Finset (Fin (4 * H)),
      cont = fun i => Finset.univ.filter fun j : Fin (4 * H) => (j : ℕ) / 2 = (i : ℕ) :=
    ⟨_, rfl⟩
  have hmem : ∀ (i : Fin (H + H)) (j : Fin (4 * H)), (j : ℕ) / 2 = (i : ℕ) → j ∈ cont i :=
    fun i j hj => by
      rw [hcont]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hof : ∀ (i : Fin (H + H)) (j : Fin (4 * H)), j ∈ cont i → (j : ℕ) / 2 = (i : ℕ) :=
    fun i j hj => by
      rw [hcont] at hj
      exact (Finset.mem_filter.mp hj).2
  have hdisj : ∀ i i', i ≠ i' → Disjoint (cont i) (cont i') := by
    intro i i' hne
    refine Finset.disjoint_left.mpr fun j h1 h2 => hne (Fin.ext ?_)
    exact (hof i j h1).symm.trans (hof i' j h2)
  have hκ : ∀ i, Real.log 2 ≤ ∑ j ∈ cont i, K i j := by
    intro i
    have hi := i.2
    have hval : ∀ j : Fin (4 * H), (j : ℕ) / 2 = (i : ℕ) → Real.log 2 / 2 ≤ K i j :=
      fun j hj => by
        rw [hKapp]
        exact log_two_div_two_le_blockWeight hQ (by omega) (by omega)
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin (4 * H), (j₀ : ℕ) = 2 * i := ⟨⟨2 * i, by omega⟩, rfl⟩
    obtain ⟨j₁, hj₁⟩ : ∃ j₁ : Fin (4 * H), (j₁ : ℕ) = 2 * i + 1 := ⟨⟨2 * i + 1, by omega⟩, rfl⟩
    have h0 : j₀ ≠ j₁ := fun h => by
      rw [h] at hj₀
      omega
    have hsub : ({j₀, j₁} : Finset (Fin (4 * H))) ⊆ cont i := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hmem i _ (by omega)
      · rw [Finset.mem_singleton.mp hx]
        exact hmem i _ (by omega)
    calc Real.log 2 = Real.log 2 / 2 + Real.log 2 / 2 := by ring
      _ ≤ K i j₀ + K i j₁ := add_le_add (hval j₀ (by omega)) (hval j₁ (by omega))
      _ = ∑ j ∈ ({j₀, j₁} : Finset (Fin (4 * H))), K i j := (Finset.sum_pair h0).symm
      _ ≤ ∑ j ∈ cont i, K i j :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hK0 i j
  -- the excess of each quarter: the contacts cannot be carried by the product of the charges
  have hE : ∀ f : Fin H → Fin (H + H), Function.Injective f →
      H * Real.log 2 - ρ ≤ ∑ i : Fin H, excessLeft K u v (f i) := by
    intro f hf
    have h : ∑ i : Fin H, ∑ j ∈ cont (f i), K (f i) j - ρ ≤
        ∑ i : Fin H, excessLeft K u v (f i) :=
      sum_contacts_sub_le_sum_excessLeft (K := fun i j => K (f i) j) (u := fun i => u (f i))
        (v := v) (fun i j => hKle (f i) j) (fun i j => hK0 (f i) j) (fun i => cont (f i))
        (S := Finset.univ) (fun i _ i' _ hne => hdisj (f i) (f i') fun h => hne (hf h)) hρ0
        fun i _ => hρ (f i)
    have hκ' : (H : ℝ) * Real.log 2 ≤ ∑ i : Fin H, ∑ j ∈ cont (f i), K (f i) j := by
      calc (H : ℝ) * Real.log 2 = ∑ _i : Fin H, Real.log 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun i _ => hκ (f i)
    linarith
  have hE1 := hE (Fin.castAdd H) fun a b h => Fin.ext (by
    have h' := congrArg Fin.val h
    rwa [Fin.coe_castAdd, Fin.coe_castAdd] at h')
  have hE2 := hE (Fin.natAdd H) fun a b h => Fin.ext (by
    have h' := congrArg Fin.val h
    rw [Fin.coe_natAdd, Fin.coe_natAdd] at h'
    omega)
  -- the three numbers
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = Real.eulerMascheroniConstant + Real.log (2 * Real.pi) :=
    ⟨_, rfl⟩
  have hc₀' : (799 / 500 : ℝ) + Real.log 2 < c₀ := by
    rw [hc₀, log_two_pi]
    linarith [l3.1]
  have hA1 : 5 * Real.log 5 - 9 * Real.log 2 - c₀ - Real.log 2 ≤ -(117 / 100) := by
    linarith [l5.2]
  have hA2 : 7 * Real.log 7 - 7 * Real.log 2 - 6 * Real.log 3 - c₀ - Real.log 2 ≤
      -(4 / 5) := by
    linarith [l7.2, l3.1]
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = (12 * Real.log 3 + 10 * Real.log 2 - 5 * Real.log 5 - 7 * Real.log 7) / 2 :=
    ⟨_, rfl⟩
  have hC1 : -(777 / 1000) ≤ C := by
    rw [hC]
    linarith [l3.1, l5.2, l7.2]
  have hC2 : C ≤ 777 / 1000 := by
    rw [hC]
    linarith [l3.2, l5.1, l7.1]
  have h1 := mul_le_mul_of_nonneg_left hA1 hHpos.le
  have h2 := mul_le_mul_of_nonneg_left hA2 hHpos.le
  have ha : H * (5 * Real.log 5 - 9 * Real.log 2 - c₀) - (H * Real.log 2 - ρ) ≤
      -(51 / 50 * H) := by linarith
  have hg : H * (7 * Real.log 7 - 7 * Real.log 2 - 6 * Real.log 3 - c₀) -
      (H * Real.log 2 - ρ) ≤ -(13 / 20 * H) := by linarith
  refine ⟨H * (5 * Real.log 5 - 9 * Real.log 2 - c₀) - (H * Real.log 2 - ρ),
    H * (7 * Real.log 7 - 7 * Real.log 2 - 6 * Real.log 3 - c₀) - (H * Real.log 2 - ρ),
    H * C, by linarith, ?_, ?_⟩
  · have hprod : 51 / 50 * H * (13 / 20 * H) ≤
        -(H * (5 * Real.log 5 - 9 * Real.log 2 - c₀) - (H * Real.log 2 - ρ)) *
          -(H * (7 * Real.log 7 - 7 * Real.log 2 - 6 * Real.log 3 - c₀) -
            (H * Real.log 2 - ρ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    have hCsq : C ^ 2 ≤ (777 / 1000) ^ 2 := sq_le_sq' hC1 hC2
    have hHC : (H * C) ^ 2 ≤ (H : ℝ) ^ 2 * (777 / 1000) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hCsq (by positivity)
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    linarith
  · intro s t
    -- the vector of the plane is the step function with the values `s`, `t`
    have hx : (fun i : Fin (H + H) =>
        s * (if (i : ℕ) < H then (1 : ℝ) else 0) + t * (if (i : ℕ) < H then (0 : ℝ) else 1)) =
          fun i => if (i : ℕ) < H then s else t := by
      funext i
      split_ifs <;> ring
    have hN : bilin (neutralWindow Q (H + H) (H + H))
        (fun i : Fin (H + H) => if (i : ℕ) < H then s else t)
        (fun i : Fin (H + H) => if (i : ℕ) < H then s else t) =
        (∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (H + H + j) (H + H + l)) * s ^ 2 +
          2 * (∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (H + H + j) (H + H + (H + l))) *
            s * t +
          (∑ j ∈ range H, ∑ l ∈ range H,
            neutralBlock Q (H + H + (H + j)) (H + H + (H + l))) * t ^ 2 :=
      (sum_fin_windowMatrix_coe (neutralBlock Q) (H + H) (H + H)
        (fun n => if n < H then s else t)).trans
        (sum_two_steps (fun j l => neutralBlock Q (H + H + j) (H + H + l))
          (fun j l => neutralBlock_comm Q _ _) H s t)
    have hD : ∑ i : Fin (H + H), excessLeft K u v i *
        (if (i : ℕ) < H then s else t) ^ 2 =
        (∑ i : Fin H, excessLeft K u v (Fin.castAdd H i)) * s ^ 2 +
          (∑ i : Fin H, excessLeft K u v (Fin.natAdd H i)) * t ^ 2 := by
      rw [Fin.sum_univ_add, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_pos (show ((Fin.castAdd H i : Fin (H + H)) : ℕ) < H by
          rw [Fin.coe_castAdd]
          exact i.2)]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_neg (show ¬((Fin.natAdd H i : Fin (H + H)) : ℕ) < H by
          rw [Fin.coe_natAdd]
          omega)]
    rw [hx, bilin_sub_diagonal]
    show bilin (neutralWindow Q (H + H) (H + H))
        (fun i : Fin (H + H) => if (i : ℕ) < H then s else t)
        (fun i : Fin (H + H) => if (i : ℕ) < H then s else t) -
        ∑ i : Fin (H + H), excessLeft K u v i * (if (i : ℕ) < H then s else t) ^ 2 ≤ _
    rw [hN, hD, sum_neutralBlock_lower_quarter Q hH1, sum_neutralBlock_upper_quarter Q hH1,
      sum_neutralBlock_cross_quarters Q hH1, ← hc₀, ← hC]
    have hs := mul_le_mul_of_nonneg_right hE1 (sq_nonneg s)
    have ht := mul_le_mul_of_nonneg_right hE2 (sq_nonneg t)
    linarith

/-! ### The halves of the window `(2H, 8H]` -/

/-- **The lowered lower half has two negative squares.** For `H ≥ 64` and every pair of
charges below the couplings of `(2H, 4H]` and `(4H, 8H]`, the neutral part of `(2H, 4H]` with
the potential lowered by the excess of the couplings over the product of the charges has at
least two negative squares. -/
theorem two_le_hermNegIndex_lowered_lower_half {H Q : ℕ} (hH : 64 ≤ H) (hQ : 2 ≤ Q) :
    ∀ (u : Fin (2 * H) → ℝ) (v : Fin (4 * H) → ℝ),
      (∀ i j, u i * v j ≤ blockWeight Q (2 * H + i) (2 * H + 2 * H + j)) →
      2 ≤ hermNegIndex ((neutralWindow Q (2 * H) (2 * H) - diagonal (excessLeft
        (fun (i : Fin (2 * H)) (j : Fin (4 * H)) =>
          blockWeight Q (2 * H + i) (2 * H + 2 * H + j)) u v)).map (↑) :
            Matrix (Fin (2 * H)) (Fin (2 * H)) ℂ) := by
  rw [two_mul]
  intro u v huv
  obtain ⟨α, γ, c, hα, hdisc, hplane⟩ := lowered_lower_half_plane hH hQ u v huv
  exact two_le_hermNegIndex_of_two_vectors _ _ _ hplane hα hdisc

/-- **The hypothesis of the gluing lemma fails for every pair of charges.** The lowered lower
half is negative on a vector without charge. -/
theorem exists_chargeless_negative_lowered_lower_half {H Q : ℕ} (hH : 64 ≤ H) (hQ : 2 ≤ Q) :
    ∀ (u : Fin (2 * H) → ℝ) (v : Fin (4 * H) → ℝ),
      (∀ i j, u i * v j ≤ blockWeight Q (2 * H + i) (2 * H + 2 * H + j)) →
      ∃ x : Fin (2 * H) → ℝ, chargeOf u x = 0 ∧
        bilin (neutralWindow Q (2 * H) (2 * H) - diagonal (excessLeft
          (fun (i : Fin (2 * H)) (j : Fin (4 * H)) =>
            blockWeight Q (2 * H + i) (2 * H + 2 * H + j)) u v)) x x < 0 := by
  rw [two_mul]
  intro u v huv
  obtain ⟨α, γ, c, hα, hdisc, hplane⟩ := lowered_lower_half_plane hH hQ u v huv
  exact exists_chargeOf_eq_zero_and_bilin_neg _ u _ _ hplane hα hdisc

/-- **The product model of the two halves of a window of ratio four never counts one bound
state.** For `H ≥ 64` and every pair of charges below the couplings, the halves `(2H, 4H]` and
`(4H, 8H]` with potentials lowered by the excess couplings, glued through the product of the
charges, have at least two negative squares. -/
theorem two_le_hermNegIndex_glued_lowered_ratio_four {H Q : ℕ} (hH : 64 ≤ H) (hQ : 2 ≤ Q)
    (u : Fin (2 * H) → ℝ) (v : Fin (4 * H) → ℝ)
    (huv : ∀ i j, u i * v j ≤ blockWeight Q (2 * H + i) (2 * H + 2 * H + j)) :
    2 ≤ hermNegIndex ((glued
      (neutralWindow Q (2 * H) (2 * H) -
        diagonal (excessLeft
          (fun (i : Fin (2 * H)) (j : Fin (4 * H)) =>
            blockWeight Q (2 * H + i) (2 * H + 2 * H + j)) u v))
      (neutralWindow Q (2 * H + 2 * H) (4 * H) -
        diagonal (excessRight
          (fun (i : Fin (2 * H)) (j : Fin (4 * H)) =>
            blockWeight Q (2 * H + i) (2 * H + 2 * H + j)) u v))
      u v).map (↑) : Matrix (Fin (2 * H) ⊕ Fin (4 * H)) (Fin (2 * H) ⊕ Fin (4 * H)) ℂ) :=
  (two_le_hermNegIndex_lowered_lower_half hH hQ u v huv).trans
    (hermNegIndex_le_hermNegIndex_glued _ _ u v)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
