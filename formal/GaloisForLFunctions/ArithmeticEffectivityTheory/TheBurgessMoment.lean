import GaloisForLFunctions.RHTower.HyperellipticCharacterSums

/-!
# The Burgess moment: short character sums counted on curves of genus `< r`

For a finite field `F` of odd characteristic, `q = |F|`, the quadratic character `χ` and a finite
set `B ⊆ F`, let `T(x) = Σ_{b ∈ B} χ(x + b)`. Then (`sum_pow_two_mul_le`)

  `Σ_{x ∈ F} T(x)^{2r} ≤ r^{2r} |B|^r q + 6r |B|^{2r} √q`.

Expanding the power, each `2r`-tuple `f` of shifts contributes the complete sum
`Σ_x χ(Π_i (x + f_i))` over the curve `y² = Π_i (x + f_i)`. If some shift occurs an odd number of
times, the Weil bound with multiplicities (`abs_sum_quadraticChar_multiset_le`) makes it `≤ 6r√q`;
otherwise `f` takes at most `r` values (`card_image_le_of_even`), and there are at most
`C(|B|, r) r^{2r}` such tuples (`card_evenTuples_le`). This is the counting input of Burgess's
method: square-root cancellation on a family of curves of growing genus, traded for length.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open RHTower.Hyperelliptic

attribute [local instance] Classical.propDecidable

/-! ### Tuples in which every value occurs an even number of times -/

section Tuples

variable {α : Type*} {n : ℕ}

/-- Every value of `f` is taken an even number of times. -/
def EvenTuple (f : Fin n → α) : Prop := ∀ c, Even (univ.filter fun i => f i = c).card

/-- An even tuple of length `n` takes at most `n / 2` values. -/
theorem card_image_le_of_even {f : Fin n → α} (hf : EvenTuple f) :
    2 * (univ.image f).card ≤ n := by
  have hsum : ∑ c ∈ univ.image f, (univ.filter fun i => f i = c).card = n := by
    rw [← Finset.card_eq_sum_card_image f univ, card_univ, Fintype.card_fin]
  have hge : ∀ c ∈ univ.image f, 2 ≤ (univ.filter fun i => f i = c).card := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
    have hpos : 0 < (univ.filter fun j => f j = f i).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨mem_univ i, rfl⟩⟩
    obtain ⟨k, hk⟩ := hf (f i)
    omega
  calc 2 * (univ.image f).card = ∑ _c ∈ univ.image f, 2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ c ∈ univ.image f, (univ.filter fun i => f i = c).card := Finset.sum_le_sum hge
    _ = n := hsum

/-- **Counting even tuples**: at most `C(|B|, r) r^{2r} ≤ r^{2r} |B|^r` tuples
`f : Fin (2r) → B` take every value an even number of times. -/
theorem card_evenTuples_le (B : Finset α) (r : ℕ) :
    ((Fintype.piFinset fun _ : Fin (2 * r) => B).filter EvenTuple).card ≤ r ^ (2 * r) * B.card ^ r := by
  rcases le_or_gt r B.card with hrB | hBr
  · have hsub : (Fintype.piFinset fun _ : Fin (2 * r) => B).filter EvenTuple ⊆
        (B.powersetCard r).biUnion fun T => Fintype.piFinset fun _ : Fin (2 * r) => T := by
      intro f hf
      obtain ⟨hfB, hfe⟩ := Finset.mem_filter.mp hf
      have himB : univ.image f ⊆ B := by
        intro c hc
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
        exact Fintype.mem_piFinset.mp hfB i
      have hcard : (univ.image f).card ≤ r := by
        have := card_image_le_of_even hfe; omega
      obtain ⟨T, hfT, hTB, hTr⟩ := Finset.exists_subsuperset_card_eq himB hcard hrB
      refine Finset.mem_biUnion.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨hTB, hTr⟩, ?_⟩
      exact Fintype.mem_piFinset.mpr fun i => hfT (Finset.mem_image_of_mem f (mem_univ i))
    calc _ ≤ ((B.powersetCard r).biUnion fun T => Fintype.piFinset fun _ : Fin (2 * r) => T).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ T ∈ B.powersetCard r, (Fintype.piFinset fun _ : Fin (2 * r) => T).card :=
          Finset.card_biUnion_le
      _ = ∑ T ∈ B.powersetCard r, r ^ (2 * r) := by
          refine Finset.sum_congr rfl fun T hT => ?_
          rw [Fintype.card_piFinset, Finset.prod_const, card_univ, Fintype.card_fin,
            (Finset.mem_powersetCard.mp hT).2]
      _ = B.card.choose r * r ^ (2 * r) := by
          rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
      _ ≤ r ^ (2 * r) * B.card ^ r := by
          rw [mul_comm]
          exact Nat.mul_le_mul_left _ (Nat.choose_le_pow _ _)
  · calc _ ≤ (Fintype.piFinset fun _ : Fin (2 * r) => B).card := Finset.card_filter_le _ _
      _ = B.card ^ (2 * r) := by
          rw [Fintype.card_piFinset, Finset.prod_const, card_univ, Fintype.card_fin]
      _ = B.card ^ r * B.card ^ r := by rw [two_mul, pow_add]
      _ ≤ r ^ (2 * r) * B.card ^ r := by
          refine Nat.mul_le_mul_right (B.card ^ r) ?_
          calc B.card ^ r ≤ r ^ r := Nat.pow_le_pow_left hBr.le r
            _ ≤ r ^ (2 * r) := Nat.pow_le_pow_right (by omega) (by omega)

end Tuples

/-! ### The moment -/

variable {F : Type*} [Field F] [Fintype F]

/-- The real quadratic character. -/
noncomputable def chiR (y : F) : ℝ := ((quadraticChar F y : ℤ) : ℝ)

theorem chiR_mul (y z : F) : chiR (y * z) = chiR y * chiR z := by
  simp [chiR, map_mul]

theorem chiR_eq_neg_one {c : F} (hc : ¬ IsSquare c) : chiR c = -1 := by
  simp [chiR, quadraticChar_neg_one_iff_not_isSquare.mpr hc]

theorem chiR_eq_one {c : F} (hc0 : c ≠ 0) (hc : IsSquare c) : chiR c = 1 := by
  simp [chiR, (quadraticChar_one_iff_isSquare hc0).mpr hc]

theorem chiR_one : chiR (1 : F) = 1 := chiR_eq_one one_ne_zero ⟨1, by ring⟩

theorem abs_chiR_le (y : F) : |chiR y| ≤ 1 := by
  rcases quadraticChar_trichotomy F y with h | h | h <;> simp [chiR, h]

theorem chiR_prod {ι : Type*} (s : Finset ι) (g : ι → F) :
    chiR (∏ i ∈ s, g i) = ∏ i ∈ s, chiR (g i) := by
  simp [chiR, map_prod]

/-- `T(x) = Σ_{b ∈ B} χ(x + b)`. -/
noncomputable def shiftSum (B : Finset F) (x : F) : ℝ := ∑ b ∈ B, chiR (x + b)

/-- The complete sum attached to a tuple of shifts. -/
theorem abs_sum_chiR_tuple_le (hF : ringChar F ≠ 2) {n : ℕ} (f : Fin n → F)
    (hf : ¬ EvenTuple f) :
    |∑ x : F, ∏ i, chiR (x + f i)| ≤ 3 * n * Real.sqrt (Fintype.card F) := by
  set s : Multiset F := univ.val.map fun i => -f i
  have hcount : ∀ c, s.count c = (univ.filter fun i => f i = -c).card := by
    intro c
    rw [Multiset.count_map, Finset.card, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun i _ => by
      constructor
      · intro h; rw [h, neg_neg]
      · intro h; rw [h, neg_neg]
  obtain ⟨c, hc⟩ : ∃ c, Odd (s.count c) := by
    unfold EvenTuple at hf
    push Not at hf
    obtain ⟨c, hc⟩ := hf
    exact ⟨-c, by rw [hcount, neg_neg]; exact Nat.not_even_iff_odd.mp hc⟩
  have hW := abs_sum_quadraticChar_multiset_le hF ⟨c, hc⟩
  have hcard : Multiset.card s = n := by simp [s]
  have hprod : ∀ x : F, (s.map (x - ·)).prod = ∏ i, (x + f i) := by
    intro x
    simp only [s, Multiset.map_map, Function.comp_def, sub_neg_eq_add]
    rfl
  have hreal : ∑ x : F, ∏ i, chiR (x + f i) =
      ((∑ x : F, quadraticChar F (s.map (x - ·)).prod : ℤ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hprod, ← chiR_prod]
    rfl
  rw [hreal]
  have : ‖((∑ x : F, quadraticChar F (s.map (x - ·)).prod : ℤ) : ℂ)‖ =
      |((∑ x : F, quadraticChar F (s.map (x - ·)).prod : ℤ) : ℝ)| := by
    rw [show ((∑ x : F, quadraticChar F (s.map (x - ·)).prod : ℤ) : ℂ) =
      (((∑ x : F, quadraticChar F (s.map (x - ·)).prod : ℤ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← this]
  rw [hcard] at hW
  push_cast
  exact hW

/-- **The Burgess moment**: `Σ_x T(x)^{2r} ≤ r^{2r} |B|^r q + 6r |B|^{2r} √q`. -/
theorem sum_pow_two_mul_le (hF : ringChar F ≠ 2) (B : Finset F) (r : ℕ) :
    ∑ x : F, shiftSum B x ^ (2 * r) ≤
      r ^ (2 * r) * B.card ^ r * Fintype.card F +
        6 * r * B.card ^ (2 * r) * Real.sqrt (Fintype.card F) := by
  set P := Fintype.piFinset fun _ : Fin (2 * r) => B
  have hexp : ∀ x : F, shiftSum B x ^ (2 * r) = ∑ f ∈ P, ∏ i, chiR (x + f i) := by
    intro x
    rw [shiftSum, ← Fin.prod_const, Finset.prod_univ_sum]
  simp_rw [hexp]
  rw [Finset.sum_comm, ← Finset.sum_filter_add_sum_filter_not P EvenTuple]
  have hq : (0 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  have heven : ∑ f ∈ P.filter EvenTuple, ∑ x : F, ∏ i, chiR (x + f i) ≤
      (r ^ (2 * r) * B.card ^ r : ℕ) * (Fintype.card F : ℝ) := by
    calc _ ≤ ∑ _f ∈ P.filter EvenTuple, (Fintype.card F : ℝ) := by
          refine Finset.sum_le_sum fun f _ => ?_
          calc ∑ x : F, ∏ i, chiR (x + f i) ≤ ∑ _x : F, (1 : ℝ) := by
                refine Finset.sum_le_sum fun x _ => ?_
                rw [← chiR_prod]
                exact (le_abs_self _).trans (abs_chiR_le _)
            _ = Fintype.card F := by simp
      _ = ((P.filter EvenTuple).card : ℝ) * Fintype.card F := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
          exact_mod_cast card_evenTuples_le B r
  have hodd : ∑ f ∈ P.filter (¬ EvenTuple ·), ∑ x : F, ∏ i, chiR (x + f i) ≤
      (B.card ^ (2 * r) : ℕ) * (6 * r * Real.sqrt (Fintype.card F)) := by
    calc _ ≤ ∑ _f ∈ P.filter (¬ EvenTuple ·), 6 * r * Real.sqrt (Fintype.card F) := by
          refine Finset.sum_le_sum fun f hf => ?_
          have h := abs_sum_chiR_tuple_le hF f (Finset.mem_filter.mp hf).2
          push_cast at h
          linarith [le_abs_self (∑ x : F, ∏ i, chiR (x + f i))]
      _ = ((P.filter (¬ EvenTuple ·)).card : ℝ) * (6 * r * Real.sqrt (Fintype.card F)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : (P.filter (¬ EvenTuple ·)).card ≤ B.card ^ (2 * r) := by
            refine (Finset.card_filter_le _ _).trans_eq ?_
            rw [Fintype.card_piFinset, Finset.prod_const, card_univ, Fintype.card_fin]
          exact_mod_cast this
  calc _ ≤ (r ^ (2 * r) * B.card ^ r : ℕ) * (Fintype.card F : ℝ) +
        (B.card ^ (2 * r) : ℕ) * (6 * r * Real.sqrt (Fintype.card F)) := add_le_add heven hodd
    _ = _ := by push_cast; ring

end GaloisForLFunctions.ArithmeticEffectivityTheory
