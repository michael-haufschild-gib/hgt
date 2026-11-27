import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedLinearCharacterNorm

/-! A nonzero finite sum of linear characters of a finite abelian group
has support of size at least the group order divided by the number of terms. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GreenExists

variable {C : Type} [CommGroup C] [Fintype C]

private theorem norm_linearCharacter (θ : C →* ℂˣ) (x : C) : ‖(θ x : ℂ)‖ = 1 := by
  have h : (θ x : ℂ) ^ Fintype.card C = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

/-- Unnormalized orthogonality for two linear characters. -/
theorem sum_linearCharacter_mul_inv (θ η : C →* ℂˣ) :
    ∑ x : C, (θ x : ℂ) * (η x⁻¹ : ℂ) = if θ = η then (Fintype.card C : ℂ) else 0 := by
  split_ifs with h
  · subst η
    simp only [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · let φ : C →* ℂ := (Units.coeHom ℂ).comp (θ * η⁻¹)
    have hφ : φ ≠ 1 := by
      intro e
      apply h
      apply MonoidHom.ext
      intro x
      have hx : θ x * (η x)⁻¹ = 1 := Units.ext (DFunLike.congr_fun e x)
      exact mul_inv_eq_one.mp hx
    calc
      _ = ∑ x : C, φ x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [φ]
      _ = 0 := by simp only [sum_hom_units, hφ, if_false, Nat.cast_zero]

private theorem sum_character_coeff (S : Finset (C →* ℂˣ)) (c : (C →* ℂˣ) → ℂ)
    (η : C →* ℂˣ) (hη : η ∈ S) :
    (∑ x : C, (∑ θ ∈ S, c θ * (θ x : ℂ)) * (η x⁻¹ : ℂ)) = (Fintype.card C : ℂ) * c η := by
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_linearCharacter_mul_inv, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' S η, if_pos hη, mul_comm]

/-- The product of the size of the character set and the size of the
nonzero-value set is at least the group order. -/
theorem card_le_characters_mul_support (S : Finset (C →* ℂˣ)) (c : (C →* ℂˣ) → ℂ)
    (hne : ∃ x : C, (∑ θ ∈ S, c θ * (θ x : ℂ)) ≠ 0) :
    Fintype.card C ≤ S.card *
      (Finset.univ.filter fun x : C => (∑ θ ∈ S, c θ * (θ x : ℂ)) ≠ 0).card := by
  obtain ⟨y, hy⟩ := hne
  let f (x : C) : ℂ := ∑ θ ∈ S, c θ * (θ x : ℂ)
  let T := Finset.univ.filter fun x : C => f x ≠ 0
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ (fun x : C => ‖f x‖)
    ⟨y, Finset.mem_univ _⟩
  have hpos : 0 < ‖f x‖ := (norm_pos_iff.mpr hy).trans_le (hx y (Finset.mem_univ y))
  have hinv (η : C →* ℂˣ) (hη : η ∈ S) :
      (Fintype.card C : ℂ) * c η = ∑ z ∈ T, f z * (η z⁻¹ : ℂ) := by
    have hsum : (∑ z ∈ T, f z * (η z⁻¹ : ℂ)) = ∑ z : C, f z * (η z⁻¹ : ℂ) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z _ hz
      have hzero : f z = 0 := by simpa [T] using hz
      rw [hzero, zero_mul]
    rw [hsum]
    exact (sum_character_coeff S c η hη).symm
  have hc (η : C →* ℂˣ) (hη : η ∈ S) :
      (Fintype.card C : ℝ) * ‖c η‖ ≤ (T.card : ℝ) * ‖f x‖ := by
    rw [← Complex.norm_natCast, ← norm_mul, hinv η hη]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
    rw [norm_mul, norm_linearCharacter, mul_one]
    exact hx z (Finset.mem_univ z)
  have hf : ‖f x‖ ≤ ∑ η ∈ S, ‖c η‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun η _ => ?_))
    rw [norm_mul, norm_linearCharacter, mul_one]
  have hprod : (Fintype.card C : ℝ) * ‖f x‖ ≤ ((S.card : ℝ) * T.card) * ‖f x‖ := by
    calc
      _ ≤ (Fintype.card C : ℝ) * ∑ η ∈ S, ‖c η‖ :=
        mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _)
      _ = ∑ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ := Finset.mul_sum _ _ _
      _ ≤ S.card • ((T.card : ℝ) * ‖f x‖) := Finset.sum_le_card_nsmul _ _ _ hc
      _ = _ := by rw [nsmul_eq_mul, mul_assoc]
  exact_mod_cast le_of_mul_le_mul_right hprod hpos

/-- Agreement of two d-term character sums outside a set smaller than
one part in 2d forces their character multisets to have a common term. -/
theorem exists_matching_character (d : ℕ) (hd : 0 < d) (A B : ℕ → C →* ℂˣ)
    (E : Finset C) (hE : 2 * d * E.card < Fintype.card C)
    (he : ∀ x ∉ E, (∑ i ∈ Finset.range d, (A i x : ℂ)) =
      ∑ i ∈ Finset.range d, (B i x : ℂ)) :
    ∃ i < d, A i = B 0 := by
  let R := Finset.range d
  let S := R.image A ∪ R.image B
  let count (D : ℕ → C →* ℂˣ) (θ : C →* ℂˣ) := (R.filter fun i => D i = θ).card
  let c (θ : C →* ℂˣ) : ℂ := (count A θ : ℂ) - (count B θ : ℂ)
  have hgroup (D : ℕ → C →* ℂˣ) (hD : ∀ i ∈ R, D i ∈ S) (x : C) :
      ∑ θ ∈ S, (count D θ : ℂ) * (θ x : ℂ) = ∑ i ∈ R, (D i x : ℂ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hD]
    refine Finset.sum_congr rfl fun θ _ => ?_
    have hconst : ∀ i ∈ R.filter (fun i => D i = θ), (D i x : ℂ) = (θ x : ℂ) :=
      fun i hi => congrArg (fun χ : C →* ℂˣ => (χ x : ℂ)) (Finset.mem_filter.mp hi).2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hsum (x : C) : (∑ θ ∈ S, c θ * (θ x : ℂ)) =
      (∑ i ∈ R, (A i x : ℂ)) - ∑ i ∈ R, (B i x : ℂ) := by
    simp only [c, sub_mul, Finset.sum_sub_distrib]
    rw [hgroup A (fun i hi => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)) x,
      hgroup B (fun i hi => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)) x]
  have hs : S.card ≤ 2 * d := by
    calc
      S.card ≤ (R.image A).card + (R.image B).card := Finset.card_union_le _ _
      _ ≤ R.card + R.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * d := by simp [R, two_mul]
  have hz (x : C) : ∑ θ ∈ S, c θ * (θ x : ℂ) = 0 := by
    by_contra hne
    have ht : (Finset.univ.filter fun z : C => ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0).card ≤ E.card := by
      apply Finset.card_le_card
      intro z hz
      by_contra hn
      exact (Finset.mem_filter.mp hz).2 (by rw [hsum, he z hn, sub_self])
    exact (not_le_of_gt hE) ((card_le_characters_mul_support S c ⟨x, hne⟩).trans (Nat.mul_le_mul hs ht))
  have hb : B 0 ∈ S := Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hd))
  have hzero : (Fintype.card C : ℂ) * c (B 0) = 0 := by
    rw [← sum_character_coeff S c (B 0) hb]
    simp only [hz, zero_mul, Finset.sum_const_zero]
  have hc : count A (B 0) = count B (B 0) := by
    have h0 := (mul_eq_zero.mp hzero).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    exact Nat.cast_inj.mp (sub_eq_zero.mp h0)
  have hp : 0 < count B (B 0) := Finset.card_pos.mpr
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd, rfl⟩⟩
  rw [← hc] at hp
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
  exact ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

end GlobalTheory.GreenExists
