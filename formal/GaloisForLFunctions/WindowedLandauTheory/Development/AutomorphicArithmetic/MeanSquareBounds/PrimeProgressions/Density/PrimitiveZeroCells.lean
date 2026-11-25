import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.MollifierZeroDetector

/-! Integer-height cells meeting the near-one zero set of primitive Dirichlet characters. -/

open Complex Finset

namespace QH.PrimeProgressions

theorem primitive_zero_re_lt_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {z : ℂ} (hz : χ.LFunction z = 0) : z.re < 1 := by
  by_contra h
  have hge := le_of_not_gt h
  by_cases h₁ : χ = 1
  · have hq : q = 1 := by
      have hp := hχ
      rw [DirichletCharacter.isPrimitive_def, h₁, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    subst q
    rw [DirichletCharacter.LFunction_modOne_eq] at hz
    exact riemannZeta_ne_zero_of_one_le_re hge hz
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl h₁) hge hz

/-- The character and the integer-height cell of a zero. -/
noncomputable def primitiveZeroCell (p : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ) :
    (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℤ := (p.1, ⌊p.2.im⌋)

private theorem one_le_abs_of_same_parity {x y : ℝ}
    (hne : ⌊x⌋ ≠ ⌊y⌋) (hpar : ⌊x⌋ % 2 = ⌊y⌋ % 2) : 1 ≤ |x - y| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hgap : (⌊x⌋ : ℝ) + 2 ≤ ⌊y⌋ := by exact_mod_cast (show ⌊x⌋ + 2 ≤ ⌊y⌋ by omega)
    exact le_abs.mpr (Or.inr (by linarith only [hgap, Int.lt_floor_add_one x, Int.floor_le y]))
  · have hgap : (⌊y⌋ : ℝ) + 2 ≤ ⌊x⌋ := by exact_mod_cast (show ⌊y⌋ + 2 ≤ ⌊x⌋ by omega)
    exact le_abs.mpr (Or.inl (by linarith only [hgap, Int.lt_floor_add_one y, Int.floor_le x]))

private theorem exists_image_representatives {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Nonempty α] (U : Finset α) (f : α → β) :
    ∃ R ⊆ U, R.card = (U.image f).card ∧ Set.InjOn f R := by
  let g := Function.invFunOn f (↑U : Set α)
  have hright (y : β) (hy : y ∈ U.image f) : f (g y) = y := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact Function.invFunOn_eq ⟨x, hx, rfl⟩
  refine ⟨(U.image f).image g, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    exact Function.invFunOn_mem ⟨z, hz, rfl⟩
  · exact card_image_of_injOn fun y hy z hz he => (hright y hy).symm.trans
      ((congrArg f he).trans (hright z hz))
  · intro x hx x' hx' he
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_image.mp hx'
    exact congrArg g ((hright y hy).symm.trans (he.trans (hright y' hy')))

open Classical in
/-- At most O(Q^(1/8)) character-height cells meet the near-one zero set. -/
theorem primitive_zero_cells_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
      ∀ U : Finset ((Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ),
      (∀ p ∈ U, ((p.1.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.1.2.IsPrimitive ∧
        p.1.2.LFunction p.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.re ∧ |p.2.im| ≤ Q) →
      ((U.image primitiveZeroCell).card : ℝ) ≤ C * Q ^ ((1 : ℝ) / 8) := by
  classical
  obtain ⟨Q₀, hzet⟩ := mollifier_detects_zeta_zero
  obtain ⟨C, hC, hbound⟩ := spaced_mollifier_detection_bound
  let K := max Q₀ 1024
  refine ⟨(2 * C + 5) * ((K : ℝ) + 2), by positivity, ?_⟩
  intro Q hQ U hU
  let V := max K ⌈Q⌉₊
  let B := (V : ℝ) ^ ((1 : ℝ) / 20)
  have hV : 1024 ≤ V := (le_max_right Q₀ 1024).trans (le_max_left _ _)
  have hQle : Q ≤ V := (Nat.le_ceil Q).trans (by exact_mod_cast le_max_right K ⌈Q⌉₊)
  have hV₁ : (1 : ℝ) ≤ V := by exact_mod_cast (show 1 ≤ V by omega)
  let S := U.filter (fun p => p.1.1 = 0 ∧ |p.2.im| < B)
  let T := U.filter (fun p => ¬ (p.1.1 = 0 ∧ |p.2.im| < B))
  let T₀ := T.filter (fun p => ⌊p.2.im⌋ % 2 = 0)
  let T₁ := T.filter (fun p => ⌊p.2.im⌋ % 2 = 1)
  letI : Nonempty ((Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ) := ⟨(⟨0, 1⟩, 0)⟩
  have hdetect (p : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ) (hp : p ∈ T) :
      p.1.1 + 1 ≤ V ∧ p.1.2.IsPrimitive ∧ 1 - 1 / 400 ≤ p.2.re ∧ p.2.re ≤ 1 ∧
      |p.2.im| ≤ (V : ℝ) ∧ (1 / 2 : ℝ) ≤ ‖mollifierTail V p.1.2 p.2‖ := by
    obtain ⟨hpU, hnsmall⟩ := mem_filter.mp hp
    obtain ⟨hq, hχ, hz, hre, him⟩ := hU p hpU
    have hqV : p.1.1 + 1 ≤ V := by exact_mod_cast (hq.trans hQle)
    have himV := him.trans hQle
    have hlt := primitive_zero_re_lt_one hχ hz
    refine ⟨hqV, hχ, hre, hlt.le, himV, ?_⟩
    obtain ⟨⟨q, χ⟩, z⟩ := p
    by_cases hq0 : q = 0
    · subst q
      have hh : B ≤ |z.im| := le_of_not_gt fun h => hnsmall ⟨rfl, h⟩
      have hz' : riemannZeta z = 0 := by simpa only [DirichletCharacter.LFunction_modOne_eq] using hz
      exact hzet V ((le_max_left Q₀ 1024).trans (le_max_left K ⌈Q⌉₊)) χ z hre hlt hh himV hz'
    · have hχ' : χ ≠ 1 := by
        intro h
        rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hχ
        change (1 : ℕ) = q + 1 at hχ
        exact hq0 (by omega)
      exact mollifier_detects_character_zero hV hqV χ hχ' hre himV hz
  have hpar (k : ℤ) :
      (((T.filter fun p => ⌊p.2.im⌋ % 2 = k).image primitiveZeroCell).card : ℝ) ≤
      C * (V : ℝ) ^ ((1 : ℝ) / 8) := by
    obtain ⟨R, hR, hcard, hinj⟩ := exists_image_representatives
      (T.filter fun p => ⌊p.2.im⌋ % 2 = k) primitiveZeroCell
    rw [← hcard]
    refine hbound V (by omega) R (fun p hp => hdetect p (mem_filter.mp (hR hp)).1) ?_
    intro p hp p' hp' hχ hne
    have hf : ⌊p.2.im⌋ ≠ ⌊p'.2.im⌋ := fun he => hne (hinj hp hp' (Prod.ext hχ he))
    exact one_le_abs_of_same_parity hf ((mem_filter.mp (hR hp)).2.trans (mem_filter.mp (hR hp')).2.symm)
  have hs : ((S.image primitiveZeroCell).card : ℝ) ≤ 5 * (V : ℝ) ^ ((1 : ℝ) / 8) := by
    let M := ⌈B⌉₊
    let g (j : ℤ) : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℤ := (⟨0, 1⟩, j)
    have hsub : S.image primitiveZeroCell ⊆ (Icc (-(M : ℤ)) M).image g := by
      intro x hx
      obtain ⟨⟨⟨q, χ⟩, z⟩, hz, rfl⟩ := mem_image.mp hx
      obtain ⟨_, hq, hsm⟩ := mem_filter.mp hz
      change q = 0 at hq
      subst q
      haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
      have hχ : χ = 1 := by
        apply MulChar.ext
        intro a
        rw [Subsingleton.elim a 1, Units.val_one, map_one, map_one]
      subst χ
      have h := abs_lt.mp (hsm.trans_le (Nat.le_ceil B))
      refine mem_image.mpr ⟨⌊z.im⌋, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · have hh : (-(M : ℤ) : ℝ) < (⌊z.im⌋ : ℝ) + 1 := by
          push_cast
          linarith only [h.1, Int.lt_floor_add_one z.im]
        have h' : -(M : ℤ) < ⌊z.im⌋ + 1 := by exact_mod_cast hh
        omega
      · have hh : (⌊z.im⌋ : ℝ) ≤ (M : ℝ) := le_trans (Int.floor_le _) h.2.le
        exact_mod_cast hh
    have hcard : ((S.image primitiveZeroCell).card : ℝ) ≤ 2 * (M : ℝ) + 1 := by
      have hh := (card_le_card hsub).trans card_image_le
      have hI : (Icc (-(M : ℤ)) M).card = 2 * M + 1 := by rw [Int.card_Icc]; omega
      rw [hI] at hh
      exact_mod_cast hh
    have hM := Nat.ceil_lt_add_one (show 0 ≤ B by positivity)
    have hB : B ≤ (V : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow_of_exponent_le hV₁ (by norm_num)
    have h₁ : (1 : ℝ) ≤ (V : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hV₁ (by norm_num)
    linarith only [hcard, hM, hB, h₁]
  have hsub : U.image primitiveZeroCell ⊆
      S.image primitiveZeroCell ∪ (T₀.image primitiveZeroCell ∪ T₁.image primitiveZeroCell) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    by_cases h : p.1.1 = 0 ∧ |p.2.im| < B
    · exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨hp, h⟩))
    have ht : p ∈ T := mem_filter.mpr ⟨hp, h⟩
    by_cases h₀ : ⌊p.2.im⌋ % 2 = 0
    · exact mem_union_right _ (mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨ht, h₀⟩)))
    · exact mem_union_right _ (mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨ht, by omega⟩)))
  have hcard : ((U.image primitiveZeroCell).card : ℝ) ≤
      (S.image primitiveZeroCell).card + ((T₀.image primitiveZeroCell).card + (T₁.image primitiveZeroCell).card) := by
    exact_mod_cast (card_le_card hsub).trans ((card_union_le _ _).trans
      (add_le_add le_rfl (card_union_le _ _)))
  have hVm : (V : ℝ) ≤ ((K : ℝ) + 2) * Q := by
    have h₁ : (V : ℝ) ≤ (K : ℝ) + ⌈Q⌉₊ := by exact_mod_cast
      (max_le (Nat.le_add_right K ⌈Q⌉₊) (Nat.le_add_left ⌈Q⌉₊ K))
    have h₂ := Nat.ceil_lt_add_one (show 0 ≤ Q by linarith only [hQ])
    have h₃ := mul_nonneg (Nat.cast_nonneg (α := ℝ) K) (show 0 ≤ Q - 1 by linarith only [hQ])
    nlinarith only [h₁, h₂, h₃, hQ]
  have hpow : (V : ℝ) ^ ((1 : ℝ) / 8) ≤ ((K : ℝ) + 2) * Q ^ ((1 : ℝ) / 8) := by
    refine (Real.rpow_le_rpow (by positivity) hVm (by norm_num)).trans ?_
    rw [Real.mul_rpow (by positivity) (by linarith only [hQ])]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K])
      (show (1 : ℝ) / 8 ≤ 1 by norm_num)).trans_eq (Real.rpow_one _)
  calc
    _ ≤ (2 * C + 5) * (V : ℝ) ^ ((1 : ℝ) / 8) := by
      have h₀ : ((T₀.image primitiveZeroCell).card : ℝ) ≤ _ := hpar 0
      have h₁ : ((T₁.image primitiveZeroCell).card : ℝ) ≤ _ := hpar 1
      linarith only [hcard, hs, h₀, h₁]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (by ring)

end QH.PrimeProgressions
