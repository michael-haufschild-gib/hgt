import GaloisForLFunctions.HTGeometry.MilnorKTwoBruhatProjection

/-!
# Milnor's rank-four Bruhat transition laws

This file formalizes both halves of Milnor's Lemma 12.7.  Exact Steinberg
upper--Weyl--upper absorption gives the right transition for all three adjacent roots;
diagonal normalization changes `w(1)` to Milnor's `w(-1)`.  Inversion equivariance of the
Bruhat projection then supplies the left transition.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix MilnorDiagonalExtension

variable {F : Type*} [Field F]

noncomputable def fin4SteinbergElementary (g : SteinbergGroup F (Fin 4)) :
    elementaryGroup F (Fin 4) :=
  ⟨steinbergToGL g, ⟨g, rfl⟩⟩

noncomputable def fin4WeylWordMonomial (word : SteinbergWeylWord F (Fin 4)) :
    fieldDetOneMonomialSubgroup (F := F) :=
  ⟨steinbergToGL word.eval,
    ⟨word.perm, word.scale, steinbergWeylWord_matrix word⟩,
    fin4_steinbergToGL_det_one word.eval⟩

theorem fin4_upperSteinberg_matrix_isUpper {t : SteinbergGroup F (Fin 4)}
    (ht : t ∈ upperSteinbergSubgroup (F := F) (Fin 4)) :
    IsUpperUnipotent
      ((steinbergToGL t : (Matrix (Fin 4) (Fin 4) F)ˣ) :
        Matrix (Fin 4) (Fin 4) F) := by
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at ht
  obtain ⟨a, b, c, d, e, f, rfl⟩ := ht
  exact fin4_upper_tetrahedron_matrix_isUpper a b c d e f

theorem fin4BruhatProjection_upper_word_upper
    (t₁ t₂ : SteinbergGroup F (Fin 4)) (word : SteinbergWeylWord F (Fin 4))
    (ht₁ : t₁ ∈ upperSteinbergSubgroup (F := F) (Fin 4))
    (ht₂ : t₂ ∈ upperSteinbergSubgroup (F := F) (Fin 4)) :
    fin4BruhatProjection (fin4SteinbergElementary (t₁ * word.eval * t₂)) =
      fin4WeylWordMonomial word := by
  let x : Fin4BruhatFactorization
      (fin4SteinbergElementary (t₁ * word.eval * t₂)) :=
    { left := (steinbergToGL t₁ : (Matrix (Fin 4) (Fin 4) F)ˣ)
      middle := fin4WeylWordMonomial word
      right := (steinbergToGL t₂ : (Matrix (Fin 4) (Fin 4) F)ˣ)
      left_upper := fin4_upperSteinberg_matrix_isUpper ht₁
      right_upper := fin4_upperSteinberg_matrix_isUpper ht₂
      eq_factor := by
        change ((steinbergToGL (t₁ * word.eval * t₂) :
              (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
          ((steinbergToGL t₁ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F) *
            ((steinbergToGL word.eval : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F) *
            ((steinbergToGL t₂ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F)
        rw [map_mul, map_mul, Units.val_mul, Units.val_mul] }
  exact fin4BruhatProjection_eq_middle x

theorem fin4BruhatProjection_mul_left_upper
    (t : SteinbergGroup F (Fin 4))
    (ht : t ∈ upperSteinbergSubgroup (F := F) (Fin 4))
    (A : elementaryGroup F (Fin 4)) :
    fin4BruhatProjection (fin4SteinbergElementary t * A) =
      fin4BruhatProjection A := by
  let x := fin4BruhatFactorization A
  let y : Fin4BruhatFactorization (fin4SteinbergElementary t * A) :=
    { left := ((steinbergToGL t : (Matrix (Fin 4) (Fin 4) F)ˣ) :
          Matrix (Fin 4) (Fin 4) F) * x.left
      middle := x.middle
      right := x.right
      left_upper := IsUpperUnipotent.mul (fin4_upperSteinberg_matrix_isUpper ht) x.left_upper
      right_upper := x.right_upper
      eq_factor := by
        change ((steinbergToGL t : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F) *
            (A.1 : Matrix (Fin 4) (Fin 4) F) =
          (((steinbergToGL t : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F) * x.left) *
            (x.middle.1 : Matrix (Fin 4) (Fin 4) F) * x.right
        rw [x.eq_factor]
        simp only [Matrix.mul_assoc] }
  exact fin4BruhatProjection_eq_middle y

theorem fin4BruhatProjection_mul_right_upper
    (A : elementaryGroup F (Fin 4))
    (t : SteinbergGroup F (Fin 4))
    (ht : t ∈ upperSteinbergSubgroup (F := F) (Fin 4)) :
    fin4BruhatProjection (A * fin4SteinbergElementary t) =
      fin4BruhatProjection A := by
  let x := fin4BruhatFactorization A
  let y : Fin4BruhatFactorization (A * fin4SteinbergElementary t) :=
    { left := x.left
      middle := x.middle
      right := x.right *
        ((steinbergToGL t : (Matrix (Fin 4) (Fin 4) F)ˣ) :
          Matrix (Fin 4) (Fin 4) F)
      left_upper := x.left_upper
      right_upper := IsUpperUnipotent.mul x.right_upper
        (fin4_upperSteinberg_matrix_isUpper ht)
      eq_factor := by
        change (A.1 : Matrix (Fin 4) (Fin 4) F) *
            ((steinbergToGL t : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F) =
          x.left * (x.middle.1 : Matrix (Fin 4) (Fin 4) F) *
            (x.right * ((steinbergToGL t : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F))
        rw [x.eq_factor]
        simp only [Matrix.mul_assoc] }
  exact fin4BruhatProjection_eq_middle y

/-- Exact local upper--Weyl--upper alternative behind Milnor Lemma 12.7. -/
theorem weylWord_upper_root_simpleWeyl_exact
    (word : SteinbergWeylWord F (Fin 4)) {i j : Fin 4}
    (hij : i ≠ j) (hupper : i < j) (a : F) :
    (∃ t₁ t₂ : SteinbergGroup F (Fin 4),
        t₁ ∈ upperSteinbergSubgroup (F := F) (Fin 4) ∧
        t₂ ∈ upperSteinbergSubgroup (F := F) (Fin 4) ∧
        word.eval * steinbergX hij a * steinbergWeyl hij 1 =
          t₁ * (SteinbergWeylWord.snoc word i j hij 1).eval * t₂) ∨
      ∃ b : Fˣ, (b : F) = a ∧
        ∃ t₁ t₂ : SteinbergGroup F (Fin 4),
          t₁ ∈ upperSteinbergSubgroup (F := F) (Fin 4) ∧
          t₂ ∈ upperSteinbergSubgroup (F := F) (Fin 4) ∧
          word.eval * steinbergX hij a * steinbergWeyl hij 1 =
            t₁ * (SteinbergWeylWord.snoc
              (SteinbergWeylWord.snoc word i j hij b) i j hij 1).eval * t₂ := by
  have hspare : ∀ p q : Fin 4, p ≠ q → ∃ m : Fin 4, p ≠ m ∧ q ≠ m := by
    intro p q _
    obtain ⟨m, hmp, hmq⟩ := exists_third_index (by decide) p q
    exact ⟨m, hmp.symm, hmq.symm⟩
  rcases lt_or_gt_of_ne (word.perm.injective.ne_iff.mpr hij) with hforward | hbackward
  · left
    let next : SteinbergWeylWord F (Fin 4) := .snoc word i j hij 1
    let t₁ := word.eval * steinbergX hij a * word.eval⁻¹
    have ht₁ : t₁ ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
      dsimp only [t₁]
      exact weylWord_conj_root_mem_upper word hspare hij a hforward
    have heq : word.eval * steinbergX hij a * steinbergWeyl hij 1 =
        t₁ * next.eval * 1 := by
      dsimp only [t₁, next, SteinbergWeylWord.eval]
      group
    exact ⟨t₁, 1, ht₁, Subgroup.one_mem _, heq⟩
  · by_cases ha : a = 0
    · left
      let next : SteinbergWeylWord F (Fin 4) := .snoc word i j hij 1
      have heq : word.eval * steinbergX hij a * steinbergWeyl hij 1 =
          1 * next.eval * 1 := by
        simp [ha, next, SteinbergWeylWord.eval, steinbergX_zero]
      exact ⟨1, 1, Subgroup.one_mem _, Subgroup.one_mem _, heq⟩
    · let b : Fˣ := Units.mk0 a ha
      refine Or.inr ⟨b, by simp [b], ?_⟩
      let wp : SteinbergWeylWord F (Fin 4) := .snoc word i j hij b
      let next : SteinbergWeylWord F (Fin 4) := .snoc wp i j hij 1
      let t₁ := wp.eval * steinbergX hij (-(b : F)) * wp.eval⁻¹
      let t₂ := steinbergX hij (-((b⁻¹ : Fˣ) : F))
      have hwp_eval : wp.eval = word.eval * steinbergWeyl hij b := by rfl
      have hwp_pos : wp.perm i < wp.perm j := by
        simpa [wp, SteinbergWeylWord.perm, Equiv.trans_apply] using hbackward
      have ht₁ : t₁ ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
        dsimp only [t₁]
        exact weylWord_conj_root_mem_upper wp hspare hij (-(b : F)) hwp_pos
      have ht₂ : t₂ ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
        exact Subgroup.subset_closure
          ⟨i, j, hij, -((b⁻¹ : Fˣ) : F), hupper, rfl⟩
      obtain ⟨m, him, hjm⟩ := hspare i j hij
      have hmove : steinbergX (Ne.symm hij) ((b⁻¹ : Fˣ) : F) * steinbergWeyl hij 1
          = steinbergWeyl hij 1 * steinbergX hij (-((b⁻¹ : Fˣ) : F)) := by
        simpa using steinbergTranspose_mul_weyl hij him hjm
          (1 : Fˣ) ((b⁻¹ : Fˣ) : F)
      have heq : word.eval * steinbergX hij a * steinbergWeyl hij 1 =
          t₁ * next.eval * t₂ := by
        rw [← show (b : F) = a by simp [b], steinbergX_eq_weyl_upper_transpose hij b]
        dsimp only [t₁, t₂, next, SteinbergWeylWord.eval]
        calc
          word.eval * (steinbergWeyl hij b * steinbergX hij (-(b : F)) *
                steinbergX (Ne.symm hij) ((b⁻¹ : Fˣ) : F)) *
              steinbergWeyl hij 1 =
              word.eval * steinbergWeyl hij b * steinbergX hij (-(b : F)) *
                ((word.eval * steinbergWeyl hij b)⁻¹) *
                ((word.eval * steinbergWeyl hij b) * steinbergWeyl hij 1) *
                steinbergX hij (-((b⁻¹ : Fˣ) : F)) := by
              rw [show word.eval * (steinbergWeyl hij b * steinbergX hij (-(b : F)) *
                    steinbergX (Ne.symm hij) ((b⁻¹ : Fˣ) : F)) *
                    steinbergWeyl hij 1 =
                  word.eval * steinbergWeyl hij b * steinbergX hij (-(b : F)) *
                    (steinbergX (Ne.symm hij) ((b⁻¹ : Fˣ) : F) *
                      steinbergWeyl hij 1) by group, hmove]
              group
          _ = (wp.eval * steinbergX hij (-(b : F)) * wp.eval⁻¹) *
                (wp.eval * steinbergWeyl hij 1) *
                steinbergX hij (-((b⁻¹ : Fˣ) : F)) := by rw [← hwp_eval]
      exact ⟨t₁, t₂, ht₁, ht₂, heq⟩

theorem fin4BruhatProjection_word_root_simpleWeyl
    (word : SteinbergWeylWord F (Fin 4)) {i j : Fin 4}
    (hij : i ≠ j) (hupper : i < j) (a : F) :
    fin4BruhatProjection
        (fin4SteinbergElementary
          (word.eval * steinbergX hij a * steinbergWeyl hij 1)) =
        fin4WeylWordMonomial (.snoc word i j hij 1) ∨
      ∃ b : Fˣ, (b : F) = a ∧
        fin4BruhatProjection
            (fin4SteinbergElementary
              (word.eval * steinbergX hij a * steinbergWeyl hij 1)) =
          fin4WeylWordMonomial (.snoc (.snoc word i j hij b) i j hij 1) := by
  rcases weylWord_upper_root_simpleWeyl_exact word hij hupper a with
      ⟨t₁, t₂, ht₁, ht₂, heq⟩ | ⟨b, hb, t₁, t₂, ht₁, ht₂, heq⟩
  · left
    rw [heq]
    exact fin4BruhatProjection_upper_word_upper t₁ t₂
      (.snoc word i j hij 1) ht₁ ht₂
  · right
    refine ⟨b, hb, ?_⟩
    rw [heq]
    exact fin4BruhatProjection_upper_word_upper t₁ t₂
      (.snoc (.snoc word i j hij b) i j hij 1) ht₁ ht₂

theorem fieldWeyl_mul_one_eq_diagonal {i j : Fin 4} (hij : i ≠ j) (b : Fˣ) :
    steinbergToGL (steinbergWeyl hij b) *
        steinbergToGL (steinbergWeyl hij (1 : Fˣ)) =
      detOneDiagonalMatrixUnitHom (fin4MatsumotoDiagonal i j (-b)) := by
  apply Units.ext
  rw [Units.val_mul, steinbergToGL_weyl, steinbergToGL_weyl,
    detOneDiagonalMatrixUnitHom_matrix,
    weylMatrix_eq_signedMonomial hij, weylMatrix_eq_signedMonomial hij,
    signedMonomialMatrix_mul]
  have hp : (Equiv.swap i j).trans (Equiv.swap i j) = 1 := by
    ext p
    simp
  rw [hp]
  congr 1
  funext p
  by_cases hpi : p = i
  · subst p
    simp [steinbergWeylRootScale, fin4MatsumotoDiagonal, hij, Ne.symm hij]
  · by_cases hpj : p = j
    · subst p
      simp [steinbergWeylRootScale, fin4MatsumotoDiagonal, Ne.symm hij]
    · have hswap : Equiv.swap i j p = p :=
        Equiv.swap_apply_of_ne_of_ne hpi hpj
      simp [steinbergWeylRootScale, fin4MatsumotoDiagonal, hpi, hpj, hswap]

noncomputable def fin4SimpleWeylMonomial {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) : fieldDetOneMonomialSubgroup (F := F) :=
  fin4WeylWordMonomial (.snoc .one i j hij u)

noncomputable def fin4SimpleWeylElementary {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) : elementaryGroup F (Fin 4) :=
  fin4SteinbergElementary (steinbergWeyl hij u)

theorem fin4WeylWordMonomial_snoc
    (word : SteinbergWeylWord F (Fin 4)) {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) :
    fin4WeylWordMonomial (.snoc word i j hij u) =
      fin4WeylWordMonomial word * fin4SimpleWeylMonomial hij u := by
  apply Subtype.ext
  change steinbergToGL (word.eval * steinbergWeyl hij u) =
    steinbergToGL word.eval * steinbergToGL (steinbergWeyl hij u)
  rw [map_mul]

theorem fin4SimpleWeylMonomial_mul_one_eq_diagonal
    {i j : Fin 4} (hij : i ≠ j) (b : Fˣ) :
    fin4SimpleWeylMonomial hij b *
        fin4SimpleWeylMonomial hij (1 : Fˣ) =
      detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j (-b)) := by
  apply Subtype.ext
  exact fieldWeyl_mul_one_eq_diagonal hij b

/-- Matrix form of Milnor Lemma 12.7 for one collected upper-root transition. -/
theorem fin4BruhatProjection_word_root_simpleWeyl_mul_or_diagonal
    (word : SteinbergWeylWord F (Fin 4)) {i j : Fin 4}
    (hij : i ≠ j) (hupper : i < j) (a : F) :
    fin4BruhatProjection
        (fin4SteinbergElementary
          (word.eval * steinbergX hij a * steinbergWeyl hij 1)) =
        fin4WeylWordMonomial word * fin4SimpleWeylMonomial hij 1 ∨
      ∃ b : Fˣ, (b : F) = a ∧
        fin4BruhatProjection
            (fin4SteinbergElementary
              (word.eval * steinbergX hij a * steinbergWeyl hij 1)) =
          fin4WeylWordMonomial word *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j (-b)) := by
  rcases fin4BruhatProjection_word_root_simpleWeyl word hij hupper a with
      hfirst | ⟨b, hb, hsecond⟩
  · left
    rw [hfirst, fin4WeylWordMonomial_snoc]
  · right
    refine ⟨b, hb, ?_⟩
    rw [hsecond, fin4WeylWordMonomial_snoc,
      fin4WeylWordMonomial_snoc, mul_assoc,
      fin4SimpleWeylMonomial_mul_one_eq_diagonal]

/-- Milnor Lemma 12.7 transition with arbitrary collected upper factors. -/
theorem fin4BruhatProjection_collected_mul_simpleWeyl
    (t q : SteinbergGroup F (Fin 4))
    (word : SteinbergWeylWord F (Fin 4)) {i j : Fin 4}
    (hij : i ≠ j) (hupper : i < j) (a : F)
    (ht : t ∈ upperSteinbergSubgroup (F := F) (Fin 4))
    (hq : q ∈ upperSteinbergSubgroup (F := F) (Fin 4))
    (hqconj : steinbergWeyl hij (-1 : Fˣ) * q * steinbergWeyl hij 1 ∈
      upperSteinbergSubgroup (F := F) (Fin 4)) :
    fin4BruhatProjection
        (fin4SteinbergElementary
          ((t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1)) =
        fin4BruhatProjection
            (fin4SteinbergElementary (t * word.eval * (steinbergX hij a * q))) *
          fin4SimpleWeylMonomial hij 1 ∨
      ∃ b : Fˣ, (b : F) = a ∧
        fin4BruhatProjection
            (fin4SteinbergElementary
              ((t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1)) =
          fin4BruhatProjection
              (fin4SteinbergElementary (t * word.eval * (steinbergX hij a * q))) *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j (-b)) := by
  have hxupper : steinbergX hij a * q ∈
      upperSteinbergSubgroup (F := F) (Fin 4) :=
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
      (Subgroup.subset_closure ⟨i, j, hij, a, hupper, rfl⟩) hq
  have hbase : fin4BruhatProjection
      (fin4SteinbergElementary (t * word.eval * (steinbergX hij a * q))) =
      fin4WeylWordMonomial word :=
    fin4BruhatProjection_upper_word_upper t (steinbergX hij a * q)
      word ht hxupper
  let q' := steinbergWeyl hij (-1 : Fˣ) * q * steinbergWeyl hij 1
  have hminus : steinbergWeyl hij (-1 : Fˣ) =
      (steinbergWeyl hij (1 : Fˣ))⁻¹ := by
    simpa using steinbergWeyl_neg hij (1 : Fˣ)
  have hpush : q * steinbergWeyl hij 1 = steinbergWeyl hij 1 * q' := by
    dsimp only [q']
    rw [hminus]
    group
  rcases weylWord_upper_root_simpleWeyl_exact word hij hupper a with
      ⟨u₁, u₂, hu₁, hu₂, heq⟩ | ⟨b, hb, u₁, u₂, hu₁, hu₂, heq⟩
  · left
    have hfull : (t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1 =
        (t * u₁) * (SteinbergWeylWord.snoc word i j hij 1).eval * (u₂ * q') := by
      rw [show (t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1 =
          t * (word.eval * steinbergX hij a * steinbergWeyl hij 1) * q' by
            calc
              (t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1 =
                  t * word.eval * steinbergX hij a *
                    (q * steinbergWeyl hij 1) := by group
              _ = t * (word.eval * steinbergX hij a * steinbergWeyl hij 1) *
                  q' := by rw [hpush]; group, heq]
      group
    rw [hfull,
      fin4BruhatProjection_upper_word_upper (t * u₁) (u₂ * q')
        (.snoc word i j hij 1)
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem ht hu₁)
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem hu₂ hqconj),
      fin4WeylWordMonomial_snoc, hbase]
  · right
    refine ⟨b, hb, ?_⟩
    have hfull : (t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1 =
        (t * u₁) *
          (SteinbergWeylWord.snoc
            (SteinbergWeylWord.snoc word i j hij b) i j hij 1).eval *
          (u₂ * q') := by
      rw [show (t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1 =
          t * (word.eval * steinbergX hij a * steinbergWeyl hij 1) * q' by
            calc
              (t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1 =
                  t * word.eval * steinbergX hij a *
                    (q * steinbergWeyl hij 1) := by group
              _ = t * (word.eval * steinbergX hij a * steinbergWeyl hij 1) *
                  q' := by rw [hpush]; group, heq]
      group
    rw [hfull,
      fin4BruhatProjection_upper_word_upper (t * u₁) (u₂ * q')
        (.snoc (.snoc word i j hij b) i j hij 1)
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem ht hu₁)
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem hu₂ hqconj),
      fin4WeylWordMonomial_snoc, fin4WeylWordMonomial_snoc,
      mul_assoc, fin4SimpleWeylMonomial_mul_one_eq_diagonal, hbase]

theorem fin4BruhatProjection_mul_simpleWeyl_of_collected_eq
    (A : elementaryGroup F (Fin 4)) (t q : SteinbergGroup F (Fin 4))
    (word : SteinbergWeylWord F (Fin 4)) {i j : Fin 4}
    (hij : i ≠ j) (hupper : i < j) (a : F)
    (ht : t ∈ upperSteinbergSubgroup (F := F) (Fin 4))
    (hq : q ∈ upperSteinbergSubgroup (F := F) (Fin 4))
    (hqconj : steinbergWeyl hij (-1 : Fˣ) * q * steinbergWeyl hij 1 ∈
      upperSteinbergSubgroup (F := F) (Fin 4))
    (hA : fin4SteinbergElementary
      (t * word.eval * (steinbergX hij a * q)) = A) :
    fin4BruhatProjection (A * fin4SimpleWeylElementary hij 1) =
        fin4BruhatProjection A * fin4SimpleWeylMonomial hij 1 ∨
      ∃ b : Fˣ, (b : F) = a ∧
        fin4BruhatProjection (A * fin4SimpleWeylElementary hij 1) =
          fin4BruhatProjection A *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j (-b)) := by
  have hnext : fin4SteinbergElementary
        ((t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1) =
      A * fin4SimpleWeylElementary hij 1 := by
    apply Subtype.ext
    have hAval := congrArg Subtype.val hA
    change steinbergToGL (t * word.eval * (steinbergX hij a * q)) = A.1 at hAval
    change steinbergToGL
        ((t * word.eval * (steinbergX hij a * q)) * steinbergWeyl hij 1) =
      A.1 * steinbergToGL (steinbergWeyl hij 1)
    rw [map_mul, hAval]
  simpa only [hA, hnext] using
    fin4BruhatProjection_collected_mul_simpleWeyl
      t q word hij hupper a ht hq hqconj

/-- Milnor Lemma 12.7, right transition for the first adjacent root. -/
theorem fin4BruhatProjection_mul_w01 (A : elementaryGroup F (Fin 4)) :
    let h01 : (0 : Fin 4) ≠ 1 := by decide
    fin4BruhatProjection (A * fin4SimpleWeylElementary h01 1) =
        fin4BruhatProjection A * fin4SimpleWeylMonomial h01 1 ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (A * fin4SimpleWeylElementary h01 1) =
          fin4BruhatProjection A *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 0 1 (-b)) := by
  dsimp only
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  obtain ⟨g, hg⟩ := A.2
  have hgTWT : g ∈ steinbergTWT (F := F) (n := Fin 4) := by
    rw [fin4_steinbergTWT_eq_top]
    exact Subgroup.mem_top g
  obtain ⟨t, w, t', ht, hw, ht', hdecomp⟩ := hgTWT
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at ht'
  obtain ⟨a, b, c, d, e, f, ht'eq⟩ := ht'
  let q : SteinbergGroup F (Fin 4) :=
    steinbergX h02 b * steinbergX h12 c * steinbergX h03 d *
      steinbergX h13 e * steinbergX h23 f
  have ht'split : t' = steinbergX h01 a * q := by
    rw [ht'eq]
    simp only [steinbergUpperTetrahedron, steinbergUpperTriangle,
      steinbergUpperColumn, q]
    group
  have hq : q ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
    exact (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
      ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
          ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
            (Subgroup.subset_closure ⟨0, 2, h02, b, by decide, rfl⟩)
            (Subgroup.subset_closure ⟨1, 2, h12, c, by decide, rfl⟩))
          (Subgroup.subset_closure ⟨0, 3, h03, d, by decide, rfl⟩))
        (Subgroup.subset_closure ⟨1, 3, h13, e, by decide, rfl⟩))
      (Subgroup.subset_closure ⟨2, 3, h23, f, by decide, rfl⟩)
  have hqconj : steinbergWeyl h01 (-1 : Fˣ) * q * steinbergWeyl h01 1 ∈
      upperSteinbergSubgroup (F := F) (Fin 4) := by
    have hq' := fin4_w01_neg_conj_upper_complement (F := F) b c d e f
    have hminus : steinbergWeyl h01 (-1 : Fˣ) =
        (steinbergWeyl h01 (1 : Fˣ))⁻¹ := by
      simpa using steinbergWeyl_neg h01 (1 : Fˣ)
    have hminus_inv : (steinbergWeyl h01 (-1 : Fˣ))⁻¹ =
        steinbergWeyl h01 (1 : Fˣ) := by rw [hminus, inv_inv]
    rw [hminus_inv] at hq'
    simpa only [q] using hq'
  have hgform : g = t * word.eval * (steinbergX h01 a * q) := by
    rw [hdecomp, ← hword, ht'split]
  have hbaseElem :
      fin4SteinbergElementary (t * word.eval * (steinbergX h01 a * q)) = A := by
    apply Subtype.ext
    change steinbergToGL (t * word.eval * (steinbergX h01 a * q)) = A.1
    rw [← hgform, hg]
  have hnextElem :
      fin4SteinbergElementary
          ((t * word.eval * (steinbergX h01 a * q)) * steinbergWeyl h01 1) =
        A * fin4SimpleWeylElementary h01 1 := by
    apply Subtype.ext
    change steinbergToGL
        ((t * word.eval * (steinbergX h01 a * q)) * steinbergWeyl h01 1) =
      A.1 * steinbergToGL (steinbergWeyl h01 1)
    rw [map_mul, ← hgform, hg]
  rcases fin4BruhatProjection_collected_mul_simpleWeyl
      t q word h01 (by decide) a ht hq hqconj with
    hfirst | ⟨v, _, hsecond⟩
  · left
    simpa only [hbaseElem, hnextElem] using hfirst
  · right
    exact ⟨v, by simpa only [hbaseElem, hnextElem] using hsecond⟩

/-- Milnor Lemma 12.7, right transition for the second adjacent root. -/
theorem fin4BruhatProjection_mul_w12 (A : elementaryGroup F (Fin 4)) :
    let h12 : (1 : Fin 4) ≠ 2 := by decide
    fin4BruhatProjection (A * fin4SimpleWeylElementary h12 1) =
        fin4BruhatProjection A * fin4SimpleWeylMonomial h12 1 ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (A * fin4SimpleWeylElementary h12 1) =
          fin4BruhatProjection A *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 1 2 (-b)) := by
  dsimp only
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  obtain ⟨g, hg⟩ := A.2
  have hgTWT : g ∈ steinbergTWT (F := F) (n := Fin 4) := by
    rw [fin4_steinbergTWT_eq_top]
    exact Subgroup.mem_top g
  obtain ⟨t, w, t', ht, hw, ht', hdecomp⟩ := hgTWT
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at ht'
  obtain ⟨a, b, c, d, e, f, ht'eq⟩ := ht'
  let q : SteinbergGroup F (Fin 4) :=
    steinbergX h02 (a * c) * steinbergX h01 a * steinbergX h02 b *
      steinbergX h03 d * steinbergX h13 e * steinbergX h23 f
  have ht'split : t' = steinbergX h12 c * q := by
    rw [ht'eq, fin4_tetrahedron_factor_w12]
  have hq : q ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
    exact (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
      ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
          ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
            ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
              (Subgroup.subset_closure ⟨0, 2, h02, a * c, by decide, rfl⟩)
              (Subgroup.subset_closure ⟨0, 1, h01, a, by decide, rfl⟩))
            (Subgroup.subset_closure ⟨0, 2, h02, b, by decide, rfl⟩))
          (Subgroup.subset_closure ⟨0, 3, h03, d, by decide, rfl⟩))
        (Subgroup.subset_closure ⟨1, 3, h13, e, by decide, rfl⟩))
      (Subgroup.subset_closure ⟨2, 3, h23, f, by decide, rfl⟩)
  have hqconj : steinbergWeyl h12 (-1 : Fˣ) * q * steinbergWeyl h12 1 ∈
      upperSteinbergSubgroup (F := F) (Fin 4) := by
    have hq' := fin4_w12_neg_conj_upper_complement (F := F) a b c d e f
    have hminus : steinbergWeyl h12 (-1 : Fˣ) =
        (steinbergWeyl h12 (1 : Fˣ))⁻¹ := by
      simpa using steinbergWeyl_neg h12 (1 : Fˣ)
    have hminus_inv : (steinbergWeyl h12 (-1 : Fˣ))⁻¹ =
        steinbergWeyl h12 (1 : Fˣ) := by rw [hminus, inv_inv]
    rw [hminus_inv] at hq'
    simpa only [q] using hq'
  have hgform : g = t * word.eval * (steinbergX h12 c * q) := by
    rw [hdecomp, ← hword, ht'split]
  have hA : fin4SteinbergElementary
      (t * word.eval * (steinbergX h12 c * q)) = A := by
    apply Subtype.ext
    change steinbergToGL (t * word.eval * (steinbergX h12 c * q)) = A.1
    rw [← hgform, hg]
  rcases fin4BruhatProjection_mul_simpleWeyl_of_collected_eq
      A t q word h12 (by decide) c ht hq hqconj hA with
    hfirst | ⟨v, _, hsecond⟩
  · exact Or.inl hfirst
  · exact Or.inr ⟨v, hsecond⟩

/-- Milnor Lemma 12.7, right transition for the final adjacent root. -/
theorem fin4BruhatProjection_mul_w23 (A : elementaryGroup F (Fin 4)) :
    let h23 : (2 : Fin 4) ≠ 3 := by decide
    fin4BruhatProjection (A * fin4SimpleWeylElementary h23 1) =
        fin4BruhatProjection A * fin4SimpleWeylMonomial h23 1 ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (A * fin4SimpleWeylElementary h23 1) =
          fin4BruhatProjection A *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 2 3 (-b)) := by
  dsimp only
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  obtain ⟨g, hg⟩ := A.2
  have hgTWT : g ∈ steinbergTWT (F := F) (n := Fin 4) := by
    rw [fin4_steinbergTWT_eq_top]
    exact Subgroup.mem_top g
  obtain ⟨t, w, t', ht, hw, ht', hdecomp⟩ := hgTWT
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at ht'
  obtain ⟨a, b, c, d, e, f, ht'eq⟩ := ht'
  let q : SteinbergGroup F (Fin 4) :=
    steinbergX h01 a * steinbergX h13 (c * f) * steinbergX h03 (b * f) *
      steinbergX h02 b * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e
  have ht'split : t' = steinbergX h23 f * q := by
    rw [ht'eq, fin4_tetrahedron_factor_w23]
  have hq : q ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
    exact (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
      ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
          ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
            ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
              ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
                (Subgroup.subset_closure ⟨0, 1, h01, a, by decide, rfl⟩)
                (Subgroup.subset_closure ⟨1, 3, h13, c * f, by decide, rfl⟩))
              (Subgroup.subset_closure ⟨0, 3, h03, b * f, by decide, rfl⟩))
            (Subgroup.subset_closure ⟨0, 2, h02, b, by decide, rfl⟩))
          (Subgroup.subset_closure ⟨1, 2, h12, c, by decide, rfl⟩))
        (Subgroup.subset_closure ⟨0, 3, h03, d, by decide, rfl⟩))
      (Subgroup.subset_closure ⟨1, 3, h13, e, by decide, rfl⟩)
  have hqconj : steinbergWeyl h23 (-1 : Fˣ) * q * steinbergWeyl h23 1 ∈
      upperSteinbergSubgroup (F := F) (Fin 4) := by
    have hq' := fin4_w23_neg_conj_upper_complement (F := F) a b c d e f
    have hminus : steinbergWeyl h23 (-1 : Fˣ) =
        (steinbergWeyl h23 (1 : Fˣ))⁻¹ := by
      simpa using steinbergWeyl_neg h23 (1 : Fˣ)
    have hminus_inv : (steinbergWeyl h23 (-1 : Fˣ))⁻¹ =
        steinbergWeyl h23 (1 : Fˣ) := by rw [hminus, inv_inv]
    rw [hminus_inv] at hq'
    simpa only [q] using hq'
  have hgform : g = t * word.eval * (steinbergX h23 f * q) := by
    rw [hdecomp, ← hword, ht'split]
  have hA : fin4SteinbergElementary
      (t * word.eval * (steinbergX h23 f * q)) = A := by
    apply Subtype.ext
    change steinbergToGL (t * word.eval * (steinbergX h23 f * q)) = A.1
    rw [← hgform, hg]
  rcases fin4BruhatProjection_mul_simpleWeyl_of_collected_eq
      A t q word h23 (by decide) f ht hq hqconj hA with
    hfirst | ⟨v, _, hsecond⟩
  · exact Or.inl hfirst
  · exact Or.inr ⟨v, hsecond⟩

theorem fin4SimpleWeylElementary_neg_one
    {i j : Fin 4} (hij : i ≠ j) :
    fin4SimpleWeylElementary hij (-1 : Fˣ) =
      fin4SimpleWeylElementary hij 1 *
        fin4DiagonalElementary (fin4MatsumotoDiagonal i j (-1 : Fˣ)) := by
  apply Subtype.ext
  change steinbergToGL (steinbergWeyl hij (-1 : Fˣ)) =
    steinbergToGL (steinbergWeyl hij (1 : Fˣ)) *
      detOneDiagonalMatrixUnitHom (fin4MatsumotoDiagonal i j (-1 : Fˣ))
  rw [detOneDiagonalMatrixUnitHom_fin4MatsumotoDiagonal hij,
    ← steinbergToGL_torus hij, ← map_mul]
  rw [steinbergTorus, steinbergWeyl_neg hij (1 : Fˣ)]
  group

theorem fin4SimpleWeylMonomial_neg_one
    {i j : Fin 4} (hij : i ≠ j) :
    fin4SimpleWeylMonomial hij (-1 : Fˣ) =
      fin4SimpleWeylMonomial hij 1 *
        detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j (-1 : Fˣ)) := by
  apply Subtype.ext
  change steinbergToGL (steinbergWeyl hij (-1 : Fˣ)) =
    steinbergToGL (steinbergWeyl hij (1 : Fˣ)) *
      detOneDiagonalMatrixUnitHom (fin4MatsumotoDiagonal i j (-1 : Fˣ))
  rw [detOneDiagonalMatrixUnitHom_fin4MatsumotoDiagonal hij,
    ← steinbergToGL_torus hij, ← map_mul]
  rw [steinbergTorus, steinbergWeyl_neg hij (1 : Fˣ)]
  group

theorem fin4MatsumotoDiagonal_neg_mul_neg_one
    {i j : Fin 4} (b : Fˣ) :
    detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j (-b)) *
        detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j (-1 : Fˣ)) =
      detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j b) := by
  rw [← map_mul, ← fin4MatsumotoDiagonal_mul]
  congr 2
  simp

theorem fin4BruhatProjection_mul_simpleWeyl_neg_one_of_one
    (A : elementaryGroup F (Fin 4)) {i j : Fin 4} (hij : i ≠ j)
    (htrans :
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij 1) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij 1 ∨
        ∃ b : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij 1) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j (-b))) :
    fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
        fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j b) := by
  have harg : A * fin4SimpleWeylElementary hij (-1 : Fˣ) =
      (A * fin4SimpleWeylElementary hij 1) *
        fin4DiagonalElementary (fin4MatsumotoDiagonal i j (-1 : Fˣ)) := by
    rw [fin4SimpleWeylElementary_neg_one]
    group
  rcases htrans with hfirst | ⟨b, hsecond⟩
  · left
    rw [harg, fin4BruhatProjection_mul_diagonal, hfirst, mul_assoc,
      ← fin4SimpleWeylMonomial_neg_one]
  · right
    refine ⟨b, ?_⟩
    rw [harg, fin4BruhatProjection_mul_diagonal, hsecond, mul_assoc,
      fin4MatsumotoDiagonal_neg_mul_neg_one]

/-- Milnor Lemma 12.7, stated with the first inverse simple Weyl factor. -/
theorem fin4BruhatProjection_mul_w01_neg_one (A : elementaryGroup F (Fin 4)) :
    let h01 : (0 : Fin 4) ≠ 1 := by decide
    fin4BruhatProjection (A * fin4SimpleWeylElementary h01 (-1 : Fˣ)) =
        fin4BruhatProjection A * fin4SimpleWeylMonomial h01 (-1 : Fˣ) ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (A * fin4SimpleWeylElementary h01 (-1 : Fˣ)) =
          fin4BruhatProjection A *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 0 1 b) := by
  dsimp only
  exact fin4BruhatProjection_mul_simpleWeyl_neg_one_of_one A (by decide)
    (fin4BruhatProjection_mul_w01 A)

/-- Milnor Lemma 12.7, stated with the second inverse simple Weyl factor. -/
theorem fin4BruhatProjection_mul_w12_neg_one (A : elementaryGroup F (Fin 4)) :
    let h12 : (1 : Fin 4) ≠ 2 := by decide
    fin4BruhatProjection (A * fin4SimpleWeylElementary h12 (-1 : Fˣ)) =
        fin4BruhatProjection A * fin4SimpleWeylMonomial h12 (-1 : Fˣ) ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (A * fin4SimpleWeylElementary h12 (-1 : Fˣ)) =
          fin4BruhatProjection A *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 1 2 b) := by
  dsimp only
  exact fin4BruhatProjection_mul_simpleWeyl_neg_one_of_one A (by decide)
    (fin4BruhatProjection_mul_w12 A)

/-- Milnor Lemma 12.7, stated with the final inverse simple Weyl factor. -/
theorem fin4BruhatProjection_mul_w23_neg_one (A : elementaryGroup F (Fin 4)) :
    let h23 : (2 : Fin 4) ≠ 3 := by decide
    fin4BruhatProjection (A * fin4SimpleWeylElementary h23 (-1 : Fˣ)) =
        fin4BruhatProjection A * fin4SimpleWeylMonomial h23 (-1 : Fˣ) ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (A * fin4SimpleWeylElementary h23 (-1 : Fˣ)) =
          fin4BruhatProjection A *
            detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 2 3 b) := by
  dsimp only
  exact fin4BruhatProjection_mul_simpleWeyl_neg_one_of_one A (by decide)
    (fin4BruhatProjection_mul_w23 A)

theorem fin4WeylWordMonomial_inv (word : SteinbergWeylWord F (Fin 4)) :
    fin4WeylWordMonomial word.inv = (fin4WeylWordMonomial word)⁻¹ := by
  apply Subtype.ext
  change steinbergToGL word.inv.eval = (steinbergToGL word.eval)⁻¹
  rw [SteinbergWeylWord.eval_inv, map_inv]

/-- Bruhat projection commutes with inversion. -/
theorem fin4BruhatProjection_inv (A : elementaryGroup F (Fin 4)) :
    fin4BruhatProjection A⁻¹ = (fin4BruhatProjection A)⁻¹ := by
  obtain ⟨g, hg⟩ := A.2
  have hgTWT : g ∈ steinbergTWT (F := F) (n := Fin 4) := by
    rw [fin4_steinbergTWT_eq_top]
    exact Subgroup.mem_top g
  obtain ⟨t₁, w, t₂, ht₁, hw, ht₂, hdecomp⟩ := hgTWT
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  have hA : fin4SteinbergElementary (t₁ * word.eval * t₂) = A := by
    apply Subtype.ext
    change steinbergToGL (t₁ * word.eval * t₂) = A.1
    rw [hword, ← hdecomp, hg]
  have hAinv : fin4SteinbergElementary
      (t₂⁻¹ * word.inv.eval * t₁⁻¹) = A⁻¹ := by
    apply Subtype.ext
    have hAval := congrArg Subtype.val hA
    change steinbergToGL (t₁ * word.eval * t₂) = A.1 at hAval
    change steinbergToGL (t₂⁻¹ * word.inv.eval * t₁⁻¹) = A.1⁻¹
    rw [SteinbergWeylWord.eval_inv, map_mul, map_mul, map_inv, map_inv, map_inv,
      ← hAval, map_mul, map_mul]
    group
  have hpA : fin4BruhatProjection A = fin4WeylWordMonomial word := by
    rw [← hA]
    exact fin4BruhatProjection_upper_word_upper t₁ t₂ word ht₁ ht₂
  have hpAinv : fin4BruhatProjection A⁻¹ =
      fin4WeylWordMonomial word.inv := by
    rw [← hAinv]
    exact fin4BruhatProjection_upper_word_upper t₂⁻¹ t₁⁻¹ word.inv
      ((upperSteinbergSubgroup (F := F) (Fin 4)).inv_mem ht₂)
      ((upperSteinbergSubgroup (F := F) (Fin 4)).inv_mem ht₁)
  rw [hpAinv, fin4WeylWordMonomial_inv, hpA]

theorem fin4SimpleWeylElementary_neg_one_inv
    {i j : Fin 4} (hij : i ≠ j) :
    (fin4SimpleWeylElementary hij (-1 : Fˣ))⁻¹ =
      fin4SimpleWeylElementary hij (1 : Fˣ) := by
  apply Subtype.ext
  change (steinbergToGL (steinbergWeyl hij (-1 : Fˣ)))⁻¹ =
    steinbergToGL (steinbergWeyl hij (1 : Fˣ))
  rw [← map_inv, steinbergWeyl_neg hij (1 : Fˣ), inv_inv]

theorem fin4SimpleWeylMonomial_neg_one_inv
    {i j : Fin 4} (hij : i ≠ j) :
    (fin4SimpleWeylMonomial hij (-1 : Fˣ))⁻¹ =
      fin4SimpleWeylMonomial hij (1 : Fˣ) := by
  apply Subtype.ext
  change (steinbergToGL (steinbergWeyl hij (-1 : Fˣ)))⁻¹ =
    steinbergToGL (steinbergWeyl hij (1 : Fˣ))
  rw [← map_inv, steinbergWeyl_neg hij (1 : Fˣ), inv_inv]

theorem fin4BruhatProjection_simpleWeyl_mul_of_inv_transition
    (A : elementaryGroup F (Fin 4)) {i j : Fin 4} (hij : i ≠ j)
    (htrans :
      fin4BruhatProjection
          (A⁻¹ * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A⁻¹ *
            fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ b : Fˣ,
          fin4BruhatProjection
              (A⁻¹ * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A⁻¹ *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j b)) :
    fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
        fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j b))⁻¹ *
            fin4BruhatProjection A := by
  have harg : fin4SimpleWeylElementary hij 1 * A =
      (A⁻¹ * fin4SimpleWeylElementary hij (-1 : Fˣ))⁻¹ := by
    rw [_root_.mul_inv_rev, inv_inv, fin4SimpleWeylElementary_neg_one_inv]
  rcases htrans with hfirst | ⟨b, hsecond⟩
  · left
    rw [harg, fin4BruhatProjection_inv, hfirst, _root_.mul_inv_rev,
      fin4BruhatProjection_inv, inv_inv,
      fin4SimpleWeylMonomial_neg_one_inv]
  · right
    refine ⟨b, ?_⟩
    rw [harg, fin4BruhatProjection_inv, hsecond, _root_.mul_inv_rev,
      fin4BruhatProjection_inv, inv_inv]

/-- Milnor Lemma 12.7, left transition for the first adjacent root. -/
theorem fin4BruhatProjection_w01_mul (A : elementaryGroup F (Fin 4)) :
    let h01 : (0 : Fin 4) ≠ 1 := by decide
    fin4BruhatProjection (fin4SimpleWeylElementary h01 1 * A) =
        fin4SimpleWeylMonomial h01 1 * fin4BruhatProjection A ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (fin4SimpleWeylElementary h01 1 * A) =
          (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 0 1 b))⁻¹ *
            fin4BruhatProjection A := by
  dsimp only
  exact fin4BruhatProjection_simpleWeyl_mul_of_inv_transition A (by decide)
    (fin4BruhatProjection_mul_w01_neg_one A⁻¹)

/-- Milnor Lemma 12.7, left transition for the second adjacent root. -/
theorem fin4BruhatProjection_w12_mul (A : elementaryGroup F (Fin 4)) :
    let h12 : (1 : Fin 4) ≠ 2 := by decide
    fin4BruhatProjection (fin4SimpleWeylElementary h12 1 * A) =
        fin4SimpleWeylMonomial h12 1 * fin4BruhatProjection A ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (fin4SimpleWeylElementary h12 1 * A) =
          (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 1 2 b))⁻¹ *
            fin4BruhatProjection A := by
  dsimp only
  exact fin4BruhatProjection_simpleWeyl_mul_of_inv_transition A (by decide)
    (fin4BruhatProjection_mul_w12_neg_one A⁻¹)

/-- Milnor Lemma 12.7, left transition for the final adjacent root. -/
theorem fin4BruhatProjection_w23_mul (A : elementaryGroup F (Fin 4)) :
    let h23 : (2 : Fin 4) ≠ 3 := by decide
    fin4BruhatProjection (fin4SimpleWeylElementary h23 1 * A) =
        fin4SimpleWeylMonomial h23 1 * fin4BruhatProjection A ∨
      ∃ b : Fˣ,
        fin4BruhatProjection (fin4SimpleWeylElementary h23 1 * A) =
          (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal 2 3 b))⁻¹ *
            fin4BruhatProjection A := by
  dsimp only
  exact fin4BruhatProjection_simpleWeyl_mul_of_inv_transition A (by decide)
    (fin4BruhatProjection_mul_w23_neg_one A⁻¹)

end GaloisForLFunctions.HTGeometry
