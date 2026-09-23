import GaloisForLFunctions.HTGeometry.Sl2ToralClassification

/-!
# Proper Lie subalgebras of `sl₂`

Every nonzero traceless bracket-closed subspace is classified without a dimension premise.  A
determinant-zero subspace is a nilpotent line.  A regular element is explicitly diagonalized, after
which the Cartan bracket projections leave only the Cartan, either Borel, or all of `sl₂`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- A bracket-closed traceless subspace containing the standard Cartan generator is one of the
four coordinate Lie subalgebras. -/
theorem sl2_subalgebra_containing_H_classification
    (V : Submodule C (Matrix (Fin 2) (Fin 2) C))
    (htr : ∀ A ∈ V, A.trace = 0)
    (hbr : ∀ A ∈ V, ∀ B ∈ V, A * B - B * A ∈ V)
    (hH : sl2H C ∈ V) :
    V = Submodule.span C ({sl2H C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
      V = Submodule.span C ({sl2H C, sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
      V = Submodule.span C ({sl2H C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
      V = Submodule.span C
        ({sl2H C, sl2E C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  classical
  have hsplit : ∀ Z ∈ V, (Z 0 1) • sl2E C ∈ V ∧ (Z 1 0) • sl2F C ∈ V := by
    intro Z hZ
    have h1 : sl2H C * Z - Z * sl2H C ∈ V := hbr _ hH _ hZ
    have h2 : sl2H C * (sl2H C * Z - Z * sl2H C) -
        (sl2H C * Z - Z * sl2H C) * sl2H C ∈ V := hbr _ hH _ h1
    have e1 : sl2H C * Z - Z * sl2H C =
        (2 * Z 0 1) • sl2E C - (2 * Z 1 0) • sl2F C := by
      simpa using bracket_toral (1 : C) Z
    have e2 : sl2H C * (sl2H C * Z - Z * sl2H C) -
        (sl2H C * Z - Z * sl2H C) * sl2H C =
          (4 * Z 0 1) • sl2E C + (4 * Z 1 0) • sl2F C := by
      simpa using bracket_toral_sq (1 : C) Z
    rw [e1] at h1
    rw [e2] at h2
    constructor
    · have hm := V.add_mem h2 (V.smul_mem (2 : C) h1)
      have hs := V.smul_mem (8 : C)⁻¹ hm
      have heq : (8 : C)⁻¹ •
          ((4 * Z 0 1) • sl2E C + (4 * Z 1 0) • sl2F C +
            (2 : C) • ((2 * Z 0 1) • sl2E C - (2 * Z 1 0) • sl2F C)) =
          (Z 0 1) • sl2E C := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2E, sl2F] <;> field_simp <;> ring
      rwa [heq] at hs
    · have hm := V.add_mem h2 (V.smul_mem (-2 : C) h1)
      have hs := V.smul_mem (8 : C)⁻¹ hm
      have heq : (8 : C)⁻¹ •
          ((4 * Z 0 1) • sl2E C + (4 * Z 1 0) • sl2F C +
            (-2 : C) • ((2 * Z 0 1) • sl2E C - (2 * Z 1 0) • sl2F C)) =
          (Z 1 0) • sl2F C := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2E, sl2F] <;> field_simp <;> ring
      rwa [heq] at hs
  have hpart : ∀ Z ∈ V, (Z 0 0) • sl2H C ∈ V := by
    intro Z hZ
    obtain ⟨hE, hF⟩ := hsplit Z hZ
    have hm := V.sub_mem (V.sub_mem hZ hE) hF
    have heq : Z - (Z 0 1) • sl2E C - (Z 1 0) • sl2F C =
        (Z 0 0) • sl2H C := by
      have h11 : Z 1 1 = -(Z 0 0) := by
        have ht := htr Z hZ
        rw [Matrix.trace_fin_two] at ht
        linear_combination ht
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2H, sl2E, sl2F, h11]
    rwa [heq] at hm
  by_cases hE : sl2E C ∈ V
  · by_cases hF : sl2F C ∈ V
    · right; right; right
      apply le_antisymm
      · intro Z hZ
        rw [traceless_decomp (htr Z hZ)]
        exact Submodule.add_mem _
          (Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [Submodule.span_le]
        intro X hX
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
        rcases hX with rfl | rfl | rfl
        exacts [hH, hE, hF]
    · right; left
      apply le_antisymm
      · intro Z hZ
        obtain ⟨hZE, hZF⟩ := hsplit Z hZ
        have hz10 : Z 1 0 = 0 := by
          by_contra hz
          have := V.smul_mem (Z 1 0)⁻¹ hZF
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul] at this
          exact hF this
        rw [traceless_decomp (htr Z hZ), hz10, zero_smul, add_zero]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [Submodule.span_le]
        intro X hX
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
        rcases hX with rfl | rfl
        exacts [hH, hE]
  · by_cases hF : sl2F C ∈ V
    · right; right; left
      apply le_antisymm
      · intro Z hZ
        obtain ⟨hZE, hZF⟩ := hsplit Z hZ
        have hz01 : Z 0 1 = 0 := by
          by_contra hz
          have := V.smul_mem (Z 0 1)⁻¹ hZE
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul] at this
          exact hE this
        rw [traceless_decomp (htr Z hZ), hz01, zero_smul, add_zero]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [Submodule.span_le]
        intro X hX
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
        rcases hX with rfl | rfl
        exacts [hH, hF]
    · left
      apply le_antisymm
      · intro Z hZ
        obtain ⟨hZE, hZF⟩ := hsplit Z hZ
        have hz01 : Z 0 1 = 0 := by
          by_contra hz
          have := V.smul_mem (Z 0 1)⁻¹ hZE
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul] at this
          exact hE this
        have hz10 : Z 1 0 = 0 := by
          by_contra hz
          have := V.smul_mem (Z 1 0)⁻¹ hZF
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul] at this
          exact hF this
        rw [traceless_decomp (htr Z hZ)]
        simpa [hz01, hz10] using
          (Submodule.smul_mem (Submodule.span C
            ({sl2H C} : Set (Matrix (Fin 2) (Fin 2) C))) (Z 0 0)
            (Submodule.subset_span (by simp)))
      · rw [Submodule.span_le]
        intro X hX
        simpa only [Set.mem_singleton_iff] using hX ▸ hH

omit [CharZero C] in
/-- A nonzero traceless linear subspace on which the determinant vanishes identically is a line. -/
theorem traceless_det_zero_submodule_eq_span_singleton
    (V : Submodule C (Matrix (Fin 2) (Fin 2) C))
    (htr : ∀ A ∈ V, A.trace = 0)
    {X : Matrix (Fin 2) (Fin 2) C} (hX : X ∈ V) (hXne : X ≠ 0)
    (hdet : ∀ A ∈ V, A.det = 0) :
    V = Submodule.span C ({X} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  classical
  apply le_antisymm
  · intro Y hY
    have hXtr := htr X hX
    have hYtr := htr Y hY
    have hX11 : X 1 1 = -(X 0 0) := by
      rw [Matrix.trace_fin_two] at hXtr
      linear_combination hXtr
    have hY11 : Y 1 1 = -(Y 0 0) := by
      rw [Matrix.trace_fin_two] at hYtr
      linear_combination hYtr
    have hXrel : X 0 0 ^ (2 : ℕ) + X 0 1 * X 1 0 = 0 := by
      have hx := hdet X hX
      rw [Matrix.det_fin_two, hX11] at hx
      linear_combination -hx
    have hYrel : Y 0 0 ^ (2 : ℕ) + Y 0 1 * Y 1 0 = 0 := by
      have hy := hdet Y hY
      rw [Matrix.det_fin_two, hY11] at hy
      linear_combination -hy
    have hcross : 2 * X 0 0 * Y 0 0 + X 0 1 * Y 1 0 + X 1 0 * Y 0 1 = 0 := by
      have hxy := hdet (X + Y) (V.add_mem hX hY)
      rw [Matrix.det_fin_two] at hxy
      simp only [Matrix.add_apply] at hxy
      rw [hX11, hY11] at hxy
      linear_combination -hxy - hXrel - hYrel
    by_cases hb : X 0 1 = 0
    · have ha : X 0 0 = 0 := by
        rw [hb, zero_mul, add_zero] at hXrel
        exact sq_eq_zero_iff.mp hXrel
      have hc : X 1 0 ≠ 0 := by
        intro hc
        apply hXne
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hX11]
      have he : Y 0 1 = 0 := by
        have hce : X 1 0 * Y 0 1 = 0 := by
          simpa [ha, hb] using hcross
        exact (mul_eq_zero.mp hce).resolve_left hc
      have hd : Y 0 0 = 0 := by
        rw [he, zero_mul, add_zero] at hYrel
        exact sq_eq_zero_iff.mp hYrel
      rw [Submodule.mem_span_singleton]
      refine ⟨Y 1 0 / X 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.smul_apply, ha, hb, hc, hd, he, hX11, hY11]
    · have hsq : (X 0 1 * Y 0 0 - Y 0 1 * X 0 0) ^ (2 : ℕ) = 0 := by
        linear_combination
          (X 0 1) ^ (2 : ℕ) * hYrel + (Y 0 1) ^ (2 : ℕ) * hXrel -
            (X 0 1 * Y 0 1) * hcross
      have hlin : X 0 1 * Y 0 0 = Y 0 1 * X 0 0 := by
        have hs := sq_eq_zero_iff.mp hsq
        linear_combination hs
      have hd : (Y 0 1 / X 0 1) * X 0 0 = Y 0 0 := by
        field_simp [hb]
        linear_combination -hlin
      have hf : (Y 0 1 / X 0 1) * X 1 0 = Y 1 0 := by
        have hlin0 : X 0 1 * Y 0 0 - Y 0 1 * X 0 0 = 0 := sub_eq_zero.mpr hlin
        have hscaled : X 0 1 *
            (X 0 1 * Y 1 0 - Y 0 1 * X 1 0) = 0 := by
          linear_combination
            X 0 1 * hcross - 2 * X 0 0 * hlin0 - 2 * Y 0 1 * hXrel
        have hbf : X 0 1 * Y 1 0 = Y 0 1 * X 1 0 := by
          exact sub_eq_zero.mp ((mul_eq_zero.mp hscaled).resolve_left hb)
        field_simp [hb]
        linear_combination -hbf
      rw [Submodule.mem_span_singleton]
      refine ⟨Y 0 1 / X 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.smul_apply, hb, hd, hf, hX11, hY11]
  · rw [Submodule.span_le]
    intro Y hY
    simpa only [Set.mem_singleton_iff] using hY ▸ hX

/-- A traceless Lie subalgebra containing a regular element is, after conjugation, Cartan,
one of the two Borels, or all of `sl₂`. -/
theorem sl2_subalgebra_regular_classification [IsAlgClosed C]
    (V : Submodule C (Matrix (Fin 2) (Fin 2) C))
    (htr : ∀ A ∈ V, A.trace = 0)
    (hbr : ∀ A ∈ V, ∀ B ∈ V, A * B - B * A ∈ V)
    {X : Matrix (Fin 2) (Fin 2) C} (hX : X ∈ V) (hXdet : X.det ≠ 0) :
    ∃ (μ : C) (P Q : Matrix (Fin 2) (Fin 2) C), μ ≠ 0 ∧ P * Q = 1 ∧ Q * P = 1 ∧
      let W := V.map (conjLinear C Q P)
      W = Submodule.span C ({sl2H C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
        W = Submodule.span C ({sl2H C, sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
        W = Submodule.span C ({sl2H C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
        W = Submodule.span C
          ({sl2H C, sl2E C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  classical
  obtain ⟨μ, P, hμ, hPdet, hXP⟩ :=
    exists_conj_toral_of_det_ne_zero (by norm_num : (2 : C) ≠ 0) X (htr X hX) hXdet
  let Q : Matrix (Fin 2) (Fin 2) C := (P.det)⁻¹ • Matrix.adjugate P
  have hPQ : P * Q = 1 := by
    change P * ((P.det)⁻¹ • Matrix.adjugate P) = 1
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul,
      inv_mul_cancel₀ hPdet, one_smul]
  have hQP : Q * P = 1 := by
    change ((P.det)⁻¹ • Matrix.adjugate P) * P = 1
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
      inv_mul_cancel₀ hPdet, one_smul]
  let W := V.map (conjLinear C Q P)
  have hμH : μ • sl2H C ∈ W := by
    refine ⟨X, hX, ?_⟩
    simp only [conjLinear_apply]
    calc
      Q * X * P = Q * (X * P) := by rw [mul_assoc]
      _ = Q * (P * (μ • sl2H C)) := by rw [hXP]
      _ = μ • sl2H C := by rw [← mul_assoc, hQP, one_mul]
  have hH : sl2H C ∈ W := by
    have hs := W.smul_mem μ⁻¹ hμH
    rwa [smul_smul, inv_mul_cancel₀ hμ, one_smul] at hs
  have hWtr : ∀ A ∈ W, A.trace = 0 := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := hA
    simp only [conjLinear_apply]
    rw [Matrix.trace_mul_cycle, hPQ, one_mul, htr B hB]
  have hWbr : ∀ A ∈ W, ∀ B ∈ W, A * B - B * A ∈ W := by
    intro A hA B hB
    obtain ⟨A₀, hA₀, rfl⟩ := hA
    obtain ⟨B₀, hB₀, rfl⟩ := hB
    refine ⟨A₀ * B₀ - B₀ * A₀, hbr A₀ hA₀ B₀ hB₀, ?_⟩
    have hmul (A B : Matrix (Fin 2) (Fin 2) C) :
        (Q * A * P) * (Q * B * P) = Q * (A * B) * P := by
      calc
        (Q * A * P) * (Q * B * P) = Q * A * (P * Q) * B * P := by
          simp only [mul_assoc]
        _ = Q * (A * B) * P := by rw [hPQ, mul_one, mul_assoc Q A B]
    simp only [conjLinear_apply, Matrix.mul_sub, Matrix.sub_mul, hmul]
  exact ⟨μ, P, Q, hμ, hPQ, hQP,
    sl2_subalgebra_containing_H_classification W hWtr hWbr hH⟩

/-- Every nonzero traceless Lie subalgebra of `sl₂` is either a nilpotent line or, after one
conjugation, Cartan, Borel, or all of `sl₂`. -/
theorem sl2_nonzero_subalgebra_classification [IsAlgClosed C]
    (V : Submodule C (Matrix (Fin 2) (Fin 2) C))
    (htr : ∀ A ∈ V, A.trace = 0)
    (hbr : ∀ A ∈ V, ∀ B ∈ V, A * B - B * A ∈ V)
    (hne : ∃ X ∈ V, X ≠ 0) :
    (∃ X : Matrix (Fin 2) (Fin 2) C, X ∈ V ∧ X ≠ 0 ∧ X.det = 0 ∧
      V = Submodule.span C ({X} : Set (Matrix (Fin 2) (Fin 2) C))) ∨
    ∃ (μ : C) (P Q : Matrix (Fin 2) (Fin 2) C), μ ≠ 0 ∧ P * Q = 1 ∧ Q * P = 1 ∧
      let W := V.map (conjLinear C Q P)
      W = Submodule.span C ({sl2H C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
        W = Submodule.span C ({sl2H C, sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
        W = Submodule.span C ({sl2H C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
        W = Submodule.span C
          ({sl2H C, sl2E C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  by_cases hreg : ∃ X ∈ V, X.det ≠ 0
  · right
    obtain ⟨X, hX, hXdet⟩ := hreg
    exact sl2_subalgebra_regular_classification V htr hbr hX hXdet
  · left
    obtain ⟨X, hX, hXne⟩ := hne
    have hdet : ∀ A ∈ V, A.det = 0 := by
      intro A hA
      by_contra hAne
      exact hreg ⟨A, hA, hAne⟩
    exact ⟨X, hX, hXne, hdet X hX,
      traceless_det_zero_submodule_eq_span_singleton V htr hX hXne hdet⟩

end

end GaloisForLFunctions.HTGeometry
