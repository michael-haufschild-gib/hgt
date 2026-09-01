import GaloisForLFunctions.HTGeometry.Sl2ProperLieClassification

/-!
# Adjoint-stable proper Lie subalgebras of `sl₂`

The proper cases are converted to their representation-theoretic content: a common invariant line
or an invariant unordered pair of lines.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
/-- Every nonzero traceless nilpotent `2 × 2` matrix is conjugate to the standard raising
matrix, with explicit two-sided conjugators. -/
theorem exists_conj_eq_E_of_trace_eq_zero_of_det_eq_zero
    (X : Matrix (Fin 2) (Fin 2) C) (htr : X.trace = 0) (hdet : X.det = 0) (hne : X ≠ 0) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) C,
      P * Q = 1 ∧ Q * P = 1 ∧ Q * X * P = sl2E C := by
  have h11 : X 1 1 = -(X 0 0) := by
    rw [Matrix.trace_fin_two] at htr
    linear_combination htr
  have hrel : X 0 0 ^ 2 + X 0 1 * X 1 0 = 0 := by
    rw [Matrix.det_fin_two, h11] at hdet
    linear_combination -hdet
  by_cases hb : X 0 1 = 0
  · have ha : X 0 0 = 0 := by
      rw [hb, zero_mul, add_zero] at hrel
      exact sq_eq_zero_iff.mp hrel
    have hc : X 1 0 ≠ 0 := by
      intro hc
      apply hne
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, h11]
    let P : Matrix (Fin 2) (Fin 2) C := !![0, (X 1 0)⁻¹; 1, 0]
    let Q : Matrix (Fin 2) (Fin 2) C := !![0, 1; X 1 0, 0]
    refine ⟨P, Q, ?_, ?_, ?_⟩
    all_goals
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, Q, sl2E, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, ha, hb, hc, h11]
  · let P : Matrix (Fin 2) (Fin 2) C := !![X 0 1, 0; -(X 0 0), 1]
    let Q : Matrix (Fin 2) (Fin 2) C :=
      !![(X 0 1)⁻¹, 0; X 0 0 * (X 0 1)⁻¹, 1]
    refine ⟨P, Q, ?_, ?_, ?_⟩
    all_goals
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, Q, sl2E, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, hb, h11] <;>
        field_simp [hb] <;> ring_nf at hrel ⊢ <;> linear_combination hrel

omit [CharZero C] in
/-- Normalizing the raising line forces upper triangularity. -/
theorem lowerLeft_eq_zero_of_conj_E_mem_span
    (g g' : Matrix (Fin 2) (Fin 2) C) (hg'g : g' * g = 1)
    (hE : g * sl2E C * g' ∈
      Submodule.span C ({sl2E C} : Set (Matrix (Fin 2) (Fin 2) C))) :
    g 1 0 = 0 := by
  rw [Submodule.mem_span_singleton] at hE
  obtain ⟨c, hc⟩ := hE
  have hrel : (c • sl2E C) * g = g * sl2E C := by
    calc
      (c • sl2E C) * g = (g * sl2E C * g') * g := by rw [hc]
      _ = g * sl2E C := by rw [mul_assoc, hg'g, mul_one]
  have h := congrFun (congrFun hrel 1) 1
  simpa [sl2E, Matrix.mul_apply, Fin.sum_univ_two] using h.symm

omit [CharZero C] in
/-- Normalizing the lowering line forces lower triangularity. -/
theorem upperRight_eq_zero_of_conj_F_mem_span
    (g g' : Matrix (Fin 2) (Fin 2) C) (hg'g : g' * g = 1)
    (hF : g * sl2F C * g' ∈
      Submodule.span C ({sl2F C} : Set (Matrix (Fin 2) (Fin 2) C))) :
    g 0 1 = 0 := by
  rw [Submodule.mem_span_singleton] at hF
  obtain ⟨c, hc⟩ := hF
  have hrel : (c • sl2F C) * g = g * sl2F C := by
    calc
      (c • sl2F C) * g = (g * sl2F C * g') * g := by rw [hc]
      _ = g * sl2F C := by rw [mul_assoc, hg'g, mul_one]
  have h := congrFun (congrFun hrel 0) 0
  simpa [sl2F, Matrix.mul_apply, Fin.sum_univ_two] using h.symm

/-- Normalizing the Cartan line forces a matrix to be diagonal or anti-diagonal. -/
theorem diagonal_or_antidiagonal_of_conj_H_mem_span
    (g g' : Matrix (Fin 2) (Fin 2) C) (hgg' : g * g' = 1) (hg'g : g' * g = 1)
    (hH : g * sl2H C * g' ∈
      Submodule.span C ({sl2H C} : Set (Matrix (Fin 2) (Fin 2) C))) :
    (g 0 1 = 0 ∧ g 1 0 = 0) ∨ (g 0 0 = 0 ∧ g 1 1 = 0) := by
  rw [Submodule.mem_span_singleton] at hH
  obtain ⟨c, hc⟩ := hH
  have hrel : (c • sl2H C) * g = g * sl2H C := by
    calc
      (c • sl2H C) * g = (g * sl2H C * g') * g := by rw [hc]
      _ = g * sl2H C := by rw [mul_assoc, hg'g, mul_one]
  have h00 := congrFun (congrFun hrel 0) 0
  have h01 := congrFun (congrFun hrel 0) 1
  have h10 := congrFun (congrFun hrel 1) 0
  have h11 := congrFun (congrFun hrel 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] at h00 h01 h10 h11
  simp [sl2H] at h00 h01 h10 h11
  by_cases hc1 : c = 1
  · left
    constructor <;> subst c
    · linear_combination h01 / 2
    · linear_combination -h10 / 2
  · by_cases hcn1 : c = -1
    · right
      constructor <;> subst c
      · linear_combination -h00 / 2
      · linear_combination -h11 / 2
    · exfalso
      have hcplus : c + 1 ≠ 0 := by
        intro h
        apply hcn1
        linear_combination h
      have ha : g 0 0 = 0 := by
        have hf : (c - 1) * g 0 0 = 0 := by linear_combination h00
        exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hc1)
      have hb : g 0 1 = 0 := by
        have hf : (c + 1) * g 0 1 = 0 := by linear_combination h01
        exact (mul_eq_zero.mp hf).resolve_left hcplus
      have hc0 : g 1 0 = 0 := by
        have hf : (c + 1) * g 1 0 = 0 := by linear_combination -h10
        exact (mul_eq_zero.mp hf).resolve_left hcplus
      have hd : g 1 1 = 0 := by
        have hf : (c - 1) * g 1 1 = 0 := by linear_combination h11
        exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hc1)
      have hg0 : g = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb, hc0, hd]
      rw [hg0, zero_mul] at hgg'
      exact zero_ne_one hgg'

omit [CharZero C] in
/-- The commutator of two upper-Borel elements belongs to the nilpotent radical. -/
theorem bracket_mem_span_E_of_mem_span_H_E
    {A B : Matrix (Fin 2) (Fin 2) C}
    (hA : A ∈ Submodule.span C
      ({sl2H C, sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)))
    (hB : B ∈ Submodule.span C
      ({sl2H C, sl2E C} : Set (Matrix (Fin 2) (Fin 2) C))) :
    A * B - B * A ∈
      Submodule.span C ({sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  rw [Submodule.mem_span_pair] at hA hB
  obtain ⟨a, b, rfl⟩ := hA
  obtain ⟨c, d, rfl⟩ := hB
  rw [Submodule.mem_span_singleton]
  refine ⟨2 * (a * d - b * c), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2H, sl2E] <;> ring

omit [CharZero C] in
/-- The commutator of two lower-Borel elements belongs to the nilpotent radical. -/
theorem bracket_mem_span_F_of_mem_span_H_F
    {A B : Matrix (Fin 2) (Fin 2) C}
    (hA : A ∈ Submodule.span C
      ({sl2H C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)))
    (hB : B ∈ Submodule.span C
      ({sl2H C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C))) :
    A * B - B * A ∈
      Submodule.span C ({sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  rw [Submodule.mem_span_pair] at hA hB
  obtain ⟨a, b, rfl⟩ := hA
  obtain ⟨c, d, rfl⟩ := hB
  rw [Submodule.mem_span_singleton]
  refine ⟨2 * (b * c - a * d), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2H, sl2F] <;> ring

omit [CharZero C] in
/-- Conjugating a two-sided inverse pair by a two-sided inverse pair preserves both inverse
identities. -/
theorem conjugated_two_sided_inverse
    (P Q g g' : Matrix (Fin 2) (Fin 2) C)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) :
    (Q * g * P) * (Q * g' * P) = 1 ∧
      (Q * g' * P) * (Q * g * P) = 1 := by
  constructor
  · calc
      (Q * g * P) * (Q * g' * P) =
          Q * g * (P * Q) * g' * P := by noncomm_ring
      _ = Q * (g * g') * P := by rw [hPQ]; simp only [mul_one, mul_assoc]
      _ = 1 := by rw [hgg', mul_one, hQP]
  · calc
      (Q * g' * P) * (Q * g * P) =
          Q * g' * (P * Q) * g * P := by noncomm_ring
      _ = Q * (g' * g) * P := by rw [hPQ]; simp only [mul_one, mul_assoc]
      _ = 1 := by rw [hg'g, mul_one, hQP]

omit [CharZero C] in
/-- Adjoint stability transports through a constant change of basis. -/
theorem conj_mem_mapped_submodule_of_conj_mem
    (V : Submodule C (Matrix (Fin 2) (Fin 2) C))
    (P Q g g' : Matrix (Fin 2) (Fin 2) C) (hPQ : P * Q = 1)
    {A : Matrix (Fin 2) (Fin 2) C}
    (hA : A ∈ V.map (conjLinear C Q P))
    (hstable : ∀ B ∈ V, g * B * g' ∈ V) :
    (Q * g * P) * A * (Q * g' * P) ∈ V.map (conjLinear C Q P) := by
  obtain ⟨B, hB, rfl⟩ := hA
  refine ⟨g * B * g', hstable B hB, ?_⟩
  simp only [conjLinear_apply]
  calc
    Q * (g * B * g') * P =
        Q * g * (P * Q) * B * (P * Q) * g' * P := by
      rw [hPQ]
      simp only [mul_one, mul_assoc]
    _ = (Q * g * P) * (Q * B * P) * (Q * g' * P) := by noncomm_ring

omit [CharZero C] in
/-- Traceless matrices are precisely contained in the coordinate span of `H,E,F`. -/
theorem mem_span_sl2_of_trace_eq_zero
    {A : Matrix (Fin 2) (Fin 2) C} (hA : A.trace = 0) :
    A ∈ Submodule.span C
      ({sl2H C, sl2E C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  rw [traceless_decomp hA]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

omit [CharZero C] in
/-- A proper traceless submodule cannot become all of `sl₂` after an invertible conjugation. -/
theorem map_ne_span_sl2_of_traceless_witness
    (V : Submodule C (Matrix (Fin 2) (Fin 2) C))
    (P Q : Matrix (Fin 2) (Fin 2) C) (hPQ : P * Q = 1)
    (hproper : ∃ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 ∧ Z ∉ V) :
    V.map (conjLinear C Q P) ≠ Submodule.span C
      ({sl2H C, sl2E C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  intro hfull
  obtain ⟨Z, hZtr, hZnot⟩ := hproper
  have hconjtr : (Q * Z * P).trace = 0 := by
    rw [Matrix.trace_mul_cycle, hPQ, one_mul, hZtr]
  have hconjmem : Q * Z * P ∈ V.map (conjLinear C Q P) := by
    rw [hfull]
    exact mem_span_sl2_of_trace_eq_zero hconjtr
  obtain ⟨B, hB, hBZ⟩ := hconjmem
  apply hZnot
  have hback := congrArg (fun A => P * A * Q) hBZ
  have hBZ' : B = Z := by
    have heq : P * (Q * B * P) * Q = P * (Q * Z * P) * Q := by
      simpa only [conjLinear_apply] using hback
    calc
      B = (P * Q) * B * (P * Q) := by rw [hPQ]; simp
      _ = P * (Q * B * P) * Q := by noncomm_ring
      _ = P * (Q * Z * P) * Q := heq
      _ = (P * Q) * Z * (P * Q) := by noncomm_ring
      _ = Z := by rw [hPQ]; simp
  rwa [← hBZ']

omit [CharZero C] in
/-- Commutators commute with conjugation by a two-sided inverse pair. -/
theorem conjugated_bracket
    (g g' A B : Matrix (Fin 2) (Fin 2) C) (hg'g : g' * g = 1) :
    (g * A * g') * (g * B * g') - (g * B * g') * (g * A * g') =
      g * (A * B - B * A) * g' := by
  calc
    (g * A * g') * (g * B * g') - (g * B * g') * (g * A * g') =
        g * A * (g' * g) * B * g' - g * B * (g' * g) * A * g' := by
      noncomm_ring
    _ = g * (A * B - B * A) * g' := by rw [hg'g]; noncomm_ring

/-- Preserving the upper Borel by conjugation preserves its nilpotent radical. -/
theorem conj_E_mem_span_of_conj_H_E_mem_span_H_E
    (g g' : Matrix (Fin 2) (Fin 2) C) (hg'g : g' * g = 1)
    (hH : g * sl2H C * g' ∈ Submodule.span C
      ({sl2H C, sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)))
    (hE : g * sl2E C * g' ∈ Submodule.span C
      ({sl2H C, sl2E C} : Set (Matrix (Fin 2) (Fin 2) C))) :
    g * sl2E C * g' ∈
      Submodule.span C ({sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  have hcomm := bracket_mem_span_E_of_mem_span_H_E hH hE
  rw [conjugated_bracket g g' (sl2H C) (sl2E C) hg'g] at hcomm
  have hHE : sl2H C * sl2E C - sl2E C * sl2H C = (2 : C) • sl2E C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2H, sl2E, one_add_one_eq_two]
  rw [hHE, Matrix.mul_smul, Matrix.smul_mul] at hcomm
  have hs := (Submodule.span C
    ({sl2E C} : Set (Matrix (Fin 2) (Fin 2) C))).smul_mem (2 : C)⁻¹ hcomm
  simpa [smul_smul] using hs

/-- Preserving the lower Borel by conjugation preserves its nilpotent radical. -/
theorem conj_F_mem_span_of_conj_H_F_mem_span_H_F
    (g g' : Matrix (Fin 2) (Fin 2) C) (hg'g : g' * g = 1)
    (hH : g * sl2H C * g' ∈ Submodule.span C
      ({sl2H C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)))
    (hF : g * sl2F C * g' ∈ Submodule.span C
      ({sl2H C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C))) :
    g * sl2F C * g' ∈
      Submodule.span C ({sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
  have hcomm := bracket_mem_span_F_of_mem_span_H_F hH hF
  rw [conjugated_bracket g g' (sl2H C) (sl2F C) hg'g] at hcomm
  have hHF : sl2H C * sl2F C - sl2F C * sl2H C = (-2 : C) • sl2F C := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2H, sl2F]
    linear_combination
  rw [hHF, Matrix.mul_smul, Matrix.smul_mul] at hcomm
  have hs := (Submodule.span C
    ({sl2F C} : Set (Matrix (Fin 2) (Fin 2) C))).smul_mem (-2 : C)⁻¹ hcomm
  simpa [smul_smul] using hs

/-- A matrix family has a common invariant coordinate line after one change of basis.  The two
alternatives record the two coordinate orientations. -/
def HasInvariantLineNormalForm (G : Set (Matrix (Fin 2) (Fin 2) C)) : Prop :=
  ∃ P Q : Matrix (Fin 2) (Fin 2) C,
    P * Q = 1 ∧ Q * P = 1 ∧
      ((∀ g ∈ G, (Q * g * P) 1 0 = 0) ∨
        ∀ g ∈ G, (Q * g * P) 0 1 = 0)

/-- A matrix family preserves the unordered pair of coordinate lines after one change of basis. -/
def HasInvariantPairNormalForm (G : Set (Matrix (Fin 2) (Fin 2) C)) : Prop :=
  ∃ P Q : Matrix (Fin 2) (Fin 2) C,
    P * Q = 1 ∧ Q * P = 1 ∧
      ∀ g ∈ G,
        ((Q * g * P) 0 1 = 0 ∧ (Q * g * P) 1 0 = 0) ∨
          ((Q * g * P) 0 0 = 0 ∧ (Q * g * P) 1 1 = 0)

/-- A nonzero proper adjoint-stable Lie subalgebra of `sl₂` forces either a common invariant line
or an invariant unordered pair of lines.  No dimension assumption is used. -/
theorem invariant_normalForm_of_nonzero_proper_adjoint_stable [IsAlgClosed C]
    (V : Submodule C (Matrix (Fin 2) (Fin 2) C))
    (htr : ∀ A ∈ V, A.trace = 0)
    (hbr : ∀ A ∈ V, ∀ B ∈ V, A * B - B * A ∈ V)
    (hne : ∃ X ∈ V, X ≠ 0)
    (hproper : ∃ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 ∧ Z ∉ V)
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hinv : ∀ g ∈ G, ∃ g' : Matrix (Fin 2) (Fin 2) C,
      g * g' = 1 ∧ g' * g = 1)
    (hstable : ∀ g ∈ G, ∀ g' : Matrix (Fin 2) (Fin 2) C,
      g * g' = 1 → g' * g = 1 → ∀ A ∈ V, g * A * g' ∈ V) :
    HasInvariantLineNormalForm G ∨ HasInvariantPairNormalForm G := by
  classical
  rcases sl2_nonzero_subalgebra_classification V htr hbr hne with
    hnil | ⟨μ, P, Q, hμ, hPQ, hQP, hcases⟩
  · obtain ⟨X, hX, hXne, hXdet, hV⟩ := hnil
    obtain ⟨P, Q, hPQ, hQP, hQXP⟩ :=
      exists_conj_eq_E_of_trace_eq_zero_of_det_eq_zero X (htr X hX) hXdet hXne
    have hW : V.map (conjLinear C Q P) =
        Submodule.span C ({sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
      apply le_antisymm
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := hA
        rw [hV] at hB
        change B ∈ Submodule.span C
          ({X} : Set (Matrix (Fin 2) (Fin 2) C)) at hB
        rw [Submodule.mem_span_singleton] at hB
        obtain ⟨c, rfl⟩ := hB
        rw [Submodule.mem_span_singleton]
        refine ⟨c, ?_⟩
        simp only [conjLinear_apply, Matrix.mul_smul, Matrix.smul_mul, hQXP]
      · rw [Submodule.span_le]
        intro A hA
        have hAE : A = sl2E C := by simpa only [Set.mem_singleton_iff] using hA
        subst A
        exact ⟨X, hX, by simpa only [conjLinear_apply] using hQXP⟩
    left
    refine ⟨P, Q, hPQ, hQP, Or.inl ?_⟩
    intro g hg
    obtain ⟨g', hgg', hg'g⟩ := hinv g hg
    obtain ⟨htinv, hinvt⟩ := conjugated_two_sided_inverse P Q g g' hPQ hQP hgg' hg'g
    have hEmem : sl2E C ∈ V.map (conjLinear C Q P) := by
      rw [hW]
      exact Submodule.subset_span (by simp)
    have hconj := conj_mem_mapped_submodule_of_conj_mem V P Q g g' hPQ hEmem
      (hstable g hg g' hgg' hg'g)
    rw [hW] at hconj
    exact lowerLeft_eq_zero_of_conj_E_mem_span (Q * g * P) (Q * g' * P) hinvt hconj
  · let W := V.map (conjLinear C Q P)
    change W = Submodule.span C ({sl2H C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
      W = Submodule.span C
        ({sl2H C, sl2E C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
      W = Submodule.span C
        ({sl2H C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) ∨
      W = Submodule.span C
        ({sl2H C, sl2E C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) at hcases
    have hnotfull : W ≠ Submodule.span C
        ({sl2H C, sl2E C, sl2F C} : Set (Matrix (Fin 2) (Fin 2) C)) := by
      exact map_ne_span_sl2_of_traceless_witness V P Q hPQ hproper
    rcases hcases with hW | hW | hW | hW
    · right
      refine ⟨P, Q, hPQ, hQP, ?_⟩
      intro g hg
      obtain ⟨g', hgg', hg'g⟩ := hinv g hg
      obtain ⟨htinv, hinvt⟩ :=
        conjugated_two_sided_inverse P Q g g' hPQ hQP hgg' hg'g
      have hHmem : sl2H C ∈ W := by
        rw [hW]
        exact Submodule.subset_span (by simp)
      have hconj := conj_mem_mapped_submodule_of_conj_mem V P Q g g' hPQ hHmem
        (hstable g hg g' hgg' hg'g)
      change Q * g * P * sl2H C * (Q * g' * P) ∈ W at hconj
      rw [hW] at hconj
      exact diagonal_or_antidiagonal_of_conj_H_mem_span
        (Q * g * P) (Q * g' * P) htinv hinvt hconj
    · left
      refine ⟨P, Q, hPQ, hQP, Or.inl ?_⟩
      intro g hg
      obtain ⟨g', hgg', hg'g⟩ := hinv g hg
      obtain ⟨htinv, hinvt⟩ :=
        conjugated_two_sided_inverse P Q g g' hPQ hQP hgg' hg'g
      have hHmem : sl2H C ∈ W := by
        rw [hW]
        exact Submodule.subset_span (by simp)
      have hEmem : sl2E C ∈ W := by
        rw [hW]
        exact Submodule.subset_span (by simp)
      have hconjH := conj_mem_mapped_submodule_of_conj_mem V P Q g g' hPQ hHmem
        (hstable g hg g' hgg' hg'g)
      have hconjE := conj_mem_mapped_submodule_of_conj_mem V P Q g g' hPQ hEmem
        (hstable g hg g' hgg' hg'g)
      change Q * g * P * sl2H C * (Q * g' * P) ∈ W at hconjH
      change Q * g * P * sl2E C * (Q * g' * P) ∈ W at hconjE
      rw [hW] at hconjH hconjE
      have hrad := conj_E_mem_span_of_conj_H_E_mem_span_H_E
        (Q * g * P) (Q * g' * P) hinvt hconjH hconjE
      exact lowerLeft_eq_zero_of_conj_E_mem_span
        (Q * g * P) (Q * g' * P) hinvt hrad
    · left
      refine ⟨P, Q, hPQ, hQP, Or.inr ?_⟩
      intro g hg
      obtain ⟨g', hgg', hg'g⟩ := hinv g hg
      obtain ⟨htinv, hinvt⟩ :=
        conjugated_two_sided_inverse P Q g g' hPQ hQP hgg' hg'g
      have hHmem : sl2H C ∈ W := by
        rw [hW]
        exact Submodule.subset_span (by simp)
      have hFmem : sl2F C ∈ W := by
        rw [hW]
        exact Submodule.subset_span (by simp)
      have hconjH := conj_mem_mapped_submodule_of_conj_mem V P Q g g' hPQ hHmem
        (hstable g hg g' hgg' hg'g)
      have hconjF := conj_mem_mapped_submodule_of_conj_mem V P Q g g' hPQ hFmem
        (hstable g hg g' hgg' hg'g)
      change Q * g * P * sl2H C * (Q * g' * P) ∈ W at hconjH
      change Q * g * P * sl2F C * (Q * g' * P) ∈ W at hconjF
      rw [hW] at hconjH hconjF
      have hrad := conj_F_mem_span_of_conj_H_F_mem_span_H_F
        (Q * g * P) (Q * g' * P) hinvt hconjH hconjF
      exact upperRight_eq_zero_of_conj_F_mem_span
        (Q * g * P) (Q * g' * P) hinvt hrad
    · exact (hnotfull hW).elim

end


end GaloisForLFunctions.HTGeometry
