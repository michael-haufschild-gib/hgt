import GaloisForLFunctions.HTGeometry.CassidySl2Classification

/-!
# Cassidy's classification for `M₂`, and for matrix groups

A `C`-subalgebra `A` of `M₂(U)` whose `U`-span is everything and whose `U`-line stabilisers are
trivial is conjugate to `M₂(C)`.  The commutators `[A, A]` lie in the traceless part `A ∩ sl₂(U)`
and `U`-span `sl₂(U)`, so the classification for `sl₂` applies to that part; conjugating it to
`sl₂(C)` and bracketing an arbitrary element of `A` against `e` and `f` reads its off-diagonal and
toral coordinates out of `C`, and the line stabiliser of `1` reads the scalar coordinate.

The consequence for a multiplicative set `G` of matrices is the form used in Galois theory: if `G`
spans `M₂(U)` and the `C`-span of `G` has trivial line stabilisers, then one conjugation puts every
element of `G` in `M₂(C)`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C U : Type*} [Field C] [Field U] [Algebra C U]

/-- The trace, as a `C`-linear map. -/
def traceLinear (C : Type*) [Field C] {U : Type*} [Field U] [Algebra C U] :
    Matrix (Fin 2) (Fin 2) U →ₗ[C] U where
  toFun Z := Z.trace
  map_add' Z W := by rw [Matrix.trace_add]
  map_smul' c Z := by
    simp only [RingHom.id_apply]
    rw [Matrix.trace_smul]

@[simp] theorem traceLinear_apply (Z : Matrix (Fin 2) (Fin 2) U) :
    traceLinear C Z = Z.trace := rfl

/-- Matrices with entries in the base field, in the `1, h, e, f` basis. -/
theorem matrix_decomp_one_hef [CharZero U] (Z : Matrix (Fin 2) (Fin 2) U) :
    Z = ((Z 0 0 + Z 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) U)
      + ((Z 0 0 - Z 1 1) / 2) • sl2H U + (Z 0 1) • sl2E U + (Z 1 0) • sl2F U := by
  have h2 : (2 : U) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] <;>
    simp [sl2H, sl2E, sl2F] <;> field_simp <;> ring

theorem mem_span_hef_iff [CharZero U] {Z : Matrix (Fin 2) (Fin 2) U} :
    Z ∈ Submodule.span C ({sl2H U, sl2E U, sl2F U} : Set (Matrix (Fin 2) (Fin 2) U)) ↔
      Z.trace = 0 ∧ ∀ i j, ∃ c : C, Z i j = algebraMap C U c := by
  constructor
  · intro hZ
    induction hZ using Submodule.span_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · refine ⟨by simp [sl2H, Matrix.trace_fin_two], fun i j => ?_⟩
          fin_cases i <;> fin_cases j <;>
            simp [sl2H] <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩; exact ⟨0, by simp⟩;
              exact ⟨-1, by simp⟩]
        · refine ⟨by simp [sl2E, Matrix.trace_fin_two], fun i j => ?_⟩
          fin_cases i <;> fin_cases j <;> simp [sl2E] <;>
            [exact ⟨0, by simp⟩; exact ⟨1, by simp⟩; exact ⟨0, by simp⟩; exact ⟨0, by simp⟩]
        · refine ⟨by simp [sl2F, Matrix.trace_fin_two], fun i j => ?_⟩
          fin_cases i <;> fin_cases j <;> simp [sl2F] <;>
            [exact ⟨0, by simp⟩; exact ⟨0, by simp⟩; exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
    | zero => exact ⟨by simp, fun i j => ⟨0, by simp⟩⟩
    | add x y _ _ hx hy =>
        refine ⟨by rw [Matrix.trace_add, hx.1, hy.1, add_zero], fun i j => ?_⟩
        obtain ⟨c, hc⟩ := hx.2 i j
        obtain ⟨d, hd⟩ := hy.2 i j
        exact ⟨c + d, by rw [Matrix.add_apply, hc, hd, map_add]⟩
    | smul a x _ hx =>
        refine ⟨?_, fun i j => ?_⟩
        · rw [Matrix.trace_smul, hx.1, smul_zero]
        · obtain ⟨c, hc⟩ := hx.2 i j
          exact ⟨a * c, by rw [Matrix.smul_apply, hc, map_mul, Algebra.smul_def]⟩
  · rintro ⟨htr, hent⟩
    obtain ⟨a, ha⟩ := hent 0 0
    obtain ⟨b, hb⟩ := hent 0 1
    obtain ⟨c, hc⟩ := hent 1 0
    have h11 : Z 1 1 = -(Z 0 0) := by
      rw [Matrix.trace_fin_two] at htr
      linear_combination htr
    have hdecomp : Z = (Z 0 0) • sl2H U + (Z 0 1) • sl2E U + (Z 1 0) • sl2F U := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2H, sl2E, sl2F, h11]
    rw [hdecomp, ha, hb, hc]
    have hs1 : sl2H U ∈ Submodule.span C ({sl2H U, sl2E U, sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    have hs2 : sl2E U ∈ Submodule.span C ({sl2H U, sl2E U, sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    have hs3 : sl2F U ∈ Submodule.span C ({sl2H U, sl2E U, sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      rw [algebraMap_smul U] <;>
      exact Submodule.smul_mem _ _ (by assumption)

theorem mem_span_one_hef_iff [CharZero U] {Z : Matrix (Fin 2) (Fin 2) U} :
    Z ∈ Submodule.span C ({1, sl2H U, sl2E U, sl2F U} : Set (Matrix (Fin 2) (Fin 2) U)) ↔
      ∀ i j, ∃ c : C, Z i j = algebraMap C U c := by
  constructor
  · intro hZ
    induction hZ using Submodule.span_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        intro i j
        rcases hx with rfl | rfl | rfl | rfl
        · fin_cases i <;> fin_cases j <;> simp <;>
            [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩; exact ⟨0, by simp⟩; exact ⟨1, by simp⟩]
        · fin_cases i <;> fin_cases j <;> simp [sl2H] <;>
            [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩; exact ⟨0, by simp⟩; exact ⟨-1, by simp⟩]
        · fin_cases i <;> fin_cases j <;> simp [sl2E] <;>
            [exact ⟨0, by simp⟩; exact ⟨1, by simp⟩; exact ⟨0, by simp⟩; exact ⟨0, by simp⟩]
        · fin_cases i <;> fin_cases j <;> simp [sl2F] <;>
            [exact ⟨0, by simp⟩; exact ⟨0, by simp⟩; exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
    | zero => exact fun i j => ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        intro i j
        obtain ⟨c, hc⟩ := hx i j
        obtain ⟨d, hd⟩ := hy i j
        exact ⟨c + d, by rw [Matrix.add_apply, hc, hd, map_add]⟩
    | smul a x _ hx =>
        intro i j
        obtain ⟨c, hc⟩ := hx i j
        exact ⟨a * c, by rw [Matrix.smul_apply, hc, map_mul, Algebra.smul_def]⟩
  · intro hent
    obtain ⟨a, ha⟩ := hent 0 0
    obtain ⟨b, hb⟩ := hent 0 1
    obtain ⟨c, hc⟩ := hent 1 0
    obtain ⟨d, hd⟩ := hent 1 1
    have hdecomp := matrix_decomp_one_hef Z
    have hα : (Z 0 0 + Z 1 1) / 2 = algebraMap C U ((a + d) / 2) := by
      rw [map_div₀, map_add, map_ofNat, ha, hd]
    have hδ : (Z 0 0 - Z 1 1) / 2 = algebraMap C U ((a - d) / 2) := by
      rw [map_div₀, map_sub, map_ofNat, ha, hd]
    rw [hdecomp, hα, hδ, hb, hc]
    have hs0 : (1 : Matrix (Fin 2) (Fin 2) U) ∈ Submodule.span C
        ({1, sl2H U, sl2E U, sl2F U} : Set (Matrix (Fin 2) (Fin 2) U)) :=
      Submodule.subset_span (by simp)
    have hs1 : sl2H U ∈ Submodule.span C ({1, sl2H U, sl2E U, sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    have hs2 : sl2E U ∈ Submodule.span C ({1, sl2H U, sl2E U, sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    have hs3 : sl2F U ∈ Submodule.span C ({1, sl2H U, sl2E U, sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      rw [algebraMap_smul U] <;>
      exact Submodule.smul_mem _ _ (by assumption)

/-- **Cassidy's classification for `M₂`.**  A `C`-subalgebra of `M₂(U)` that `U`-spans and has
trivial `U`-line stabilisers is conjugate to `M₂(C)`. -/
theorem cassidy_matrixAlgebra [IsAlgClosed C] [IsAlgClosed U] [CharZero U]
    (A : Submodule C (Matrix (Fin 2) (Fin 2) U))
    (hone : (1 : Matrix (Fin 2) (Fin 2) U) ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A)
    (hspan : ∀ Z : Matrix (Fin 2) (Fin 2) U,
      Z ∈ Submodule.span U (A : Set (Matrix (Fin 2) (Fin 2) U)))
    (hline : ∀ c : U, c • (1 : Matrix (Fin 2) (Fin 2) U) ∈ A →
      ∃ c₀ : C, c = algebraMap C U c₀) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) U, P * Q = 1 ∧ Q * P = 1 ∧
      A.map (conjLinear C P Q)
        = Submodule.span C {1, sl2H U, sl2E U, sl2F U} := by
  classical
  set L : Submodule C (Matrix (Fin 2) (Fin 2) U) := A ⊓ LinearMap.ker (traceLinear C) with hLdef
  have hLmem : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z ∈ L ↔ Z ∈ A ∧ Z.trace = 0 := by
    intro Z
    rw [hLdef, Submodule.mem_inf, LinearMap.mem_ker, traceLinear_apply]
  have hLle : L ≤ A := fun _ hZ => ((hLmem _).mp hZ).1
  have htrL : ∀ Z ∈ L, Z.trace = 0 := fun Z hZ => ((hLmem Z).mp hZ).2
  have hbrL : ∀ Z ∈ L, ∀ W ∈ L, Z * W - W * Z ∈ L := by
    intro Z hZ W hW
    obtain ⟨hZA, -⟩ := (hLmem Z).mp hZ
    obtain ⟨hWA, -⟩ := (hLmem W).mp hW
    refine (hLmem _).mpr ⟨A.sub_mem (hmul Z hZA W hWA) (hmul W hWA Z hZA), ?_⟩
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have hcomm : ∀ a ∈ A, ∀ x ∈ Submodule.span U (A : Set (Matrix (Fin 2) (Fin 2) U)),
      x * a - a * x ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) := by
    intro a ha x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        refine Submodule.subset_span ((hLmem _).mpr ⟨A.sub_mem (hmul y hy a ha) (hmul a ha y hy),
          ?_⟩)
        rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    | zero => simp
    | add y z _ _ hy hz =>
        have heq : (y + z) * a - a * (y + z) = (y * a - a * y) + (z * a - a * z) := by
          rw [Matrix.add_mul, Matrix.mul_add]
          abel
        rw [heq]
        exact Submodule.add_mem _ hy hz
    | smul u y _ hy =>
        have heq : (u • y) * a - a * (u • y) = u • (y * a - a * y) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
        rw [heq]
        exact Submodule.smul_mem _ _ hy
  have hcomm2 : ∀ x y : Matrix (Fin 2) (Fin 2) U,
      x * y - y * x ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) := by
    intro x y
    have hy := hspan y
    induction hy using Submodule.span_induction with
    | mem b hb => exact hcomm b hb x (hspan x)
    | zero => simp
    | add w z _ _ hw hz =>
        have heq : x * (w + z) - (w + z) * x = (x * w - w * x) + (x * z - z * x) := by
          rw [Matrix.add_mul, Matrix.mul_add]
          abel
        rw [heq]
        exact Submodule.add_mem _ hw hz
    | smul u w _ hw =>
        have heq : x * (u • w) - (u • w) * x = u • (x * w - w * x) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
        rw [heq]
        exact Submodule.smul_mem _ _ hw
  have hHspan : sl2H U ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) := by
    have h := hcomm2 (sl2E U) (sl2F U)
    have heq : sl2E U * sl2F U - sl2F U * sl2E U = sl2H U := by
      have h1 := sl2_bracket_smul_E_F (1 : U) (1 : U)
      simpa using h1
    rwa [heq] at h
  have hEspan : sl2E U ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) := by
    have h := Submodule.smul_mem _ ((2 : U)⁻¹) (hcomm2 (sl2H U) (sl2E U))
    have heq : ((2 : U)⁻¹) • (sl2H U * sl2E U - sl2E U * sl2H U) = sl2E U := by
      have h1 := bracket_toral (1 : U) (sl2E U)
      have h2 : (1 : U) • sl2H U = sl2H U := one_smul _ _
      rw [h2] at h1
      rw [h1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;>
        simp [sl2E, sl2F]
    rwa [heq] at h
  have hFspan : sl2F U ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) := by
    have h := Submodule.smul_mem _ (-((2 : U)⁻¹)) (hcomm2 (sl2H U) (sl2F U))
    have heq : (-((2 : U)⁻¹)) • (sl2H U * sl2F U - sl2F U * sl2H U) = sl2F U := by
      have h1 := bracket_toral (1 : U) (sl2F U)
      have h2 : (1 : U) • sl2H U = sl2H U := one_smul _ _
      rw [h2] at h1
      rw [h1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;>
        simp [sl2E, sl2F]
    rwa [heq] at h
  have hdenseL : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) := by
    intro Z hZ
    rw [traceless_decomp hZ]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hHspan)
      (Submodule.smul_mem _ _ hEspan)) (Submodule.smul_mem _ _ hFspan)
  have hCH : ∀ W : Matrix (Fin 2) (Fin 2) U, W.trace = 0 →
      W * W = (-W.det) • (1 : Matrix (Fin 2) (Fin 2) U) := by
    intro W hW
    have h11 : W 1 1 = -(W 0 0) := by
      rw [Matrix.trace_fin_two] at hW
      linear_combination hW
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
        Matrix.det_fin_two] <;>
      simp [h11] <;> ring
  have hlineL : ∀ Z ∈ L, Z.det ≠ 0 → ∀ c : U, c • Z ∈ L → ∃ c₀ : C, c = algebraMap C U c₀ := by
    intro Z hZ hZdet c hc
    obtain ⟨hZA, hZtr⟩ := (hLmem Z).mp hZ
    obtain ⟨hcZA, hcZtr⟩ := (hLmem _).mp hc
    have hsq1 : (-Z.det) • (1 : Matrix (Fin 2) (Fin 2) U) ∈ A := by
      rw [← hCH Z hZtr]
      exact hmul Z hZA Z hZA
    obtain ⟨d₀, hd₀⟩ := hline _ hsq1
    have hdetcz : (c • Z).det = c ^ (2 : ℕ) * Z.det := by
      simp only [Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
      ring
    have hsq2 : (-(c ^ (2 : ℕ) * Z.det)) • (1 : Matrix (Fin 2) (Fin 2) U) ∈ A := by
      rw [← hdetcz, ← hCH _ hcZtr]
      exact hmul _ hcZA _ hcZA
    obtain ⟨e₀, he₀⟩ := hline _ hsq2
    have hd₀ne : d₀ ≠ 0 := by
      intro h0
      apply hZdet
      rw [h0, map_zero] at hd₀
      linear_combination -hd₀
    have hd₀U : algebraMap C U d₀ ≠ 0 := by
      simpa using (map_ne_zero_iff (algebraMap C U) (algebraMap C U).injective).mpr hd₀ne
    have hc2 : c ^ (2 : ℕ) * algebraMap C U d₀ = algebraMap C U e₀ := by
      linear_combination he₀ - c ^ (2 : ℕ) * hd₀
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (e₀ / d₀) (n := 2) (by norm_num)
    have hsq : (algebraMap C U r) ^ (2 : ℕ) = c ^ (2 : ℕ) := by
      rw [← map_pow, hr, map_div₀, div_eq_iff hd₀U]
      exact hc2.symm
    have hfac : (c - algebraMap C U r) * (c + algebraMap C U r) = 0 := by
      linear_combination -hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨r, by linear_combination h⟩
    · exact ⟨-r, by rw [map_neg]; linear_combination h⟩
  obtain ⟨P, Q, hPQ, hQP, hLeq⟩ := cassidy_sl2 L htrL hbrL hdenseL hlineL
  refine ⟨P, Q, hPQ, hQP, ?_⟩
  have hA'mul : ∀ a ∈ A.map (conjLinear C P Q), ∀ b ∈ A.map (conjLinear C P Q),
      a * b ∈ A.map (conjLinear C P Q) := by
    rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    refine ⟨x * y, hmul x hx y hy, ?_⟩
    show P * (x * y) * Q = (P * x * Q) * (P * y * Q)
    rw [conj_mul_conj hQP]
  have hA'one : (1 : Matrix (Fin 2) (Fin 2) U) ∈ A.map (conjLinear C P Q) := by
    refine ⟨1, hone, ?_⟩
    show P * 1 * Q = 1
    rw [mul_one, hPQ]
  have hA'line : ∀ c : U, c • (1 : Matrix (Fin 2) (Fin 2) U) ∈ A.map (conjLinear C P Q) →
      ∃ c₀ : C, c = algebraMap C U c₀ := by
    intro c hc
    obtain ⟨y, hy, hyeq⟩ := hc
    have hy1 : y = c • (1 : Matrix (Fin 2) (Fin 2) U) := by
      have h1 : Q * (P * y * Q) * P = y := conj_conj_eq hQP y
      have h2 : P * y * Q = c • (1 : Matrix (Fin 2) (Fin 2) U) := hyeq
      rw [h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQP] at h1
      exact h1.symm
    exact hline c (hy1 ▸ hy)
  have hsplitA : ∀ Z ∈ A.map (conjLinear C P Q), Z.trace = 0 →
      Z ∈ Submodule.span C ({sl2H U, sl2E U, sl2F U} : Set (Matrix (Fin 2) (Fin 2) U)) := by
    rintro Z ⟨Y, hY, rfl⟩ htrZ
    rw [← hLeq]
    refine ⟨Y, (hLmem Y).mpr ⟨hY, ?_⟩, rfl⟩
    rw [conjLinear_apply] at htrZ
    have hcomm' : (P * Y * Q).trace = (Q * P * Y).trace := by
      rw [Matrix.trace_mul_comm (P * Y) Q, mul_assoc]
    rw [hcomm', hQP, one_mul] at htrZ
    exact htrZ
  have hhefle : Submodule.span C ({sl2H U, sl2E U, sl2F U} :
      Set (Matrix (Fin 2) (Fin 2) U)) ≤ A.map (conjLinear C P Q) := by
    rw [← hLeq]
    exact Submodule.map_mono hLle
  refine le_antisymm ?_ ?_
  · intro Z hZ
    have hEmem : sl2E U ∈ A.map (conjLinear C P Q) :=
      hhefle (Submodule.subset_span (by simp))
    have hFmem : sl2F U ∈ A.map (conjLinear C P Q) :=
      hhefle (Submodule.subset_span (by simp))
    have hHmem : sl2H U ∈ A.map (conjLinear C P Q) :=
      hhefle (Submodule.subset_span (by simp))
    have hZe : Z * sl2E U - sl2E U * Z ∈
        Submodule.span C ({sl2H U, sl2E U, sl2F U} : Set (Matrix (Fin 2) (Fin 2) U)) := by
      refine hsplitA _ (Submodule.sub_mem _ (hA'mul _ hZ _ hEmem) (hA'mul _ hEmem _ hZ)) ?_
      rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    have hZf : Z * sl2F U - sl2F U * Z ∈
        Submodule.span C ({sl2H U, sl2E U, sl2F U} : Set (Matrix (Fin 2) (Fin 2) U)) := by
      refine hsplitA _ (Submodule.sub_mem _ (hA'mul _ hZ _ hFmem) (hA'mul _ hFmem _ hZ)) ?_
      rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    obtain ⟨-, hZeent⟩ := mem_span_hef_iff.mp hZe
    obtain ⟨-, hZfent⟩ := mem_span_hef_iff.mp hZf
    obtain ⟨c₁, hc₁⟩ := hZeent 0 0
    obtain ⟨c₂, hc₂⟩ := hZeent 0 1
    obtain ⟨c₃, hc₃⟩ := hZfent 0 0
    have he00 : (Z * sl2E U - sl2E U * Z) 0 0 = -(Z 1 0) := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      simp [sl2E]
    have he01 : (Z * sl2E U - sl2E U * Z) 0 1 = Z 0 0 - Z 1 1 := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      simp [sl2E]
    have hf00 : (Z * sl2F U - sl2F U * Z) 0 0 = Z 0 1 := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      simp [sl2F]
    rw [he00] at hc₁
    rw [he01] at hc₂
    rw [hf00] at hc₃
    have hZ10 : Z 1 0 = algebraMap C U (-c₁) := by rw [map_neg, ← hc₁, neg_neg]
    have hZ01 : Z 0 1 = algebraMap C U c₃ := hc₃
    have hδ : (Z 0 0 - Z 1 1) / 2 = algebraMap C U (c₂ / 2) := by
      rw [map_div₀, map_ofNat, ← hc₂]
    have hmemsub : Z - (Z 0 1) • sl2E U - (Z 1 0) • sl2F U - ((Z 0 0 - Z 1 1) / 2) • sl2H U
        ∈ A.map (conjLinear C P Q) := by
      refine Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hZ ?_) ?_) ?_
      · rw [hZ01, algebraMap_smul U]
        exact Submodule.smul_mem _ _ hEmem
      · rw [hZ10, algebraMap_smul U]
        exact Submodule.smul_mem _ _ hFmem
      · rw [hδ, algebraMap_smul U]
        exact Submodule.smul_mem _ _ hHmem
    have hone_eq : Z - (Z 0 1) • sl2E U - (Z 1 0) • sl2F U - ((Z 0 0 - Z 1 1) / 2) • sl2H U
        = ((Z 0 0 + Z 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) U) := by
      have hd := matrix_decomp_one_hef Z
      rw [hd]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          Matrix.one_apply] <;>
        simp [sl2H, sl2E, sl2F] <;> ring
    rw [hone_eq] at hmemsub
    obtain ⟨c₀, hc₀⟩ := hA'line _ hmemsub
    refine mem_span_one_hef_iff.mpr ?_
    intro i j
    have h00 : Z 0 0 = algebraMap C U (c₀ + c₂ / 2) := by
      rw [map_add, ← hc₀, map_div₀, map_ofNat, ← hc₂]
      field_simp
      ring
    have h11 : Z 1 1 = algebraMap C U (c₀ - c₂ / 2) := by
      rw [map_sub, ← hc₀, map_div₀, map_ofNat, ← hc₂]
      field_simp
      ring
    fin_cases i <;> fin_cases j
    · exact ⟨_, h00⟩
    · exact ⟨_, hZ01⟩
    · exact ⟨_, hZ10⟩
    · exact ⟨_, h11⟩
  · rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hA'one
    · exact hhefle (Submodule.subset_span (by simp))
    · exact hhefle (Submodule.subset_span (by simp))
    · exact hhefle (Submodule.subset_span (by simp))

/-- The `C`-span of a multiplicatively closed set of matrices is closed under multiplication. -/
theorem mul_mem_span_of_mul_mem (G : Set (Matrix (Fin 2) (Fin 2) U))
    (hmulG : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) :
    ∀ a ∈ Submodule.span C G, ∀ b ∈ Submodule.span C G, a * b ∈ Submodule.span C G := by
  have hGA : G ⊆ (Submodule.span C G : Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span
  have hstep1 : ∀ g ∈ G, ∀ b ∈ Submodule.span C G, g * b ∈ Submodule.span C G := by
    intro g hg b hb
    induction hb using Submodule.span_induction with
    | mem y hy => exact hGA (hmulG g hg y hy)
    | zero => simp
    | add y z _ _ hy hz =>
        rw [Matrix.mul_add]
        exact Submodule.add_mem _ hy hz
    | smul u y _ hy =>
        rw [Matrix.mul_smul]
        exact Submodule.smul_mem _ u hy
  intro a ha b hb
  induction ha using Submodule.span_induction with
  | mem y hy => exact hstep1 y hy b hb
  | zero => simp
  | add y z _ _ hy hz =>
      rw [Matrix.add_mul]
      exact Submodule.add_mem _ hy hz
  | smul u y _ hy =>
      rw [Matrix.smul_mul]
      exact Submodule.smul_mem _ u hy

/-- **A matrix group with trivial line stabilisers becomes constant after one conjugation.**  If a
multiplicative set of matrices spans `M₂(U)` over `U` and its `C`-span has trivial `U`-line
stabilisers, then a single conjugation puts every one of its elements in `M₂(C)`. -/
theorem cassidy_gl2_constant_conjugate [IsAlgClosed C] [IsAlgClosed U] [CharZero U]
    (G : Set (Matrix (Fin 2) (Fin 2) U))
    (hone : (1 : Matrix (Fin 2) (Fin 2) U) ∈ G)
    (hmulG : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    (hspanG : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z ∈ Submodule.span U G)
    (hlineG : ∀ c : U, c • (1 : Matrix (Fin 2) (Fin 2) U) ∈ Submodule.span C G →
      ∃ c₀ : C, c = algebraMap C U c₀) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) U, P * Q = 1 ∧ Q * P = 1 ∧
      ∀ g ∈ G, ∀ i j, ∃ c : C, (P * g * Q) i j = algebraMap C U c := by
  classical
  set A : Submodule C (Matrix (Fin 2) (Fin 2) U) := Submodule.span C G with hAdef
  have hGA : G ⊆ (A : Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span
  have hAone : (1 : Matrix (Fin 2) (Fin 2) U) ∈ A := hGA hone
  have hAmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A := mul_mem_span_of_mul_mem G hmulG
  have hAspan : ∀ Z : Matrix (Fin 2) (Fin 2) U,
      Z ∈ Submodule.span U (A : Set (Matrix (Fin 2) (Fin 2) U)) := by
    intro Z
    exact Submodule.span_mono hGA (hspanG Z)
  obtain ⟨P, Q, hPQ, hQP, hAeq⟩ := cassidy_matrixAlgebra A hAone hAmul hAspan hlineG
  refine ⟨P, Q, hPQ, hQP, ?_⟩
  intro g hg
  have hmem : P * g * Q ∈ A.map (conjLinear C P Q) :=
    Submodule.mem_map_of_mem (hGA hg)
  rw [hAeq] at hmem
  exact mem_span_one_hef_iff.mp hmem

end

end GaloisForLFunctions.HTGeometry
