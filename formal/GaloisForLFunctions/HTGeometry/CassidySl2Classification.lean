import GaloisForLFunctions.HTGeometry.Sl2ToralClassification

/-!
# Cassidy's classification for `sl₂`

A `C`-Lie subalgebra `L` of `sl₂(U)` whose `U`-span is all of `sl₂(U)` and whose `U`-line
stabilisers are trivial is conjugate to `sl₂(C)`, for `C` algebraically closed inside an
algebraically closed `U` of characteristic zero.

The reduction is in three steps.  The span hypothesis puts a matrix of nonzero determinant in `L`;
over an algebraically closed field such a traceless matrix is conjugate to `μ h`; and conjugation
carries all four hypotheses along, so the toral case applies and returns `L` as the `C`-span of
`h`, `v₀ e`, `w₀ f`.  A final conjugation by `diag(1, v₀)` normalises that to the `C`-span of
`h`, `e`, `f`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C U : Type*} [Field C] [Field U] [Algebra C U]


theorem conj_mul_conj {P Q : Matrix (Fin 2) (Fin 2) U} (h : P * Q = 1)
    (A B : Matrix (Fin 2) (Fin 2) U) : (Q * A * P) * (Q * B * P) = Q * (A * B) * P := by
  simp only [mul_assoc]
  rw [← mul_assoc P Q (B * P), h, one_mul]

theorem conj_conj_eq {P Q : Matrix (Fin 2) (Fin 2) U} (h : P * Q = 1)
    (M : Matrix (Fin 2) (Fin 2) U) : P * (Q * M * P) * Q = M := by
  rw [← mul_assoc, ← mul_assoc, h, one_mul, mul_assoc, h, mul_one]

theorem conj_injective {P Q : Matrix (Fin 2) (Fin 2) U} (h : P * Q = 1)
    {A B : Matrix (Fin 2) (Fin 2) U} (hAB : Q * A * P = Q * B * P) : A = B := by
  have h2 : P * (Q * A * P) * Q = P * (Q * B * P) * Q := by rw [hAB]
  rwa [conj_conj_eq h, conj_conj_eq h] at h2

theorem conjLinear_comp (P Q P' Q' : Matrix (Fin 2) (Fin 2) U) :
    (conjLinear C P' Q').comp (conjLinear C P Q) = conjLinear C (P' * P) (Q * Q') :=
  LinearMap.ext fun Z => by
    simp only [LinearMap.comp_apply, conjLinear_apply, mul_assoc]

/-- **Cassidy's classification for `sl₂`.** -/
theorem cassidy_sl2 [IsAlgClosed C] [IsAlgClosed U] [CharZero U]
    (L : Submodule C (Matrix (Fin 2) (Fin 2) U))
    (htr : ∀ A ∈ L, A.trace = 0)
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)))
    (hline : ∀ A ∈ L, A ≠ 0 → ∀ c : U, c • A ∈ L → ∃ c₀ : C, c = algebraMap C U c₀) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) U, P * Q = 1 ∧ Q * P = 1 ∧
      L.map (conjLinear C P Q) = Submodule.span C {sl2H U, sl2E U, sl2F U} := by
  classical
  have htwo : (2 : U) ≠ 0 := two_ne_zero
  have hHtr : (sl2H U).trace = 0 := by simp [sl2H, Matrix.trace_fin_two]
  have hHdet : (sl2H U).det ≠ 0 := by
    simp [sl2H, Matrix.det_fin_two]
  obtain ⟨X, hXL, hXdet⟩ := exists_det_ne_zero_of_mem_span L (hdense _ hHtr) hHdet
  obtain ⟨μ, P, hμ, hPdet, hXP⟩ :=
    exists_conj_toral_of_det_ne_zero htwo X (htr X hXL) hXdet
  have hPunit : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  set Q := P⁻¹ with hQdef
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hPunit
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hPunit
  set L' : Submodule C (Matrix (Fin 2) (Fin 2) U) := L.map (conjLinear C Q P) with hL'def
  have hL'mem : ∀ Y ∈ L, Q * Y * P ∈ L' := fun Y hY => Submodule.mem_map_of_mem hY
  have htr' : ∀ A ∈ L', A.trace = 0 := by
    rintro A ⟨Y, hY, rfl⟩
    have hcomm : (Q * Y * P).trace = (P * Q * Y).trace := by
      rw [Matrix.trace_mul_comm (Q * Y) P, mul_assoc]
    show (Q * Y * P).trace = 0
    rw [hcomm, hPQ, one_mul]
    exact htr Y hY
  have hbr' : ∀ A ∈ L', ∀ B ∈ L', A * B - B * A ∈ L' := by
    rintro A ⟨Y, hY, rfl⟩ B ⟨W, hW, rfl⟩
    have heq : (Q * Y * P) * (Q * W * P) - (Q * W * P) * (Q * Y * P)
        = Q * (Y * W - W * Y) * P := by
      rw [conj_mul_conj hPQ, conj_mul_conj hPQ, Matrix.mul_sub, Matrix.sub_mul]
    show (Q * Y * P) * (Q * W * P) - (Q * W * P) * (Q * Y * P) ∈ L'
    rw [heq]
    exact hL'mem _ (hbr Y hY W hW)
  have hdense' : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L' : Set (Matrix (Fin 2) (Fin 2) U)) := by
    intro Z hZ
    have h1 : (P * Z * Q).trace = 0 := by
      have hcomm : (P * Z * Q).trace = (Q * P * Z).trace := by
        rw [Matrix.trace_mul_comm (P * Z) Q, mul_assoc]
      rw [hcomm, hQP, one_mul]
      exact hZ
    have h2 : P * Z * Q ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) := hdense _ h1
    have h3 : (conjLinear U Q P) (P * Z * Q) ∈
        Submodule.map (conjLinear U Q P)
          (Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U))) :=
      Submodule.mem_map_of_mem h2
    rw [Submodule.map_span] at h3
    have h4 : ⇑(conjLinear U Q P) '' (L : Set (Matrix (Fin 2) (Fin 2) U))
        = (L' : Set (Matrix (Fin 2) (Fin 2) U)) := by
      rw [hL'def, Submodule.map_coe]
      rfl
    rw [h4] at h3
    have h5 : (conjLinear U Q P) (P * Z * Q) = Z := conj_conj_eq hQP Z
    rwa [h5] at h3
  have hline' : ∀ A ∈ L', A ≠ 0 → ∀ c : U, c • A ∈ L' → ∃ c₀ : C, c = algebraMap C U c₀ := by
    rintro A ⟨Y, hY, rfl⟩ hAne c hc
    obtain ⟨Y', hY', hY'eq⟩ := hc
    have hsmul : c • (Q * Y * P) = Q * (c • Y) * P := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    have hYY' : Y' = c • Y := by
      refine conj_injective hPQ ?_
      have h : Q * Y' * P = c • (Q * Y * P) := hY'eq
      rw [h, hsmul]
    have hYne : Y ≠ 0 := by
      intro h0
      apply hAne
      show Q * Y * P = 0
      rw [h0, Matrix.mul_zero, Matrix.zero_mul]
    exact hline Y hY hYne c (hYY' ▸ hY')
  have hXmem' : μ • sl2H U ∈ L' := by
    have h : Q * X * P ∈ L' := hL'mem _ hXL
    rwa [mul_assoc, hXP, ← mul_assoc, hQP, one_mul] at h
  obtain ⟨v₀, w₀, b₀, hv₀, hw₀, hb₀, hprod, hL'eq⟩ :=
    cassidy_sl2_of_toral L' htr' hbr' hdense' hline' hμ hXmem'
  refine ⟨sl2Diag v₀ * Q, P * sl2Diag v₀⁻¹, ?_, ?_, ?_⟩
  · have hD : sl2Diag v₀ * sl2Diag v₀⁻¹ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2Diag, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hv₀]
    calc (sl2Diag v₀ * Q) * (P * sl2Diag v₀⁻¹)
        = sl2Diag v₀ * (Q * P) * sl2Diag v₀⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hQP, mul_one, hD]
  · have hD : sl2Diag v₀⁻¹ * sl2Diag v₀ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2Diag, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hv₀]
    calc (P * sl2Diag v₀⁻¹) * (sl2Diag v₀ * Q)
        = P * (sl2Diag v₀⁻¹ * sl2Diag v₀) * Q := by simp only [mul_assoc]
      _ = 1 := by rw [hD, mul_one, hPQ]
  · have hmapcomp : L.map (conjLinear C (sl2Diag v₀ * Q) (P * sl2Diag v₀⁻¹))
        = L'.map (conjLinear C (sl2Diag v₀) (sl2Diag v₀⁻¹)) := by
      rw [hL'def, ← Submodule.map_comp, conjLinear_comp]
    rw [hmapcomp, hL'eq, Submodule.map_span]
    have himg : ⇑(conjLinear C (sl2Diag v₀) (sl2Diag v₀⁻¹)) ''
        ({sl2H U, v₀ • sl2E U, w₀ • sl2F U} : Set (Matrix (Fin 2) (Fin 2) U))
        = {sl2H U, sl2E U, (algebraMap C U b₀) • sl2F U} := by
      rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      congr 1
      · exact sl2Diag_conj_H hv₀
      congr 1
      · exact sl2Diag_conj_E hv₀
      · rw [conjLinear_apply, sl2Diag_conj_F, hprod]
    rw [himg]
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · rw [algebraMap_smul U]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · have hmem : (algebraMap C U b₀) • sl2F U ∈
            Submodule.span C ({sl2H U, sl2E U, (algebraMap C U b₀) • sl2F U} :
              Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
        have hval : b₀⁻¹ • ((algebraMap C U b₀) • sl2F U) = sl2F U := by
          rw [algebraMap_smul U, smul_smul, inv_mul_cancel₀ hb₀, one_smul]
        have hsm := Submodule.smul_mem _ b₀⁻¹ hmem
        rwa [hval] at hsm

end

end GaloisForLFunctions.HTGeometry
