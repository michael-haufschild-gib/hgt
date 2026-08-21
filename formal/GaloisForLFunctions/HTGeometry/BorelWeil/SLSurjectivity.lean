import GaloisForLFunctions.HTGeometry.BorelWeil.ColumnScaling

/-!
# Surjectivity of the comparison with the group model

Every section in the group model `bwSections λ` — a regular function on `SL(N,k)` transforming by a
character of the Borel — extends to a polynomial section on all matrices.  The extension divides
one column by the determinant, which introduces a bounded power of `det` in the denominator; the
numerator is a polynomial section of weight `λ + R·1`, and the divisibility supplied by
`DetTwist.exists_eq_detPow_mul` removes the power of `det` again.

Together with the injectivity of `PolyVanishing.eq_zero_of_restrictToSL_eq_zero` this identifies
the two models of `H⁰(λ)`.

## Main results

* `exists_polySections_restrict` — surjectivity of the comparison map.
* `restrictToSL_bijective` — the comparison is a bijection.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

@[simp] theorem matEval_C (g : Matrix (Fin N) (Fin N) k) (c : k) :
    matEval g (MvPolynomial.C c) = c := by simp [matEval]

theorem matEval_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin N × Fin N) k)
    (g : Matrix (Fin N) (Fin N) k) :
    matEval g (∑ i ∈ s, f i) = ∑ i ∈ s, matEval g (f i) := by simp [matEval]

theorem colScaleMat_mul (j₀ : Fin N) (a b : k) :
    colScaleMat j₀ a * colScaleMat j₀ b = colScaleMat j₀ (a * b) := by
  rw [colScaleMat, colScaleMat, colScaleMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = j₀ <;> simp [h]

@[simp] theorem colScaleMat_one (j₀ : Fin N) : colScaleMat j₀ (1 : k) = 1 := by
  rw [colScaleMat, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = j₀ <;> simp [h]

/-- The `SL` part of an invertible matrix: divide the `j₀`-th column by the determinant. -/
noncomputable def slPart (j₀ : Fin N) (g : Matrix (Fin N) (Fin N) k) (hg : g.det ≠ 0) :
    SpecialLinearGroup (Fin N) k :=
  ⟨g * colScaleMat j₀ (g.det)⁻¹, by
    rw [Matrix.det_mul, det_colScaleMat, mul_inv_cancel₀ hg]⟩

theorem coe_slPart (j₀ : Fin N) (g : Matrix (Fin N) (Fin N) k) (hg : g.det ≠ 0) :
    ((slPart j₀ g hg : SpecialLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)
      = g * colScaleMat j₀ (g.det)⁻¹ := rfl

/-- The polynomial extension of a regular function, obtained by clearing the determinants. -/
noncomputable def extendPoly (j₀ : Fin N) (q : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial (Fin N × Fin N) k :=
  ∑ r ∈ Finset.range ((scaleCol j₀ q).natDegree + 1),
    (detPoly N k) ^ ((scaleCol j₀ q).natDegree - r) * (scaleCol j₀ q).coeff r

theorem matEval_extendPoly_sl (j₀ : Fin N) (q : MvPolynomial (Fin N × Fin N) k)
    (h : SpecialLinearGroup (Fin N) k) :
    matEval (h : Matrix (Fin N) (Fin N) k) (extendPoly j₀ q)
      = matEval (h : Matrix (Fin N) (Fin N) k) q := by
  have hdet : ((h : Matrix (Fin N) (Fin N) k)).det = 1 := h.2
  rw [extendPoly, matEval_sum]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ _) => by
    rw [matEval_mul, matEval_pow, matEval_detPoly, hdet, one_pow, one_mul]]
  rw [← matEval_sum, sum_scaleCol_coeff]

theorem matEval_extendPoly_of_det_ne_zero (j₀ : Fin N) (q : MvPolynomial (Fin N × Fin N) k)
    {g : Matrix (Fin N) (Fin N) k} (hg : g.det ≠ 0) :
    matEval g (extendPoly j₀ q)
      = g.det ^ ((scaleCol j₀ q).natDegree)
        * matEval ((slPart j₀ g hg : SpecialLinearGroup (Fin N) k) :
            Matrix (Fin N) (Fin N) k) q := by
  set R := (scaleCol j₀ q).natDegree with hR
  rw [coe_slPart, matEval_mul_colScaleMat, Polynomial.eval₂_eq_sum_range, Finset.mul_sum,
    extendPoly, matEval_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrR : r ≤ R := by
    have := Finset.mem_range.mp hr
    omega
  rw [matEval_mul, matEval_pow, matEval_detPoly, matEvalHom_apply, inv_pow,
    pow_sub₀ _ hg hrR]
  ring

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- The Borel element relating the `SL` parts of `g` and `g * B`. -/
noncomputable def borelFactor (j₀ : Fin N) (g B : Matrix (Fin N) (Fin N) k)
    (hg : g.det ≠ 0) (hB : B.det ≠ 0) : SpecialLinearGroup (Fin N) k :=
  ⟨colScaleMat j₀ g.det * B * colScaleMat j₀ ((g * B).det)⁻¹, by
    rw [Matrix.det_mul, Matrix.det_mul, det_colScaleMat, det_colScaleMat, Matrix.det_mul]
    field_simp⟩

theorem coe_borelFactor (j₀ : Fin N) (g B : Matrix (Fin N) (Fin N) k)
    (hg : g.det ≠ 0) (hB : B.det ≠ 0) :
    ((borelFactor j₀ g B hg hB : SpecialLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)
      = colScaleMat j₀ g.det * B * colScaleMat j₀ ((g * B).det)⁻¹ := rfl

theorem slPart_mul (j₀ : Fin N) {g B : Matrix (Fin N) (Fin N) k}
    (hg : g.det ≠ 0) (hB : B.det ≠ 0) (hgB : (g * B).det ≠ 0) :
    slPart j₀ (g * B) hgB = slPart j₀ g hg * borelFactor j₀ g B hg hB := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, coe_slPart, coe_slPart, coe_borelFactor]
  have hcancel : colScaleMat j₀ (g.det)⁻¹ * colScaleMat j₀ g.det
      = (1 : Matrix (Fin N) (Fin N) k) := by
    rw [colScaleMat_mul, inv_mul_cancel₀ hg, colScaleMat_one]
  calc g * B * colScaleMat j₀ ((g * B).det)⁻¹
      = g * (colScaleMat j₀ (g.det)⁻¹ * colScaleMat j₀ g.det) * B
          * colScaleMat j₀ ((g * B).det)⁻¹ := by rw [hcancel, Matrix.mul_one]
    _ = g * colScaleMat j₀ (g.det)⁻¹ * (colScaleMat j₀ g.det * B
          * colScaleMat j₀ ((g * B).det)⁻¹) := by simp only [Matrix.mul_assoc]

theorem borelFactor_mem_borel (j₀ : Fin N) {g B : Matrix (Fin N) (Fin N) k}
    (hg : g.det ≠ 0) (hB : IsBorelMat B) (hBd : B.det ≠ 0) :
    borelFactor j₀ g B hg hBd ∈ borel (Fin N) k := by
  rw [mem_borel_iff, coe_borelFactor]
  exact ((colScaleMat_blockTriangular j₀ g.det).mul hB.1).mul
    (colScaleMat_blockTriangular j₀ ((g * B).det)⁻¹)

theorem borelChar_borelFactor {lam : Fin N → ℕ} (j₀ : Fin N) (hlam0 : lam j₀ = 0)
    {g B : Matrix (Fin N) (Fin N) k} (hg : g.det ≠ 0) (hB : IsBorelMat B) (hBd : B.det ≠ 0) :
    borelChar lam (borelFactor j₀ g B hg hBd) = borelCharMat lam B := by
  rw [borelChar, borelCharMat]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = j₀
  · subst hi
    rw [hlam0, pow_zero, pow_zero]
  · congr 1
    rw [coe_borelFactor,
      diag_mul_of_blockTriangular ((colScaleMat_blockTriangular j₀ g.det).mul hB.1)
        (colScaleMat_blockTriangular j₀ ((g * B).det)⁻¹) i,
      diag_mul_of_blockTriangular (colScaleMat_blockTriangular j₀ g.det) hB.1 i,
      colScaleMat_apply_diag, colScaleMat_apply_diag, if_neg hi, if_neg hi, one_mul, mul_one]

/-- **The extension is a polynomial section** of the shifted weight. -/
theorem extendPoly_mem_polySections [Infinite k] {lam : Fin N → ℕ} (j₀ : Fin N)
    (hlam0 : lam j₀ = 0) {f : SpecialLinearGroup (Fin N) k → k} (hf : f ∈ bwSections lam)
    {q : MvPolynomial (Fin N × Fin N) k}
    (hq : ∀ h : SpecialLinearGroup (Fin N) k, matEval (h : Matrix (Fin N) (Fin N) k) q = f h) :
    extendPoly j₀ q ∈ polySections (fun i => lam i + (scaleCol j₀ q).natDegree) := by
  classical
  set R := (scaleCol j₀ q).natDegree with hR
  set P := extendPoly j₀ q with hP
  intro g B hB
  have hBdet : B.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hB.1]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hB.2 i
  have hkey : ∀ g' : Matrix (Fin N) (Fin N) k, g'.det ≠ 0 →
      matEval (g' * B) P = borelCharMat (fun i => lam i + R) B * matEval g' P := by
    intro g' hg'
    have hgB : (g' * B).det ≠ 0 := by
      rw [Matrix.det_mul]; exact mul_ne_zero hg' hBdet
    rw [hP, matEval_extendPoly_of_det_ne_zero j₀ q hgB,
      matEval_extendPoly_of_det_ne_zero j₀ q hg', slPart_mul j₀ hg' hBdet hgB, hq, hq,
      hf.2 _ _ (borelFactor_mem_borel j₀ hg' hB hBdet), borelChar_borelFactor j₀ hlam0 hg' hB hBdet,
      Matrix.det_mul, mul_pow, borelCharMat_add_const lam R hB.1]
    ring
  have h0 : (substRight B P - MvPolynomial.C (borelCharMat (fun i => lam i + R) B) * P)
      * detPoly N k = 0 := by
    refine matEval_injective fun g' => ?_
    rw [matEval_mul, matEval_zero, matEval_detPoly]
    by_cases hg' : g'.det = 0
    · rw [hg', mul_zero]
    · rw [matEval_sub, matEval_substRight, matEval_mul, matEval_C, hkey g' hg', sub_self, zero_mul]
  have hpoly : substRight B P - MvPolynomial.C (borelCharMat (fun i => lam i + R) B) * P = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h detPoly_ne_zero
  have hfin := congrArg (matEval g) hpoly
  rw [matEval_sub, matEval_substRight, matEval_mul, matEval_C, matEval_zero, sub_eq_zero] at hfin
  exact hfin

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

theorem exists_polySections_restrict_of_zero [CharZero k] {lam : Fin N → ℕ}
    (hlam : Antitone lam) (j₀ : Fin N) (hlam0 : lam j₀ = 0)
    {f : SpecialLinearGroup (Fin N) k → k} (hf : f ∈ bwSections lam) :
    ∃ Q, Q ∈ polySections lam ∧ restrictToSL Q = f := by
  obtain ⟨q, hq⟩ := hf.1
  have hqf : ∀ h : SpecialLinearGroup (Fin N) k,
      matEval (h : Matrix (Fin N) (Fin N) k) q = f h := by
    intro h
    have hq' : (coordEval (Fin N) k) q = f := hq
    rw [← coordEval_apply q h, hq']
  obtain ⟨Q, hQ, hPQ⟩ :=
    exists_eq_detPow_mul hlam ((scaleCol j₀ q).natDegree)
      (extendPoly_mem_polySections j₀ hlam0 hf hqf)
  refine ⟨Q, hQ, ?_⟩
  funext h
  have hdet : ((h : Matrix (Fin N) (Fin N) k)).det = 1 := h.2
  have h1 : matEval (h : Matrix (Fin N) (Fin N) k) (extendPoly j₀ q)
      = matEval (h : Matrix (Fin N) (Fin N) k) Q := by
    rw [hPQ, matEval_mul, matEval_pow, matEval_detPoly, hdet, one_pow, one_mul]
  show matEval (h : Matrix (Fin N) (Fin N) k) Q = f h
  rw [← h1, matEval_extendPoly_sl, hqf h]

/-- **Surjectivity of the comparison map.**  Every section in the group model comes from a
polynomial section. -/
theorem exists_polySections_restrict [CharZero k] {lam : Fin N → ℕ} (hlam : Antitone lam)
    {f : SpecialLinearGroup (Fin N) k → k} (hf : f ∈ bwSections lam) :
    ∃ Q, Q ∈ polySections lam ∧ restrictToSL Q = f := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    obtain ⟨q, hq⟩ := hf.1
    refine ⟨q, ?_, ?_⟩
    · intro g B hB
      have hgB : g * B = g := by
        ext i
        exact i.elim0
      rw [hgB, borelCharMat]
      simp
    · funext h
      show matEval (h : Matrix (Fin 0) (Fin 0) k) q = f h
      have hq' : (coordEval (Fin 0) k) q = f := hq
      rw [← coordEval_apply q h, hq']
  · set j₀ : Fin N := ⟨N - 1, by omega⟩ with hj₀
    set c := lam j₀ with hc
    set lam' : Fin N → ℕ := fun i => lam i - c with hlam'
    have hle : ∀ i, c ≤ lam i := by
      intro i
      refine hlam ?_
      have := i.isLt
      exact Fin.le_def.mpr (by simp only [hj₀]; omega)
    have hsum : ∀ i, lam' i + c = lam i := by
      intro i
      have := hle i
      simp only [hlam']
      omega
    have hlam'anti : Antitone lam' := by
      intro i j hij
      have h1 := hlam hij
      simp only [hlam']
      omega
    have hlam'0 : lam' j₀ = 0 := by simp [hlam', hc]
    have hf' : f ∈ bwSections lam' := by
      refine ⟨hf.1, fun g b hb => ?_⟩
      rw [hf.2 g b hb]
      congr 1
      have hbdet : ((b : Matrix (Fin N) (Fin N) k)).det = 1 := b.2
      rw [borelChar, borelChar]
      rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => by rw [← hsum i, pow_add]]
      rw [Finset.prod_mul_distrib, Finset.prod_pow,
        ← Matrix.det_of_upperTriangular (mem_borel_iff.mp hb), hbdet, one_pow, mul_one]
    obtain ⟨Q', hQ', hQ'f⟩ := exists_polySections_restrict_of_zero hlam'anti j₀ hlam'0 hf'
    refine ⟨detPoly N k ^ c * Q', ?_, ?_⟩
    · have h := detPow_mem_polySections hQ' c
      have heq : (fun i => lam' i + c) = lam := funext hsum
      rwa [heq] at h
    · funext h
      have hdet : ((h : Matrix (Fin N) (Fin N) k)).det = 1 := h.2
      show matEval (h : Matrix (Fin N) (Fin N) k) (detPoly N k ^ c * Q') = f h
      rw [matEval_mul, matEval_pow, matEval_detPoly, hdet, one_pow, one_mul, ← hQ'f]
      rfl

/-- **The two models of `H⁰(λ)` agree.**  Restriction to `SL(N,k)` is a bijection from the
polynomial sections onto the group-model sections. -/
theorem restrictToSL_bijective [CharZero k] {lam : Fin N → ℕ} (hlam : Antitone lam) :
    Function.Bijective
      (fun Q : polySections (k := k) lam => (⟨restrictToSL (Q : MvPolynomial (Fin N × Fin N) k),
        restrictToSL_mem_bwSections Q.2⟩ : bwSections (k := k) lam)) := by
  constructor
  · rintro ⟨Q₁, hQ₁⟩ ⟨Q₂, hQ₂⟩ hEq
    have h : restrictToSL Q₁ = restrictToSL Q₂ := congrArg Subtype.val hEq
    have hzero : Q₁ - Q₂ = 0 := by
      refine eq_zero_of_restrictToSL_eq_zero (Submodule.sub_mem _ hQ₁ hQ₂) fun g => ?_
      have hg : matEval (g : Matrix (Fin N) (Fin N) k) Q₁
          = matEval (g : Matrix (Fin N) (Fin N) k) Q₂ := congrFun h g
      rw [matEval_sub, hg, sub_self]
    exact Subtype.ext (sub_eq_zero.mp hzero)
  · rintro ⟨f, hf⟩
    obtain ⟨Q, hQ, hQf⟩ := exists_polySections_restrict hlam hf
    exact ⟨⟨Q, hQ⟩, Subtype.ext hQf⟩

end GaloisForLFunctions.HTGeometry.BorelWeil
