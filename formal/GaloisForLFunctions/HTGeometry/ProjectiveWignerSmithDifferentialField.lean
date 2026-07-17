import GaloisForLFunctions.HTGeometry.MatrixWignerSmithConstantGauge
import GaloisForLFunctions.HTGeometry.MatrixWignerSmithReporterField
import GaloisForLFunctions.HTGeometry.ProjectiveWignerSmithTomography
import GaloisForLFunctions.HTGeometry.FiniteGeneratorDifferentialEscape

/-!
# Projective Wigner--Smith differential-field completeness

For an invertible finite scattering matrix, pivot-normalized entry ratios are invariant under
arbitrary nonzero scalar dressing. The traceless Wigner--Smith connection belongs to their
differential field, while the ratios satisfy a closed finite differential system over that
connection. Consequently the projective scattering field is differentially algebraic over the
traceless delay field and the two finite families have equal differential-matroid rank.

The nonredundant projective delay panel deletes one diagonal reporter. On the trace-zero sector its
remaining `(n+1)^2-1` reporters generate exactly the full traceless matrix-entry field.
-/

open scoped Differential Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

universe u

def matrixTracelessPartField
    {E : Type u} [Field E] [CharZero E] {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  Q + (-(Matrix.trace Q / (n + 1 : E))) • 1

theorem matrixTracelessPartField_trace
    {E : Type u} [Field E] [CharZero E] {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    Matrix.trace (matrixTracelessPartField Q) = 0 := by
  rw [matrixTracelessPartField, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  simp only [smul_eq_mul, Fintype.card_fin]
  have hcard : (n + 1 : E) ≠ 0 := Nat.cast_add_one_ne_zero n
  field_simp
  push_cast
  ring

theorem matrixTracelessPartField_add_scalar
    {E : Type u} [Field E] [CharZero E] {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (c : E) :
    matrixTracelessPartField (Q + c • 1) = matrixTracelessPartField Q := by
  ext i j
  simp only [matrixTracelessPartField, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp
    have hcard : (n + 1 : E) ≠ 0 := Nat.cast_add_one_ne_zero n
    field_simp
    ring
  · simp [hij]

theorem matrix_eq_tracelessPartField_add_scalar
    {E : Type u} [Field E] [CharZero E] {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    Q = matrixTracelessPartField Q +
      (Matrix.trace Q / (n + 1 : E)) • 1 := by
  ext i j
  simp only [matrixTracelessPartField, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem matrixDifferential_smul
    {E : Type u} [Field E] [Differential E] {n : ℕ}
    (f : E) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    matrixDifferential (f • S) = f′ • S + f • matrixDifferential S := by
  ext a b
  simp [matrixDifferential, Derivation.leibniz]
  ring

theorem matrixWignerSmith_smul
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hdet : S.det ≠ 0) (f : E) (hf : f ≠ 0) :
    matrixWignerSmith ι (f • S) =
      matrixWignerSmith ι S +
        (-(algebraMap F E ι) * (f′ / f)) • 1 := by
  letI : Invertible f := invertibleOfNonzero hf
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
  rw [matrixWignerSmith, matrixWignerSmith, Matrix.inv_smul S f hunit,
    matrixDifferential_smul]
  rw [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.nonsing_inv_mul S hunit]
  simp [hf, div_eq_mul_inv, mul_comm, mul_left_comm]
  module

theorem matrixTracelessPartField_matrixWignerSmith_smul
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [CharZero E] {n : ℕ}
    (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hdet : S.det ≠ 0) (f : E) (hf : f ≠ 0) :
    matrixTracelessPartField (matrixWignerSmith ι (f • S)) =
      matrixTracelessPartField (matrixWignerSmith ι S) := by
  rw [matrixWignerSmith_smul ι S hdet f hf]
  exact matrixTracelessPartField_add_scalar _ _

def matrixPivotNormalize
    {E : Type u} [Field E] {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p : Fin (n + 1) × Fin (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  (S p.1 p.2)⁻¹ • S

theorem matrixPivotNormalize_pivot
    {E : Type u} [Field E] {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p : Fin (n + 1) × Fin (n + 1)) (hp : S p.1 p.2 ≠ 0) :
    matrixPivotNormalize S p p.1 p.2 = 1 := by
  simp [matrixPivotNormalize, hp]

theorem matrixPivotNormalize_smul
    {E : Type u} [Field E] {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p : Fin (n + 1) × Fin (n + 1))
    (f : E) (hf : f ≠ 0) :
    matrixPivotNormalize (f • S) p = matrixPivotNormalize S p := by
  ext a b
  simp only [matrixPivotNormalize, Matrix.smul_apply, smul_eq_mul]
  field_simp

theorem matrixPivotNormalize_change_pivot
    {E : Type u} [Field E] {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p q : Fin (n + 1) × Fin (n + 1))
    (hp : S p.1 p.2 ≠ 0) (hq : S q.1 q.2 ≠ 0)
    (a b : Fin (n + 1)) :
    matrixPivotNormalize S q a b =
      matrixPivotNormalize S p a b / matrixPivotNormalize S p q.1 q.2 := by
  simp only [matrixPivotNormalize, Matrix.smul_apply, smul_eq_mul]
  field_simp

theorem differentialAdjoin_matrixPivotNormalize_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p q : Fin (n + 1) × Fin (n + 1))
    (hp : S p.1 p.2 ≠ 0) (hq : S q.1 q.2 ≠ 0) :
    differentialAdjoin F
        (Set.range fun r : Fin (n + 1) × Fin (n + 1) ↦
          matrixPivotNormalize S p r.1 r.2) =
      differentialAdjoin F
        (Set.range fun r : Fin (n + 1) × Fin (n + 1) ↦
          matrixPivotNormalize S q r.1 r.2) := by
  apply le_antisymm
  · apply differentialAdjoin_le F
    · rintro _ ⟨r, rfl⟩
      change matrixPivotNormalize S p r.1 r.2 ∈ _
      rw [matrixPivotNormalize_change_pivot S q p hq hp]
      exact IntermediateField.div_mem _
        (subset_differentialAdjoin F _ ⟨r, rfl⟩)
        (subset_differentialAdjoin F _ ⟨p, rfl⟩)
    · exact derivationClosed_differentialAdjoin F _
  · apply differentialAdjoin_le F
    · rintro _ ⟨r, rfl⟩
      change matrixPivotNormalize S q r.1 r.2 ∈ _
      rw [matrixPivotNormalize_change_pivot S p q hp hq]
      exact IntermediateField.div_mem _
        (subset_differentialAdjoin F _ ⟨r, rfl⟩)
        (subset_differentialAdjoin F _ ⟨q, rfl⟩)
    · exact derivationClosed_differentialAdjoin F _

theorem differentialAlgebraicOver_projectiveFiniteSystem
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (iota : F)
    (B R : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p : Fin (n + 1) × Fin (n + 1))
    (hsystem : ∀ a b, (R a b)′ = algebraMap F E iota *
      ((R * B) a b - (R * B) p.1 p.2 * R a b))
    (a b : Fin (n + 1)) :
    DifferentialAlgebraicOver
      (differentialAdjoin F
        (Set.range fun q : Fin (n + 1) × Fin (n + 1) ↦ B q.1 q.2))
      (R a b) := by
  let bFamily : Fin (n + 1) × Fin (n + 1) → E := fun q ↦ B q.1 q.2
  let rFamily : Fin (n + 1) × Fin (n + 1) → E := fun q ↦ R q.1 q.2
  let BQ := differentialAdjoin F (Set.range bFamily)
  letI : DifferentialAlgebra BQ E :=
    ⟨fun c ↦ derivationClosedDifferential_apply BQ
      (derivationClosed_differentialAdjoin F (Set.range bFamily)) c⟩
  let M := IntermediateField.adjoin BQ (Set.range rFamily)
  have hmul : ∀ i j, (R * B) i j ∈ M := by
    intro i j
    rw [Matrix.mul_apply]
    apply M.sum_mem
    intro k _
    apply M.mul_mem
    · exact IntermediateField.subset_adjoin BQ (Set.range rFamily) ⟨(i, k), rfl⟩
    · exact M.algebraMap_mem
        ⟨B k j, subset_differentialAdjoin F (Set.range bFamily) ⟨(k, j), rfl⟩⟩
  have hrderiv : ∀ q, (rFamily q)′ ∈ M := by
    intro q
    change (R q.1 q.2)′ ∈ M
    rw [hsystem]
    apply M.mul_mem
    · exact M.algebraMap_mem ⟨algebraMap F E iota, BQ.algebraMap_mem iota⟩
    · apply M.sub_mem (hmul q.1 q.2)
      exact M.mul_mem (hmul p.1 p.2)
        (IntermediateField.subset_adjoin BQ (Set.range rFamily) ⟨q, rfl⟩)
  exact differentialAlgebraicOver_of_mem_finiteGeneratorState
    (F := BQ) (E := E) rFamily hrderiv
    (IntermediateField.subset_adjoin BQ (Set.range rFamily) ⟨(a, b), rfl⟩)

theorem matrixPivotNormalize_deriv_eq_tracelessWignerSmith
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [CharZero E] {n : ℕ}
    (iota : F) (hiota : iota * iota = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    (p : Fin (n + 1) × Fin (n + 1)) (hp : S p.1 p.2 ≠ 0)
    (a b : Fin (n + 1)) :
    let R := matrixPivotNormalize S p
    let B := matrixTracelessPartField (matrixWignerSmith iota S)
    (R a b)′ = algebraMap F E iota *
      ((R * B) a b - (R * B) p.1 p.2 * R a b) := by
  let R := matrixPivotNormalize S p
  let Q := matrixWignerSmith iota S
  let QR := matrixWignerSmith iota R
  let B := matrixTracelessPartField Q
  let c : E := Matrix.trace QR / (n + 1 : E)
  have hiota0 : iota ≠ 0 := by
    intro h
    subst iota
    simp at hiota
  have hiotaE0 : algebraMap F E iota ≠ 0 := by
    simpa using (algebraMap F E).injective.ne hiota0
  have hdetR : R.det ≠ 0 := by
    change (((S p.1 p.2)⁻¹ • S).det) ≠ 0
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hp)) hdet
  have htraceGauge : matrixTracelessPartField QR = B := by
    exact matrixTracelessPartField_matrixWignerSmith_smul
      iota S hdet (S p.1 p.2)⁻¹ (inv_ne_zero hp)
  have hQR : QR = B + c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := by
    rw [matrix_eq_tracelessPartField_add_scalar QR, htraceGauge]
  have hdiff := matrixDifferential_eq_mul_matrixWignerSmith iota hiota R hdetR
  have hentry : ∀ i j, (R i j)′ = algebraMap F E iota * (R * QR) i j := by
    intro i j
    have h := congrArg (fun M ↦ M i j) hdiff
    simpa [matrixDifferential] using h
  have hmul : ∀ i j, (R * QR) i j = (R * B) i j + c * R i j := by
    intro i j
    rw [hQR, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    simp
  have hpR : R p.1 p.2 = 1 := matrixPivotNormalize_pivot S p hp
  have hpzero : (R * B) p.1 p.2 + c = 0 := by
    have h := hentry p.1 p.2
    rw [hpR] at h
    rw [hmul, hpR, mul_one] at h
    have hz : algebraMap F E iota * ((R * B) p.1 p.2 + c) = 0 := by
      simpa using h.symm
    exact (mul_eq_zero.mp hz).resolve_left hiotaE0
  change (R a b)′ = _
  rw [hentry, hmul]
  have hc : c = -(R * B) p.1 p.2 := by
    linear_combination hpzero
  rw [hc]
  ring

theorem matrixTracelessWignerSmith_entry_mem_projectiveAdjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [CharZero E] {n : ℕ}
    (iota : F)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    (p : Fin (n + 1) × Fin (n + 1)) (hp : S p.1 p.2 ≠ 0)
    (a b : Fin (n + 1)) :
    matrixTracelessPartField (matrixWignerSmith iota S) a b ∈
      differentialAdjoin F
        (Set.range fun q : Fin (n + 1) × Fin (n + 1) ↦
          matrixPivotNormalize S p q.1 q.2) := by
  let R := matrixPivotNormalize S p
  let Q := matrixWignerSmith iota S
  let QR := matrixWignerSmith iota R
  let BR := differentialAdjoin F
    (Set.range fun q : Fin (n + 1) × Fin (n + 1) ↦ R q.1 q.2)
  have htraceGauge : matrixTracelessPartField QR = matrixTracelessPartField Q := by
    exact matrixTracelessPartField_matrixWignerSmith_smul
      iota S hdet (S p.1 p.2)⁻¹ (inv_ne_zero hp)
  have hQR : ∀ i j, QR i j ∈ BR := by
    intro i j
    exact matrixWignerSmith_entry_mem_differentialAdjoin iota R i j
  have htrace : Matrix.trace QR ∈ BR := by
    rw [Matrix.trace]
    exact BR.sum_mem fun i _ ↦ hQR i i
  have hcard : (n + 1 : E) ∈ BR := by
    simpa using BR.algebraMap_mem (n + 1 : F)
  have hentry : matrixTracelessPartField QR a b ∈ BR := by
    rw [matrixTracelessPartField]
    apply BR.add_mem (hQR a b)
    by_cases hab : a = b
    · subst b
      simpa using BR.neg_mem (BR.div_mem htrace hcard)
    · simp [hab]
  change matrixTracelessPartField Q a b ∈ BR
  rw [← htraceGauge]
  exact hentry

theorem differentialAlgebraicOver_matrixPivotNormalize_entries
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (iota : F) (hiota : iota * iota = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    (p : Fin (n + 1) × Fin (n + 1)) (hp : S p.1 p.2 ≠ 0)
    (a b : Fin (n + 1)) :
    DifferentialAlgebraicOver
      (differentialAdjoin F
        (Set.range fun q : Fin (n + 1) × Fin (n + 1) ↦
          matrixTracelessPartField (matrixWignerSmith iota S) q.1 q.2))
      (matrixPivotNormalize S p a b) := by
  apply differentialAlgebraicOver_projectiveFiniteSystem iota
    (matrixTracelessPartField (matrixWignerSmith iota S))
    (matrixPivotNormalize S p) p
  · exact matrixPivotNormalize_deriv_eq_tracelessWignerSmith
      iota hiota S hdet p hp

theorem matrixTracelessWignerSmith_projective_eRk_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (iota : F) (hiota : iota * iota = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    (p : Fin (n + 1) × Fin (n + 1)) (hp : S p.1 p.2 ≠ 0) :
    (differentialMatroid F E).eRk
        (Set.range fun q : Fin (n + 1) × Fin (n + 1) ↦
          matrixTracelessPartField (matrixWignerSmith iota S) q.1 q.2) =
      (differentialMatroid F E).eRk
        (Set.range fun q : Fin (n + 1) × Fin (n + 1) ↦
          matrixPivotNormalize S p q.1 q.2) := by
  let M := differentialMatroid F E
  let bFamily : Fin (n + 1) × Fin (n + 1) → E := fun q ↦
    matrixTracelessPartField (matrixWignerSmith iota S) q.1 q.2
  let rFamily : Fin (n + 1) × Fin (n + 1) → E := fun q ↦
    matrixPivotNormalize S p q.1 q.2
  have hBclose : Set.range bFamily ⊆ M.closure (Set.range rFamily) := by
    rintro _ ⟨q, rfl⟩
    apply (differentialMatroid_mem_closure_range_fintype_iff
      (F := F) (E := E) rFamily (bFamily q)).mpr
    let BR := differentialAdjoin F (Set.range rFamily)
    let bBR : BR := ⟨bFamily q,
      matrixTracelessWignerSmith_entry_mem_projectiveAdjoin
        iota S hdet p hp q.1 q.2⟩
    have hb : DifferentialAlgebraicOver BR (algebraMap BR E bBR) :=
      differentialAlgebraicOver_algebraMap bBR
    simpa [BR, bBR] using hb
  have hRclose : Set.range rFamily ⊆ M.closure (Set.range bFamily) := by
    rintro _ ⟨q, rfl⟩
    apply (differentialMatroid_mem_closure_range_fintype_iff
      (F := F) (E := E) bFamily (rFamily q)).mpr
    exact differentialAlgebraicOver_matrixPivotNormalize_entries
      iota hiota S hdet p hp q.1 q.2
  apply le_antisymm
  · calc
      M.eRk (Set.range bFamily) ≤ M.eRk (M.closure (Set.range rFamily)) :=
        M.eRk_mono hBclose
      _ = M.eRk (Set.range rFamily) := M.eRk_closure_eq _
  · calc
      M.eRk (Set.range rFamily) ≤ M.eRk (M.closure (Set.range bFamily)) :=
        M.eRk_mono hRclose
      _ = M.eRk (Set.range bFamily) := M.eRk_closure_eq _

def projectiveDelayPanelField
    {F E : Type u} [Field F] [Field E] [Algebra F E] {n : ℕ}
    (iota : F) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    ProjectiveDelayIndex n → E := fun p ↦ matrixDelayPanelField iota Q p.1

theorem projectiveDelayPanelField_mem_entry_differentialAdjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    {n : ℕ} (iota : F) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p : ProjectiveDelayIndex n) :
    projectiveDelayPanelField iota Q p ∈ differentialAdjoin F
      (Set.range fun q : Fin (n + 1) × Fin (n + 1) ↦ Q q.1 q.2) := by
  exact matrixDelayPanelField_mem_entry_differentialAdjoin iota Q p.1

theorem matrixEntry_mem_projectiveDelayPanelField_differentialAdjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E] [CharZero E]
    {n : ℕ} (iota : F) (hiota : iota * iota = -1)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (htrace : Matrix.trace Q = 0) (j k : Fin (n + 1)) :
    Q j k ∈ differentialAdjoin F (Set.range (projectiveDelayPanelField iota Q)) := by
  let BP := differentialAdjoin F (Set.range (projectiveDelayPanelField iota Q))
  have hdiag_ne_last : ∀ a, a ≠ Fin.last n → Q a a ∈ BP := by
    intro a ha
    have hp : (a, a) ≠ (Fin.last n, Fin.last n) := by
      intro h
      exact ha (congrArg Prod.fst h)
    have h := subset_differentialAdjoin F
      (Set.range (projectiveDelayPanelField iota Q)) ⟨⟨(a, a), hp⟩, rfl⟩
    simpa [projectiveDelayPanelField] using h
  have hlast : Q (Fin.last n) (Fin.last n) ∈ BP := by
    have hsum : ∑ a : Fin n, Q a.castSucc a.castSucc ∈ BP := by
      exact BP.sum_mem fun a _ ↦ hdiag_ne_last a.castSucc (Fin.castSucc_ne_last a)
    have htrace' :
        (∑ a : Fin n, Q a.castSucc a.castSucc) + Q (Fin.last n) (Fin.last n) = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_castSucc] using htrace
    have heq : Q (Fin.last n) (Fin.last n) =
        -(∑ a : Fin n, Q a.castSucc a.castSucc) := by
      linear_combination htrace'
    rw [heq]
    exact BP.neg_mem hsum
  have hdiag : ∀ a, Q a a ∈ BP := by
    intro a
    by_cases ha : a = Fin.last n
    · subst a
      exact hlast
    · exact hdiag_ne_last a ha
  by_cases heq : j = k
  · subst k
    exact hdiag j
  rcases lt_or_gt_of_ne heq with hjk | hkj
  · have hpjk : (j, k) ≠ (Fin.last n, Fin.last n) := by
      intro h
      exact (ne_of_lt hjk) ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)
    have hpkj : (k, j) ≠ (Fin.last n, Fin.last n) := by
      intro h
      exact (ne_of_lt hjk) ((congrArg Prod.snd h).trans (congrArg Prod.fst h).symm)
    have hplus : matrixDelayPlusField Q j k ∈ BP := by
      have h := subset_differentialAdjoin F
        (Set.range (projectiveDelayPanelField iota Q)) ⟨⟨(j, k), hpjk⟩, rfl⟩
      change matrixDelayPanelField iota Q (j, k) ∈ BP at h
      rwa [matrixDelayPanelField_plus iota Q j k hjk] at h
    have himag : matrixDelayImaginaryField iota Q j k ∈ BP := by
      have h := subset_differentialAdjoin F
        (Set.range (projectiveDelayPanelField iota Q)) ⟨⟨(k, j), hpkj⟩, rfl⟩
      change matrixDelayPanelField iota Q (k, j) ∈ BP at h
      rwa [matrixDelayPanelField_imaginary iota Q j k hjk] at h
    rw [matrixDelayField_offDiagonal_reconstruct iota hiota Q j k]
    exact BP.div_mem
      (BP.sub_mem
        (BP.sub_mem (BP.sub_mem hplus (hdiag j)) (hdiag k))
        (BP.mul_mem (BP.algebraMap_mem iota)
          (BP.sub_mem (BP.sub_mem himag (hdiag j)) (hdiag k))))
      (BP.natCast_mem 2)
  · have hpkj : (k, j) ≠ (Fin.last n, Fin.last n) := by
      intro h
      exact (ne_of_lt hkj) ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)
    have hpjk : (j, k) ≠ (Fin.last n, Fin.last n) := by
      intro h
      exact (ne_of_lt hkj) ((congrArg Prod.snd h).trans (congrArg Prod.fst h).symm)
    have hplus : matrixDelayPlusField Q k j ∈ BP := by
      have h := subset_differentialAdjoin F
        (Set.range (projectiveDelayPanelField iota Q)) ⟨⟨(k, j), hpkj⟩, rfl⟩
      change matrixDelayPanelField iota Q (k, j) ∈ BP at h
      rwa [matrixDelayPanelField_plus iota Q k j hkj] at h
    have himag : matrixDelayImaginaryField iota Q k j ∈ BP := by
      have h := subset_differentialAdjoin F
        (Set.range (projectiveDelayPanelField iota Q)) ⟨⟨(j, k), hpjk⟩, rfl⟩
      change matrixDelayPanelField iota Q (j, k) ∈ BP at h
      rwa [matrixDelayPanelField_imaginary iota Q k j hkj] at h
    rw [matrixDelayField_reverseOffDiagonal_reconstruct iota hiota Q k j]
    exact BP.div_mem
      (BP.add_mem
        (BP.sub_mem (BP.sub_mem hplus (hdiag k)) (hdiag j))
        (BP.mul_mem (BP.algebraMap_mem iota)
          (BP.sub_mem (BP.sub_mem himag (hdiag k)) (hdiag j))))
      (BP.natCast_mem 2)

theorem differentialAdjoin_projectiveDelayPanelField_eq_entries
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (iota : F) (hiota : iota * iota = -1)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (htrace : Matrix.trace Q = 0) :
    differentialAdjoin F (Set.range (projectiveDelayPanelField iota Q)) =
      differentialAdjoin F
        (Set.range fun p : Fin (n + 1) × Fin (n + 1) ↦ Q p.1 p.2) := by
  apply le_antisymm
  · apply differentialAdjoin_le F
    · rintro _ ⟨p, rfl⟩
      exact projectiveDelayPanelField_mem_entry_differentialAdjoin iota Q p
    · exact derivationClosed_differentialAdjoin F _
  · apply differentialAdjoin_le F
    · rintro _ ⟨p, rfl⟩
      exact matrixEntry_mem_projectiveDelayPanelField_differentialAdjoin
        iota hiota Q htrace p.1 p.2
    · exact derivationClosed_differentialAdjoin F _

theorem projectiveDelayPanelField_differentialMatroid_eRk_eq_entries
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (iota : F) (hiota : iota * iota = -1)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (htrace : Matrix.trace Q = 0) (hn : 0 < n) :
    (differentialMatroid F E).eRk
        (Set.range (projectiveDelayPanelField iota Q)) =
      (differentialMatroid F E).eRk
        (Set.range fun p : Fin (n + 1) × Fin (n + 1) ↦ Q p.1 p.2) := by
  letI : Nonempty (ProjectiveDelayIndex n) := by
    refine ⟨⟨(0, 0), ?_⟩⟩
    intro h
    have hz : (0 : Fin (n + 1)) = Fin.last n := congrArg Prod.fst h
    have hv : 0 = n := by simpa using congrArg Fin.val hz
    omega
  let M := differentialMatroid F E
  let qFamily : Fin (n + 1) × Fin (n + 1) → E := fun p ↦ Q p.1 p.2
  let pFamily : ProjectiveDelayIndex n → E := projectiveDelayPanelField iota Q
  have hPclose : Set.range pFamily ⊆ M.closure (Set.range qFamily) := by
    rintro _ ⟨p, rfl⟩
    apply (differentialMatroid_mem_closure_range_fintype_iff
      (F := F) (E := E) qFamily (pFamily p)).mpr
    let BQ := differentialAdjoin F (Set.range qFamily)
    let pBQ : BQ := ⟨pFamily p,
      projectiveDelayPanelField_mem_entry_differentialAdjoin iota Q p⟩
    have hp : DifferentialAlgebraicOver BQ (algebraMap BQ E pBQ) :=
      differentialAlgebraicOver_algebraMap pBQ
    simpa [BQ, pBQ] using hp
  have hQclose : Set.range qFamily ⊆ M.closure (Set.range pFamily) := by
    rintro _ ⟨p, rfl⟩
    apply (differentialMatroid_mem_closure_range_fintype_iff
      (F := F) (E := E) pFamily (qFamily p)).mpr
    let BP := differentialAdjoin F (Set.range pFamily)
    let qBP : BP := ⟨qFamily p,
      matrixEntry_mem_projectiveDelayPanelField_differentialAdjoin
        iota hiota Q htrace p.1 p.2⟩
    have hq : DifferentialAlgebraicOver BP (algebraMap BP E qBP) :=
      differentialAlgebraicOver_algebraMap qBP
    simpa [BP, qBP] using hq
  apply le_antisymm
  · calc
      M.eRk (Set.range pFamily) ≤ M.eRk (M.closure (Set.range qFamily)) :=
        M.eRk_mono hPclose
      _ = M.eRk (Set.range qFamily) := M.eRk_closure_eq _
  · calc
      M.eRk (Set.range qFamily) ≤ M.eRk (M.closure (Set.range pFamily)) :=
        M.eRk_mono hQclose
      _ = M.eRk (Set.range pFamily) := M.eRk_closure_eq _

theorem matrixWignerSmith_projectiveDelayPanel_eRk_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (iota : F) (hiota : iota * iota = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    (p : Fin (n + 1) × Fin (n + 1)) (hp : S p.1 p.2 ≠ 0)
    (hn : 0 < n) :
    (differentialMatroid F E).eRk
        (Set.range (projectiveDelayPanelField iota
          (matrixTracelessPartField (matrixWignerSmith iota S)))) =
      (differentialMatroid F E).eRk
        (Set.range fun q : Fin (n + 1) × Fin (n + 1) ↦
          matrixPivotNormalize S p q.1 q.2) := by
  rw [projectiveDelayPanelField_differentialMatroid_eRk_eq_entries
    iota hiota _ (matrixTracelessPartField_trace _) hn]
  exact matrixTracelessWignerSmith_projective_eRk_eq iota hiota S hdet p hp

theorem projectiveDelayPanelField_matrixWignerSmith_smul
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] [CharZero E] {n : ℕ}
    (iota : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hdet : S.det ≠ 0) (f : E) (hf : f ≠ 0) :
    projectiveDelayPanelField iota
        (matrixTracelessPartField (matrixWignerSmith iota (f • S))) =
      projectiveDelayPanelField iota
        (matrixTracelessPartField (matrixWignerSmith iota S)) := by
  rw [matrixTracelessPartField_matrixWignerSmith_smul iota S hdet f hf]

end

end GaloisForLFunctions.HTGeometry

