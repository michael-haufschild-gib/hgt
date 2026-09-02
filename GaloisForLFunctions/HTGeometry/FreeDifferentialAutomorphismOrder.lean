import GaloisForLFunctions.HTGeometry.DifferentialVariationalOreModule
import GaloisForLFunctions.HTGeometry.HypertranscendentalClockIncompressibility
import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableNet
import GaloisForLFunctions.HTGeometry.JetFieldOrderCharacterization

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DifferentialFieldAut

noncomputable section

variable {C : Type u} {ι : Type v} [Field C] [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

abbrev FreeAut := DifferentialFieldAut C (JetField C ι)

def freeFrechetMatrix (σ : FreeAut (C := C) (ι := ι)) :
    Matrix ι ι (DiffOp (JetField C ι)) :=
  fun i j => JetField.frechet (σ.toRingEquiv (JetField.jet (i, 0))) j

def freeDifferentialOrder (σ : FreeAut (C := C) (ι := ι)) : ℕ :=
  DiffOp.matDeg (freeFrechetMatrix σ)

/-- Applying a coefficient automorphism entrywise to an operator matrix. -/
def mapFreeFrechetMatrix (τ : FreeAut (C := C) (ι := ι))
    (P : Matrix ι ι (DiffOp (JetField C ι))) :
    Matrix ι ι (DiffOp (JetField C ι)) :=
  fun i j => DiffOp.map τ.toRingEquiv.toRingHom (P i j)

theorem freeDifferentialOrder_eq_sup_ordJet
    (σ : FreeAut (C := C) (ι := ι)) :
    freeDifferentialOrder σ = Finset.univ.sup fun i =>
      JetField.ordJet (σ.toRingEquiv (JetField.jet (i, 0))) := rfl

/-- Free-field order is exactly degree of the literal Fréchet Jacobian `(18)`. -/
theorem freeDifferentialOrder_eq_matDeg_freeFrechetMatrix
    (σ : FreeAut (C := C) (ι := ι)) :
    freeDifferentialOrder σ = DiffOp.matDeg (freeFrechetMatrix σ) := rfl

/-- The order bound is exactly rational expressibility in jets through that level. -/
theorem freeDifferentialOrder_le_iff
    [CharZero C] (σ : FreeAut (C := C) (ι := ι)) (N : ℕ) :
    freeDifferentialOrder σ ≤ N ↔
      ∀ i : ι, σ.toRingEquiv (JetField.jet (i, 0)) ∈
        IntermediateField.adjoin C
          ((fun p => (JetField.jet p : JetField C ι)) ''
            {p : ι × ℕ | p.2 ≤ N}) := by
  rw [freeDifferentialOrder_eq_sup_ordJet]
  constructor
  · intro h i
    apply (JetField.ordJet_le_iff _ N).mp
    exact le_trans
      (Finset.le_sup (f := fun j =>
        JetField.ordJet (σ.toRingEquiv (JetField.jet (j, 0)))) (Finset.mem_univ i)) h
  · intro h
    refine Finset.sup_le fun i _ => ?_
    exact (JetField.ordJet_le_iff _ N).mpr (h i)

theorem ordJet_generator (i : ι) :
    JetField.ordJet (JetField.jet (i, 0) : JetField C ι) = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [JetField.ordJet, DiffOp.degVec_le_iff]
  intro j
  by_cases h : j = i
  · subst j
    rw [JetField.frechet_jet_self, DiffOp.degree_mono (one_ne_zero : (1 : JetField C ι) ≠ 0)]
  · rw [JetField.frechet_jet_of_ne (n := 0) h, DiffOp.degree_zero]

@[simp] theorem freeDifferentialOrder_one :
    freeDifferentialOrder (1 : FreeAut (C := C) (ι := ι)) = 0 := by
  rw [freeDifferentialOrder_eq_sup_ordJet]
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun i _ => ?_
  change JetField.ordJet (JetField.jet (i, 0) : JetField C ι) ≤ 0
  rw [ordJet_generator (C := C) i]

private theorem ordJet_apply_le
    (τ : FreeAut (C := C) (ι := ι)) (u : JetField C ι) :
    JetField.ordJet (τ.toRingEquiv u) ≤
      JetField.ordJet u + freeDifferentialOrder τ := by
  letI algTau : Algebra (JetField C ι) (JetField C ι) :=
    τ.toRingEquiv.toRingHom.toAlgebra
  letI : SMul (JetField C ι) (JetField C ι) := algTau.toSMul
  haveI : IsScalarTower C (JetField C ι) (JetField C ι) :=
    @IsScalarTower.of_algebraMap_eq C (JetField C ι) (JetField C ι)
      _ _ _ _ algTau _ fun c => by
        change algebraMap C (JetField C ι) c =
          τ.toRingEquiv (algebraMap C (JetField C ι) c)
        rw [τ.fixes]
  have hδ : ∀ x : JetField C ι,
      algebraMap (JetField C ι) (JetField C ι) x′ =
        (algebraMap (JetField C ι) (JetField C ι) x)′ := τ.deriv_comm
  have hmap : algebraMap (JetField C ι) (JetField C ι) =
      τ.toRingEquiv.toRingHom := rfl
  have hmatrix :
      (JetField.frechetMatrix (C := C) (ι' := ι) (ι := ι)) =
        freeFrechetMatrix τ := by
    funext i j
    rfl
  have h := JetField.ordJet_algebraMap_le hδ u
  rw [hmap, hmatrix] at h
  exact h

/-- The free differential substitution chain rule, as a literal row-product identity. -/
theorem frechet_apply_eq_vecMul
    (τ : FreeAut (C := C) (ι := ι)) (u : JetField C ι) (j : ι) :
    JetField.frechet (τ.toRingEquiv u) j =
      DiffOp.vecMul
        (fun i => DiffOp.map τ.toRingEquiv.toRingHom (JetField.frechet u i))
        (freeFrechetMatrix τ) j := by
  letI algTau : Algebra (JetField C ι) (JetField C ι) :=
    τ.toRingEquiv.toRingHom.toAlgebra
  letI : SMul (JetField C ι) (JetField C ι) := algTau.toSMul
  haveI : IsScalarTower C (JetField C ι) (JetField C ι) :=
    @IsScalarTower.of_algebraMap_eq C (JetField C ι) (JetField C ι)
      _ _ _ _ algTau _ fun c => by
        change algebraMap C (JetField C ι) c =
          τ.toRingEquiv (algebraMap C (JetField C ι) c)
        rw [τ.fixes]
  have hδ : ∀ x : JetField C ι,
      algebraMap (JetField C ι) (JetField C ι) x′ =
        (algebraMap (JetField C ι) (JetField C ι) x)′ := τ.deriv_comm
  have hmap : algebraMap (JetField C ι) (JetField C ι) =
      τ.toRingEquiv.toRingHom := rfl
  have hmatrix :
      (JetField.frechetMatrix (C := C) (ι' := ι) (ι := ι)) =
        freeFrechetMatrix τ := by
    funext i k
    rfl
  have h := JetField.frechet_algebraMap_eq_vecMul hδ u j
  rw [hmap, hmatrix] at h
  exact h

/-- Fréchet matrices obey the exact differential-substitution cocycle law. -/
theorem freeFrechetMatrix_mul_apply
    (σ τ : FreeAut (C := C) (ι := ι)) (i j : ι) :
    freeFrechetMatrix (σ * τ) i j =
      DiffOp.vecMul
        (fun k => DiffOp.map τ.toRingEquiv.toRingHom (freeFrechetMatrix σ i k))
        (freeFrechetMatrix τ) j := by
  change JetField.frechet
      (τ.toRingEquiv (σ.toRingEquiv (JetField.jet (i, 0)))) j = _
  exact frechet_apply_eq_vecMul τ _ j

/-- Matrix form of the exact Fréchet cocycle. -/
theorem freeFrechetMatrix_mul
    (σ τ : FreeAut (C := C) (ι := ι)) :
    freeFrechetMatrix (σ * τ) =
      mapFreeFrechetMatrix τ (freeFrechetMatrix σ) * freeFrechetMatrix τ := by
  ext i j
  rw [freeFrechetMatrix_mul_apply]
  rfl

/-- Identity differential substitution has the identity Fréchet matrix. -/
omit [Fintype ι] in
@[simp] theorem freeFrechetMatrix_one :
    freeFrechetMatrix (1 : FreeAut (C := C) (ι := ι)) = 1 := by
  funext i j
  by_cases h : i = j
  · subst j
    rw [Matrix.one_apply_eq]
    change JetField.frechet (JetField.jet (i, 0) : JetField C ι) i = 1
    rw [JetField.frechet_jet_self, DiffOp.one_def]
  · rw [Matrix.one_apply_ne h]
    change JetField.frechet (JetField.jet (i, 0) : JetField C ι) j = 0
    exact JetField.frechet_jet_of_ne (n := 0) (Ne.symm h)

/-- The inverse substitution gives a right twisted inverse for the Fréchet matrix. -/
theorem freeFrechetMatrix_mul_inverse
    (σ : FreeAut (C := C) (ι := ι)) :
    mapFreeFrechetMatrix σ⁻¹ (freeFrechetMatrix σ) *
      freeFrechetMatrix σ⁻¹ = 1 := by
  rw [← freeFrechetMatrix_mul, mul_inv_cancel, freeFrechetMatrix_one]

/-- The inverse substitution gives the complementary twisted inverse. -/
theorem freeFrechetMatrix_inverse_mul
    (σ : FreeAut (C := C) (ι := ι)) :
    mapFreeFrechetMatrix σ (freeFrechetMatrix σ⁻¹) *
      freeFrechetMatrix σ = 1 := by
  rw [← freeFrechetMatrix_mul, inv_mul_cancel, freeFrechetMatrix_one]

theorem freeDifferentialOrder_mul_le
    (σ τ : FreeAut (C := C) (ι := ι)) :
    freeDifferentialOrder (σ * τ) ≤
      freeDifferentialOrder σ + freeDifferentialOrder τ := by
  rw [freeDifferentialOrder_eq_sup_ordJet]
  refine Finset.sup_le fun i _ => ?_
  exact le_trans (ordJet_apply_le τ (σ.toRingEquiv (JetField.jet (i, 0))))
    (Nat.add_le_add_right
      (Finset.le_sup (f := fun j =>
        JetField.ordJet (σ.toRingEquiv (JetField.jet (j, 0)))) (Finset.mem_univ i)) _)

/-- A coordinate conjugacy changes every finite free-field order by a fixed additive overhead. -/
theorem freeDifferentialOrder_conjugate_le
    (h σ : FreeAut (C := C) (ι := ι)) :
    freeDifferentialOrder (SubadditiveClockGauge.conjugate h σ) ≤
      freeDifferentialOrder σ +
        (freeDifferentialOrder h + freeDifferentialOrder h⁻¹) := by
  calc
    freeDifferentialOrder (h * σ * h⁻¹) ≤
        freeDifferentialOrder (h * σ) + freeDifferentialOrder h⁻¹ :=
      freeDifferentialOrder_mul_le _ _
    _ ≤ (freeDifferentialOrder h + freeDifferentialOrder σ) +
        freeDifferentialOrder h⁻¹ :=
      Nat.add_le_add_right (freeDifferentialOrder_mul_le h σ) _
    _ = freeDifferentialOrder σ +
        (freeDifferentialOrder h + freeDifferentialOrder h⁻¹) := by omega

/-- Reverse finite-overhead comparison for a coordinate conjugacy. -/
theorem freeDifferentialOrder_le_conjugate
    (h σ : FreeAut (C := C) (ι := ι)) :
    freeDifferentialOrder σ ≤
      freeDifferentialOrder (SubadditiveClockGauge.conjugate h σ) +
        (freeDifferentialOrder h + freeDifferentialOrder h⁻¹) := by
  have hle := freeDifferentialOrder_conjugate_le h⁻¹
    (SubadditiveClockGauge.conjugate h σ)
  have heq : SubadditiveClockGauge.conjugate h⁻¹
      (SubadditiveClockGauge.conjugate h σ) = σ := by
    simp [SubadditiveClockGauge.conjugate, mul_assoc]
  rw [heq] at hle
  simpa [add_comm] using hle

/-- Absolute finite-order coordinate overhead, formula `(23)` of the card. -/
theorem abs_freeDifferentialOrder_conjugate_sub_le
    (h σ : FreeAut (C := C) (ι := ι)) :
    abs ((freeDifferentialOrder (SubadditiveClockGauge.conjugate h σ) : ℝ) -
      freeDifferentialOrder σ) ≤
        ((freeDifferentialOrder h + freeDifferentialOrder h⁻¹ : ℕ) : ℝ) := by
  rw [abs_le]
  constructor
  · have hle := freeDifferentialOrder_le_conjugate h σ
    have hleR : (freeDifferentialOrder σ : ℝ) ≤
        freeDifferentialOrder (SubadditiveClockGauge.conjugate h σ) +
          (freeDifferentialOrder h + freeDifferentialOrder h⁻¹) := by
      exact_mod_cast hle
    push_cast at hleR ⊢
    linarith
  · have hle := freeDifferentialOrder_conjugate_le h σ
    have hleR :
        (freeDifferentialOrder (SubadditiveClockGauge.conjugate h σ) : ℝ) ≤
          freeDifferentialOrder σ +
            (freeDifferentialOrder h + freeDifferentialOrder h⁻¹) := by
      exact_mod_cast hle
    push_cast at hleR ⊢
    linarith

def freeOrderGauge : SubadditiveClockGauge (FreeAut (C := C) (ι := ι)) where
  cost σ := freeDifferentialOrder σ
  cost_nonneg σ := Nat.cast_nonneg _
  cost_one := by simp
  cost_mul_le σ τ := by exact_mod_cast freeDifferentialOrder_mul_le σ τ

theorem freeOrderGauge_orbitCost (σ : FreeAut (C := C) (ι := ι)) (n : ℕ) :
    freeOrderGauge.orbitCost σ n = freeDifferentialOrder (σ ^ n) := rfl

theorem tendsto_normalized_freeDifferentialOrder
    (σ : FreeAut (C := C) (ι := ι)) :
    Filter.Tendsto (fun n : ℕ => (freeDifferentialOrder (σ ^ n) : ℝ) / n)
      Filter.atTop (nhds (freeOrderGauge.translationLength σ)) := by
  simpa [freeOrderGauge_orbitCost] using freeOrderGauge.tendsto_normalizedOrbitCost σ

/-- Intrinsic clock speed is invariant under every differential-birational coordinate change. -/
theorem freeOrderTranslationLength_conjugate
    (h σ : FreeAut (C := C) (ι := ι)) :
    freeOrderGauge.translationLength (SubadditiveClockGauge.conjugate h σ) =
      freeOrderGauge.translationLength σ :=
  freeOrderGauge.translationLength_conjugate h σ

end

end DifferentialFieldAut

end GaloisForLFunctions.HTGeometry
