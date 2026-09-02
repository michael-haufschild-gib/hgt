import GaloisForLFunctions.HTGeometry.FreeDifferentialAutomorphismOrder
import GaloisForLFunctions.HTGeometry.KaehlerDifferentialIndependence
import GaloisForLFunctions.HTGeometry.DifferentialIndependentTower
import GaloisForLFunctions.HTGeometry.FreeCoordinateField

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DifferentialFieldAut

variable {C : Type u} [Field C] [CharZero C] {r : ℕ}

private abbrev K (C : Type u) [Field C] (r : ℕ) := JetField C (Fin r)

private instance : IsConstantBase C (K C r) where
  deriv_algebraMap c := by
    rw [JetField.deriv_eq]
    exact Derivation.map_algebraMap (JetField.jetDerivation (C := C) (ι := Fin r)) c

/-- Order-zero free differential generators. -/
def freeGenerator (C : Type u) [Field C] (r : ℕ) (i : Fin r) : K C r :=
  JetField.jet (i, 0)

omit [CharZero C] in
theorem differentialJet_freeGenerator (i : Fin r) (n : ℕ) :
    differentialJet n (freeGenerator C r i) = (JetField.jet (i, n) : K C r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [differentialJet_succ, ih, JetField.deriv_jet]

omit [CharZero C] in
theorem differentialIndependent_freeGenerator :
    DifferentialIndependent C (freeGenerator C r) := by
  unfold DifferentialIndependent
  convert JetField.algebraicIndependent_jet (C := C) (ι := Fin r) using 1
  funext p
  exact differentialJet_freeGenerator (C := C) p.1 p.2

theorem differentialAdjoin_freeGenerator_eq_top :
    differentialAdjoin C (Set.range (freeGenerator C r)) = ⊤ := by
  rw [differentialAdjoin, differentialJetSet_range]
  have hset :
      Set.range (fun p : Fin r × ℕ => differentialJet p.2 (freeGenerator C r p.1)) =
        Set.range (fun p : Fin r × ℕ => (JetField.jet p : K C r)) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, (differentialJet_freeGenerator (C := C) p.1 p.2).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, differentialJet_freeGenerator (C := C) p.1 p.2⟩
  rw [hset]
  have hrange : Set.range (fun p : Fin r × ℕ => (JetField.jet p : K C r)) =
      freeCoordinate C (Fin r × ℕ) '' Set.univ := by
    rw [Set.image_univ]
    rfl
  rw [hrange]
  exact freeCoordinateField_univ

private abbrev freeOreTorsion (C : Type u) [Field C] [CharZero C] (r : ℕ) :=
  DiffOp.oreTorsionSubmodule (K := K C r) (M := Ω[K C r⁄C])

/-- Natural classes of the free-coordinate differentials in the torsion-free Ore quotient. -/
def freeVariationalBasisVector (i : Fin r) : VariationalOreModule C (K C r) :=
  (freeOreTorsion C r).mkQ (KaehlerDifferential.D C (K C r) (freeGenerator C r i))

theorem linearIndependent_freeVariationalBasisVector :
    LinearIndependent (DiffOp (K C r)) (freeVariationalBasisVector (C := C) (r := r)) := by
  apply linearIndependent_mkQ_of_torsion (freeOreTorsion C r)
  · intro ω hω
    exact hω
  · exact linearIndependent_diffOp_D_of_differentialIndependent
      (differentialIndependent_freeGenerator (C := C) (r := r))

theorem span_freeVariationalBasisVector_eq_top :
    Submodule.span (DiffOp (K C r))
      (Set.range (freeVariationalBasisVector (C := C) (r := r))) = ⊤ := by
  let N := freeOreTorsion C r
  have himg : Submodule.map N.mkQ
      (Submodule.span (DiffOp (K C r))
        (KaehlerDifferential.D C (K C r) '' Set.range (freeGenerator C r))) = ⊤ := by
    rw [span_diffOp_D_eq_top (differentialAdjoin_freeGenerator_eq_top (C := C) (r := r)),
      Submodule.map_top, N.range_mkQ]
  rw [Submodule.map_span] at himg
  have hset : (N.mkQ : Ω[K C r⁄C] → (Ω[K C r⁄C]) ⧸ N) ''
      (KaehlerDifferential.D C (K C r) '' Set.range (freeGenerator C r)) =
        Set.range (freeVariationalBasisVector (C := C) (r := r)) := by
    rw [← Set.image_comp, ← Set.range_comp]
    rfl
  rwa [hset] at himg

/-- Canonical free-coordinate operator basis of the variational Ore module. -/
def freeVariationalOreBasis :
    Module.Basis (Fin r) (DiffOp (K C r)) (VariationalOreModule C (K C r)) :=
  Module.Basis.mk linearIndependent_freeVariationalBasisVector (by
    rw [span_freeVariationalBasisVector_eq_top])

@[simp] theorem freeVariationalOreBasis_apply (i : Fin r) :
    freeVariationalOreBasis (C := C) (r := r) i = freeVariationalBasisVector (C := C) i := by
  rw [freeVariationalOreBasis, Module.Basis.mk_apply]

omit [CharZero C] in
/-- Universal Kähler differential in the free field, expanded in the Fréchet row. -/
theorem kaehlerD_eq_sum_frechet_smul (u : K C r) :
    KaehlerDifferential.D C (K C r) u =
      ∑ j : Fin r, JetField.frechet u j •
        KaehlerDifferential.D C (K C r) (freeGenerator C r j) := by
  classical
  obtain ⟨s, hs, hexp⟩ :=
    JetField.exists_pd_expansion (KaehlerDifferential.D C (K C r)) u
  let T : Finset ℕ := s.image Prod.snd
  have hT (j : Fin r) : ∀ n ∉ T, DiffOp.coeff (JetField.frechet u j) n = 0 := by
    intro n hn
    rw [JetField.coeff_frechet, hs (j, n)]
    intro hmem
    exact hn (Finset.mem_image.mpr ⟨(j, n), hmem, rfl⟩)
  have hrow (j : Fin r) :
      JetField.frechet u j • KaehlerDifferential.D C (K C r) (freeGenerator C r j) =
        ∑ n ∈ T, JetField.pd (j, n) u •
          KaehlerDifferential.D C (K C r) (JetField.jet (j, n)) := by
    rw [diffOp_smul_def, diffOpSMul_eq_sum _ _ _ T (hT j)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [JetField.coeff_frechet, kaehlerConnection_iterate_D,
      differentialJet_freeGenerator]
  have hsub : s ⊆ (Finset.univ : Finset (Fin r)) ×ˢ T := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_univ p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hsum :
      ∑ p ∈ s, JetField.pd p u • KaehlerDifferential.D C (K C r) (JetField.jet p) =
        ∑ p ∈ (Finset.univ : Finset (Fin r)) ×ˢ T,
          JetField.pd p u • KaehlerDifferential.D C (K C r) (JetField.jet p) := by
    refine Finset.sum_subset hsub ?_
    intro p _ hp
    rw [hs p hp, zero_smul]
  rw [hexp, hsum, Finset.sum_product]
  exact (Finset.sum_congr rfl fun j _ => hrow j).symm

/-- Canonical variational action sends a free basis vector by its literal Fréchet row. -/
theorem variationalOreModuleEquiv_freeVariationalOreBasis_apply
    (σ : FreeAut (C := C) (ι := Fin r)) (i : Fin r) :
    variationalOreModuleEquiv σ.fixes σ.deriv_comm
        (freeVariationalOreBasis (C := C) (r := r) i) =
      ∑ j, freeFrechetMatrix σ i j • freeVariationalOreBasis (C := C) (r := r) j := by
  rw [freeVariationalOreBasis_apply, freeVariationalBasisVector,
    variationalOreModuleEquiv_apply, variationalOreSemilinearMap_mk,
    kaehlerSemilinear_D, kaehlerD_eq_sum_frechet_smul]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_smul, freeVariationalOreBasis_apply, freeVariationalBasisVector]
    rfl

/-- In natural free coordinates, canonical Ore action matrix is exactly Fréchet matrix `(18)`. -/
theorem variationalOre_basisMapMatrix_free_eq_freeFrechetMatrix
    (σ : FreeAut (C := C) (ι := Fin r)) :
    basisMapMatrix (freeVariationalOreBasis (C := C) (r := r))
        (variationalOreModuleEquiv σ.fixes σ.deriv_comm) = freeFrechetMatrix σ := by
  symm
  exact matrix_eq_basisMapMatrix_of_apply _ _ _
    (variationalOreModuleEquiv_freeVariationalOreBasis_apply (C := C) σ)

/-- The canonical invertible Ore matrix is literally the Fréchet matrix in free coordinates. -/
theorem variationalOreOperatorMatrixUnit_free_val
    (σ : FreeAut (C := C) (ι := Fin r)) :
    (variationalOreOperatorMatrixUnit σ.fixes σ.deriv_comm
        (freeVariationalOreBasis (C := C) (r := r)) :
      Matrix (Fin r) (Fin r) (DiffOp (K C r))) = freeFrechetMatrix σ := by
  exact variationalOre_basisMapMatrix_free_eq_freeFrechetMatrix (C := C) σ

/-- The free Fréchet matrix is invertible over the differential-operator ring itself. -/
theorem isUnit_freeFrechetMatrix (σ : FreeAut (C := C) (ι := Fin r)) :
    IsUnit (freeFrechetMatrix σ) := by
  exact ⟨variationalOreOperatorMatrixUnit σ.fixes σ.deriv_comm
      (freeVariationalOreBasis (C := C) (r := r)),
    variationalOreOperatorMatrixUnit_free_val (C := C) σ⟩

/-- Free differential order is degree of the actual canonical variational action matrix. -/
theorem freeDifferentialOrder_eq_variationalOreActionMatrix_matDeg
    (σ : FreeAut (C := C) (ι := Fin r)) :
    freeDifferentialOrder σ =
      DiffOp.matDeg
        (basisMapMatrix (freeVariationalOreBasis (C := C) (r := r))
          (variationalOreModuleEquiv σ.fixes σ.deriv_comm)) := by
  rw [variationalOre_basisMapMatrix_free_eq_freeFrechetMatrix]
  exact freeDifferentialOrder_eq_matDeg_freeFrechetMatrix σ

/-- Completion preserves the literal Fréchet matrix of the canonical variational action. -/
theorem variationalOreCompletedMatrixUnit_free_val
    (σ : FreeAut (C := C) (ι := Fin r)) :
    (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm
        (freeVariationalOreBasis (C := C) (r := r)) :
      Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp (K C r))) =
        (freeFrechetMatrix σ).map DiffOp.diffOpToCompletedPseudoRingHom := by
  rw [variationalOreCompletedMatrixUnit_val,
    variationalOre_basisMapMatrix_free_eq_freeFrechetMatrix]

private theorem isUnit_finOne_entry {R : Type*} [Ring R]
    {A : Matrix (Fin 1) (Fin 1) R} (hA : IsUnit A) : IsUnit (A 0 0) := by
  obtain ⟨U, rfl⟩ := hA
  let V : Matrix (Fin 1) (Fin 1) R := (↑U⁻¹ : Matrix (Fin 1) (Fin 1) R)
  have hUV : (↑U : Matrix (Fin 1) (Fin 1) R) * V = 1 := by
    simp [V]
  have hVU : V * (↑U : Matrix (Fin 1) (Fin 1) R) = 1 := by
    simp [V]
  have hUV00 := congrFun (congrFun hUV 0) 0
  have hVU00 := congrFun (congrFun hVU 0) 0
  refine ⟨⟨(↑U : Matrix (Fin 1) (Fin 1) R) 0 0, V 0 0, ?_, ?_⟩, rfl⟩
  · simpa [Matrix.mul_apply] using hUV00
  · simpa [Matrix.mul_apply] using hVU00

private theorem degree_eq_zero_of_isUnit_local {L : Type*} [Field L] [Differential L]
    {p : DiffOp L} (hp : IsUnit p) : DiffOp.degree p = 0 := by
  obtain ⟨u, rfl⟩ := hp
  have hu : ((u : DiffOp L) ≠ 0) := Units.ne_zero u
  have huinv : ((↑u⁻¹ : DiffOp L) ≠ 0) := Units.ne_zero u⁻¹
  have hdeg := DiffOp.degree_mul hu huinv
  rw [Units.mul_inv] at hdeg
  have hone : DiffOp.degree (1 : DiffOp L) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply DiffOp.degree_le_iff.mpr
    intro n hn
    rw [DiffOp.one_def, DiffOp.coeff_mono_of_ne 1 (Nat.ne_of_gt hn).symm]
  rw [hone] at hdeg
  exact (Nat.add_eq_zero_iff.mp hdeg.symm).1

/-- Exact rank-one no-go: every free differential automorphism has order zero. -/
theorem freeDifferentialOrder_finOne_eq_zero
    (σ : FreeAut (C := C) (ι := Fin 1)) : freeDifferentialOrder σ = 0 := by
  have hunit : IsUnit (freeFrechetMatrix σ 0 0) :=
    isUnit_finOne_entry (isUnit_freeFrechetMatrix σ)
  have hdegree := degree_eq_zero_of_isUnit_local hunit
  simpa [freeDifferentialOrder, DiffOp.matDeg, DiffOp.degVec] using hdegree

/-- Every iterate in free differential rank one has order zero. -/
theorem freeDifferentialOrder_pow_finOne_eq_zero
    (σ : FreeAut (C := C) (ι := Fin 1)) (n : ℕ) :
    freeDifferentialOrder (σ ^ n) = 0 :=
  freeDifferentialOrder_finOne_eq_zero (σ ^ n)

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
