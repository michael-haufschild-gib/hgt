import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ResourceFilteredRelations
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.PassiveRelationHermitianCrossFibre
import GaloisForLFunctions.HTGeometry.HermitianSubmoduleTraceOrthonormal
import GaloisForLFunctions.HTGeometry.FiniteUnitaryEnergyDefectLaw
import GaloisForLFunctions.HTGeometry.TwoReplicaPositiveGraphEdgeCasimir
import Mathlib.LinearAlgebra.Trace

/-!
# Aggregate bipartite tidal tomography

This file proves the arbitrary finite-dimensional adjoint Casimir identity and the exact
aggregate boundary-leakage coefficient from Card Theorem 5.3. The proof is basis-independent:
the trace of the squared commutator is evaluated in matrix-unit coordinates, then evaluated again
in a Hilbert--Schmidt orthonormal traceless-Hermitian basis completed by the identity direction.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix
open GaloisForLFunctions.HTGeometry
open scoped BigOperators Kronecker

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- Canonical trace-orthonormal basis of the traceless Hermitian factor space. -/
noncomputable abbrev tracelessHermitianGenerator (m : Type*)
    [Fintype m] [DecidableEq m] [Nonempty m] :=
  GaloisForLFunctions.HTGeometry.traceOrthonormalSubmoduleGenerator
    (hermitianTracelessMatrices m)
    (fun _ h => h.1)

theorem tracelessHermitianGenerator_mem
    (i : Fin (Module.finrank ℝ (hermitianTracelessMatrices m))) :
    tracelessHermitianGenerator m i ∈ hermitianTracelessMatrices m :=
  GaloisForLFunctions.HTGeometry.traceOrthonormalSubmoduleGenerator_mem
    (hermitianTracelessMatrices m) (fun _ h => h.1) i

theorem tracelessHermitianGenerator_isHermitian
    (i : Fin (Module.finrank ℝ (hermitianTracelessMatrices m))) :
    (tracelessHermitianGenerator m i).IsHermitian :=
  GaloisForLFunctions.HTGeometry.traceOrthonormalSubmoduleGenerator_isHermitian
    (hermitianTracelessMatrices m) (fun _ h => h.1) i

theorem tracelessHermitianGenerator_trace
    (i : Fin (Module.finrank ℝ (hermitianTracelessMatrices m))) :
    (tracelessHermitianGenerator m i).trace = 0 :=
  (tracelessHermitianGenerator_mem i).2

theorem tracelessHermitianGenerator_hsInner
    (i j : Fin (Module.finrank ℝ (hermitianTracelessMatrices m))) :
    QuantumAlg.hsInner (tracelessHermitianGenerator m i)
        (tracelessHermitianGenerator m j) = if i = j then 1 else 0 := by
  simpa [QuantumAlg.hsInner,
    (tracelessHermitianGenerator_isHermitian i).eq] using
    GaloisForLFunctions.HTGeometry.traceOrthonormalSubmoduleGenerator_trace_mul
      (hermitianTracelessMatrices m) (fun _ h => h.1) i j

/-- Identity followed by a trace-orthonormal traceless-Hermitian family. -/
noncomputable def completedTracelessHermitianFamily (m : Type*)
    [Fintype m] [DecidableEq m] [Nonempty m] :
    Option (Fin (Module.finrank ℝ (hermitianTracelessMatrices m))) → Matrix m m ℂ
  | none => 1
  | some i => tracelessHermitianGenerator m i

theorem completedTracelessHermitianFamily_linearIndependent :
    LinearIndependent ℂ (completedTracelessHermitianFamily m) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hnone : c none = 0 := by
    have htrace := congrArg (Matrix.traceLinearMap m ℂ ℂ) hc
    simp [completedTracelessHermitianFamily, Fintype.sum_option,
      tracelessHermitianGenerator_trace] at htrace
    exact htrace
  intro p
  cases p with
  | none => exact hnone
  | some i =>
      have hip := congrArg
        (fun X : Matrix m m ℂ => QuantumAlg.hsInner (tracelessHermitianGenerator m i) X) hc
      rw [QuantumAlg.hsInner_sum_right] at hip
      simp only [Fintype.sum_option, completedTracelessHermitianFamily,
        QuantumAlg.hsInner_smul_right, tracelessHermitianGenerator_hsInner] at hip
      have hident : QuantumAlg.hsInner (tracelessHermitianGenerator m i)
          (1 : Matrix m m ℂ) = 0 := by
        simp [QuantumAlg.hsInner, (tracelessHermitianGenerator_isHermitian i).eq,
          tracelessHermitianGenerator_trace i]
      rw [hident, mul_zero, zero_add] at hip
      simpa using hip

theorem traceCenter_mem_hermitianTracelessMatrices
    {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    traceCenter H ∈ hermitianTracelessMatrices m := by
  exact ⟨IsSelfAdjoint.traceCenter hH, trace_traceCenter H⟩

theorem selfAdjoint_mem_span_completedTracelessHermitianFamily
    {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    H ∈ Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m)) := by
  classical
  let L := hermitianTracelessMatrices m
  have hcenter : traceCenter H ∈ L := traceCenter_mem_hermitianTracelessMatrices hH
  obtain ⟨θ, hθ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_traceOrthonormalCoordinates
      L (fun _ h => h.1) hcenter
  have hgen (i : Fin (Module.finrank ℝ L)) :
      tracelessHermitianGenerator m i ∈
        Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m)) := by
    apply Submodule.subset_span
    exact ⟨some i, rfl⟩
  have hcenterSpan : traceCenter H ∈
      Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m)) := by
    rw [← hθ]
    exact Submodule.sum_mem _ fun i _ =>
      (Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m))).smul_mem
        (θ i : ℂ) (hgen i)
  have hone : (1 : Matrix m m ℂ) ∈
      Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m)) := by
    apply Submodule.subset_span
    exact ⟨none, rfl⟩
  have hscalar :=
    (Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m))).smul_mem
      ((Fintype.card m : ℂ)⁻¹ * H.trace) hone
  have hsplit : H = traceCenter H +
      (((Fintype.card m : ℂ)⁻¹ * H.trace) • (1 : Matrix m m ℂ)) := by
    simp [traceCenter]
  rw [hsplit]
  exact (Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m))).add_mem
    hcenterSpan hscalar

theorem completedTracelessHermitianFamily_span_top :
    Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m)) = ⊤ := by
  apply top_unique
  intro X _
  have hre := selfAdjoint_mem_span_completedTracelessHermitianFamily
    (m := m) (realPart X).property
  have him := selfAdjoint_mem_span_completedTracelessHermitianFamily
    (m := m) (imaginaryPart X).property
  have himI :=
    (Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m))).smul_mem
      Complex.I him
  rw [← realPart_add_I_smul_imaginaryPart X]
  exact (Submodule.span ℂ (Set.range (completedTracelessHermitianFamily m))).add_mem hre himI

/-- Complex basis obtained by completing a real traceless-Hermitian orthonormal basis with the
identity. -/
noncomputable def completedTracelessHermitianBasis :
    Module.Basis (Option (Fin (Module.finrank ℝ (hermitianTracelessMatrices m)))) ℂ
      (Matrix m m ℂ) :=
  Module.Basis.mk completedTracelessHermitianFamily_linearIndependent
    (by rw [completedTracelessHermitianFamily_span_top])

@[simp] theorem completedTracelessHermitianBasis_apply
    (p : Option (Fin (Module.finrank ℝ (hermitianTracelessMatrices m)))) :
    completedTracelessHermitianBasis (m := m) p =
      completedTracelessHermitianFamily m p := by
  rw [completedTracelessHermitianBasis, Module.Basis.mk_apply]

/-- Complex-linear commutator on one finite factor. -/
def factorCommutatorLinear (C : Matrix m m ℂ) :
    Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun X := ringCommutator C X
  map_add' X Y := by
    simp only [ringCommutator, Matrix.mul_add, Matrix.add_mul]
    noncomm_ring
  map_smul' c X := by
    simp only [ringCommutator, Matrix.mul_smul, Matrix.smul_mul]
    simp only [RingHom.id_apply]
    module

@[simp] theorem factorCommutatorLinear_apply (C X : Matrix m m ℂ) :
    factorCommutatorLinear C X = ringCommutator C X := rfl

theorem completedTracelessHermitianBasis_repr_some (X : Matrix m m ℂ)
    (i : Fin (Module.finrank ℝ (hermitianTracelessMatrices m))) :
    (completedTracelessHermitianBasis (m := m)).repr X (some i) =
      QuantumAlg.hsInner (tracelessHermitianGenerator m i) X := by
  classical
  let b := completedTracelessHermitianBasis (m := m)
  have hsum := b.sum_repr X
  have h := congrArg
    (fun Y : Matrix m m ℂ => QuantumAlg.hsInner (tracelessHermitianGenerator m i) Y)
    hsum
  rw [QuantumAlg.hsInner_sum_right] at h
  have hident : QuantumAlg.hsInner (tracelessHermitianGenerator m i)
      (1 : Matrix m m ℂ) = 0 := by
    simp [QuantumAlg.hsInner, (tracelessHermitianGenerator_isHermitian i).eq,
      tracelessHermitianGenerator_trace i]
  simp only [b, completedTracelessHermitianBasis_apply,
    completedTracelessHermitianFamily, Fintype.sum_option,
    QuantumAlg.hsInner_smul_right, hident, mul_zero, zero_add,
    tracelessHermitianGenerator_hsInner] at h
  simpa using h

/-- Trace of the squared adjoint action evaluated in a traceless-Hermitian orthonormal basis. -/
theorem sum_tracelessHermitianGenerator_hsInner_commutator_eq_trace_square
    (C : Matrix m m ℂ) (hC : C.IsHermitian) :
    (∑ i, QuantumAlg.hsInner
        (ringCommutator C (tracelessHermitianGenerator m i))
        (ringCommutator C (tracelessHermitianGenerator m i))) =
      (LinearMap.trace ℂ (Matrix m m ℂ))
        ((factorCommutatorLinear C).comp (factorCommutatorLinear C)) := by
  classical
  let b := completedTracelessHermitianBasis (m := m)
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  have hnone : ((b.repr
      (((factorCommutatorLinear C).comp (factorCommutatorLinear C)) (b none))) none) = 0 := by
    have hbnone : b none = (1 : Matrix m m ℂ) := by
      rw [show b none = completedTracelessHermitianFamily m none by simp [b]]
      rfl
    rw [hbnone]
    simp [factorCommutatorLinear, ringCommutator]
  rw [Fintype.sum_option, hnone, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [completedTracelessHermitianBasis_repr_some]
  have hbSome : b (some i) = tracelessHermitianGenerator m i := by
    rw [show b (some i) = completedTracelessHermitianFamily m (some i) by simp [b]]
    rfl
  rw [hbSome]
  change QuantumAlg.hsInner
      (ringCommutator C (tracelessHermitianGenerator m i))
      (ringCommutator C (tracelessHermitianGenerator m i)) =
    QuantumAlg.hsInner (tracelessHermitianGenerator m i)
      (ringCommutator C (ringCommutator C (tracelessHermitianGenerator m i)))
  exact GaloisForLFunctions.HTGeometry.hsInner_ringCommutator_selfAdjoint
    C (tracelessHermitianGenerator m i)
      (ringCommutator C (tracelessHermitianGenerator m i)) hC

theorem ringCommutator_sq_single_coefficient (C : Matrix m m ℂ) (i j : m) :
    ringCommutator C (ringCommutator C (Matrix.single i j 1)) i j =
      (C * C) i i + (C * C) j j - 2 * C i i * C j j := by
  classical
  simp only [ringCommutator, Matrix.sub_apply, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_apply, Matrix.single]
  simp
  have hleft (x : m) :
      (∑ y : m, if i = x ∧ j = y then C y j else 0) =
        if i = x then C j j else 0 := by
    by_cases hx : i = x
    · subst x
      simp
    · simp [hx]
  have hright (x : m) :
      (∑ y : m, if i = y ∧ j = x then C i y else 0) =
        if j = x then C i i else 0 := by
    by_cases hx : j = x
    · subst x
      simp
    · simp [hx]
  simp_rw [hleft, hright]
  simp
  ring

@[simp] theorem matrixStdBasis_repr_apply (X : Matrix m m ℂ) (p : m × m) :
    ((Matrix.stdBasis ℂ m m).repr X) p = X p.1 p.2 := rfl

/-- Basis-free trace of the squared adjoint action, evaluated explicitly in matrix units. -/
theorem factorCommutatorLinear_square_trace (C : Matrix m m ℂ) :
    (LinearMap.trace ℂ (Matrix m m ℂ))
        ((factorCommutatorLinear C).comp (factorCommutatorLinear C)) =
      2 * (Fintype.card m : ℂ) * (C * C).trace - 2 * C.trace ^ (2 : ℕ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ m m)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.comp_apply, factorCommutatorLinear_apply, matrixStdBasis_repr_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Matrix.stdBasis_eq_single]
  simp_rw [ringCommutator_sq_single_coefficient]
  let S : ℂ := ∑ i : m, C i i
  let Q : ℂ := ∑ i : m, (C * C) i i
  have hfirst : (∑ i : m, ∑ _j : m, (C * C) i i) = (Fintype.card m : ℂ) * Q := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hsecond : (∑ _i : m, ∑ j : m, (C * C) j j) =
      (Fintype.card m : ℂ) * Q := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have hcross : (∑ i : m, ∑ j : m, 2 * C i i * C j j) = 2 * S ^ (2 : ℕ) := by
    calc
      _ = ∑ i : m, (2 * C i i) * S := by
        dsimp [S]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = (∑ i : m, 2 * C i i) * S := by rw [Finset.sum_mul]
      _ = 2 * S ^ (2 : ℕ) := by rw [← Finset.mul_sum]; ring
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hfirst, hsecond, hcross]
  change _ = 2 * (Fintype.card m : ℂ) * Q - 2 * S ^ (2 : ℕ)
  ring

/-- Hilbert--Schmidt self-pairing is the complexification of the real entrywise energy. -/
theorem hsInner_self_eq_finiteMatrixHilbertSchmidtEnergy (X : Matrix m m ℂ) :
    QuantumAlg.hsInner X X =
      (GaloisForLFunctions.HTGeometry.finiteMatrixHilbertSchmidtEnergy X : ℂ) := by
  change (Xᴴ * X).trace = (((Xᴴ * X).trace).re : ℂ)
  rw [trace_conjTranspose_mul_self]
  norm_cast

/-- **Card adjoint Casimir `(5.9)`.** Every traceless Hermitian factor matrix has total
commutator energy exactly `2 dim` times its Hilbert--Schmidt energy in a complete
trace-orthonormal traceless-Hermitian reporter basis. -/
theorem sum_tracelessHermitianGenerator_commutatorEnergy
    (C : Matrix m m ℂ) (hC : C.IsHermitian) (htrace : C.trace = 0) :
    (∑ i, GaloisForLFunctions.HTGeometry.finiteMatrixHilbertSchmidtEnergy
      (ringCommutator C (tracelessHermitianGenerator m i))) =
      2 * (Fintype.card m : ℝ) *
        GaloisForLFunctions.HTGeometry.finiteMatrixHilbertSchmidtEnergy C := by
  have hcomplex :=
    sum_tracelessHermitianGenerator_hsInner_commutator_eq_trace_square C hC
  rw [factorCommutatorLinear_square_trace C, htrace,
    zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero, sub_zero] at hcomplex
  have hCenergy : (C * C).trace =
      (GaloisForLFunctions.HTGeometry.finiteMatrixHilbertSchmidtEnergy C : ℂ) := by
    rw [← hsInner_self_eq_finiteMatrixHilbertSchmidtEnergy C]
    simp [QuantumAlg.hsInner, hC.eq]
  rw [hCenergy] at hcomplex
  simp_rw [hsInner_self_eq_finiteMatrixHilbertSchmidtEnergy] at hcomplex
  exact_mod_cast hcomplex

/-- Hilbert--Schmidt adjoint of commutation by `C` is commutation by `Cᴴ`. -/
theorem hsInner_ringCommutator_adjoint (C X Y : Matrix m m ℂ) :
    QuantumAlg.hsInner (ringCommutator C X) Y =
      QuantumAlg.hsInner X (ringCommutator Cᴴ Y) := by
  simp only [QuantumAlg.hsInner, ringCommutator, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [← Matrix.trace_mul_cycle Xᴴ Y Cᴴ]
  simp only [Matrix.mul_assoc]

/-- Trace of `ad(C)† ad(C)` evaluated in the completed traceless-Hermitian basis. -/
theorem sum_tracelessHermitianGenerator_hsInner_commutator_eq_trace_adjoint_comp
    (C : Matrix m m ℂ) :
    (∑ i, QuantumAlg.hsInner
        (ringCommutator C (tracelessHermitianGenerator m i))
        (ringCommutator C (tracelessHermitianGenerator m i))) =
      (LinearMap.trace ℂ (Matrix m m ℂ))
        ((factorCommutatorLinear Cᴴ).comp (factorCommutatorLinear C)) := by
  classical
  let b := completedTracelessHermitianBasis (m := m)
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  have hnone : ((b.repr
      (((factorCommutatorLinear Cᴴ).comp (factorCommutatorLinear C)) (b none))) none) = 0 := by
    have hbnone : b none = (1 : Matrix m m ℂ) := by
      rw [show b none = completedTracelessHermitianFamily m none by simp [b]]
      rfl
    rw [hbnone]
    simp [factorCommutatorLinear, ringCommutator]
  rw [Fintype.sum_option, hnone, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [completedTracelessHermitianBasis_repr_some]
  have hbSome : b (some i) = tracelessHermitianGenerator m i := by
    rw [show b (some i) = completedTracelessHermitianFamily m (some i) by simp [b]]
    rfl
  rw [hbSome]
  change QuantumAlg.hsInner
      (ringCommutator C (tracelessHermitianGenerator m i))
      (ringCommutator C (tracelessHermitianGenerator m i)) =
    QuantumAlg.hsInner (tracelessHermitianGenerator m i)
      (ringCommutator Cᴴ (ringCommutator C (tracelessHermitianGenerator m i)))
  exact hsInner_ringCommutator_adjoint C (tracelessHermitianGenerator m i)
    (ringCommutator C (tracelessHermitianGenerator m i))

theorem ringCommutator_adjoint_comp_single_coefficient
    (C : Matrix m m ℂ) (i j : m) :
    ringCommutator Cᴴ (ringCommutator C (Matrix.single i j 1)) i j =
      (Cᴴ * C) i i + (C * Cᴴ) j j - Cᴴ i i * C j j - C i i * Cᴴ j j := by
  classical
  simp only [ringCommutator, Matrix.sub_apply, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_apply, Matrix.single]
  simp
  have hleft (x : m) :
      (∑ y : m, if i = x ∧ j = y then C y j else 0) =
        if i = x then C j j else 0 := by
    by_cases hx : i = x
    · subst x
      simp
    · simp [hx]
  have hright (x : m) :
      (∑ y : m, if i = y ∧ j = x then C i y else 0) =
        if j = x then C i i else 0 := by
    by_cases hx : j = x
    · subst x
      simp
    · simp [hx]
  simp_rw [hleft, hright]
  simp
  ring

/-- Explicit trace of `ad(C)† ad(C)` in matrix units. -/
theorem factorCommutatorLinear_adjoint_comp_trace (C : Matrix m m ℂ) :
    (LinearMap.trace ℂ (Matrix m m ℂ))
        ((factorCommutatorLinear Cᴴ).comp (factorCommutatorLinear C)) =
      2 * (Fintype.card m : ℂ) * (Cᴴ * C).trace -
        2 * star C.trace * C.trace := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ m m)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.comp_apply, factorCommutatorLinear_apply, matrixStdBasis_repr_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Matrix.stdBasis_eq_single]
  simp_rw [ringCommutator_adjoint_comp_single_coefficient]
  let S : ℂ := ∑ i : m, C i i
  let Q : ℂ := ∑ i : m, (Cᴴ * C) i i
  have htraceOther : (∑ i : m, (C * Cᴴ) i i) = Q := by
    change (C * Cᴴ).trace = (Cᴴ * C).trace
    exact Matrix.trace_mul_comm C Cᴴ
  have hfirst : (∑ i : m, ∑ _j : m, (Cᴴ * C) i i) =
      (Fintype.card m : ℂ) * Q := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hsecond : (∑ _i : m, ∑ j : m, (C * Cᴴ) j j) =
      (Fintype.card m : ℂ) * Q := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [htraceOther]
  have hdiagStar : (∑ i : m, Cᴴ i i) = star S := by
    dsimp [S]
    rw [map_sum]
  have hcrossOne : (∑ i : m, ∑ j : m, Cᴴ i i * C j j) = star S * S := by
    calc
      _ = ∑ i : m, Cᴴ i i * S := by
        dsimp [S]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = (∑ i : m, Cᴴ i i) * S := by rw [Finset.sum_mul]
      _ = star S * S := by rw [hdiagStar]
  have hcrossTwo : (∑ i : m, ∑ j : m, C i i * Cᴴ j j) = S * star S := by
    calc
      _ = ∑ i : m, C i i * (star S) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hdiagStar, Finset.mul_sum]
      _ = (∑ i : m, C i i) * star S := by rw [Finset.sum_mul]
      _ = S * star S := by rfl
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hfirst, hsecond, hcrossOne, hcrossTwo]
  change _ = 2 * (Fintype.card m : ℂ) * Q - 2 * star S * S
  ring

/-- General complex traceless adjoint Casimir, needed for off-diagonal bipartite coefficient
blocks. -/
theorem sum_tracelessHermitianGenerator_commutatorEnergy_of_trace_zero
    (C : Matrix m m ℂ) (htrace : C.trace = 0) :
    (∑ i, GaloisForLFunctions.HTGeometry.finiteMatrixHilbertSchmidtEnergy
      (ringCommutator C (tracelessHermitianGenerator m i))) =
      2 * (Fintype.card m : ℝ) *
        GaloisForLFunctions.HTGeometry.finiteMatrixHilbertSchmidtEnergy C := by
  have hcomplex :=
    sum_tracelessHermitianGenerator_hsInner_commutator_eq_trace_adjoint_comp C
  rw [factorCommutatorLinear_adjoint_comp_trace C, htrace, star_zero,
    mul_zero, sub_zero] at hcomplex
  have hCenergy : (Cᴴ * C).trace =
      (GaloisForLFunctions.HTGeometry.finiteMatrixHilbertSchmidtEnergy C : ℂ) := by
    rw [← hsInner_self_eq_finiteMatrixHilbertSchmidtEnergy C]
    rfl
  rw [hCenergy] at hcomplex
  simp_rw [hsInner_self_eq_finiteMatrixHilbertSchmidtEnergy] at hcomplex
  exact_mod_cast hcomplex

end

section BipartiteAggregate

variable {m n : Type*}
variable [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n] [Nonempty n]

/-- Left-factor coefficient block, indexed in energy-compatible order. -/
def leftCoefficientBlock (H : Matrix (m × n) (m × n) ℂ) (k l : n) : Matrix m m ℂ :=
  fun i j => H (i, l) (j, k)

/-- Right-factor coefficient block, indexed in energy-compatible order. -/
def rightCoefficientBlock (H : Matrix (m × n) (m × n) ℂ) (i j : m) : Matrix n n ℂ :=
  fun k l => H (j, k) (i, l)

theorem leftCoefficientBlock_trace (H : Matrix (m × n) (m × n) ℂ) (k l : n) :
    (leftCoefficientBlock H k l).trace = partialTraceLeft H l k := by
  rfl

theorem rightCoefficientBlock_trace (H : Matrix (m × n) (m × n) ℂ) (i j : m) :
    (rightCoefficientBlock H i j).trace = partialTraceRight H j i := by
  rfl

theorem leftCoefficientBlock_matrixCommutator_leftLocal
    (H : Matrix (m × n) (m × n) ℂ) (A : Matrix m m ℂ) (k l : n) :
    leftCoefficientBlock (matrixCommutator H (A ⊗ₖ (1 : Matrix n n ℂ))) k l =
      ringCommutator (leftCoefficientBlock H k l) A := by
  ext i j
  change (matrixCommutator H (A ⊗ₖ (1 : Matrix n n ℂ))) (i, l) (j, k) =
    ((leftCoefficientBlock H k l) * A - A * (leftCoefficientBlock H k l)) i j
  rw [matrixCommutator, Matrix.sub_apply, mul_leftLocal_apply, leftLocal_mul_apply,
    Matrix.sub_apply]
  rfl

theorem rightCoefficientBlock_matrixCommutator_rightLocal
    (H : Matrix (m × n) (m × n) ℂ) (B : Matrix n n ℂ) (i j : m) :
    rightCoefficientBlock (matrixCommutator H ((1 : Matrix m m ℂ) ⊗ₖ B)) i j =
      ringCommutator (rightCoefficientBlock H i j) B := by
  ext k l
  simp [rightCoefficientBlock, matrixCommutator, ringCommutator,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]

theorem finiteMatrixHilbertSchmidtEnergy_eq_sum_leftCoefficientBlock
    (H : Matrix (m × n) (m × n) ℂ) :
    finiteMatrixHilbertSchmidtEnergy H =
      ∑ k : n, ∑ l : n, finiteMatrixHilbertSchmidtEnergy (leftCoefficientBlock H k l) := by
  simp only [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq, Fintype.sum_prod_type,
    leftCoefficientBlock]
  calc
    _ = ∑ k : n, ∑ i : m, ∑ j : m, ∑ l : n,
        Complex.normSq (H (j, l) (i, k)) := by rw [Finset.sum_comm]
    _ = ∑ k : n, ∑ i : m, ∑ l : n, ∑ j : m,
        Complex.normSq (H (j, l) (i, k)) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : n, ∑ l : n, ∑ i : m, ∑ j : m,
        Complex.normSq (H (j, l) (i, k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

theorem finiteMatrixHilbertSchmidtEnergy_eq_sum_rightCoefficientBlock
    (H : Matrix (m × n) (m × n) ℂ) :
    finiteMatrixHilbertSchmidtEnergy H =
      ∑ i : m, ∑ j : m, finiteMatrixHilbertSchmidtEnergy (rightCoefficientBlock H i j) := by
  simp only [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq, Fintype.sum_prod_type,
    rightCoefficientBlock]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- The algebraic cross projection is literally the identity on its range. -/
theorem crossMatrixPart_eq_self_of_mem_matrixCrossFibre
    {X : Matrix (m × n) (m × n) ℂ}
    (hX : X ∈ matrixCrossFibre (m := m) (n := n)) :
    crossMatrixPart X = X := by
  rw [mem_matrixCrossFibre] at hX
  have htrace : X.trace = 0 := by
    rw [← trace_partialTraceRight X, hX.1, Matrix.trace_zero]
  simp [crossMatrixPart, leftLocalPart, rightLocalPart, scalarMatrixPart,
    leftReducedComponent, rightReducedComponent, traceCenter, bipartiteScalarCoeff,
    hX.1, hX.2, htrace]

/-- On a cross-valued commutator, reporter tidal form is its full Hilbert--Schmidt energy. -/
theorem matrixReporterTidalForm_of_mem_cross
    {H : Matrix (m × n) (m × n) ℂ}
    (L : Matrix (m × n) (m × n) ℂ)
    (hcomm : matrixCommutator H L ∈ matrixCrossFibre (m := m) (n := n)) :
    matrixReporterTidalForm H L = finiteMatrixHilbertSchmidtEnergy (matrixCommutator H L) := by
  rw [matrixReporterTidalForm, crossMatrixPart_eq_self_of_mem_matrixCrossFibre hcomm,
    finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  rw [Finset.sum_comm]

theorem finiteMatrixHilbertSchmidtEnergy_smul
    (c : ℂ) (A : Matrix m m ℂ) :
    finiteMatrixHilbertSchmidtEnergy (c • A) =
      Complex.normSq c * finiteMatrixHilbertSchmidtEnergy A := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq,
    finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- Positive scalar `1 / sqrt(dim)`, used in the normalized reporter basis. -/
noncomputable def inverseSqrtCardScalar (n : Type*) [Fintype n] : ℂ :=
  (Real.sqrt (Fintype.card n : ℝ))⁻¹

theorem inverseSqrtCardScalar_normSq :
    Complex.normSq (inverseSqrtCardScalar n) = (Fintype.card n : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  simp [inverseSqrtCardScalar, Complex.normSq_apply]

/-- Literal reporters `Aα ⊗ I / sqrt(b)` from Card equation (5.6). -/
noncomputable def normalizedLeftReporter (A : Matrix m m ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  inverseSqrtCardScalar n • (A ⊗ₖ (1 : Matrix n n ℂ))

/-- Literal reporters `I ⊗ Bβ / sqrt(a)` from Card equation (5.6). -/
noncomputable def normalizedRightReporter (B : Matrix n n ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  inverseSqrtCardScalar m • ((1 : Matrix m m ℂ) ⊗ₖ B)

theorem matrixReporterTidalForm_normalizedLeftReporter
    {H : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixCrossFibre (m := m) (n := n)) (A : Matrix m m ℂ) :
    matrixReporterTidalForm H (normalizedLeftReporter (n := n) A) =
      (Fintype.card n : ℝ)⁻¹ *
        matrixReporterTidalForm H (A ⊗ₖ (1 : Matrix n n ℂ)) := by
  have hbase := matrixCommutator_leftLocal_mem_cross hH A
  have hnormalized : matrixCommutator H (normalizedLeftReporter (n := n) A) ∈
      matrixCrossFibre (m := m) (n := n) := by
    rw [normalizedLeftReporter, matrixCommutator_smul_right]
    exact (matrixCrossFibre (m := m) (n := n)).smul_mem _ hbase
  rw [matrixReporterTidalForm_of_mem_cross _ hnormalized,
    normalizedLeftReporter, matrixCommutator_smul_right,
    finiteMatrixHilbertSchmidtEnergy_smul, inverseSqrtCardScalar_normSq,
    matrixReporterTidalForm_of_mem_cross _ hbase]

theorem matrixReporterTidalForm_normalizedRightReporter
    {H : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixCrossFibre (m := m) (n := n)) (B : Matrix n n ℂ) :
    matrixReporterTidalForm H (normalizedRightReporter (m := m) B) =
      (Fintype.card m : ℝ)⁻¹ *
        matrixReporterTidalForm H ((1 : Matrix m m ℂ) ⊗ₖ B) := by
  have hbase := matrixCommutator_rightLocal_mem_cross hH B
  have hnormalized : matrixCommutator H (normalizedRightReporter (m := m) B) ∈
      matrixCrossFibre (m := m) (n := n) := by
    rw [normalizedRightReporter, matrixCommutator_smul_right]
    exact (matrixCrossFibre (m := m) (n := n)).smul_mem _ hbase
  rw [matrixReporterTidalForm_of_mem_cross _ hnormalized,
    normalizedRightReporter, matrixCommutator_smul_right,
    finiteMatrixHilbertSchmidtEnergy_smul, inverseSqrtCardScalar_normSq,
    matrixReporterTidalForm_of_mem_cross _ hbase]

theorem sum_matrixReporterTidalForm_leftLocal
    {H : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixCrossFibre (m := m) (n := n)) :
    (∑ α, matrixReporterTidalForm H
      ((tracelessHermitianGenerator m α) ⊗ₖ (1 : Matrix n n ℂ))) =
      2 * (Fintype.card m : ℝ) * finiteMatrixHilbertSchmidtEnergy H := by
  have hpartials := mem_matrixCrossFibre.mp hH
  calc
    _ = ∑ α, finiteMatrixHilbertSchmidtEnergy
        (matrixCommutator H
          ((tracelessHermitianGenerator m α) ⊗ₖ (1 : Matrix n n ℂ))) := by
      apply Finset.sum_congr rfl
      intro α _
      exact matrixReporterTidalForm_of_mem_cross _
        (matrixCommutator_leftLocal_mem_cross hH _)
    _ = ∑ α, ∑ k : n, ∑ l : n,
        finiteMatrixHilbertSchmidtEnergy
          (ringCommutator (leftCoefficientBlock H k l)
            (tracelessHermitianGenerator m α)) := by
      apply Finset.sum_congr rfl
      intro α _
      rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_leftCoefficientBlock]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [leftCoefficientBlock_matrixCommutator_leftLocal]
    _ = ∑ k : n, ∑ l : n, ∑ α,
        finiteMatrixHilbertSchmidtEnergy
          (ringCommutator (leftCoefficientBlock H k l)
            (tracelessHermitianGenerator m α)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ k : n, ∑ l : n,
        2 * (Fintype.card m : ℝ) *
          finiteMatrixHilbertSchmidtEnergy (leftCoefficientBlock H k l) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply sum_tracelessHermitianGenerator_commutatorEnergy_of_trace_zero
      rw [leftCoefficientBlock_trace]
      exact congrFun (congrFun hpartials.2 l) k
    _ = 2 * (Fintype.card m : ℝ) * finiteMatrixHilbertSchmidtEnergy H := by
      trans 2 * (Fintype.card m : ℝ) *
        (∑ k : n, ∑ l : n,
          finiteMatrixHilbertSchmidtEnergy (leftCoefficientBlock H k l))
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      · rw [← finiteMatrixHilbertSchmidtEnergy_eq_sum_leftCoefficientBlock]

theorem sum_matrixReporterTidalForm_rightLocal
    {H : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixCrossFibre (m := m) (n := n)) :
    (∑ β, matrixReporterTidalForm H
      ((1 : Matrix m m ℂ) ⊗ₖ (tracelessHermitianGenerator n β))) =
      2 * (Fintype.card n : ℝ) * finiteMatrixHilbertSchmidtEnergy H := by
  have hpartials := mem_matrixCrossFibre.mp hH
  calc
    _ = ∑ β, finiteMatrixHilbertSchmidtEnergy
        (matrixCommutator H
          ((1 : Matrix m m ℂ) ⊗ₖ (tracelessHermitianGenerator n β))) := by
      apply Finset.sum_congr rfl
      intro β _
      exact matrixReporterTidalForm_of_mem_cross _
        (matrixCommutator_rightLocal_mem_cross hH _)
    _ = ∑ β, ∑ i : m, ∑ j : m,
        finiteMatrixHilbertSchmidtEnergy
          (ringCommutator (rightCoefficientBlock H i j)
            (tracelessHermitianGenerator n β)) := by
      apply Finset.sum_congr rfl
      intro β _
      rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_rightCoefficientBlock]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [rightCoefficientBlock_matrixCommutator_rightLocal]
    _ = ∑ i : m, ∑ j : m, ∑ β,
        finiteMatrixHilbertSchmidtEnergy
          (ringCommutator (rightCoefficientBlock H i j)
            (tracelessHermitianGenerator n β)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : m, ∑ j : m,
        2 * (Fintype.card n : ℝ) *
          finiteMatrixHilbertSchmidtEnergy (rightCoefficientBlock H i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply sum_tracelessHermitianGenerator_commutatorEnergy_of_trace_zero
      rw [rightCoefficientBlock_trace]
      exact congrFun (congrFun hpartials.1 j) i
    _ = 2 * (Fintype.card n : ℝ) * finiteMatrixHilbertSchmidtEnergy H := by
      trans 2 * (Fintype.card n : ℝ) *
        (∑ i : m, ∑ j : m,
          finiteMatrixHilbertSchmidtEnergy (rightCoefficientBlock H i j))
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      · rw [← finiteMatrixHilbertSchmidtEnergy_eq_sum_rightCoefficientBlock]

theorem sum_matrixReporterTidalForm_normalizedLeft
    {H : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixCrossFibre (m := m) (n := n)) :
    (∑ α, matrixReporterTidalForm H
      (normalizedLeftReporter (n := n) (tracelessHermitianGenerator m α))) =
      2 * ((Fintype.card m : ℝ) / (Fintype.card n : ℝ)) *
        finiteMatrixHilbertSchmidtEnergy H := by
  simp_rw [matrixReporterTidalForm_normalizedLeftReporter hH]
  rw [← Finset.mul_sum, sum_matrixReporterTidalForm_leftLocal hH]
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem sum_matrixReporterTidalForm_normalizedRight
    {H : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixCrossFibre (m := m) (n := n)) :
    (∑ β, matrixReporterTidalForm H
      (normalizedRightReporter (m := m) (tracelessHermitianGenerator n β))) =
      2 * ((Fintype.card n : ℝ) / (Fintype.card m : ℝ)) *
        finiteMatrixHilbertSchmidtEnergy H := by
  simp_rw [matrixReporterTidalForm_normalizedRightReporter hH]
  rw [← Finset.mul_sum, sum_matrixReporterTidalForm_rightLocal hH]
  have hm : (Fintype.card m : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Total squared normal velocity across the normalized local reporter basis. -/
noncomputable def aggregateBoundaryTidalEnergy
    (H : Matrix (m × n) (m × n) ℂ) : ℝ :=
  (∑ α, matrixReporterTidalForm H
    (normalizedLeftReporter (n := n) (tracelessHermitianGenerator m α))) +
  (∑ β, matrixReporterTidalForm H
    (normalizedRightReporter (m := m) (tracelessHermitianGenerator n β)))

/-- Exact aggregate reporter tidal energy before the acceleration factor from Theorem 5.1. -/
theorem aggregateBoundaryTidalEnergy_eq
    {H : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixCrossFibre (m := m) (n := n)) :
    aggregateBoundaryTidalEnergy H =
      2 * ((Fintype.card m : ℝ) / (Fintype.card n : ℝ) +
        (Fintype.card n : ℝ) / (Fintype.card m : ℝ)) *
        finiteMatrixHilbertSchmidtEnergy H := by
  rw [aggregateBoundaryTidalEnergy,
    sum_matrixReporterTidalForm_normalizedLeft hH,
    sum_matrixReporterTidalForm_normalizedRight hH]
  ring

/-- Sum of initial hidden-weight accelerations, each twice its reporter tidal form. -/
noncomputable def aggregateBoundaryHiddenAcceleration
    (H : Matrix (m × n) (m × n) ℂ) : ℝ :=
  2 * aggregateBoundaryTidalEnergy H

/-- **Card Theorem 5.3, equation (5.7).** Complete second-order boundary leakage
recovers the full Hilbert--Schmidt energy of every cross interaction with the exact coefficient. -/
theorem aggregateBoundaryHiddenAcceleration_eq
    {H : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixCrossFibre (m := m) (n := n)) :
    aggregateBoundaryHiddenAcceleration H =
      4 * ((Fintype.card m : ℝ) / (Fintype.card n : ℝ) +
        (Fintype.card n : ℝ) / (Fintype.card m : ℝ)) *
        finiteMatrixHilbertSchmidtEnergy H := by
  rw [aggregateBoundaryHiddenAcceleration, aggregateBoundaryTidalEnergy_eq hH]
  ring

theorem normalizedLeftReporter_mem_matrixLocalReporter
    (α : Fin (Module.finrank ℝ (hermitianTracelessMatrices m))) :
    normalizedLeftReporter (n := n) (tracelessHermitianGenerator m α) ∈
      matrixLocalReporter (m := m) (n := n) := by
  rw [mem_matrixLocalReporter_iff]
  refine ⟨inverseSqrtCardScalar n • tracelessHermitianGenerator m α, ?_, 0, ?_, ?_⟩
  · simp [Matrix.trace_smul, tracelessHermitianGenerator_trace]
  · simp
  · simp [normalizedLeftReporter, Matrix.smul_kronecker]

theorem normalizedRightReporter_mem_matrixLocalReporter
    (β : Fin (Module.finrank ℝ (hermitianTracelessMatrices n))) :
    normalizedRightReporter (m := m) (tracelessHermitianGenerator n β) ∈
      matrixLocalReporter (m := m) (n := n) := by
  rw [mem_matrixLocalReporter_iff]
  refine ⟨0, ?_, inverseSqrtCardScalar m • tracelessHermitianGenerator n β, ?_, ?_⟩
  · simp
  · simp [Matrix.trace_smul, tracelessHermitianGenerator_trace]
  · simp [normalizedRightReporter, Matrix.kronecker_smul]

/-- Local and scalar Hamiltonian pieces produce no normal component on a normalized left
reporter; only the canonical cross component survives. -/
theorem matrixReporterTidalForm_normalizedLeft_eq_crossMatrixPart
    (H : Matrix (m × n) (m × n) ℂ)
    (α : Fin (Module.finrank ℝ (hermitianTracelessMatrices m))) :
    matrixReporterTidalForm H
        (normalizedLeftReporter (n := n) (tracelessHermitianGenerator m α)) =
      matrixReporterTidalForm (crossMatrixPart H)
        (normalizedLeftReporter (n := n) (tracelessHermitianGenerator m α)) := by
  let L := normalizedLeftReporter (n := n) (tracelessHermitianGenerator m α)
  let Hlocal :=
    leftReducedComponent H ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix m m ℂ) ⊗ₖ rightReducedComponent H +
      bipartiteScalarCoeff H •
        ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ))
  have hL : L ∈ matrixLocalReporter (m := m) (n := n) :=
    normalizedLeftReporter_mem_matrixLocalReporter α
  have hlocal : matrixCommutator Hlocal L ∈
      matrixLocalReporter (m := m) (n := n) := by
    exact matrixCommutator_localForm_mem _ _ _ hL
  have hcross : matrixCommutator (crossMatrixPart H) L ∈
      matrixCrossFibre (m := m) (n := n) := by
    dsimp [L, normalizedLeftReporter]
    rw [matrixCommutator_smul_right]
    exact (matrixCrossFibre (m := m) (n := n)).smul_mem _
      (matrixCommutator_leftLocal_mem_cross (crossMatrixPart_mem H) _)
  have hdecomp : H = Hlocal + crossMatrixPart H := by
    simpa [Hlocal, leftLocalPart, rightLocalPart, scalarMatrixPart] using
      bipartite_decomposition H
  have hprojection : crossMatrixPart (matrixCommutator H L) =
      matrixCommutator (crossMatrixPart H) L := by
    calc
      _ = crossMatrixPart
          (matrixCommutator (Hlocal + crossMatrixPart H) L) :=
        congrArg (fun K => crossMatrixPart (matrixCommutator K L)) hdecomp
      _ = _ := by
        rw [matrixCommutator_add_left, crossMatrixPart_add,
          crossMatrixPart_eq_zero_of_mem_matrixLocalReporter hlocal,
          crossMatrixPart_eq_self_of_mem_matrixCrossFibre hcross, zero_add]
  simp only [matrixReporterTidalForm]
  rw [hprojection]
  rw [crossMatrixPart_eq_self_of_mem_matrixCrossFibre hcross]

/-- Local and scalar Hamiltonian pieces produce no normal component on a normalized right
reporter; only the canonical cross component survives. -/
theorem matrixReporterTidalForm_normalizedRight_eq_crossMatrixPart
    (H : Matrix (m × n) (m × n) ℂ)
    (β : Fin (Module.finrank ℝ (hermitianTracelessMatrices n))) :
    matrixReporterTidalForm H
        (normalizedRightReporter (m := m) (tracelessHermitianGenerator n β)) =
      matrixReporterTidalForm (crossMatrixPart H)
        (normalizedRightReporter (m := m) (tracelessHermitianGenerator n β)) := by
  let L := normalizedRightReporter (m := m) (tracelessHermitianGenerator n β)
  let Hlocal :=
    leftReducedComponent H ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix m m ℂ) ⊗ₖ rightReducedComponent H +
      bipartiteScalarCoeff H •
        ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ))
  have hL : L ∈ matrixLocalReporter (m := m) (n := n) :=
    normalizedRightReporter_mem_matrixLocalReporter β
  have hlocal : matrixCommutator Hlocal L ∈
      matrixLocalReporter (m := m) (n := n) := by
    exact matrixCommutator_localForm_mem _ _ _ hL
  have hcross : matrixCommutator (crossMatrixPart H) L ∈
      matrixCrossFibre (m := m) (n := n) := by
    dsimp [L, normalizedRightReporter]
    rw [matrixCommutator_smul_right]
    exact (matrixCrossFibre (m := m) (n := n)).smul_mem _
      (matrixCommutator_rightLocal_mem_cross (crossMatrixPart_mem H) _)
  have hdecomp : H = Hlocal + crossMatrixPart H := by
    simpa [Hlocal, leftLocalPart, rightLocalPart, scalarMatrixPart] using
      bipartite_decomposition H
  have hprojection : crossMatrixPart (matrixCommutator H L) =
      matrixCommutator (crossMatrixPart H) L := by
    calc
      _ = crossMatrixPart
          (matrixCommutator (Hlocal + crossMatrixPart H) L) :=
        congrArg (fun K => crossMatrixPart (matrixCommutator K L)) hdecomp
      _ = _ := by
        rw [matrixCommutator_add_left, crossMatrixPart_add,
          crossMatrixPart_eq_zero_of_mem_matrixLocalReporter hlocal,
          crossMatrixPart_eq_self_of_mem_matrixCrossFibre hcross, zero_add]
  simp only [matrixReporterTidalForm]
  rw [hprojection]
  rw [crossMatrixPart_eq_self_of_mem_matrixCrossFibre hcross]

/-- Aggregate tidal energy is exactly insensitive to every local and scalar Hamiltonian term. -/
theorem aggregateBoundaryTidalEnergy_eq_crossMatrixPart
    (H : Matrix (m × n) (m × n) ℂ) :
    aggregateBoundaryTidalEnergy H = aggregateBoundaryTidalEnergy (crossMatrixPart H) := by
  simp only [aggregateBoundaryTidalEnergy]
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply Finset.sum_congr rfl
    intro α _
    exact matrixReporterTidalForm_normalizedLeft_eq_crossMatrixPart H α
  · apply Finset.sum_congr rfl
    intro β _
    exact matrixReporterTidalForm_normalizedRight_eq_crossMatrixPart H β

/-- **Card Theorem 5.3, full equation (5.7).** For every bipartite Hamiltonian, complete
second-order boundary leakage ignores all local and scalar terms and measures exactly the
Hilbert--Schmidt energy of its canonical cross component. -/
theorem aggregateBoundaryHiddenAcceleration_full_eq
    (H : Matrix (m × n) (m × n) ℂ) :
    aggregateBoundaryHiddenAcceleration H =
      4 * ((Fintype.card m : ℝ) / (Fintype.card n : ℝ) +
        (Fintype.card n : ℝ) / (Fintype.card m : ℝ)) *
        finiteMatrixHilbertSchmidtEnergy (crossMatrixPart H) := by
  rw [aggregateBoundaryHiddenAcceleration, aggregateBoundaryTidalEnergy_eq_crossMatrixPart,
    aggregateBoundaryTidalEnergy_eq (crossMatrixPart_mem H)]
  ring

end BipartiteAggregate

end HTGeometry.ConstraintRelativity
