import GaloisForLFunctions.HTGeometry.ComparisonJetAlgebra

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

/-- The tensor flip commutes with the tensor-square derivation. -/
theorem tensorFlip_tensorSquareDerivation (x : R ⊗[K] R) :
    Algebra.TensorProduct.comm K R R (tensorSquareDerivation (K := K) x) =
      tensorSquareDerivation (K := K) (Algebra.TensorProduct.comm K R R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [tensorSquareDerivation_tmul, map_add,
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.comm_tmul, tensorSquareDerivation_tmul]
      exact add_comm _ _
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

omit [Differential K] [Differential R] [DifferentialAlgebra K R] in
/-- The tensor flip is an involution. -/
theorem tensorFlip_involutive (x : R ⊗[K] R) :
    Algebra.TensorProduct.comm K R R (Algebra.TensorProduct.comm K R R x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [Differential K] [Differential R] [DifferentialAlgebra K R] in
/-- The tensor flip exchanges the two copies of a matrix. -/
theorem map_leftFundamental_tensorFlip {n : ℕ} (Y : Matrix (Fin n) (Fin n) R) :
    (leftFundamental K Y).map (Algebra.TensorProduct.comm K R R) =
      rightFundamental K Y := by
  ext i j
  simp [leftFundamental_apply, rightFundamental_apply]

omit [Differential K] [Differential R] [DifferentialAlgebra K R] in
/-- The tensor flip exchanges the two copies of a matrix. -/
theorem map_rightFundamental_tensorFlip {n : ℕ} (Y : Matrix (Fin n) (Fin n) R) :
    (rightFundamental K Y).map (Algebra.TensorProduct.comm K R R) =
      leftFundamental K Y := by
  ext i j
  simp [leftFundamental_apply, rightFundamental_apply]

omit [Differential K] [Differential R] [DifferentialAlgebra K R] in
/-- Flipping the comparison matrix gives its two-sided inverse. -/
theorem comparisonMatrix_flip_inverse {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) R) (u : R) (hu : Y.det * u = 1)
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R))
    (hZ : leftFundamental K Y * Z = rightFundamental K Y) :
    Z * Z.map (Algebra.TensorProduct.comm K R R) = 1 ∧
      Z.map (Algebra.TensorProduct.comm K R R) * Z = 1 := by
  classical
  let τ := Algebra.TensorProduct.comm K R R
  have hflip := congrArg (fun M : Matrix (Fin n) (Fin n) (R ⊗[K] R) => M.map τ) hZ
  have hZflip : rightFundamental K Y * Z.map τ = leftFundamental K Y := by
    rw [Matrix.map_mul, map_leftFundamental_tensorFlip, map_rightFundamental_tensorFlip] at hflip
    exact hflip
  have hdetL : (leftFundamental K Y).det * (u ⊗ₜ[K] (1 : R)) = 1 := by
    rw [det_leftFundamental, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hu,
      ← Algebra.TensorProduct.one_def]
  have hdetLunit : IsUnit (leftFundamental K Y).det :=
    ⟨⟨(leftFundamental K Y).det, u ⊗ₜ[K] (1 : R), hdetL,
      mul_eq_one_comm.mp hdetL⟩, rfl⟩
  have hLunit : IsUnit (leftFundamental K Y) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hdetLunit
  have hmul : Z * Z.map τ = 1 := by
    apply hLunit.mul_left_cancel
    calc
      leftFundamental K Y * (Z * Z.map τ) =
          (leftFundamental K Y * Z) * Z.map τ := by rw [mul_assoc]
      _ = rightFundamental K Y * Z.map τ := by rw [hZ]
      _ = leftFundamental K Y := hZflip
      _ = leftFundamental K Y * 1 := (Matrix.mul_one _).symm
  have hmulFlip := congrArg
    (fun M : Matrix (Fin n) (Fin n) (R ⊗[K] R) => M.map τ) hmul
  have hmul' : Z.map τ * Z = 1 := by
    rw [Matrix.map_mul] at hmulFlip
    have hdouble : (Z.map τ).map τ = Z := by
      ext i j
      exact tensorFlip_involutive (Z i j)
    rw [hdouble] at hmulFlip
    simpa only [Matrix.map_one, map_zero, map_one] using hmulFlip
  exact ⟨hmul, hmul'⟩

omit [Differential K] [Differential R] [DifferentialAlgebra K R] in
private theorem comparisonInverseDet_eq_det
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (w : R ⊗[K] R)
    (hw : Z.det * w = 1) (hdet : Z.det ^ 2 = 1) : w = Z.det := by
  calc
    w = 1 * w := (one_mul w).symm
    _ = Z.det ^ 2 * w := by rw [hdet]
    _ = Z.det * (Z.det * w) := by ring
    _ = Z.det := by rw [hw, mul_one]

omit [Differential C] [DifferentialAlgebra C R] in
/-- Every flipped comparison-matrix entry remains in the comparison-jet algebra. -/
theorem comparisonMatrix_flip_entry_mem
    (Y : Matrix (Fin 2) (Fin 2) R) (u : R) (hu : Y.det * u = 1)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (w : R ⊗[K] R)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hw : Z.det * w = 1) (hdet : Z.det ^ 2 = 1) (i j : Fin 2) :
    Algebra.TensorProduct.comm K R R (Z i j) ∈ comparisonJetAlgebra (C := C) Z w := by
  classical
  let E := comparisonJetAlgebra (C := C) Z w
  let τ := Algebra.TensorProduct.comm K R R
  let F := Z.map τ
  have hinv := comparisonMatrix_flip_inverse Y u hu Z hZ
  have hZunit : IsUnit Z := ⟨⟨Z, F, hinv.1, hinv.2⟩, rfl⟩
  have hwdet : w = Z.det := comparisonInverseDet_eq_det Z w hw hdet
  let A : Matrix (Fin 2) (Fin 2) (R ⊗[K] R) := Z.det • Z.adjugate
  have hZA : Z * A = 1 := by
    dsimp [A]
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    rw [← pow_two, hdet, one_smul]
  have hFA : F = A := by
    apply hZunit.mul_left_cancel
    rw [hinv.1, hZA]
  have hdetmem : Z.det ∈ E := comparisonJetCore_le Z w (det_mem_comparisonJetCore Z)
  have hadjmem : Z.adjugate i j ∈ E := by
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two, E, mem_comparisonJetAlgebra_entry]
  have hAmem : A i j ∈ E := by
    dsimp [A]
    exact E.mul_mem hdetmem hadjmem
  change F i j ∈ E
  rw [hFA]
  exact hAmem

/-- The tensor flip preserves the comparison-jet algebra. -/
theorem comparisonJetAlgebra_flip_mem
    (Y : Matrix (Fin 2) (Fin 2) R) (u : R) (hu : Y.det * u = 1)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (w : R ⊗[K] R)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hw : Z.det * w = 1) (hdet : Z.det ^ 2 = 1)
    {e : R ⊗[K] R} (he : e ∈ comparisonJetAlgebra (C := C) Z w) :
    Algebra.TensorProduct.comm K R R e ∈ comparisonJetAlgebra (C := C) Z w := by
  classical
  let E := comparisonJetAlgebra (C := C) Z w
  let τ := Algebra.TensorProduct.comm K R R
  have hentry : ∀ i j, τ (Z i j) ∈ E :=
    comparisonMatrix_flip_entry_mem Y u hu Z w hZ hw hdet
  have hjets : ∀ k i j, τ (tensorJet (K := K) k (Z i j)) ∈ E := by
    intro k i j
    induction k with
    | zero => exact hentry i j
    | succ k hk =>
        rw [tensorJet_succ, tensorFlip_tensorSquareDerivation]
        exact comparisonJetAlgebra_deriv_stable Z hw hk
  have hwdet : w = Z.det := comparisonInverseDet_eq_det Z w hw hdet
  have hwflip : τ w ∈ E := by
    rw [hwdet]
    have hmapdet : τ Z.det = (Z.map τ).det := by
      simpa [RingHom.mapMatrix_apply] using
        (RingHom.map_det τ.toRingEquiv.toRingHom Z)
    rw [hmapdet, Matrix.det_fin_two]
    exact E.sub_mem
      (E.mul_mem (hentry 0 0) (hentry 1 1))
      (E.mul_mem (hentry 0 1) (hentry 1 0))
  induction he using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨k, p, rfl⟩ := Set.mem_iUnion.mp hx
        exact hjets k p.1 p.2
      · rw [Set.mem_singleton_iff] at hx
        simpa [hx] using hwflip
  | algebraMap c =>
      have hc : algebraMap C (R ⊗[K] R) c =
          (algebraMap C R c) ⊗ₜ[K] (1 : R) := by
        rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
        rfl
      rw [hc, Algebra.TensorProduct.comm_tmul]
      have hbalanced : (1 : R) ⊗ₜ[K] algebraMap C R c =
          algebraMap C R c ⊗ₜ[K] (1 : R) := by
        rw [IsScalarTower.algebraMap_apply C K R]
        calc
          (1 : R) ⊗ₜ[K] algebraMap K R (algebraMap C K c) =
              (1 : R) ⊗ₜ[K] ((algebraMap C K c) • (1 : R)) := by
                simp [Algebra.smul_def]
          _ = ((algebraMap C K c) • (1 : R)) ⊗ₜ[K] (1 : R) := by
                exact (TensorProduct.smul_tmul (algebraMap C K c) (1 : R) (1 : R)).symm
          _ = algebraMap K R (algebraMap C K c) ⊗ₜ[K] (1 : R) := by
                simp [Algebra.smul_def]
      rw [hbalanced, ← hc]
      exact E.algebraMap_mem c
  | add x y _ _ hx hy => rw [map_add]; exact E.add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact E.mul_mem hx hy

/-- Tensor flip restricted to the comparison-jet algebra. -/
def comparisonJetAlgebraFlip
    (Y : Matrix (Fin 2) (Fin 2) R) (u : R) (hu : Y.det * u = 1)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (w : R ⊗[K] R)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hw : Z.det * w = 1) (hdet : Z.det ^ 2 = 1) :
    comparisonJetAlgebra (C := C) Z w →ₐ[C] comparisonJetAlgebra (C := C) Z w where
  toFun e := ⟨Algebra.TensorProduct.comm K R R e,
    comparisonJetAlgebra_flip_mem Y u hu Z w hZ hw hdet e.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.1 y.1)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  commutes' c := by
    apply Subtype.ext
    have hc : algebraMap C (R ⊗[K] R) c =
        (algebraMap C R c) ⊗ₜ[K] (1 : R) := by
      rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
      rfl
    change Algebra.TensorProduct.comm K R R (algebraMap C (R ⊗[K] R) c) =
      algebraMap C (R ⊗[K] R) c
    rw [hc, Algebra.TensorProduct.comm_tmul]
    have hbalanced : (1 : R) ⊗ₜ[K] algebraMap C R c =
        algebraMap C R c ⊗ₜ[K] (1 : R) := by
      rw [IsScalarTower.algebraMap_apply C K R]
      calc
        (1 : R) ⊗ₜ[K] algebraMap K R (algebraMap C K c) =
            (1 : R) ⊗ₜ[K] ((algebraMap C K c) • (1 : R)) := by
              simp [Algebra.smul_def]
        _ = ((algebraMap C K c) • (1 : R)) ⊗ₜ[K] (1 : R) := by
              exact (TensorProduct.smul_tmul (algebraMap C K c) (1 : R) (1 : R)).symm
        _ = algebraMap K R (algebraMap C K c) ⊗ₜ[K] (1 : R) := by
              simp [Algebra.smul_def]
    rw [hbalanced, ← hc]

/-- Composing a differential point with tensor flip gives the inverse Galois matrix. -/
theorem exists_flip_inverse_tensorDifferentialPoint
    (Y : Matrix (Fin 2) (Fin 2) R) (u : R) (hu : Y.det * u = 1)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (w : R ⊗[K] R)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hw : Z.det * w = 1) (hdet : Z.det ^ 2 = 1)
    (hEδ : ∀ e ∈ comparisonJetAlgebra (C := C) Z w,
      tensorSquareDerivation (K := K) e ∈ comparisonJetAlgebra (C := C) Z w)
    (χ : comparisonJetAlgebra (C := C) Z w →ₐ[C] C)
    (hχ : χ ∈ tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w) hEδ) :
    ∃ χ' ∈ tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w) hEδ,
      galoisMatrixAt (comparisonJetAlgebra (C := C) Z w) Z
          (fun i j => mem_comparisonJetAlgebra_entry Z w i j) χ *
        galoisMatrixAt (comparisonJetAlgebra (C := C) Z w) Z
          (fun i j => mem_comparisonJetAlgebra_entry Z w i j) χ' = 1 := by
  classical
  let E := comparisonJetAlgebra (C := C) Z w
  let τE := comparisonJetAlgebraFlip (K := K) (C := C) Y u hu Z w hZ hw hdet
  let χ' : E →ₐ[C] C := χ.comp τE
  have hχ' : χ' ∈ tensorDifferentialPoints E hEδ := by
    intro e he
    change χ (τE ⟨tensorSquareDerivation (K := K) e, hEδ e he⟩) =
      Differential.deriv (χ (τE ⟨e, he⟩))
    have hτD : τE ⟨tensorSquareDerivation (K := K) e, hEδ e he⟩ =
        ⟨tensorSquareDerivation (K := K) (Algebra.TensorProduct.comm K R R e),
          hEδ _ (comparisonJetAlgebra_flip_mem (K := K) (C := C)
            Y u hu Z w hZ hw hdet he)⟩ := by
      apply Subtype.ext
      exact tensorFlip_tensorSquareDerivation e
    rw [hτD]
    exact hχ _ _
  refine ⟨χ', hχ', ?_⟩
  let hZE : ∀ i j, Z i j ∈ E := fun i j => mem_comparisonJetAlgebra_entry Z w i j
  let ZE : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j => ⟨Z i j, hZE i j⟩
  let FE : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j =>
    ⟨Algebra.TensorProduct.comm K R R (Z i j),
      comparisonMatrix_flip_entry_mem Y u hu Z w hZ hw hdet i j⟩
  have hZEF : ZE * FE = 1 := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    have honecoe :
        ((↑((1 : Matrix (Fin 2) (Fin 2) E) i j) : R ⊗[K] R)) =
          (1 : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) i j := by
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    rw [honecoe]
    simpa [Matrix.mul_apply, ZE, FE] using
      congrFun (congrFun (comparisonMatrix_flip_inverse Y u hu Z hZ).1 i) j
  change ZE.map χ * FE.map χ = 1
  rw [← Matrix.map_mul, hZEF]
  exact Matrix.map_one χ (map_zero χ) (map_one χ)

/-- The comparison-jet Galois monoid is closed under inverses, directly by tensor flip. -/
theorem comparisonJetGaloisMonoid_exists_inverse_mem
    (Y : Matrix (Fin 2) (Fin 2) R) (u : R) (hu : Y.det * u = 1)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (w : R ⊗[K] R)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hw : Z.det * w = 1) (hdet : Z.det ^ 2 = 1)
    {g : Matrix (Fin 2) (Fin 2) C}
    (hg : g ∈ galoisMonoid (comparisonJetAlgebra (C := C) Z w) Z
      (fun i j => mem_comparisonJetAlgebra_entry Z w i j)
      (tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w)
        (fun _e he => comparisonJetAlgebra_deriv_stable Z hw he))) :
    ∃ g' ∈ galoisMonoid (comparisonJetAlgebra (C := C) Z w) Z
        (fun i j => mem_comparisonJetAlgebra_entry Z w i j)
        (tensorDifferentialPoints (comparisonJetAlgebra (C := C) Z w)
          (fun _e he => comparisonJetAlgebra_deriv_stable Z hw he)),
      g * g' = 1 := by
  let E := comparisonJetAlgebra (C := C) Z w
  let hZE : ∀ i j, Z i j ∈ E := fun i j => mem_comparisonJetAlgebra_entry Z w i j
  let hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E :=
    fun _e he => comparisonJetAlgebra_deriv_stable Z hw he
  change g ∈ Submonoid.closure {x : Matrix (Fin 2) (Fin 2) C |
    ∃ χ ∈ tensorDifferentialPoints E hEδ, galoisMatrixAt E Z hZE χ = x} at hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨χ, hχ, rfl⟩ := hx
      obtain ⟨χ', hχ', hinv⟩ := exists_flip_inverse_tensorDifferentialPoint
        Y u hu Z w hZ hw hdet hEδ χ hχ
      refine ⟨galoisMatrixAt E Z hZE χ', ?_, hinv⟩
      exact Submonoid.subset_closure ⟨χ', hχ', rfl⟩
  | one => exact ⟨1, Submonoid.one_mem _, one_mul 1⟩
  | mul x y _ _ hx hy =>
      obtain ⟨x', hx', hxx'⟩ := hx
      obtain ⟨y', hy', hyy'⟩ := hy
      refine ⟨y' * x', Submonoid.mul_mem _ hy' hx', ?_⟩
      calc
        (x * y) * (y' * x') = x * (y * y') * x' := by simp only [mul_assoc]
        _ = x * x' := by rw [hyy', mul_one]
        _ = 1 := hxx'

end

end GaloisForLFunctions.HTGeometry
