import GaloisForLFunctions.HTGeometry.GomesSpecialOrthogonalCommutant
import GaloisForLFunctions.HTGeometry.ConstitutiveOrbitGeneratedReflectionProperness

/-!
# Reflection-menu reconstruction and frame transport

The existing constitutive reflections determine independent coordinate weights. Quarter-turns
reduce those weights to one scalar, an application of the representation-menu distinction in
Gomes, arXiv:2607.24901. Orthogonal transport of the whole family preserves the exact tight
cycle-work identity, applying associated-action covariance from arXiv:2404.10461.

https://arxiv.org/abs/2607.24901
https://arxiv.org/abs/2404.10461
-/

open scoped Matrix BigOperators
noncomputable section
namespace HTGeometry
open GaloisForLFunctions.HTGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix of the corpus reflection that fixes one coordinate and reverses its complement. -/
def coordinateReflectionMatrix (k : ι) : Matrix ι ι ℝ := -gomesAxisReflection k

/-- The matrix model acts exactly as the existing source-coordinate reflection. -/
theorem coordinateReflectionMatrix_mulVec (k : ι) (x : ι → ℝ) :
    coordinateReflectionMatrix k *ᵥ x = coordinateReflection k x := by
  funext j
  by_cases hj : j=k <;>
    simp [coordinateReflectionMatrix,gomesAxisReflection,Matrix.mulVec_diagonal,
      coordinateReflection,hj]

/-- The source-coordinate reflection is an orthogonal transformation. -/
theorem coordinateReflectionMatrix_orthogonal (k : ι) :
    coordinateReflectionMatrix k ∈ Matrix.orthogonalGroup ι ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  simpa only [coordinateReflectionMatrix,Matrix.transpose_neg,neg_mul_neg] using
    (Matrix.mem_orthogonalGroup_iff' _ _).mp (gomesAxisReflection_orthogonal k)

/-- The complete coordinate-reflection family reconstructs diagonal endomorphisms, allowing
independent weights on different source coordinates. -/
theorem coordinateReflection_matrix_commutant (C : Matrix ι ι ℝ) :
    (∀ k, C * coordinateReflectionMatrix k = coordinateReflectionMatrix k * C) ↔
      C = Matrix.diagonal (fun i => C i i) := by
  constructor
  · intro h
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · have he := congrFun (congrFun (h i) i) j
      simp [coordinateReflectionMatrix,gomesAxisReflection,Matrix.mul_diagonal,
        Matrix.diagonal_mul,Ne.symm hij] at he
      have hz : C i j = 0 := by linarith
      simp [Matrix.diagonal,hij,hz]
  · intro h k
    rw [h]
    simp [coordinateReflectionMatrix,gomesAxisReflection,Matrix.diagonal_mul_diagonal,mul_comm]

/-- Invariant bilinear forms under the corpus reflections are precisely arbitrary diagonal forms. -/
theorem coordinateReflection_invariant_bilinear_matrix (C : Matrix ι ι ℝ) :
    (∀ k, (coordinateReflectionMatrix k)ᵀ * C * coordinateReflectionMatrix k = C) ↔
      C = Matrix.diagonal (fun i => C i i) := by
  rw [← coordinateReflection_matrix_commutant]
  have ht (k : ι) : (coordinateReflectionMatrix k)ᵀ = coordinateReflectionMatrix k := by
    simp [coordinateReflectionMatrix,gomesAxisReflection]
  have hs (k : ι) : coordinateReflectionMatrix k * coordinateReflectionMatrix k = 1 := by
    simpa only [coordinateReflectionMatrix,neg_mul_neg] using gomesAxisReflection_sq k
  constructor
  · intro h k
    have hk := h k
    rw [ht] at hk
    calc
      C * coordinateReflectionMatrix k =
          coordinateReflectionMatrix k *
            (coordinateReflectionMatrix k * C * coordinateReflectionMatrix k) := by
              simp only [← mul_assoc,hs,one_mul]
      _ = coordinateReflectionMatrix k * C := by rw [hk]
  · intro h k
    rw [ht,mul_assoc,h k,← mul_assoc,hs,one_mul]

/-- Adding all coordinate-plane quarter-turns removes the independent coordinate weights and
reconstructs a single scalar Euclidean metric. -/
theorem coordinateReflection_rotation_reconstruction (n : ℕ)
    (C : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) :
    ((∀ k, C * coordinateReflectionMatrix k = coordinateReflectionMatrix k * C) ∧
      ∀ i j, C * gomesPlaneRotation i j = gomesPlaneRotation i j * C) ↔
        C = C 0 0 • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) := by
  constructor
  · rintro ⟨hr,hp⟩
    have hd := (coordinateReflection_matrix_commutant C).mp hr
    have heq (i j : Fin (n+3)) : C i i = C j j := by
      by_cases hij : i=j
      · simp [hij]
      · have he := congrFun (congrFun (hp i j) i) j
        conv_lhs at he => rw [hd,Matrix.diagonal_mul]
        conv_rhs at he => rw [hd,Matrix.mul_diagonal]
        change C i i * gomesPlaneRotation i j i j = gomesPlaneRotation i j i j * C j j at he
        rw [gomesPlaneRotation_axis_entry,if_neg hij] at he
        linarith
    calc
      C = Matrix.diagonal (fun i => C i i) := hd
      _ = C 0 0 • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) := by
        ext i j
        by_cases hij : i=j
        · subst j; simpa using heq i 0
        · simp [Matrix.diagonal,hij]
  · intro h
    constructor
    · intro k; rw [h]; simp
    · intro i j; rw [h]; simp

/-- Squared source energy is invariant under every orthogonal change of frame. -/
theorem coordinateEnergy_orthogonal_mulVec (Q : Matrix.orthogonalGroup ι ℝ) (x : ι → ℝ) :
    coordinateEnergy (Q.val *ᵥ x) = coordinateEnergy x := by
  simp only [coordinateEnergy,pow_two]
  change dotProduct (Q.val *ᵥ x) (Q.val *ᵥ x) = dotProduct x x
  rw [← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,
    (Matrix.mem_orthogonalGroup_iff' _ _).mp Q.property,Matrix.one_mulVec]

/-- Complete reflection-cycle work is independent of an orthogonal change of state coordinates. -/
theorem orbitReflectionCycleWork_orthogonal_mulVec (Q : Matrix.orthogonalGroup ι ℝ)
    (x : ι → ℝ) : orbitReflectionCycleWork (Q.val *ᵥ x) = orbitReflectionCycleWork x := by
  rw [orbitReflectionCycleWork_eq_four_energy,orbitReflectionCycleWork_eq_four_energy,
    coordinateEnergy_orthogonal_mulVec]

/-- Transport the existing reflection to a new orthogonal frame by conjugation. -/
def reframedCoordinateReflection (Q : Matrix.orthogonalGroup ι ℝ) (k : ι) (x : ι → ℝ) : ι → ℝ :=
  Q.val *ᵥ coordinateReflection k (Q.valᵀ *ᵥ x)

/-- Conjugated reflection defects are exactly the transported old defects. -/
theorem reframedCoordinateReflection_defect (Q : Matrix.orthogonalGroup ι ℝ)
    (k : ι) (x : ι → ℝ) :
    x + reframedCoordinateReflection Q k x =
      Q.val *ᵥ coordinateReflectionDefect k (Q.valᵀ *ᵥ x) := by
  change x + Q.val *ᵥ coordinateReflection k (Q.valᵀ *ᵥ x) =
    Q.val *ᵥ ((Q.valᵀ *ᵥ x) + coordinateReflection k (Q.valᵀ *ᵥ x))
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,
    (Matrix.mem_orthogonalGroup_iff _ _).mp Q.property,Matrix.one_mulVec]

/-- Full marked work of the transported reflection family. -/
def reframedOrbitReflectionCycleWork (Q : Matrix.orthogonalGroup ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ k, coordinateEnergy (x + reframedCoordinateReflection Q k x)

/-- The exact tight-frame work identity survives arbitrary orthogonal transport of the whole
reflection family. -/
theorem reframedOrbitReflectionCycleWork_eq_four_energy (Q : Matrix.orthogonalGroup ι ℝ)
    (x : ι → ℝ) : reframedOrbitReflectionCycleWork Q x = 4 * coordinateEnergy x := by
  have hQt : Q.valᵀ ∈ Matrix.orthogonalGroup ι ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']
    simpa using (Matrix.mem_orthogonalGroup_iff _ _).mp Q.property
  calc
    reframedOrbitReflectionCycleWork Q x = orbitReflectionCycleWork (Q.valᵀ *ᵥ x) := by
      simp only [reframedOrbitReflectionCycleWork,reframedCoordinateReflection_defect,
        coordinateEnergy_orthogonal_mulVec]
      rfl
    _ = 4 * coordinateEnergy (Q.valᵀ *ᵥ x) := orbitReflectionCycleWork_eq_four_energy _
    _ = 4 * coordinateEnergy x := by rw [coordinateEnergy_orthogonal_mulVec ⟨Q.valᵀ,hQt⟩]

/-- The transported observer cycle is proper at exactly the same neutral state. -/
theorem reframedOrbitReflectionCycleWork_eq_zero_iff (Q : Matrix.orthogonalGroup ι ℝ)
    (x : ι → ℝ) : reframedOrbitReflectionCycleWork Q x = 0 ↔ x = 0 := by
  rw [reframedOrbitReflectionCycleWork_eq_four_energy,← orbitReflectionCycleWork_eq_four_energy]
  exact orbitReflectionCycleWork_eq_zero_iff x

end HTGeometry
