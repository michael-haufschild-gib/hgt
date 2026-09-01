import GaloisForLFunctions.HTGeometry.DifferentialMatrixGroupGenericPoint

/-!
# Nonzero identity tangents of infinite differential matrix groups

An infinite injectively represented differential matrix group has a transcendental differential
generic point.  A commuting derivation at that point translates through the Hopf antipode to a
nonzero derivation at the identity.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

universe u v

/-- A commuting derivation that kills differential generators of the whole field is zero. -/
theorem derivation_eq_zero_of_differentialAdjoin_eq_top
    {C K E : Type u} {κ : Type v} [Field C] [Field K] [Field E]
    [Algebra C K] [Algebra C E]
    [Algebra K E] [IsScalarTower C K E] [Differential K] [Differential E]
    (D : Derivation C K E) (y : κ → K)
    (hcomm : ∀ x, D (Differential.deriv x) = Differential.deriv (D x))
    (hy : ∀ i, D (y i) = 0) (hgen : differentialAdjoin C (Set.range y) = ⊤) :
    D = 0 := by
  apply Derivation.ext
  intro x
  change D x = (0 : E)
  have hx : x ∈ differentialAdjoin C (Set.range y) := by
    rw [hgen]
    trivial
  rw [differentialAdjoin] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz =>
      obtain ⟨a, ⟨i, rfl⟩, n, rfl⟩ := hz
      induction n with
      | zero => exact hy i
      | succ n ih =>
          rw [differentialJet_succ, hcomm, ih, map_zero]
  | algebraMap c =>
      have h := D.map_smul c (1 : K)
      rw [D.map_one_eq_zero, smul_zero] at h
      simpa [Algebra.smul_def] using h
  | add x z _ _ hx hz =>
      rw [map_add, hx, hz, add_zero]
  | inv x _ hx =>
      by_cases hx0 : x = 0
      · rw [hx0, inv_zero, map_zero]
      · have hone : D (x * x⁻¹) = 0 := by
          rw [mul_inv_cancel₀ hx0]
          exact D.map_one_eq_zero
        rw [D.leibniz, hx, smul_zero, add_zero] at hone
        exact (smul_eq_zero.mp hone).resolve_left hx0
  | mul x z _ _ hx hz =>
      rw [D.leibniz, hx, hz, smul_zero, smul_zero, add_zero]

variable {C G : Type u} [Field C] [Differential C] [Group G]

namespace DifferentialMatrixGroupRepresentation

variable (r : DifferentialMatrixGroupRepresentation (C := C) (G := G))

local instance nonzeroTangentAmbientDifferential : Differential (G → C) :=
  pointwiseFunctionDifferential G

local instance nonzeroTangentCoordinateDifferential : Differential r.coordinateAlgebra :=
  r.coordinateAlgebraDifferential

/-- Comultiplication of a matrix coordinate is matrix multiplication of coordinate functions. -/
theorem coordinateComul_coordinate (q : Fin 2 × Fin 2) :
    r.coordinateComul
        ⟨r.coordinate q, Algebra.subset_adjoin ⟨(q, 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ =
      ∑ k : Fin 2,
        (⟨r.coordinate (q.1, k), Algebra.subset_adjoin ⟨((q.1, k), 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ : r.coordinateAlgebra) ⊗ₜ[C]
        ⟨r.coordinate (k, q.2), Algebra.subset_adjoin ⟨((k, q.2), 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ := by
  apply r.coordinateTensorEval_injective
  ext z
  rw [r.coordinateTensorEval_coordinateComul]
  simp only [map_sum]
  change r.matrix (z.1 * z.2) q.1 q.2 =
    ∑ k : Fin 2, r.matrix z.1 q.1 k * r.matrix z.2 k q.2
  rw [r.matrix.map_mul, Matrix.mul_apply]

/-- Counit of a matrix coordinate is the corresponding identity-matrix entry. -/
theorem coordinateCounit_coordinate (q : Fin 2 × Fin 2) :
    r.coordinateCounit
        ⟨r.coordinate q, Algebra.subset_adjoin ⟨(q, 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ =
      (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2 := by
  change r.matrix 1 q.1 q.2 = _
  rw [r.matrix.map_one]

/-- The identity-antipode convolution of a coordinate function is its counit. -/
theorem coordinateLift_id_antipode_comul (a : r.coordinateAlgebra) :
    Algebra.TensorProduct.lift (AlgHom.id C r.coordinateAlgebra)
        r.coordinateAntipode (fun _ _ => Commute.all _ _) (r.coordinateComul a) =
      algebraMap C r.coordinateAlgebra (r.coordinateCounit a) := by
  apply Subtype.ext
  funext g
  rw [r.coordinateLift_id_antipode_apply,
    r.coordinateTensorEval_coordinateComul]
  simp
  rfl

/-- **Infinite represented differential matrix groups have nonzero identity tangent.**  No
smoothness or finite-type hypothesis is assumed: the coordinate Hopf algebra, differential generic
point, Kähler derivation, and translation through the antipode construct the tangent directly. -/
theorem exists_nonzero_identity_tangent_of_infinite [CharZero C] [Algebra ℚ C] [Infinite G]
    (hinj : Function.Injective r.matrix) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra ℚ L) (_ : Algebra C L)
      (_ : Differential L) (_ : DifferentialAlgebra C L)
      (ell : r.coordinateAlgebra →ₗ[C] L),
      ell ≠ 0 ∧
      (∀ a b, ell (a * b) =
        r.tangentIdentityCharacter a * ell b +
          r.tangentIdentityCharacter b * ell a) ∧
      (∀ a, ell (Differential.deriv a) = Differential.deriv (ell a)) := by
  classical
  obtain ⟨q, hq⟩ := r.exists_coordinate_infinite_range hinj
  obtain ⟨K, hKfield, hKrat, hKC, hKdiff, hKdiffAlg,
      φ, hφδ, hztrans, hgen⟩ :=
    r.exists_transcendental_differential_genericPoint q hq
  letI : Field K := hKfield
  letI : Algebra ℚ K := hKrat
  letI : Algebra C K := hKC
  letI : Differential K := hKdiff
  letI : DifferentialAlgebra C K := hKdiffAlg
  let c0 : Fin 2 × Fin 2 → r.coordinateAlgebra := fun ij =>
    ⟨r.coordinate ij, Algebra.subset_adjoin ⟨(ij, 0), by
      funext g
      exact (differentialJet_zero _).symm⟩⟩
  change Transcendental C (φ (c0 q)) at hztrans
  change differentialAdjoin C (Set.range fun ij => φ (c0 ij)) = ⊤ at hgen
  have hz : ¬ IsAlgebraic C (φ (c0 q)) := by
    intro halg
    exact hztrans halg
  obtain ⟨D, hDne, hDcomm⟩ :=
    exists_nonzero_commuting_derivation_to_diffClosure
      (C := C) (K := K) (fun ij => φ (c0 ij)) hgen hz
  let L := RelativeDiffClosure C K
  letI : DifferentialAlgebra C L := by
    constructor
    intro c
    change Differential.deriv
        (algebraMap K L (algebraMap C K c)) =
      algebraMap K L (algebraMap C K (Differential.deriv c))
    rw [DifferentialAlgebra.deriv_algebraMap,
      DifferentialAlgebra.deriv_algebraMap]
  let iota : K →ₐ[C] L :=
    { toRingHom := algebraMap K L
      commutes' := fun _ => rfl }
  let φL : r.coordinateAlgebra →ₐ[C] L := iota.comp φ
  let d : r.coordinateAlgebra →ₗ[C] L := D.toLinearMap.comp φ.toLinearMap
  have hd (a b : r.coordinateAlgebra) :
      d (a * b) = φL a * d b + φL b * d a := by
    change D (φ (a * b)) =
      algebraMap K L (φ a) * D (φ b) + algebraMap K L (φ b) * D (φ a)
    rw [map_mul φ, D.leibniz]
    rfl
  have hdδ (a : r.coordinateAlgebra) :
      d (Differential.deriv a) = Differential.deriv (d a) := by
    change D (φ (Differential.deriv a)) = Differential.deriv (D (φ a))
    rw [hφδ, hDcomm]
  have hφLδ (a : r.coordinateAlgebra) :
      φL (Differential.deriv a) = Differential.deriv (φL a) := by
    change algebraMap K L (φ (Differential.deriv a)) =
      Differential.deriv (algebraMap K L (φ a))
    rw [DifferentialAlgebra.deriv_algebraMap, hφδ]
  let ell : r.coordinateAlgebra →ₗ[C] L := r.tangentTranslatedLinear φL d
  have hellMul (a b : r.coordinateAlgebra) :
      ell (a * b) = r.tangentIdentityCharacter a * ell b +
        r.tangentIdentityCharacter b * ell a :=
    r.tangentTranslatedLinear_mul φL d hd a b
  have hellδ (a : r.coordinateAlgebra) :
      ell (Differential.deriv a) = Differential.deriv (ell a) :=
    r.tangentTranslatedLinear_deriv φL d hφLδ hdδ a
  have hellNe : ell ≠ 0 := by
    intro hell
    let B : Matrix (Fin 2) (Fin 2) L := fun i j => φL (c0 (i, j))
    let A : Matrix (Fin 2) (Fin 2) L := fun i j =>
      φL (r.coordinateAntipode (c0 (i, j)))
    let V : Matrix (Fin 2) (Fin 2) L := fun i j => d (c0 (i, j))
    have hBA : B * A = 1 := by
      ext i j
      have hconv := congrArg φL (r.coordinateLift_id_antipode_comul (c0 (i, j)))
      rw [r.coordinateComul_coordinate (i, j), map_sum] at hconv
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply] at hconv
      have hsum : (∑ x : Fin 2,
          φL (c0 (i, x)) * φL (r.coordinateAntipode (c0 (x, j)))) =
          algebraMap C L (r.coordinateCounit (c0 (i, j))) := by
        simpa only [map_sum, map_mul, φL.commutes, c0] using hconv
      have hcounit : r.coordinateCounit (c0 (i, j)) =
          (1 : Matrix (Fin 2) (Fin 2) C) i j := by
        exact r.coordinateCounit_coordinate (i, j)
      rw [Matrix.mul_apply]
      change (∑ x : Fin 2,
          φL (c0 (i, x)) * φL (r.coordinateAntipode (c0 (x, j)))) = _
      rw [hsum, hcounit]
      simp [Matrix.one_apply]
    have hAV : A * V = 0 := by
      ext i j
      rw [Matrix.mul_apply]
      change ∑ k : Fin 2,
          φL (r.coordinateAntipode (c0 (i, k))) * d (c0 (k, j)) = 0
      rw [← r.tangentTranslatedLinear_coordinate φL d (i, j)]
      have h := LinearMap.congr_fun hell (c0 (i, j))
      exact h
    have hV : V = 0 := by
      calc
        V = 1 * V := (Matrix.one_mul V).symm
        _ = (B * A) * V := by rw [hBA]
        _ = B * (A * V) := Matrix.mul_assoc B A V
        _ = B * 0 := by rw [hAV]
        _ = 0 := Matrix.mul_zero B
    have hDy (ij : Fin 2 × Fin 2) : D (φ (c0 ij)) = 0 := by
      change d (c0 ij) = 0
      exact congrArg (fun M => M ij.1 ij.2) hV
    apply hDne
    exact derivation_eq_zero_of_differentialAdjoin_eq_top
      (C := C) (K := K) (E := L) (κ := Fin 2 × Fin 2)
      D (fun ij => φ (c0 ij)) hDcomm hDy hgen
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ell, hellNe, hellMul, hellδ⟩

end DifferentialMatrixGroupRepresentation

end

end GaloisForLFunctions.HTGeometry
