import GaloisForLFunctions.HTGeometry.CausalRayPolarityNonselection
import GaloisForLFunctions.HTGeometry.GomesTensorConjugation

/-!
# Conjugate Higgs geometry of the existing causal spin flip

The corpus's causal spin flip is, up to a constant sign convention, the
conjugate Higgs doublet of Gomes, arXiv:2509.25276v7, Section 4.2 and Appendix B.
Its scalar charge reverses. The complex matrices commuting with the flip
are exactly quaternionic matrices. Simultaneous conjugation on a scalar
line extends the flip to the tensor product and retains its odd square.
The Hermitian and volume contractions are related by this same flip.
-/

open scoped TensorProduct ComplexConjugate Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The existing spin flip bundled as a conjugate-linear map. -/
def causalSpinFlipSemilinear : (Fin 2 → ℂ) →ₗ⋆[ℂ] (Fin 2 → ℂ) where
  toFun := causalSpinFlip
  map_add' H K := by
    funext i
    fin_cases i <;> simp [causalSpinFlip, Pi.add_apply, star_add, add_comm]
  map_smul' z H := by
    funext i
    fin_cases i <;> simp [causalSpinFlip, Pi.smul_apply, smul_eq_mul, star_mul] <;> ring

/-- Every unit-circle tensor charge is reversed by the conjugate doublet. -/
theorem causalSpinFlip_charge (u : Circle) (n : ℤ) (H : Fin 2 → ℂ) :
    causalSpinFlip (((u^n : Circle) : ℂ) • H) =
      (((u^(-n) : Circle) : ℂ)) • causalSpinFlip H := by
  change causalSpinFlipSemilinear (((u^n : Circle) : ℂ) • H) = _
  rw [map_smulₛₗ]
  have hc : conj (((u^n : Circle) : ℂ)) = (((u^(-n) : Circle) : ℂ)) := by
    rw [← Circle.coe_inv_eq_conj, zpow_neg]
  rw [hc]
  rfl

/-- Quaternionic matrices in their two-component complex realization. -/
def spinFlipQuaternionMatrix (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a, -conj b; b, conj a]

/-- Quaternionic transformations act identically on a doublet and its conjugate. -/
theorem causalSpinFlip_quaternion_matrix (a b : ℂ) (H : Fin 2 → ℂ) :
    causalSpinFlip ((spinFlipQuaternionMatrix a b).mulVec H) =
      (spinFlipQuaternionMatrix a b).mulVec (causalSpinFlip H) := by
  funext i
  fin_cases i <;>
    simp [causalSpinFlip, spinFlipQuaternionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, star_add, star_mul] <;> ring

/-- The complete complex-linear commutant of the antilinear flip is quaternionic. -/
theorem causalSpinFlip_matrix_commutant (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ H, causalSpinFlip (A.mulVec H) = A.mulVec (causalSpinFlip H)) ↔
      ∃ a b : ℂ, A = spinFlipQuaternionMatrix a b := by
  constructor
  · intro h
    have hh := h (![1, 0] : Fin 2 → ℂ)
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    simp [causalSpinFlip, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    refine ⟨A 0 0, A 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spinFlipQuaternionMatrix, h0, h1]
  · rintro ⟨a, b, rfl⟩
    exact causalSpinFlip_quaternion_matrix a b

/-- Canonical weak Hermitian contraction. -/
def weakHermitianContraction (H K : Fin 2 → ℂ) : ℂ :=
  conj (H 0) * K 0 + conj (H 1) * K 1

/-- Canonical weak volume contraction. -/
def weakVolumeContraction (H K : Fin 2 → ℂ) : ℂ := H 0 * K 1 - H 1 * K 0

/-- Spin flip converts the volume contraction into the Hermitian contraction. -/
theorem weakVolumeContraction_spinFlip (H K : Fin 2 → ℂ) :
    weakVolumeContraction (causalSpinFlip H) K = -weakHermitianContraction H K := by
  simp [weakVolumeContraction, weakHermitianContraction, causalSpinFlip]
  ring

/-- A doublet is Hermitian-orthogonal to its conjugate doublet. -/
theorem weakHermitianContraction_spinFlip_self (H : Fin 2 → ℂ) :
    weakHermitianContraction H (causalSpinFlip H) = 0 := by
  simp [weakHermitianContraction, causalSpinFlip]
  ring

/-- The scalar-line conjugation used to repair tensor balancing. -/
def scalarLineConjugation : ℂ →ₗ⋆[ℂ] ℂ where
  toFun := conj
  map_add' := map_add _
  map_smul' z w := map_mul _ z w

/-- Simultaneous spin and line conjugation on the literal complex tensor product. -/
def conjugateHiggsTensor : ((Fin 2 → ℂ) ⊗[ℂ] ℂ) →ₗ⋆[ℂ] ((Fin 2 → ℂ) ⊗[ℂ] ℂ) :=
  TensorProduct.map causalSpinFlipSemilinear scalarLineConjugation

theorem conjugateHiggsTensor_tmul (H : Fin 2 → ℂ) (z : ℂ) :
    conjugateHiggsTensor (H ⊗ₜ[ℂ] z) = causalSpinFlip H ⊗ₜ[ℂ] conj z := rfl

/-- The balanced tensor extension retains the quaternionic odd square. -/
theorem conjugateHiggsTensor_twice (x : (Fin 2 → ℂ) ⊗[ℂ] ℂ) :
    conjugateHiggsTensor (conjugateHiggsTensor x) = -x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_comm]
  | tmul H z => simp [conjugateHiggsTensor_tmul, causalSpinFlip_twice, TensorProduct.neg_tmul]

end GaloisForLFunctions.HTGeometry
