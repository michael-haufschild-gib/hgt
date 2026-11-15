import GaloisForLFunctions.HTGeometry.Homology.AugmentedHochschildOne

/-!
# Alternating tangent moments in ordinary cyclic homology

A scalar and a vector augmentation derivation define the alternating tensor
moment `δ(a) • μ(b) - δ(b) • μ(a)`. The Leibniz rules kill Hochschild boundaries;
alternation kills signed rotations. The resulting detector acts on the ordinary
cyclic quotient and can retain two-tangent classes after unit tangents vanish.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.SquareZeroCyclic
variable {A V : Type*} [CommRing A] [Algebra ℂ A]
  [AddCommGroup V] [Module ℂ V]

/-- Degree-one ordinary cyclic homology for a commutative complex algebra. -/
abbrev CyclicOne (A : Type*) [CommRing A] [Algebra ℂ A] :=
  CyclicBarTensor ℂ A 1 ⧸ cyclicRelations (A := A)

/-- Tensoring on the left by a fixed algebra element is linear. -/
def pairLinearRight (a : A) : A →ₗ[ℂ] CyclicBarTensor ℂ A 1 where
  toFun := pair a
  map_add' b c := by
    have h (z : A) : Function.update ![a,b] 1 z = ![a,z] := by
      ext i; fin_cases i <;> simp
    simpa only [pair, h] using
      (PiTensorProduct.tprod ℂ (s := fun _ : Fin 2 => A)).map_update_add ![a,b] 1 b c
  map_smul' c b := by
    change pair a (c • b) = c • pair a b
    have h (z : A) : Function.update ![a,b] 1 z = ![a,z] := by
      ext i; fin_cases i <;> simp
    simpa only [pair, h] using
      (PiTensorProduct.tprod ℂ (s := fun _ : Fin 2 => A)).map_update_smul ![a,b] 1 c b

/-- An alternating two-moment detector, with one scalar and one vector moment. -/
def alternatingDetector (δ : A →ₗ[ℂ] ℂ) (μ : A →ₗ[ℂ] V) :
    CyclicBarTensor ℂ A 1 →ₗ[ℂ] V :=
  PiTensorProduct.lift (MultilinearMap.mk'
    (fun x : Fin 2 → A => δ (x 0) • μ (x 1) - δ (x 1) • μ (x 0))
    (by
      intro x j a b
      fin_cases j <;> simp [Function.update, add_smul, smul_add] <;> abel)
    (by
      intro x j c a
      fin_cases j <;> simp [Function.update, smul_smul, smul_sub, mul_comm]))

@[simp] theorem alternatingDetector_pair (δ : A →ₗ[ℂ] ℂ) (μ : A →ₗ[ℂ] V) (a b : A) :
    alternatingDetector δ μ (pair a b) = δ a • μ b - δ b • μ a := by
  simp [alternatingDetector, pair]

theorem alternatingDetector_boundaryTwo (ε : A →ₐ[ℂ] ℂ)
    (δ : A →ₗ[ℂ] ℂ) (μ : A →ₗ[ℂ] V)
    (hδ : ∀ a b, δ (a*b) = ε a * δ b + ε b * δ a)
    (hμ : ∀ a b, μ (a*b) = ε a • μ b + ε b • μ a) :
    (alternatingDetector δ μ).comp boundaryTwo = 0 := by
  apply PiTensorProduct.ext
  ext x
  change alternatingDetector δ μ (boundaryTwo (PiTensorProduct.tprod ℂ x)) = 0
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]
  change alternatingDetector δ μ (boundaryTwo (triple _ _ _)) = 0
  rw [boundaryTwo_triple]
  simp only [map_add, map_sub, alternatingDetector_pair, hδ, hμ,
    add_smul, smul_add, mul_smul]
  simp only [smul_comm (δ (x 0)), smul_comm (δ (x 1)), smul_comm (δ (x 2))]
  abel

theorem alternatingDetector_rotation (δ : A →ₗ[ℂ] ℂ) (μ : A →ₗ[ℂ] V) :
    (alternatingDetector δ μ).comp
      (LinearMap.id + (cyclicBarRotate (R := ℂ) (A := A) 1).toLinearMap) = 0 := by
  apply PiTensorProduct.ext
  ext x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  change alternatingDetector δ μ (PiTensorProduct.tprod ℂ x +
    cyclicBarRotate (R := ℂ) 1 (PiTensorProduct.tprod ℂ x)) = 0
  rw [hx]
  change alternatingDetector δ μ (pair _ _ + cyclicBarRotate (R := ℂ) 1 (pair _ _)) = 0
  rw [rotate_pair, map_add, alternatingDetector_pair, alternatingDetector_pair]
  abel

/-- Alternating tangent moments descend through the ordinary cyclic relations. -/
def cyclicAlternatingDetector (ε : A →ₐ[ℂ] ℂ)
    (δ : A →ₗ[ℂ] ℂ) (μ : A →ₗ[ℂ] V)
    (hδ : ∀ a b, δ (a*b) = ε a * δ b + ε b * δ a)
    (hμ : ∀ a b, μ (a*b) = ε a • μ b + ε b • μ a) :
    CyclicOne A →ₗ[ℂ] V :=
  (cyclicRelations (A := A)).liftQ (alternatingDetector δ μ) (by
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (alternatingDetector_boundaryTwo ε δ μ hδ hμ) x
    · rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (alternatingDetector_rotation δ μ) x)

@[simp] theorem cyclicAlternatingDetector_pair (ε : A →ₐ[ℂ] ℂ)
    (δ : A →ₗ[ℂ] ℂ) (μ : A →ₗ[ℂ] V)
    (hδ : ∀ a b, δ (a*b) = ε a * δ b + ε b * δ a)
    (hμ : ∀ a b, μ (a*b) = ε a • μ b + ε b • μ a) (a b : A) :
    cyclicAlternatingDetector ε δ μ hδ hμ
      ((cyclicRelations (A := A)).mkQ (pair a b)) = δ a • μ b - δ b • μ a :=
  alternatingDetector_pair δ μ a b

#print axioms alternatingDetector_boundaryTwo
#print axioms cyclicAlternatingDetector
end GaloisForLFunctions.RHTower.SquareZeroCyclic
