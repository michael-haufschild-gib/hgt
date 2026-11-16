import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw

/-!
# Normalized Hochschild deformations of the dual-number event

Every normalized bilinear cochain is determined by its value on `(ε, ε)`.
All these cochains are cocycles and integrate to associative products.
Coboundaries are exactly the multiples of the ε-valued cochain, whereas
cyclic cochains for the fixed Frobenius pairing are exactly the scalar-valued
ones. Thus every deformation class has a unique cyclic representative.

The insertion and weight identities specialize the Gerstenhaber operations
in Abbaspour, arXiv:1302.6534, §1, and the deformation mechanism of Lopatkin,
arXiv:2611.04022, Proposition 11.4, to the existing dual-number product.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent

noncomputable section

/-- A normalized binary cochain with prescribed value on `(ε, ε)`. -/
def binary (u : Dual) (x y : Dual) : Dual := (x.2 * y.2) • u

@[simp] theorem binary_eps_eps (u : Dual) : binary u eps eps = u := by
  simp [binary, eps]

@[simp] theorem binary_one_left (u x : Dual) : binary u one x = 0 := by
  simp [binary, one]

@[simp] theorem binary_one_right (u x : Dual) : binary u x one = 0 := by
  simp [binary, one]

private theorem coordinates (x : Dual) : x = x.1 • one + x.2 • eps := by
  ext <;> simp [one, eps]

/-- Normalization leaves exactly the two coordinates of the value at `(ε, ε)`. -/
theorem normalized_bilinear_iff (F : Dual →ₗ[ℝ] Dual →ₗ[ℝ] Dual) :
    (∀ x, F one x = 0 ∧ F x one = 0) ↔
      ∀ x y, F x y = binary (F eps eps) x y := by
  constructor
  · intro h x y
    conv_lhs => rw [coordinates x, coordinates y]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      (h one).1, (h eps).1, (h eps).2, smul_zero, zero_add, add_zero,
      smul_smul, binary, mul_comm]
  · intro h x
    exact ⟨by rw [h, binary_one_left], by rw [h, binary_one_right]⟩

/-- Every normalized binary cochain is a Hochschild cocycle. -/
theorem binary_cocycle (u x y z : Dual) : deltaTwo (binary u) x y z = 0 := by
  ext <;> dsimp [deltaTwo, binary, product] <;> ring

/-- Its self-insertion vanishes, so the second-order associativity obstruction is zero. -/
theorem binary_self_insertion (u x y z : Dual) :
    binary u (binary u x y) z - binary u x (binary u y z) = 0 := by
  ext <;> dsimp [binary] <;> ring

/-- The product with relation `ε² = t • u`. -/
def deformedProduct (u : Dual) (t : ℝ) (x y : Dual) : Dual :=
  product 0 x y + t • binary u x y

theorem deformedProduct_assoc (u : Dual) (t : ℝ) (x y z : Dual) :
    deformedProduct u t (deformedProduct u t x y) z =
      deformedProduct u t x (deformedProduct u t y z) := by
  ext <;> dsimp [deformedProduct, binary, product] <;> ring

theorem deformedProduct_unital (u : Dual) (t : ℝ) (x : Dual) :
    deformedProduct u t one x = x ∧ deformedProduct u t x one = x := by
  simp [deformedProduct]

/-- The normalized change of coordinates sending `ε` to a scalar multiple of `1`. -/
def scalarGauge (a : ℝ) : Dual →ₗ[ℝ] Dual where
  toFun x := (a * x.2, 0)
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' r x := by ext <;> dsimp <;> ring

/-- A scalar shift of ε has exactly the ε-valued Hochschild coboundary. -/
theorem deltaOne_scalarGauge (a : ℝ) (x y : Dual) :
    deltaOne (scalarGauge a) x y = binary (0, 2 * a) x y := by
  ext <;> dsimp [deltaOne, scalarGauge, product, binary] <;> ring

/-- Complete boundary classification, allowing all linear one-cochains. -/
theorem binary_coboundary_iff (u : Dual) :
    (∃ ξ : Dual →ₗ[ℝ] Dual, ∀ x y, deltaOne ξ x y = binary u x y) ↔ u.1 = 0 := by
  constructor
  · rintro ⟨ξ, hξ⟩
    have h := congrArg Prod.fst (hξ eps eps)
    rw [deltaOne_eps_eps_fst, binary_eps_eps] at h
    exact h.symm
  · intro hu
    refine ⟨scalarGauge (u.2 / 2), fun x y => ?_⟩
    rw [deltaOne_scalarGauge]
    congr 1
    ext <;> dsimp
    · exact hu.symm
    · ring

/-- Two normalized cocycles represent the same class exactly when their scalar values agree. -/
theorem binary_same_class_iff (u v : Dual) :
    (∃ ξ : Dual →ₗ[ℝ] Dual,
      ∀ x y, deltaOne ξ x y = binary u x y - binary v x y) ↔ u.1 = v.1 := by
  have h : ∀ x y, binary u x y - binary v x y = binary (u - v) x y := by
    intro x y
    exact (smul_sub _ _ _).symm
  simp only [h, binary_coboundary_iff, Prod.fst_sub, sub_eq_zero]

/-- Cyclicity for the original Frobenius pairing detects the ε-valued part exactly. -/
theorem binary_cyclic_iff (u : Dual) :
    (∀ x y z, pairing (binary u x y) z = pairing x (binary u y z)) ↔ u.2 = 0 := by
  constructor
  · intro h
    simpa [pairing, trace, product, binary, eps, one] using h eps eps one
  · intro hu x y z
    dsimp [pairing, trace, product, binary]
    rw [hu]
    ring

/-- The fixed pairing survives the whole deformation precisely on the scalar cocycle line. -/
theorem deformedProduct_cyclic_iff (u : Dual) :
    (∀ t x y z, pairing (deformedProduct u t x y) z =
      pairing x (deformedProduct u t y z)) ↔ u.2 = 0 := by
  constructor
  · intro h
    simpa [pairing, trace, product, deformedProduct, binary, eps, one]
      using h 1 eps eps one
  · intro hu t x y z
    dsimp [pairing, trace, product, deformedProduct, binary]
    rw [hu]
    ring

/-- Every normalized class has one and only one representative cyclic for the fixed pairing. -/
theorem unique_cyclic_representative (u : Dual) :
    ∃! v : Dual, (∀ x y z, pairing (binary v x y) z = pairing x (binary v y z)) ∧
      ∃ ξ : Dual →ₗ[ℝ] Dual,
        ∀ x y, deltaOne ξ x y = binary u x y - binary v x y := by
  refine ⟨(u.1, 0), ⟨(binary_cyclic_iff _).mpr rfl,
    (binary_same_class_iff _ _).mpr rfl⟩, ?_⟩
  intro v hv
  have hfst := (binary_same_class_iff u v).mp hv.2
  have hsnd := (binary_cyclic_iff v).mp hv.1
  exact Prod.ext hfst.symm hsnd

/-- Euler derivation for the grading in which ε has weight one. -/
def euler (x : Dual) : Dual := (0, x.2)

theorem euler_leibniz (x y : Dual) :
    euler (product 0 x y) = product 0 (euler x) y + product 0 x (euler y) := by
  ext <;> dsimp [euler, product] <;> ring

/-- The Gerstenhaber action records output weight minus total input weight. -/
theorem euler_binary_bracket (u x y : Dual) :
    euler (binary u x y) - binary u (euler x) y - binary u x (euler y) =
      binary (-2 * u.1, -u.2) x y := by
  ext <;> dsimp [euler, binary] <;> ring

/-- The nonzero cyclic deformation class has Euler weight minus two. -/
theorem euler_phi_bracket (x y : Dual) :
    euler (phi x y) - phi (euler x) y - phi x (euler y) = (-2 : ℝ) • phi x y := by
  ext <;> dsimp [euler, phi] <;> ring

end

end HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent

#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.normalized_bilinear_iff
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.unique_cyclic_representative
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.deformedProduct_assoc
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.euler_phi_bracket
