import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonomialBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonomialTraceLift
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Brauer lifts via monomial realizations of nilpotent-group representations. -/

namespace GlobalTheory.CuspGL

private theorem basis_smul_eq_smul_cancel {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) {x y : k} {i j : ι} (hx : x ≠ 0) (h : x • b i = y • b j) :
    i = j ∧ x = y := by
  classical
  have h1 := congrArg (fun v => b.repr v i) h
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, Finsupp.single_apply] at h1
  by_cases hij : j = i
  · subst hij
    simpa using h1
  · simp [hij, hx] at h1

/-- Lifting the roots of a nilpotent-group representation in nonmodular characteristic
gives the traces of an actual complex matrix representation. -/
theorem exists_matrix_brauer_lift (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    (G : Type) [Group G] [Finite G] [Group.IsNilpotent G] (hc : (Nat.card G : k) ≠ 0)
    (n : ℕ) (ρ : G →* GL (Fin n) k) :
    ∃ (m : ℕ) (L : G →* GL (Fin m) ℂ), ∀ g,
      ((Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) k)).roots.map θ).sum =
        (L g : Matrix (Fin m) (Fin m) ℂ).trace := by
  classical
  let R : Representation k G (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _).toMonoidHom.comp
      (Units.coeHom _)).comp ρ
  have hR : ∀ g, R g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k) := fun g => rfl
  obtain ⟨m, b, hb⟩ := exists_monomial_basis_of_nilpotent k G (Fin n → k) R hc
  choose s c hsc using hb
  have hc0 : ∀ g i, c g i ≠ 0 := by
    intro g i h0
    have h1 : R g (b i) = 0 := by rw [hsc, h0, zero_smul]
    have h2 : R (g⁻¹ * g) (b i) = 0 := by
      rw [map_mul, Module.End.mul_apply, h1, map_zero]
    rw [inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact b.ne_zero i h2
  have hmul : ∀ g h i, s (g * h) i = s g (s h i) ∧ c (g * h) i = c g (s h i) * c h i := by
    intro g h i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_mul, Module.End.mul_apply, hsc, map_smul, hsc, smul_smul, mul_comm]
  have hone : ∀ i, s 1 i = i ∧ c 1 i = 1 := by
    intro i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_one, Module.End.one_apply, one_smul]
  let σ : G → Equiv.Perm (Fin m) := fun g =>
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun i => by rw [← (hmul _ _ _).1, inv_mul_cancel, (hone i).1]
      right_inv := fun i => by rw [← (hmul _ _ _).1, mul_inv_cancel, (hone i).1] }
  let L : G →* Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Matrix.of fun i j => if i = σ g j then θ (c g j) else 0
      map_one' := by
        ext i j
        simp [σ, (hone j).1, (hone j).2, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext i j
        simp [σ, Matrix.mul_apply, (hmul g h j).1, (hmul g h j).2] }
  have hM : ∀ g, (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      = LinearMap.toMatrix b b (R g) := by
    intro g
    ext i j
    simp [σ, LinearMap.toMatrix_apply, hsc, Finsupp.single_apply, eq_comm]
  refine ⟨m, L.toHomUnits, fun g => ?_⟩
  have h1 : (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      ^ Nat.card G = 1 := by
    rw [hM, LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one', map_one, LinearMap.toMatrix_one]
  have h2 : L g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have h3 := trace_lift_monomial k θ hθ (σ g) (c g) (hc0 g) hc h1 h2
  rw [hM, LinearMap.charpoly_toMatrix, hR, Matrix.charpoly_toLin'] at h3
  exact h3.symm

end GlobalTheory.CuspGL
