import GaloisForLFunctions.HTGeometry.CDGATensorAlgebra
import GaloisForLFunctions.HTGeometry.CDGAUnital

/-!
# The unit of a tensor product of algebras

The unit of `A ⊗ B` is `1 ⊗ 1` in the single bidegree of total degree zero.  A splitting of an
output bidegree whose left part has total degree zero is unique — the left part is `(0,0)` and the
right part is the whole output — so the product with the unit is a one-term sum.

* `HTGeometry.tensorCDGAUnit` : the unit.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  (A : CDGAStructure R X) (B : CDGAStructure R Y)

/-- A splitting whose left part has total degree zero is determined by the output. -/
instance splittingZeroSubsingleton (b : ℕ) {n : ℕ} (p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    Subsingleton (Splitting 0 b p) := by
  refine ⟨fun rs rs' => ?_⟩
  have hr : rs.1.1.1.1 + rs.1.1.1.2 = 0 := rs.1.1.2
  have hr' : rs'.1.1.1.1 + rs'.1.1.1.2 = 0 := rs'.1.1.2
  have h1 := rs.2.1
  have h2 := rs.2.2
  have h1' := rs'.2.1
  have h2' := rs'.2.2
  refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) (Subtype.ext (Prod.ext ?_ ?_))) <;>
    omega

/-- The unit of the tensor product: `1 ⊗ 1`. -/
noncomputable def tensorAlgOne (u : CDGAUnit A) (v : CDGAUnit B) :
    TensorCarrier (R := R) X Y 0 :=
  tensorSingle (M := X) (N := Y) (⟨(0, 0), rfl⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = 0})
    (u.one ⊗ₜ[R] v.one)

/-- **The tensor product of two unital algebras is unital.** -/
noncomputable def tensorCDGAUnit (u : CDGAUnit A) (v : CDGAUnit B) :
    CDGAUnit (tensorCDGA A B) where
  one := tensorAlgOne A B u v
  one_mul b y := by
    funext p
    show (∑ rs : Splitting 0 b p, splittingTerm A B (tensorAlgOne A B u v) y rs) = y p
    have hp : p.1.1 + p.1.2 = b := p.2
    have hzero : (0, 0).1 + (0, 0).2 = 0 := rfl
    rw [Finset.sum_eq_single_of_mem
      (⟨(⟨(0, 0), hzero⟩, p), ⟨Nat.zero_add p.1.1, Nat.zero_add p.1.2⟩⟩ : Splitting 0 b p)
      (Finset.mem_univ _) (fun rs _ hne => absurd (Subsingleton.elim rs _) hne)]
    show tensorPairₗ A B (Nat.zero_add p.1.1) (Nat.zero_add p.1.2)
      (tensorAlgOne A B u v ⟨(0, 0), hzero⟩) (y p) = y p
    rw [show tensorAlgOne A B u v ⟨(0, 0), hzero⟩ = u.one ⊗ₜ[R] v.one from
      tensorSingle_same (M := X) (N := Y) _ _]
    induction (y p) using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul x w =>
        rw [tensorPairₗ_tmul, Nat.zero_mul, pow_zero, one_smul, u.one_mul, v.one_mul]
    | add z z' hz hz' => rw [map_add, hz, hz']
  d_one := by
    funext p
    obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
    show tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) 0
        (tensorAlgOne A B u v) ⟨(p₁, p₂), hp⟩
      + tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) 0
        (tensorAlgOne A B u v) ⟨(p₁, p₂), hp⟩ = 0
    have hzero : (0, 0).1 + (0, 0).2 = 0 := rfl
    have hone : tensorAlgOne A B u v ⟨(0, 0), hzero⟩ = u.one ⊗ₜ[R] v.one :=
      tensorSingle_same (M := X) (N := Y) _ _
    cases p₁ with
    | zero =>
        cases p₂ with
        | zero => exact absurd hp (by omega)
        | succ β =>
            obtain rfl : β = 0 := by omega
            have hL : tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) 0
                (tensorAlgOne A B u v) ⟨(0, 0 + 1), hp⟩ = 0 := tensorDL_zero _ _ _ _ _ hp
            have hR : tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) 0
                (tensorAlgOne A B u v) ⟨(0, 0 + 1), hp⟩ = 0 := by
              rw [tensorDR_succ]
              show ((-1 : R)) ^ 0 • TensorProduct.map LinearMap.id (B.dₗ 0)
                (tensorAlgOne A B u v ⟨(0, 0), hzero⟩) = 0
              rw [hone, pow_zero, one_smul, TensorProduct.map_tmul]
              show (LinearMap.id u.one : X 0) ⊗ₜ[R] B.d 0 v.one = 0
              rw [v.d_one, TensorProduct.tmul_zero]
            rw [hL, hR, add_zero]
    | succ α =>
        obtain ⟨rfl, rfl⟩ : α = 0 ∧ p₂ = 0 := by omega
        have hR : tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) 0
            (tensorAlgOne A B u v) ⟨(0 + 1, 0), hp⟩ = 0 := tensorDR_zero _ _ _ _ _ hp
        have hL : tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) 0
            (tensorAlgOne A B u v) ⟨(0 + 1, 0), hp⟩ = 0 := by
          rw [tensorDL_succ]
          show TensorProduct.map (A.dₗ 0) LinearMap.id
            (tensorAlgOne A B u v ⟨(0, 0), hzero⟩) = 0
          rw [hone, TensorProduct.map_tmul]
          show A.d 0 u.one ⊗ₜ[R] (LinearMap.id v.one : Y 0) = 0
          rw [u.d_one, TensorProduct.zero_tmul]
        rw [hL, hR, add_zero]

end GaloisForLFunctions.HTGeometry
