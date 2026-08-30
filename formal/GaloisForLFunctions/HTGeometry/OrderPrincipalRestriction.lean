import GaloisForLFunctions.HTGeometry.HumbertCoordinates
import GaloisForLFunctions.HTGeometry.OrderSymmetricSpace

/-!
# Principal restrictions of order forms

Restricting a balanced form to any collection of complete order blocks preserves balancedness.
For an injective block selection it also preserves symmetry and positive definiteness.  In
particular, both canonical rank-lowering restrictions of an order-cone point are again order-cone
points, with no retained form, positivity, or balance hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {m n d : ℕ} {R : Type*} [CommRing R]

/-- The real regular-representation block attached to one order element. -/
noncomputable def basisEntryRep (ω : Module.Basis (Fin d) ℤ R) (α : R) :
    Matrix (Fin d) (Fin d) ℝ :=
  (Algebra.leftMulMatrix ω α).map (fun z : ℤ => (z : ℝ))

/-- Balancedness is equivalent to the self-adjointness relation on every complete order block. -/
theorem mem_balancedSubspace_iff_blocks (ω : Module.Basis (Fin d) ℤ R)
    {A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ} :
    A ∈ balancedSubspace ω ↔
      ∀ i j : Fin n, ∀ α : R,
        (basisEntryRep ω α)ᵀ * blockUnembed A i j =
          blockUnembed A i j * basisEntryRep ω α := by
  classical
  have hdiagT (α : R) :
      (Matrix.of fun i j : Fin n =>
          ((Matrix.diagonal fun _ : Fin n =>
            (Algebra.leftMulMatrix ω α).map (fun z : ℤ => (z : ℝ))) j i)ᵀ) =
        Matrix.diagonal fun _ : Fin n =>
          ((Algebra.leftMulMatrix ω α).map (fun z : ℤ => (z : ℝ)))ᵀ := by
    funext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  constructor
  · intro hA i j α
    have h := hA α
    rw [blockEmbed_smulOne, ← blockEmbed_blockUnembed A,
      blockEmbed_transpose, ← blockEmbed_mul, ← blockEmbed_mul] at h
    have hb := blockEmbed_injective h
    rw [hdiagT] at hb
    have hij := congrFun (congrFun hb i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
    exact hij
  · intro hA α
    rw [blockEmbed_smulOne, ← blockEmbed_blockUnembed A,
      blockEmbed_transpose, ← blockEmbed_mul, ← blockEmbed_mul]
    apply congrArg blockEmbed
    rw [hdiagT]
    funext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact hA i j α

/-- Restriction of a block matrix along a selection of complete order blocks. -/
def orderPrincipal (f : Fin m → Fin n) (A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) :
    Matrix (Fin (m * d)) (Fin (m * d)) ℝ :=
  blockEmbed (Matrix.of fun i j => blockUnembed A (f i) (f j))

/-- The flattened coordinate selection underlying `orderPrincipal`. -/
def orderPrincipalIndex (f : Fin m → Fin n) (p : Fin (m * d)) : Fin (n * d) :=
  finProdFinEquiv (f (Fin.divNat p), Fin.modNat p)

theorem orderPrincipalIndex_injective {f : Fin m → Fin n} (hf : Function.Injective f) :
    Function.Injective (orderPrincipalIndex (d := d) f) := by
  intro p q hpq
  have hpairs := finProdFinEquiv.injective hpq
  have hdiv : Fin.divNat p = Fin.divNat q := hf (congrArg Prod.fst hpairs)
  have hmod : Fin.modNat p = Fin.modNat q := congrArg Prod.snd hpairs
  rw [← finProdFinEquiv_divNat_modNat p, ← finProdFinEquiv_divNat_modNat q, hdiv, hmod]

theorem orderPrincipal_eq_submatrix
    (f : Fin m → Fin n) (A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) :
    orderPrincipal f A = A.submatrix (orderPrincipalIndex f) (orderPrincipalIndex f) := by
  ext p q
  rfl

@[simp]
theorem blockUnembed_orderPrincipal
    (f : Fin m → Fin n) (A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) (i j : Fin m) :
    blockUnembed (orderPrincipal f A) i j = blockUnembed A (f i) (f j) := by
  rw [orderPrincipal, blockUnembed_blockEmbed]
  rfl

theorem orderPrincipal_mem_balanced (ω : Module.Basis (Fin d) ℤ R)
    (f : Fin m → Fin n) {A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ}
    (hA : A ∈ balancedSubspace ω) : orderPrincipal f A ∈ balancedSubspace ω := by
  rw [mem_balancedSubspace_iff_blocks] at hA ⊢
  intro i j α
  rw [blockUnembed_orderPrincipal]
  exact hA (f i) (f j) α

theorem orderPrincipal_mem_symm (f : Fin m → Fin n)
    {A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ}
    (hA : A ∈ symmMatrices (n * d)) : orderPrincipal f A ∈ symmMatrices (m * d) := by
  rw [mem_symmMatrices_iff] at hA ⊢
  rw [orderPrincipal_eq_submatrix]
  ext p q
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
  have hpq := congrFun (congrFun hA (orderPrincipalIndex f q)) (orderPrincipalIndex f p)
  simpa only [Matrix.transpose_apply] using hpq.symm

theorem orderPrincipal_posDef {f : Fin m → Fin n} (hf : Function.Injective f)
    {A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ} (hA : A.PosDef) :
    (orderPrincipal f A).PosDef := by
  rw [orderPrincipal_eq_submatrix]
  exact hA.submatrix (orderPrincipalIndex_injective hf)

/-- Every injective complete-block restriction of an order-cone point remains in the order cone. -/
noncomputable def orderConePrincipal (ω : Module.Basis (Fin d) ℤ R)
    (f : Fin m → Fin n) (hf : Function.Injective f)
    (A : ↥(orderCone (nb := n) ω)) : ↥(orderCone (nb := m) ω) :=
  ⟨⟨orderPrincipal f A,
      ⟨orderPrincipal_mem_symm f A.1.2.1,
        orderPrincipal_mem_balanced ω f A.1.2.2⟩⟩,
    orderPrincipal_posDef hf A.2⟩

/-- The leading rank-`n` restriction of a rank-`n+1` order form, with every property discharged. -/
noncomputable def orderConeCastSucc (ω : Module.Basis (Fin d) ℤ R)
    (A : ↥(orderCone (nb := n + 1) ω)) : ↥(orderCone (nb := n) ω) :=
  orderConePrincipal ω Fin.castSucc (Fin.castSucc_injective n) A

/-- The trailing rank-`n` restriction of a rank-`n+1` order form, with every property discharged. -/
noncomputable def orderConeTail (ω : Module.Basis (Fin d) ℤ R)
    (A : ↥(orderCone (nb := n + 1) ω)) : ↥(orderCone (nb := n) ω) :=
  orderConePrincipal ω Fin.succ (Fin.succ_injective n) A

end GaloisForLFunctions.HTGeometry
