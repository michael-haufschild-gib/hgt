import GaloisForLFunctions.HTGeometry.CDGATensorConstExchange
import GaloisForLFunctions.HTGeometry.CDGARelTensor
import GaloisForLFunctions.HTGeometry.CDGATensorConst

/-!
# The relations of a tensor product with a constant coefficient module

Moving a constant module out of the second graded factor sends a relator to a relator with the
coefficient adjoined to the cell argument.  Nothing else changes: the action on `N ⊗ V` acts on `N`
and carries `V` along, which is exactly what the exchange does.

* `HTGeometry.tensorConstExchange_tmul` : the exchange on a pure tensor.
* `HTGeometry.tensorConstExchange_tensorSingle` : on a single-bidegree element.
* `HTGeometry.tensorConstExchange_relTensorRelator` : the relator correspondence.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {V : Type w} [AddCommGroup V] [Module R V]

/-- Associativity on an element tensored with a fixed vector is adjoining that vector. -/
theorem assoc_tmul_right {a b : ℕ} (w : V) (z : TensorProduct R (M a) (N b)) :
    TensorProduct.assoc R (M a) (N b) V (z ⊗ₜ[R] w)
      = TensorProduct.map LinearMap.id ((TensorProduct.mk R (N b) V).flip w) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u u' hu hu' =>
      rw [TensorProduct.add_tmul, map_add, map_add, hu, hu']

/-- **The exchange on a pure tensor** adjoins the coefficient to the second factor. -/
theorem tensorConstExchange_tmul (n : ℕ) (f : TensorCarrier (R := R) M N n) (w : V)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    tensorConstExchange (R := R) (M := M) (N := N) V n (f ⊗ₜ[R] w) p
      = TensorProduct.map LinearMap.id ((TensorProduct.mk R (N p.1.2) V).flip w) (f p) := by
  show TensorProduct.assoc R (M p.1.1) (N p.1.2) V
      (TensorProduct.comm R V (TensorProduct R (M p.1.1) (N p.1.2)) (w ⊗ₜ[R] f p)) = _
  rw [TensorProduct.comm_tmul, assoc_tmul_right]

/-- **The exchange on a single-bidegree element.** -/
theorem tensorConstExchange_tensorSingle (n : ℕ) {a b : ℕ}
    (h : (a, b).1 + (a, b).2 = n) (z : TensorProduct R (M a) (N b)) (w : V) :
    tensorConstExchange (R := R) (M := M) (N := N) V n
        (tensorSingle (N := N) ⟨(a, b), h⟩ z ⊗ₜ[R] w)
      = tensorSingle (N := fun m => TensorProduct R (N m) V) ⟨(a, b), h⟩
        (TensorProduct.map LinearMap.id ((TensorProduct.mk R (N b) V).flip w) z) := by
  funext p
  rw [tensorConstExchange_tmul]
  by_cases hp : p = (⟨(a, b), h⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
  · subst hp
    rw [tensorSingle_same, tensorSingle_same]
  · rw [tensorSingle_ne _ hp, map_zero, tensorSingle_ne _ hp]

section Relator

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)

/-- **A relator tensored with a coefficient is a relator with that coefficient adjoined.** -/
theorem tensorConstExchange_relTensorRelator {c a b n α β : ℕ} (hα : c + a = α)
    (hβ : c + b = β) (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : N b) (w : V) :
    tensorConstExchange (R := R) (M := M) (N := N) V n
        (relTensorRelator P Q hα hβ hn hn' x m v ⊗ₜ[R] w)
      = relTensorRelator P (tensorConstModule Q V) hα hβ hn hn' x m (v ⊗ₜ[R] w) := by
  simp only [relTensorRelator]
  rw [show ((((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v)
        - tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v)) ⊗ₜ[R] w)
      = ((-1 : R)) ^ (c * a) • (tensorSingle (N := N) ⟨(α, b), hn⟩
            (P.act hα x m ⊗ₜ[R] v) ⊗ₜ[R] w)
        - (tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v) ⊗ₜ[R] w) by
      rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul'],
    map_sub, map_smul, tensorConstExchange_tensorSingle, tensorConstExchange_tensorSingle,
    TensorProduct.map_tmul, TensorProduct.map_tmul]
  rfl

end Relator

end GaloisForLFunctions.HTGeometry
