import GaloisForLFunctions.HTGeometry.AffineEigenbranchSecondOrderLaw
import GaloisForLFunctions.HTGeometry.LocalSpectralExtensionRelationRigidity
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-!
# Exact two-layer local spectral response

Attaching a two-level local factor and coupling only opposite layers reorganizes
the full second-order eigenvalue response into a simple-pole packet.  Each
residue is an observable coefficient difference across one oriented transition.
This is the algebraic bridge from local interaction to spectral-relation
rigidity.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unperturbed energy after adjoining a two-level local factor whose false
layer is shifted by `z`. -/
def twoLayerEnergy
    {α : Type*} (energy : α → ℂ) (z : ℂ) : α × Bool → ℂ
  | (a, false) => energy a + z
  | (a, true) => energy a

/-- A coupling supported only between opposite local layers. -/
def twoLayerCoupling
    {α : Type*} (transition : Matrix α α ℂ) :
    Matrix (α × Bool) (α × Bool) ℂ
  | (a, r), (b, s) => if r = s then 0 else transition a b

@[simp] theorem twoLayerEnergy_false
    {α : Type*} (energy : α → ℂ) (z : ℂ) (a : α) :
    twoLayerEnergy energy z (a, false) = energy a + z := rfl

@[simp] theorem twoLayerEnergy_true
    {α : Type*} (energy : α → ℂ) (z : ℂ) (a : α) :
    twoLayerEnergy energy z (a, true) = energy a := rfl

@[simp] theorem twoLayerCoupling_same
    {α : Type*} (transition : Matrix α α ℂ)
    (a b : α) (r : Bool) :
    twoLayerCoupling transition (a, r) (b, r) = 0 := by
  simp [twoLayerCoupling]

@[simp] theorem twoLayerCoupling_false_true
    {α : Type*} (transition : Matrix α α ℂ) (a b : α) :
    twoLayerCoupling transition (a, false) (b, true) =
      transition a b := by
  simp [twoLayerCoupling]

@[simp] theorem twoLayerCoupling_true_false
    {α : Type*} (transition : Matrix α α ℂ) (a b : α) :
    twoLayerCoupling transition (a, true) (b, false) =
      transition a b := by
  simp [twoLayerCoupling]

/-- The two-layer coupling has zero diagonal without any assumption on the
old-system transition matrix. -/
theorem twoLayerCoupling_diagonal_zero
    {α : Type*} (transition : Matrix α α ℂ) :
    ∀ i, twoLayerCoupling transition i i = 0 := by
  rintro ⟨a, r⟩
  exact twoLayerCoupling_same transition a a r

/-- Removing the diagonal from the second-order response changes nothing
when the perturbation has zero diagonal. -/
theorem secondOrderResponse_erase_eq_full
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (hVdiag : ∀ i, V i i = 0) (coefficient : ι → ℂ) :
    (∑ i, coefficient i *
        ∑ j ∈ Finset.univ.erase i,
          V i j * V j i / (energy i - energy j)) =
      ∑ i, coefficient i *
        ∑ j, V i j * V j i / (energy i - energy j) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => V i j * V j i / (energy i - energy j))
    (Finset.mem_univ i)]
  simp [hVdiag i]

/-- **Two-layer residue law.** The complete second-order response of an
opposite-layer coupling is exactly a simple-pole packet.  The pole indexed by
the oriented transition `a → b` carries residue
`(c(a,false)-c(b,true)) A(a,b) A(b,a)`. -/
theorem twoLayerSecondOrderResponse_eq_residuePacket
    {α : Type*} [Fintype α] [DecidableEq α]
    (energy : α → ℂ) (transition : Matrix α α ℂ)
    (coefficient : α × Bool → ℂ) (z : ℂ) :
    (∑ i, coefficient i *
        ∑ j ∈ Finset.univ.erase i,
          twoLayerCoupling transition i j *
              twoLayerCoupling transition j i /
            (twoLayerEnergy energy z i -
              twoLayerEnergy energy z j)) =
      ∑ a, ∑ b,
        ((coefficient (a, false) - coefficient (b, true)) *
            (transition a b * transition b a)) /
          (z + energy a - energy b) := by
  classical
  rw [secondOrderResponse_erase_eq_full
    (twoLayerEnergy energy z) (twoLayerCoupling transition)
    (twoLayerCoupling_diagonal_zero transition) coefficient]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp_rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, twoLayerCoupling_same,
    twoLayerCoupling_false_true, twoLayerCoupling_true_false,
    twoLayerEnergy_false, twoLayerEnergy_true, zero_mul, zero_div,
    zero_add, add_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  conv_lhs =>
    lhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show energy b - (energy a + z) =
      -(z + energy a - energy b) by ring, div_neg]
  rw [show energy a + z - energy b =
      z + energy a - energy b by ring]
  ring

end

end GaloisForLFunctions.HTGeometry
