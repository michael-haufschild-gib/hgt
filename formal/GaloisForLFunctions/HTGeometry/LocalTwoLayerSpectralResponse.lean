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

open Filter Topology
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

/-- Finite collision set excluded from the local layer-shift parameter. -/
def twoLayerForbiddenShift
    {α : Type*} (energy : α → ℂ) : Set ℂ :=
  Set.range fun p : α × α => energy p.2 - energy p.1

theorem twoLayerForbiddenShift_finite
    {α : Type*} [Fintype α] (energy : α → ℂ) :
    (twoLayerForbiddenShift energy).Finite :=
  Set.finite_range _

/-- Outside the finite collision set, adjoining a shifted two-level factor
preserves simplicity of every old energy level. -/
theorem twoLayerEnergy_injective_of_not_forbidden
    {α : Type*} [Fintype α]
    (energy : α → ℂ) (henergy : Function.Injective energy)
    {z : ℂ} (hz : z ∉ twoLayerForbiddenShift energy) :
    Function.Injective (twoLayerEnergy energy z) := by
  rintro ⟨a, r⟩ ⟨b, s⟩ h
  cases r <;> cases s
  · exact Prod.ext (henergy (add_right_cancel h)) rfl
  · exfalso
    apply hz
    refine ⟨(a, b), ?_⟩
    change energy b - energy a = z
    change energy a + z = energy b at h
    calc
      energy b - energy a =
          (energy a + z) - energy a := by rw [h]
      _ = z := by ring
  · exfalso
    apply hz
    refine ⟨(b, a), ?_⟩
    change energy a - energy b = z
    change energy a = energy b + z at h
    calc
      energy a - energy b =
          (energy b + z) - energy b := by rw [h]
      _ = z := by ring
  · exact Prod.ext (henergy h) rfl

/-- There are always infinitely many collision-free local shifts. -/
theorem twoLayerAdmissibleShift_infinite
    {α : Type*} [Fintype α] (energy : α → ℂ) :
    (twoLayerForbiddenShift energy)ᶜ.Infinite :=
  (twoLayerForbiddenShift_finite energy).infinite_compl

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

/-- Maximal projective rank makes the complex poles on every interaction
subgraph canonically labelled by oriented transitions. -/
theorem maximallyProjectiveEnergy_orientedTransitionPole_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (energy : α → ℝ)
    (hmax : MaximallyProjectiveEnergy energy) :
    Function.Injective
      (orientedTransitionPole G fun a => (energy a : ℂ)) := by
  let fullGap :
      {p : α × α // p.1 ≠ p.2} → ℝ :=
    fun p => energy p.1.1 - energy p.1.2
  have hfull : Function.Injective fullGap :=
    maximallyProjectiveEnergy_orientedGap_injective energy hmax
  intro p q hpq
  let p' : {x : α × α // x.1 ≠ x.2} :=
    ⟨p.1, p.2.ne⟩
  let q' : {x : α × α // x.1 ≠ x.2} :=
    ⟨q.1, q.2.ne⟩
  have hreal : fullGap p' = fullGap q' := by
    apply Complex.ofReal_injective
    simpa [fullGap, p', q', orientedTransitionPole] using hpq
  have hp'q' := hfull hreal
  apply Subtype.ext
  change p.1 = q.1
  simpa [p', q'] using congrArg Subtype.val hp'q'

/-- Maximal projective rank in particular forces a simple labelled
spectrum. -/
theorem maximallyProjectiveEnergy_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy) :
    Function.Injective energy := by
  have hfull :=
    maximallyProjectiveEnergy_orientedGap_injective energy hmax
  intro a b hab
  by_contra hne
  let p : {x : α × α // x.1 ≠ x.2} := ⟨(a, b), hne⟩
  let q : {x : α × α // x.1 ≠ x.2} := ⟨(b, a), Ne.symm hne⟩
  have hpq :
      (fun x : {x : α × α // x.1 ≠ x.2} =>
        energy x.1.1 - energy x.1.2) p =
      (fun x : {x : α × α // x.1 ≠ x.2} =>
        energy x.1.1 - energy x.1.2) q := by
    simp [p, q, hab]
  have heq := hfull hpq
  exact hne (by
    simpa [p, q] using congrArg (fun x => x.1.1) heq)

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

/-- A double finite sum splits canonically into its diagonal and ordered
off-diagonal parts. -/
theorem sum_pair_eq_diag_add_offDiagonal
    {α M : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid M] (f : α → α → M) :
    (∑ a, ∑ b, f a b) =
      (∑ a, f a a) +
        ∑ p : Σ a : α, {b : α // b ≠ a}, f p.1 p.2 := by
  calc
    (∑ a, ∑ b, f a b) =
        ∑ a, (f a a +
          ∑ b : {b : α // b ≠ a}, f a b) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact Fintype.sum_eq_add_sum_subtype_ne (f a) a
    _ = _ := by
      rw [Finset.sum_add_distrib, Fintype.sum_sigma]

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

/-- **Actual off-diagonal residue extraction.** A repeated zero-gap pole
from diagonal transition matrix elements cannot conceal any nonzero ordered
transition residue.  Under maximal projective rank, vanishing of the full
response on infinitely many collision-free shifts forces every nonzero
transition product to identify the corresponding left and right
coefficients. -/
theorem crossCoefficient_eq_of_residueIdentity
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (leftCoefficient rightCoefficient : α → ℂ)
    (S : Set ℂ) (hS : S.Infinite)
    (hadmissible :
      ∀ z ∈ S,
        z ∉ twoLayerForbiddenShift (fun a => (energy a : ℂ)))
    (hidentity :
      ∀ z ∈ S,
        ∑ a, ∑ b,
          ((leftCoefficient a - rightCoefficient b) *
              (transition a b * transition b a)) /
            (z + (energy a : ℂ) - energy b) = 0) :
    ∀ a b, a ≠ b →
      transition a b * transition b a ≠ 0 →
      leftCoefficient a = rightCoefficient b := by
  classical
  let ι := Σ a : α, {b : α // b ≠ a}
  let pole : ι → ℂ :=
    fun p => (energy p.1 : ℂ) - energy p.2
  let residue : ι → ℂ :=
    fun p =>
      (leftCoefficient p.1 - rightCoefficient p.2) *
        (transition p.1 p.2 * transition p.2 p.1)
  let zeroResidue : ℂ :=
    ∑ a,
      (leftCoefficient a - rightCoefficient a) *
        (transition a a * transition a a)
  have hfull :=
    maximallyProjectiveEnergy_orientedGap_injective energy hmax
  have hpole : Function.Injective pole := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hp
    have hreal :
        energy a - energy b = energy c - energy d := by
      apply Complex.ofReal_injective
      simpa [pole] using hp
    have hpairs :
        (⟨(a, b.1), b.2.symm⟩ :
            {p : α × α // p.1 ≠ p.2}) =
          ⟨(c, d.1), d.2.symm⟩ :=
      hfull hreal
    have hac : a = c :=
      congrArg (fun x => x.1.1) hpairs
    subst c
    have hbd : b = d := by
      apply Subtype.ext
      exact congrArg (fun x => x.1.2) hpairs
    subst d
    rfl
  have hpole_ne : ∀ p, pole p ≠ 0 := by
    rintro ⟨a, b⟩ hp
    let p : {x : α × α // x.1 ≠ x.2} :=
      ⟨(a, b.1), b.2.symm⟩
    let q : {x : α × α // x.1 ≠ x.2} :=
      ⟨(b.1, a), b.2⟩
    have hpq : (fun x : {x : α × α // x.1 ≠ x.2} =>
        energy x.1.1 - energy x.1.2) p =
        (fun x : {x : α × α // x.1 ≠ x.2} =>
          energy x.1.1 - energy x.1.2) q := by
      have hpReal :
          energy a - energy b = 0 := by
        apply Complex.ofReal_injective
        simpa [pole] using hp
      simp only [p, q]
      linarith
    have heq := hfull hpq
    have hab : a = b := by
      have := congrArg (fun x =>
        x.1.1) heq
      simpa [p, q] using this
    exact b.2 hab.symm
  have hzeroAvoid : ∀ z ∈ S, z ≠ 0 := by
    intro z hz hzero
    apply hadmissible z hz
    refine ⟨(Classical.arbitrary α, Classical.arbitrary α), ?_⟩
    simp [hzero]
  have hpoleAvoid : ∀ z ∈ S, ∀ p, z ≠ -pole p := by
    intro z hz p hp
    apply hadmissible z hz
    refine ⟨(p.1, p.2), ?_⟩
    simpa [pole] using hp.symm
  have hsplit :
      ∀ z ∈ S,
        zeroResidue / z +
          ∑ p : ι, residue p / (z + pole p) = 0 := by
    intro z hz
    rw [← hidentity z hz]
    rw [sum_pair_eq_diag_add_offDiagonal]
    congr 1
    · unfold zeroResidue
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      rw [show z + (energy a : ℂ) - energy a = z by ring]
    · simp only [residue, pole, ι, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [show z + ((energy a : ℂ) - energy b) =
          z + (energy a : ℂ) - energy b by ring]
  have hresidueZero :
      residue = 0 :=
    coefficients_eq_zero_of_shifted_rational_identity_with_zeroPole
      pole residue zeroResidue S hS hpole hpole_ne
      hzeroAvoid hpoleAvoid hsplit
  intro a b hab htransition
  let p : ι := ⟨a, ⟨b, hab.symm⟩⟩
  have hp := congrFun hresidueZero p
  simp only [Pi.zero_apply] at hp
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp (by simpa [residue, p] using hp)).resolve_right
      htransition)

/-- Two-layer specialization of off-diagonal residue extraction. -/
theorem crossLayer_eq_of_twoLayerResidueIdentity
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (coefficient : α × Bool → ℂ)
    (S : Set ℂ) (hS : S.Infinite)
    (hadmissible :
      ∀ z ∈ S,
        z ∉ twoLayerForbiddenShift (fun a => (energy a : ℂ)))
    (hidentity :
      ∀ z ∈ S,
        ∑ a, ∑ b,
          ((coefficient (a, false) - coefficient (b, true)) *
              (transition a b * transition b a)) /
            (z + (energy a : ℂ) - energy b) = 0) :
    ∀ a b, a ≠ b →
      transition a b * transition b a ≠ 0 →
      coefficient (a, false) = coefficient (b, true) :=
  crossCoefficient_eq_of_residueIdentity
    energy hmax transition
    (fun a => coefficient (a, false))
    (fun b => coefficient (b, true))
    S hS hadmissible hidentity

/-- **Analytic local-interaction relation erasure.** Every branchwise linear
relation among actual analytic eigenvalue branches of the shifted
two-layer Hamiltonian obeys the residue law above.  Hence maximal old-system
projective rank forces coefficient equality across every transition whose
forward-backward product is nonzero. -/
theorem crossLayer_eq_of_twoLayerAnalyticBranchRelation
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (coefficient : α × Bool → ℂ)
    (S : Set ℂ) (hS : S.Infinite)
    (hadmissible :
      ∀ z ∈ S,
        z ∉ twoLayerForbiddenShift (fun a => (energy a : ℂ)))
    (branch : ℂ → (α × Bool) → ℂ → ℂ)
    (hbranch :
      ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0)
    (hbase :
      ∀ z ∈ S, ∀ i,
        branch z i 0 =
          twoLayerEnergy (fun a => (energy a : ℂ)) z i)
    (hroot :
      ∀ z ∈ S, ∀ i,
        ∀ᶠ g in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (twoLayerEnergy
                  (fun a => (energy a : ℂ)) z) +
              g • twoLayerCoupling transition,
              branch z i g) = 0)
    (hrelation :
      ∀ z ∈ S,
        ∀ᶠ g in 𝓝 0,
          ∑ i, coefficient i * branch z i g = 0) :
    ∀ a b, a ≠ b →
      transition a b * transition b a ≠ 0 →
      coefficient (a, false) = coefficient (b, true) := by
  apply crossLayer_eq_of_twoLayerResidueIdentity
    energy hmax transition coefficient S hS hadmissible
  intro z hz
  have henergyComplex :
      Function.Injective (fun a => (energy a : ℂ)) :=
    Complex.ofReal_injective.comp
      (maximallyProjectiveEnergy_injective energy hmax)
  have hresponse :=
    affineEigenbranch_linear_relation_secondOrder
      (twoLayerEnergy (fun a => (energy a : ℂ)) z)
      (twoLayerEnergy_injective_of_not_forbidden
        (fun a => (energy a : ℂ)) henergyComplex
        (hadmissible z hz))
      (twoLayerCoupling transition)
      (twoLayerCoupling_diagonal_zero transition)
      coefficient (branch z)
      (hbranch z hz) (hbase z hz) (hroot z hz)
      (hrelation z hz)
  rw [twoLayerSecondOrderResponse_eq_residuePacket] at hresponse
  exact hresponse

end

end GaloisForLFunctions.HTGeometry
