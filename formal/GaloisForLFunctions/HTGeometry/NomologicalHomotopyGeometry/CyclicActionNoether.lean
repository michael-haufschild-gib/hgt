import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Tactic

/-!
# Cyclic formal actions, Euler--Lagrange equations, and higher Noether identity

All infinite expressions are handled through their finite arity quotients.  The identities below
hold at every truncation, hence coefficientwise in the separated inverse-limit completion.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.CyclicActionNoether

universe u v

variable {k : Type u} [Field k] [CharZero k]
variable {L : Type v} [AddCommGroup L] [Module k L]

/-- Positive arities, used to exclude a curved zero-ary operation. -/
abbrev PositiveNat := {n : ℕ // 0 < n}

/-- Cyclic multilinear operations in the shifted Maurer--Cartan degree.  The displayed cyclic law
is exactly the specialization needed when all but one input equal the sourced field `α`; in the
standard shifted convention every contribution has the same sign. -/
structure CyclicOperations where
  pairing : L →ₗ[k] L →ₗ[k] k
  pairing_nondegenerate : ∀ z, (∀ η, pairing η z = 0) → z = 0
  ell : ∀ n : PositiveNat, MultilinearMap k (fun _ : Fin n.1 ↦ L) L
  diagonal_cyclic : ∀ (n : PositiveNat) (α η : L) (i : Fin n.1),
    pairing α (ell n (Function.update (fun _ : Fin n.1 ↦ α) i η)) =
      pairing η (ell n (fun _ : Fin n.1 ↦ α))

/-- `n`th Maurer--Cartan summand. -/
def mcTerm (A : CyclicOperations (k := k) (L := L)) (n : PositiveNat) (α : L) : L :=
  (n.1.factorial : k)⁻¹ • A.ell n (fun _ ↦ α)

/-- `n`th homotopy Chern--Simons action summand. -/
def actionTerm (A : CyclicOperations (k := k) (L := L)) (n : PositiveNat) (α : L) : k :=
  ((n.1 + 1).factorial : k)⁻¹ * A.pairing α (A.ell n (fun _ ↦ α))

/-- Algebraic first variation of one action summand.  Multilinearity makes this the coefficient of
the first-order parameter without invoking analytic differentiation. -/
def firstVariationTerm (A : CyclicOperations (k := k) (L := L))
    (n : PositiveNat) (α η : L) : k :=
  ((n.1 + 1).factorial : k)⁻¹ *
    (A.pairing η (A.ell n (fun _ ↦ α)) +
      A.pairing α (∑ i : Fin n.1,
        A.ell n (Function.update (fun _ : Fin n.1 ↦ α) i η)))

theorem factorial_variation_identity (n : ℕ) (z : k) :
    (((n + 1).factorial : ℕ) : k)⁻¹ * (z + z * (n : k)) =
      (n.factorial : k)⁻¹ * z := by
  have hn : (n.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Nat.factorial_succ]
  push_cast
  rw [mul_inv_rev]
  field_simp [hn, hn1]
  ring

/-- Euler--Lagrange identity at one arity. -/
theorem firstVariationTerm_eq_pairing_mcTerm
    (A : CyclicOperations (k := k) (L := L)) (n : PositiveNat) (α η : L) :
    firstVariationTerm A n α η = A.pairing η (mcTerm A n α) := by
  rw [firstVariationTerm, mcTerm, map_smul]
  rw [map_sum]
  simp_rw [A.diagonal_cyclic n α η]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  simpa [smul_eq_mul, mul_comm] using
    factorial_variation_identity n.1 (A.pairing η (A.ell n (fun _ ↦ α)))

/-- Maurer--Cartan equation through arity `N`. -/
def mcPartial (A : CyclicOperations (k := k) (L := L)) (N : ℕ) (α : L) : L :=
  ∑ i : Fin N, mcTerm A ⟨i.1 + 1, Nat.succ_pos i.1⟩ α

/-- Homotopy Chern--Simons action through arity `N`. -/
def actionPartial (A : CyclicOperations (k := k) (L := L)) (N : ℕ) (α : L) : k :=
  ∑ i : Fin N, actionTerm A ⟨i.1 + 1, Nat.succ_pos i.1⟩ α

/-- First variation through arity `N`. -/
def firstVariationPartial (A : CyclicOperations (k := k) (L := L))
    (N : ℕ) (α η : L) : k :=
  ∑ i : Fin N, firstVariationTerm A ⟨i.1 + 1, Nat.succ_pos i.1⟩ α η

/-- Euler--Lagrange equals Maurer--Cartan at every finite arity quotient. -/
theorem firstVariationPartial_eq_pairing_mcPartial
    (A : CyclicOperations (k := k) (L := L)) (N : ℕ) (α η : L) :
    firstVariationPartial A N α η = A.pairing η (mcPartial A N α) := by
  rw [firstVariationPartial, mcPartial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact firstVariationTerm_eq_pairing_mcTerm A ⟨i.1 + 1, Nat.succ_pos i.1⟩ α η

/-- Criticality of a finite formal quotient. -/
def IsCriticalPartial (A : CyclicOperations (k := k) (L := L)) (N : ℕ) (α : L) : Prop :=
  ∀ η, firstVariationPartial A N α η = 0

/-- Nondegeneracy identifies the critical locus with the Maurer--Cartan locus. -/
theorem criticalPartial_iff_mcPartial_eq_zero
    (A : CyclicOperations (k := k) (L := L)) (N : ℕ) (α : L) :
    IsCriticalPartial A N α ↔ mcPartial A N α = 0 := by
  constructor
  · intro h
    apply A.pairing_nondegenerate
    intro η
    rw [← firstVariationPartial_eq_pairing_mcPartial]
    exact h η
  · intro h η
    rw [firstVariationPartial_eq_pairing_mcPartial, h]
    simp

/-- A sourced cyclic Maurer--Cartan law.  `twisted` is the convergent twisted unary operation.
Its three displayed identities are the zero-, one-, and two-input components of the square-zero
twisted codifferential. -/
structure CyclicMaurerCartanLaw extends CyclicOperations (k := k) (L := L) where
  mc : L → L
  twisted : L → Module.End k L
  bianchi : ∀ α, twisted α (mc α) = 0
  twisted_square : ∀ α, mc α = 0 → (twisted α).comp (twisted α) = 0
  twisted_cyclic : ∀ α x y, pairing (twisted α x) y = pairing x (twisted α y)

/-- Sourced Hessian determined by the twisted unary bracket. -/
def hessian (A : CyclicMaurerCartanLaw (k := k) (L := L)) (α η ξ : L) : k :=
  A.pairing η (A.twisted α ξ)

omit [CharZero k] in
/-- The sourced Hessian and linearized field equation are the same bilinear object. -/
theorem hessian_eq_pairing_twisted
    (A : CyclicMaurerCartanLaw (k := k) (L := L)) (α η ξ : L) :
    hessian A α η ξ = A.pairing η (A.twisted α ξ) :=
  rfl

omit [CharZero k] in
/-- At a Maurer--Cartan point the sourced deformation differential squares to zero. -/
theorem twisted_square_zero
    (A : CyclicMaurerCartanLaw (k := k) (L := L)) (α : L) (hα : A.mc α = 0) :
    (A.twisted α).comp (A.twisted α) = 0 :=
  A.twisted_square α hα

/-- Infinitesimal gauge direction. -/
def gaugeVariation (A : CyclicMaurerCartanLaw (k := k) (L := L)) (α ε : L) : L :=
  A.twisted α ε

/-- Variational one-form supplied by the completed action. -/
def variationalForm (A : CyclicMaurerCartanLaw (k := k) (L := L)) (α η : L) : k :=
  A.pairing η (A.mc α)

omit [CharZero k] in
/-- Higher Noether theorem: Bianchi plus cyclicity makes every infinitesimal gauge direction
annihilate the variational one-form off shell. -/
theorem infinitesimal_gauge_invariance
    (A : CyclicMaurerCartanLaw (k := k) (L := L)) (α ε : L) :
    variationalForm A α (gaugeVariation A α ε) = 0 := by
  rw [variationalForm, gaugeVariation, A.twisted_cyclic]
  rw [A.bianchi]
  simp

/-- Complete formal variational package, valid at every finite quotient and in the separated
inverse limit. -/
theorem cyclic_action_euler_lagrange_noether
    (A : CyclicMaurerCartanLaw (k := k) (L := L)) :
    (∀ N α η,
      firstVariationPartial A.toCyclicOperations N α η =
        A.pairing η (mcPartial A.toCyclicOperations N α)) ∧
      (∀ N α, IsCriticalPartial A.toCyclicOperations N α ↔
        mcPartial A.toCyclicOperations N α = 0) ∧
      (∀ α, A.twisted α (A.mc α) = 0) ∧
      (∀ α ε, variationalForm A α (gaugeVariation A α ε) = 0) :=
  ⟨firstVariationPartial_eq_pairing_mcPartial A.toCyclicOperations,
    criticalPartial_iff_mcPartial_eq_zero A.toCyclicOperations,
    A.bianchi, infinitesimal_gauge_invariance A⟩

/-! ## Cyclic formal-coordinate covariance -/

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- Strict cyclic isomorphism of all multilinear law operations. -/
structure CyclicOperationsEquiv
    (A : CyclicOperations (k := k) (L := L))
    (B : CyclicOperations (k := k) (L := M)) where
  map : L ≃ₗ[k] M
  pairing_natural : ∀ x y, B.pairing (map x) (map y) = A.pairing x y
  ell_natural : ∀ (n : PositiveNat) (x : Fin n.1 → L),
    B.ell n (fun i ↦ map (x i)) = map (A.ell n x)

omit [CharZero k] in
theorem CyclicOperationsEquiv.map_mcTerm
    {A : CyclicOperations (k := k) (L := L)}
    {B : CyclicOperations (k := k) (L := M)}
    (F : CyclicOperationsEquiv A B) (n : PositiveNat) (α : L) :
    F.map (mcTerm A n α) = mcTerm B n (F.map α) := by
  rw [mcTerm, mcTerm, map_smul, F.ell_natural]

omit [CharZero k] in
theorem CyclicOperationsEquiv.map_mcPartial
    {A : CyclicOperations (k := k) (L := L)}
    {B : CyclicOperations (k := k) (L := M)}
    (F : CyclicOperationsEquiv A B) (N : ℕ) (α : L) :
    F.map (mcPartial A N α) = mcPartial B N (F.map α) := by
  rw [mcPartial, mcPartial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact F.map_mcTerm ⟨i.1 + 1, Nat.succ_pos i.1⟩ α

/-- Cyclic formal coordinates preserve every finite critical Maurer--Cartan quotient. -/
theorem CyclicOperationsEquiv.criticalPartial_iff
    {A : CyclicOperations (k := k) (L := L)}
    {B : CyclicOperations (k := k) (L := M)}
    (F : CyclicOperationsEquiv A B) (N : ℕ) (α : L) :
    IsCriticalPartial B N (F.map α) ↔ IsCriticalPartial A N α := by
  rw [criticalPartial_iff_mcPartial_eq_zero, criticalPartial_iff_mcPartial_eq_zero]
  constructor
  · intro h
    apply F.map.injective
    rw [F.map_mcPartial, h, map_zero]
  · intro h
    rw [← F.map_mcPartial, h, map_zero]

/-- Structured isomorphism of completed sourced cyclic Maurer--Cartan laws. -/
structure CyclicMaurerCartanLawEquiv
    (A : CyclicMaurerCartanLaw (k := k) (L := L))
    (B : CyclicMaurerCartanLaw (k := k) (L := M))
    extends CyclicOperationsEquiv A.toCyclicOperations B.toCyclicOperations where
  mc_natural : ∀ α, B.mc (map α) = map (A.mc α)
  twisted_natural : ∀ α x, B.twisted (map α) (map x) = map (A.twisted α x)

omit [CharZero k] in
/-- Cyclic formal coordinates transport the sourced Hessian exactly. -/
theorem CyclicMaurerCartanLawEquiv.hessian_natural
    {A : CyclicMaurerCartanLaw (k := k) (L := L)}
    {B : CyclicMaurerCartanLaw (k := k) (L := M)}
    (F : CyclicMaurerCartanLawEquiv A B) (α η ξ : L) :
    hessian B (F.map α) (F.map η) (F.map ξ) = hessian A α η ξ := by
  rw [hessian, hessian, F.twisted_natural, F.pairing_natural]

omit [CharZero k] in
/-- Maurer--Cartan solutions, hence total critical points, are preserved and reflected. -/
theorem CyclicMaurerCartanLawEquiv.mc_eq_zero_iff
    {A : CyclicMaurerCartanLaw (k := k) (L := L)}
    {B : CyclicMaurerCartanLaw (k := k) (L := M)}
    (F : CyclicMaurerCartanLawEquiv A B) (α : L) :
    B.mc (F.map α) = 0 ↔ A.mc α = 0 := by
  rw [F.mc_natural]
  constructor
  · intro h
    apply F.map.injective
    simpa using h
  · intro h
    simp [h]

end HTGeometry.NomologicalHomotopyGeometry.CyclicActionNoether
