import GaloisForLFunctions.HTGeometry.StableDifferentialCore
import Mathlib.Tactic

/-!
# Stable tails for a nonautonomous sequence of differential injections

For a time-dependent sequence of injective field maps, the phase tail is the intersection of all
finite-depth prefix images.  Each microscopic map becomes an isomorphism on these tails.  This is
the field-theoretic core of the projective-time law for persistent HT information.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `n`-step constraint map beginning at phase `i`. -/
def forwardPrefix
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) : ℕ → F →ₐ[K] F
  | 0 => AlgHom.id K F
  | n + 1 => (φ i).comp (forwardPrefix φ (i + 1) n)

@[simp]
theorem forwardPrefix_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) :
    forwardPrefix φ i 0 = AlgHom.id K F := rfl

@[simp]
theorem forwardPrefix_succ_apply
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i n : ℕ) (x : F) :
    forwardPrefix φ i (n + 1) x = φ i (forwardPrefix φ (i + 1) n x) := rfl

/-- The field visible after every finite depth of the protocol beginning at phase `i`. -/
def nonautonomousTail
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) : IntermediateField K F :=
  ⨅ n : ℕ, IntermediateField.map (forwardPrefix φ i n) ⊤

/-- Tail membership is the existence of a preimage at every protocol depth. -/
theorem mem_nonautonomousTail_iff
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (x : F) :
    x ∈ nonautonomousTail φ i ↔ ∀ n : ℕ, ∃ y : F, forwardPrefix φ i n y = x := by
  rw [show nonautonomousTail φ i =
    ⨅ n : ℕ, IntermediateField.map (forwardPrefix φ i n) ⊤ from rfl]
  rw [← SetLike.mem_coe, IntermediateField.coe_iInf, Set.mem_iInter]
  constructor
  · intro h n
    have hn := h n
    change x ∈ IntermediateField.map (forwardPrefix φ i n) ⊤ at hn
    rw [IntermediateField.mem_map] at hn
    obtain ⟨y, _, hy⟩ := hn
    exact ⟨y, hy⟩
  · intro h n
    change x ∈ IntermediateField.map (forwardPrefix φ i n) ⊤
    rw [IntermediateField.mem_map]
    obtain ⟨y, hy⟩ := h n
    exact ⟨y, trivial, hy⟩

theorem nonautonomousTail_map_le
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) :
    IntermediateField.map (φ i) (nonautonomousTail φ (i + 1)) ≤
      nonautonomousTail φ i := by
  intro x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [mem_nonautonomousTail_iff] at hy ⊢
  intro n
  cases n with
  | zero => exact ⟨φ i y, rfl⟩
  | succ n =>
      obtain ⟨z, hz⟩ := hy n
      exact ⟨z, by rw [forwardPrefix_succ_apply, hz]⟩

theorem nonautonomousTail_le_map
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) :
    nonautonomousTail φ i ≤
      IntermediateField.map (φ i) (nonautonomousTail φ (i + 1)) := by
  intro x hx
  rw [mem_nonautonomousTail_iff] at hx
  obtain ⟨y, hy⟩ := hx 1
  have hφy : φ i y = x := by simpa using hy
  rw [IntermediateField.mem_map]
  refine ⟨y, ?_, hφy⟩
  rw [mem_nonautonomousTail_iff]
  intro n
  obtain ⟨z, hz⟩ := hx (n + 1)
  refine ⟨z, ?_⟩
  apply (φ i).injective
  have hz' : φ i (forwardPrefix φ (i + 1) n z) = x := by
    simpa using hz
  exact hz'.trans hφy.symm

/-- Exact phase transport: the microscopic injection maps the next tail onto the current tail. -/
theorem map_nonautonomousTail_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) :
    IntermediateField.map (φ i) (nonautonomousTail φ (i + 1)) =
      nonautonomousTail φ i :=
  le_antisymm (nonautonomousTail_map_le φ i) (nonautonomousTail_le_map φ i)

/-- The microscopic injection restricted to successive tails. -/
def nonautonomousTailTransitionAlgHom
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) :
    nonautonomousTail φ (i + 1) →ₐ[K] nonautonomousTail φ i :=
  ((φ i).comp (nonautonomousTail φ (i + 1)).val).codRestrict
    (nonautonomousTail φ i).toSubalgebra (fun x => by
      change φ i (x : F) ∈ nonautonomousTail φ i
      rw [← map_nonautonomousTail_eq φ i]
      rw [IntermediateField.mem_map]
      exact ⟨x, x.2, rfl⟩)

theorem nonautonomousTailTransitionAlgHom_bijective
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) :
    Function.Bijective (nonautonomousTailTransitionAlgHom φ i) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (φ i).injective
    exact congrArg (fun z : nonautonomousTail φ i => (z : F)) h
  · intro x
    have hxmap : (x : F) ∈
        IntermediateField.map (φ i) (nonautonomousTail φ (i + 1)) := by
      rw [map_nonautonomousTail_eq φ i]
      exact x.2
    rw [IntermediateField.mem_map] at hxmap
    obtain ⟨y, hy, hxy⟩ := hxmap
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Successive nonautonomous tails are canonically isomorphic through the microscopic injection. -/
def nonautonomousTailTransitionAlgEquiv
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) :
    nonautonomousTail φ (i + 1) ≃ₐ[K] nonautonomousTail φ i :=
  AlgEquiv.ofBijective (nonautonomousTailTransitionAlgHom φ i)
    (nonautonomousTailTransitionAlgHom_bijective φ i)

/-- Every finite protocol prefix commutes with the derivation when its steps do. -/
theorem forwardPrefix_deriv
    {K F : Type*} [Field K] [Field F] [Algebra K F] [Differential F]
    (φ : ℕ → F →ₐ[K] F) (hφ : ∀ i x, φ i x′ = (φ i x)′)
    (i n : ℕ) (x : F) :
    forwardPrefix φ i n x′ = (forwardPrefix φ i n x)′ := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [forwardPrefix_succ_apply, forwardPrefix_succ_apply, ih, hφ]

/-- Every phase tail is closed under the derivation. -/
theorem derivationClosed_nonautonomousTail
    {K F : Type*} [Field K] [Field F] [Algebra K F] [Differential F]
    (φ : ℕ → F →ₐ[K] F) (hφ : ∀ i x, φ i x′ = (φ i x)′) (i : ℕ) :
    DerivationClosed (nonautonomousTail φ i) := by
  intro x hx
  rw [mem_nonautonomousTail_iff] at hx ⊢
  intro n
  obtain ⟨y, hy⟩ := hx n
  refine ⟨y′, ?_⟩
  rw [forwardPrefix_deriv φ hφ i n y, hy]

end


end GaloisForLFunctions.HTGeometry
