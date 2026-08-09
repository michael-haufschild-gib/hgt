import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import GaloisForLFunctions.HTGeometry.ObserverVisibleLocalTimeDimension

/-!
# Fixed blocks bound the observer-invisible coefficient dimension

A fixed complex subspace `B` containing the input state has a projective tangent channel
`B ∩ ψ^⊥` of real dimension `2 (dim_ℂ B - 1)`.  Every real coefficient direction whose assembled
Hamiltonian preserves `B` sends the state into that channel, so the observer-channel codimension
law bounds the dimension of any block-preserving coefficient subspace by the coefficient
dimension minus the observer rank plus twice the nontrivial block dimension.

The observer rank appearing in the bound is the rank of the quantum Fisher information matrix.
-/

namespace QuantumAlg

open Matrix

variable {n : Type*} [Fintype n] {M : ℕ}

noncomputable section

/-! ## The projective tangent channel of a fixed block -/

/-- Hermitian inner product against a fixed state, as a complex-linear functional. -/
def stateFunctional (ψ : n → ℂ) : (n → ℂ) →ₗ[ℂ] ℂ where
  toFun v := star ψ ⬝ᵥ v
  map_add' v w := by
    simp only [dotProduct, Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

@[simp] theorem stateFunctional_apply (ψ v : n → ℂ) :
    stateFunctional ψ v = star ψ ⬝ᵥ v := rfl

/-- Projective tangent channel of a fixed block at a state: the block vectors orthogonal to
the state. -/
def blockTangentChannel (ψ : n → ℂ) (B : Submodule ℂ (n → ℂ)) : Submodule ℂ (n → ℂ) :=
  B ⊓ LinearMap.ker (stateFunctional ψ)

theorem blockTangentChannel_le (ψ : n → ℂ) (B : Submodule ℂ (n → ℂ)) :
    blockTangentChannel ψ B ≤ B := inf_le_left

theorem mem_blockTangentChannel {ψ : n → ℂ} {B : Submodule ℂ (n → ℂ)} {v : n → ℂ} :
    v ∈ blockTangentChannel ψ B ↔ v ∈ B ∧ star ψ ⬝ᵥ v = 0 := by
  simp [blockTangentChannel, LinearMap.mem_ker]

/-- A unit state inside a block cuts exactly one complex dimension off it. -/
theorem finrank_blockTangentChannel_add_one
    {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (B : Submodule ℂ (n → ℂ)) (hψB : ψ ∈ B) :
    Module.finrank ℂ (blockTangentChannel ψ B) + 1 = Module.finrank ℂ B := by
  classical
  set f : B →ₗ[ℂ] ℂ := (stateFunctional ψ).comp B.subtype with hf
  have hrange : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨c • (⟨ψ, hψB⟩ : B), ?_⟩
    have : f (c • (⟨ψ, hψB⟩ : B)) = c * (star ψ ⬝ᵥ ψ) := by
      simp [hf, dotProduct, Finset.mul_sum]
    rw [this, hψ, mul_one]
  have hker : LinearMap.ker f = (blockTangentChannel ψ B).comap B.subtype := by
    ext x
    simp [hf, blockTangentChannel, LinearMap.mem_ker]
  have hkerRank : Module.finrank ℂ (LinearMap.ker f) =
      Module.finrank ℂ (blockTangentChannel ψ B) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe (blockTangentChannel_le ψ B)).finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self, hkerRank] at hrn
  omega

/-- Real dimension of the projective tangent channel of a block containing a unit state. -/
theorem finrank_real_blockTangentChannel_add_two
    {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (B : Submodule ℂ (n → ℂ)) (hψB : ψ ∈ B) :
    Module.finrank ℝ (blockTangentChannel ψ B) + 2 = 2 * Module.finrank ℂ B := by
  have hmul :
      Module.finrank ℝ ℂ * Module.finrank ℂ (blockTangentChannel ψ B) =
        Module.finrank ℝ (blockTangentChannel ψ B) :=
    Module.finrank_mul_finrank ℝ ℂ (blockTangentChannel ψ B)
  rw [Complex.finrank_real_complex] at hmul
  have hcut := finrank_blockTangentChannel_add_one hψ B hψB
  omega

/-! ## The observer action as a real-linear map -/

/-- Real-linear projective action of the coefficient space on the state. -/
def observerActionMap (ψ : n → ℂ) (h : Fin M → Matrix n n ℂ) :
    (Fin M → ℝ) →ₗ[ℝ] (n → ℂ) where
  toFun x := observerAction ψ h x
  map_add' x y := by
    simp only [observerAction, Pi.add_apply, Complex.ofReal_add, add_smul]
    exact Finset.sum_add_distrib
  map_smul' r x := by
    funext i
    simp only [observerAction, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      RingHom.id_apply, Finset.sum_apply, Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

@[simp] theorem observerActionMap_apply (ψ : n → ℂ) (h : Fin M → Matrix n n ℂ)
    (x : Fin M → ℝ) : observerActionMap ψ h x = observerAction ψ h x := rfl

/-- The centered action of any operator is orthogonal to a unit state. -/
theorem stateFunctional_centered {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (A : Matrix n n ℂ) : stateFunctional ψ (centered ψ A) = 0 := by
  have hsmul : star ψ ⬝ᵥ ((expval ψ A) • ψ) = expval ψ A * (star ψ ⬝ᵥ ψ) := by
    simp [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [stateFunctional_apply, centered, dotProduct_sub, hsmul, hψ, mul_one,
    expval_def, sub_self]

/-- A block-preserving Hamiltonian moves the state inside the block's projective tangent
channel. -/
theorem centered_mem_blockTangentChannel
    {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {B : Submodule ℂ (n → ℂ)} (hψB : ψ ∈ B)
    {A : Matrix n n ℂ} (hA : ∀ v ∈ B, A *ᵥ v ∈ B) :
    centered ψ A ∈ blockTangentChannel ψ B := by
  refine mem_blockTangentChannel.mpr ⟨?_, ?_⟩
  · exact B.sub_mem (hA ψ hψB) (B.smul_mem _ hψB)
  · exact stateFunctional_centered hψ A

/-! ## The fixed-block codimension bound -/

/-- **Fixed observer-block codimension law.**  If every coefficient direction of `U` assembles a
Hamiltonian preserving the fixed block `B ∋ ψ`, then the dimension of `U` plus the observer rank
is at most the coefficient dimension plus twice the nontrivial complex block dimension. -/
theorem finrank_blockPreserving_add_observerRank_le
    {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (h : Fin M → Matrix n n ℂ)
    {B : Submodule ℂ (n → ℂ)} (hψB : ψ ∈ B)
    (U : Submodule ℝ (Fin M → ℝ))
    (hU : ∀ x ∈ U, ∀ v ∈ B, generatorCombination h x *ᵥ v ∈ B) :
    Module.finrank ℝ U +
        Module.finrank ℝ (LinearMap.range (observerActionMap ψ h)) + 2 ≤
      M + 2 * Module.finrank ℂ B := by
  classical
  set K : Submodule ℝ (n → ℂ) := (blockTangentChannel ψ B).restrictScalars ℝ with hK
  have hUK : ∀ x : U, observerActionMap ψ h x.1 ∈ K := by
    intro x
    have hcent : observerAction ψ h x.1 = centered ψ (generatorCombination h x.1) :=
      (centered_generatorCombination ψ h x.1).symm
    have := centered_mem_blockTangentChannel hψ hψB (hU x.1 x.2)
    rw [hK]
    simpa [hcent] using this
  have hbound :=
    observerChannel_subspace_finrank_add_rank_le (observerActionMap ψ h) U K hUK
  have hV : Module.finrank ℝ (Fin M → ℝ) = M := Module.finrank_fin_fun ℝ
  have hKrank : Module.finrank ℝ K + 2 = 2 * Module.finrank ℂ B := by
    rw [hK]
    exact finrank_real_blockTangentChannel_add_two hψ B hψB
  rw [hV] at hbound
  omega

/-! ## The observer rank is the quantum Fisher rank -/

/-- Real and imaginary coordinates of a complex vector, as an injective real-linear map. -/
def realSplit : (n → ℂ) →ₗ[ℝ] (n ⊕ n → ℝ) where
  toFun v := Sum.elim (fun i => (v i).re) (fun i => (v i).im)
  map_add' v w := by funext i; cases i <;> simp
  map_smul' r v := by funext i; cases i <;> simp

omit [Fintype n] in
theorem realSplit_injective : Function.Injective (realSplit (n := n)) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  funext i
  have hl : (v i).re = 0 := congrFun hv (Sum.inl i)
  have hr : (v i).im = 0 := congrFun hv (Sum.inr i)
  exact Complex.ext hl hr

theorem realSplit_comp_observerActionMap (ψ : n → ℂ) (h : Fin M → Matrix n n ℂ) :
    (realSplit (n := n)).comp (observerActionMap ψ h) =
      (centeredRealification ψ h).mulVecLin := by
  refine LinearMap.ext fun x => ?_
  funext i
  cases i with
  | inl i =>
      show (observerAction ψ h x i).re = (centeredRealification ψ h *ᵥ x) (Sum.inl i)
      exact (centeredRealification_mulVec_apply_inl ψ h x i).symm
  | inr i =>
      show (observerAction ψ h x i).im = (centeredRealification ψ h *ᵥ x) (Sum.inr i)
      exact (centeredRealification_mulVec_apply_inr ψ h x i).symm

/-- The real rank of the projective observer action is the rank of the realified centered
action matrix. -/
theorem finrank_range_observerActionMap_eq_centeredRealification_rank
    (ψ : n → ℂ) (h : Fin M → Matrix n n ℂ) :
    Module.finrank ℝ (LinearMap.range (observerActionMap ψ h)) =
      (centeredRealification ψ h).rank := by
  have hcomp := realSplit_comp_observerActionMap ψ h
  have hrange :
      LinearMap.range ((centeredRealification ψ h).mulVecLin) =
        (LinearMap.range (observerActionMap ψ h)).map (realSplit (n := n)) := by
    rw [← hcomp, LinearMap.range_comp]
  have hrank : (centeredRealification ψ h).rank =
      Module.finrank ℝ (LinearMap.range ((centeredRealification ψ h).mulVecLin)) := rfl
  rw [hrank, hrange]
  exact (Submodule.equivMapOfInjective (realSplit (n := n)) realSplit_injective
    (LinearMap.range (observerActionMap ψ h))).finrank_eq

/-- For a Hermitian dictionary and a unit state, the observer rank is the quantum Fisher rank. -/
theorem finrank_range_observerActionMap_eq_qfim_rank
    {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) {h : Fin M → Matrix n n ℂ}
    (hh : ∀ a, (h a)ᴴ = h a) :
    Module.finrank ℝ (LinearMap.range (observerActionMap ψ h)) = (qfim ψ h).rank := by
  rw [finrank_range_observerActionMap_eq_centeredRealification_rank,
    qfim_rank_eq_centeredRealification_rank hψ hh]

/-- **Quantum Fisher form of the fixed-block codimension law.**  A fixed complex block of
dimension `d` containing the input state can carry a block-preserving coefficient subspace of
dimension at most `M - rank(QFI) + 2(d-1)`. -/
theorem finrank_blockPreserving_add_qfim_rank_le
    {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) {h : Fin M → Matrix n n ℂ}
    (hh : ∀ a, (h a)ᴴ = h a)
    {B : Submodule ℂ (n → ℂ)} (hψB : ψ ∈ B)
    (U : Submodule ℝ (Fin M → ℝ))
    (hU : ∀ x ∈ U, ∀ v ∈ B, generatorCombination h x *ᵥ v ∈ B) :
    Module.finrank ℝ U + (qfim ψ h).rank + 2 ≤ M + 2 * Module.finrank ℂ B := by
  have hrank := finrank_range_observerActionMap_eq_qfim_rank hψ hh
  have hbound := finrank_blockPreserving_add_observerRank_le hψ h hψB U hU
  rw [hrank] at hbound
  exact hbound

end

end QuantumAlg
