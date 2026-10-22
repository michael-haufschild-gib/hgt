import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterColimit
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterTopology

/-!
# The inductive limit topology on `X̌ (C)`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §7 and
Proposition 7.4(b) (`t10`).

The colimit `X̌ (C) = colim_{N₀} X̂ (C)` carries the finest topology for which all the maps
`X̂ (C) → X̌ (C)`, `P ↦ F_ν⁻¹ P`, are continuous; equivalently a subset is open exactly when each
of its preimages under those maps is open.  That is the supremum, in the lattice of topologies, of
the coinduced ones.

For this topology the Frobenius operators are homeomorphisms of `X̌ (C)`: the inverse of `F_ν`
sends the class of `(μ, P)` to the class of `(μν, P)`, and both `F_ν` and this inverse are
compatible with the structural maps from `X̂ (C)`.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C] [TopologicalSpace C] {N₀ : Submonoid ℕ}

variable (N₀) in
/-- **Deninger, §7.**  The inductive limit topology on `X̌ (C)`. -/
noncomputable instance deningerColimTopology :
    TopologicalSpace (DeningerColimPoints N₀ X C) :=
  ⨆ ν : N₀, TopologicalSpace.coinduced (deningerColimMk (X := X) (C := C) N₀ ν) inferInstance

theorem deningerColim_isOpen_iff (s : Set (DeningerColimPoints N₀ X C)) :
    IsOpen s ↔ ∀ ν : N₀, IsOpen (deningerColimMk (X := X) (C := C) N₀ ν ⁻¹' s) := by
  constructor
  · intro hs ν
    exact isOpen_coinduced.1 (isOpen_iSup_iff.1 hs ν)
  · intro h
    exact isOpen_iSup_iff.2 fun ν => isOpen_coinduced.2 (h ν)

theorem deningerColimMk_continuous (ν : N₀) :
    Continuous (deningerColimMk (X := X) (C := C) N₀ ν) := by
  rw [continuous_def]
  intro s hs
  exact (deningerColim_isOpen_iff s).1 hs ν

/-- The inverse of the Frobenius operator on the colimit: it shifts the index. -/
noncomputable def deningerColimFrobeniusInv (ν : N₀) (z : DeningerColimPoints N₀ X C) :
    DeningerColimPoints N₀ X C := by
  refine Quotient.liftOn z (fun P => deningerColimMk N₀ (P.1 * ν) P.2) ?_
  rintro ⟨μ, P⟩ ⟨μ', Q⟩ ⟨a, b, h1, h2⟩
  refine deningerColimMk_eq_iff.2 ⟨a, b, ?_, h2⟩
  push_cast
  calc (μ : ℕ) * (ν : ℕ) * (a : ℕ) = ((μ : ℕ) * (a : ℕ)) * (ν : ℕ) := by ring
    _ = ((μ' : ℕ) * (b : ℕ)) * (ν : ℕ) := by rw [h1]
    _ = (μ' : ℕ) * (ν : ℕ) * (b : ℕ) := by ring

omit [TopologicalSpace C] in
@[simp] theorem deningerColimFrobeniusInv_mk (ν μ : N₀) (P : DeningerCharPoints X C) :
    deningerColimFrobeniusInv ν (deningerColimMk N₀ μ P) = deningerColimMk N₀ (μ * ν) P := rfl

omit [TopologicalSpace C] in
theorem deningerColimFrobenius_inv_left (ν : N₀) (z : DeningerColimPoints N₀ X C) :
    deningerColimFrobeniusInv ν (deningerColimFrobenius (X := X) (C := C) N₀ (ν : ℕ) z) = z := by
  obtain ⟨μ, P, rfl⟩ := deningerColimMk_surjective z
  rw [deningerColimFrobenius_mk, deningerColimFrobeniusInv_mk]
  refine deningerColimMk_eq_iff.2 ⟨1, ν, ?_, ?_⟩
  · simp
  · simp

omit [TopologicalSpace C] in
theorem deningerColimFrobenius_inv_right (ν : N₀) (z : DeningerColimPoints N₀ X C) :
    deningerColimFrobenius (X := X) (C := C) N₀ (ν : ℕ) (deningerColimFrobeniusInv ν z) = z := by
  obtain ⟨μ, P, rfl⟩ := deningerColimMk_surjective z
  rw [deningerColimFrobeniusInv_mk, deningerColimFrobenius_mk]
  refine deningerColimMk_eq_iff.2 ⟨1, ν, ?_, ?_⟩
  · simp
  · simp

variable [ContinuousMul C]

theorem deningerColimFrobenius_continuous {ν : ℕ} (hν : 0 < ν) :
    Continuous (deningerColimFrobenius (X := X) (C := C) N₀ ν) := by
  rw [continuous_iSup_dom]
  intro μ
  rw [continuous_coinduced_dom]
  have hcomp : (deningerColimFrobenius (X := X) (C := C) N₀ ν) ∘ (deningerColimMk N₀ μ)
      = (deningerColimMk N₀ μ) ∘ (deningerCharFrobenius (X := X) (C := C) ν) := rfl
  rw [hcomp]
  exact (deningerColimMk_continuous μ).comp (deningerCharFrobenius_continuous hν)

omit [ContinuousMul C] in
theorem deningerColimFrobeniusInv_continuous (ν : N₀) :
    Continuous (deningerColimFrobeniusInv (X := X) (C := C) (N₀ := N₀) ν) := by
  rw [continuous_iSup_dom]
  intro μ
  rw [continuous_coinduced_dom]
  have hcomp : (deningerColimFrobeniusInv (X := X) (C := C) (N₀ := N₀) ν) ∘
      (deningerColimMk N₀ μ) = deningerColimMk N₀ (μ * ν) := rfl
  rw [hcomp]
  exact deningerColimMk_continuous _

/-- **Deninger, Proposition 7.4(b) (`t10`).**  The Frobenius operators are homeomorphisms of
`X̌ (C)`. -/
noncomputable def deningerColimFrobeniusHomeomorph (ν : N₀) (hν : 0 < (ν : ℕ)) :
    DeningerColimPoints N₀ X C ≃ₜ DeningerColimPoints N₀ X C where
  toFun := deningerColimFrobenius N₀ (ν : ℕ)
  invFun := deningerColimFrobeniusInv ν
  left_inv := deningerColimFrobenius_inv_left ν
  right_inv := deningerColimFrobenius_inv_right ν
  continuous_toFun := deningerColimFrobenius_continuous hν
  continuous_invFun := deningerColimFrobeniusInv_continuous ν

end RHTower
