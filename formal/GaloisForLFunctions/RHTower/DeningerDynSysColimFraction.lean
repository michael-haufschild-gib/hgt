import GaloisForLFunctions.RHTower.DeningerDynSysCharacterColimit

/-!
# The `Q^{>0}_0`-action on the colimit of character points

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §3 and §5.

On the colimit `X̌ (C)` every Frobenius operator `F_ν` with `ν ∈ N₀` is a bijection, so a positive
rational `q = ν / ν'` with `ν , ν' ∈ N₀` acts by `F_q = F_ν ∘ F_{ν'}^{-1}`.  This is well defined,
multiplicative, and `F_q` fixes a point exactly when `F_ν` and `F_{ν'}` agree on it — the form in
which Deninger uses the isotropy condition in Theorem 5.2.
-/

namespace RHTower

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C] {N₀ : Submonoid ℕ}

theorem deningerColimFrobenius_comp (ν μ : ℕ) (z : DeningerColimPoints N₀ X C) :
    deningerColimFrobenius N₀ ν (deningerColimFrobenius N₀ μ z)
      = deningerColimFrobenius N₀ (μ * ν) z := by
  obtain ⟨a, P, rfl⟩ := deningerColimMk_surjective z
  rw [deningerColimFrobenius_mk, deningerColimFrobenius_mk, deningerColimFrobenius_mk,
    deningerCharFrobenius_comp]

@[simp] theorem deningerColimFrobenius_one' (z : DeningerColimPoints N₀ X C) :
    deningerColimFrobenius N₀ 1 z = z := by
  obtain ⟨a, P, rfl⟩ := deningerColimMk_surjective z
  rw [deningerColimFrobenius_mk, deningerCharFrobenius_one]

theorem deningerColimFrobenius_commute (ν μ : ℕ) (z : DeningerColimPoints N₀ X C) :
    deningerColimFrobenius N₀ ν (deningerColimFrobenius N₀ μ z)
      = deningerColimFrobenius N₀ μ (deningerColimFrobenius N₀ ν z) := by
  rw [deningerColimFrobenius_comp, deningerColimFrobenius_comp, Nat.mul_comm]

variable (N₀) in
/-- The Frobenius operator as an equivalence of the colimit. -/
noncomputable def deningerColimFrobEquiv (ν : N₀) :
    DeningerColimPoints N₀ X C ≃ DeningerColimPoints N₀ X C :=
  Equiv.ofBijective _ (deningerColimFrobenius_bijective (X := X) (C := C) ν.2)

@[simp] theorem deningerColimFrobEquiv_apply (ν : N₀) (z : DeningerColimPoints N₀ X C) :
    deningerColimFrobEquiv N₀ ν z = deningerColimFrobenius N₀ (ν : ℕ) z := rfl

@[simp] theorem deningerColimFrobEquiv_apply_symm (ν : N₀) (z : DeningerColimPoints N₀ X C) :
    deningerColimFrobenius N₀ (ν : ℕ) ((deningerColimFrobEquiv N₀ ν).symm z) = z :=
  (deningerColimFrobEquiv N₀ ν).apply_symm_apply z

variable (N₀) in
/-- **Deninger, §3.**  The operator `F_{ν/ν'}` attached to a positive rational in `Q^{>0}_0`. -/
noncomputable def deningerColimFrac (ν ν' : N₀) :
    DeningerColimPoints N₀ X C ≃ DeningerColimPoints N₀ X C :=
  (deningerColimFrobEquiv N₀ ν').symm.trans (deningerColimFrobEquiv N₀ ν)

theorem deningerColimFrac_apply (ν ν' : N₀) (z : DeningerColimPoints N₀ X C) :
    deningerColimFrac N₀ ν ν' z
      = deningerColimFrobenius N₀ (ν : ℕ) ((deningerColimFrobEquiv N₀ ν').symm z) := rfl

/-- **Deninger, §3.**  The operator depends only on the rational number `ν / ν'`. -/
theorem deningerColimFrac_congr {ν ν' μ μ' : N₀}
    (h : (ν : ℕ) * (μ' : ℕ) = (μ : ℕ) * (ν' : ℕ)) :
    deningerColimFrac (X := X) (C := C) N₀ ν ν' = deningerColimFrac N₀ μ μ' := by
  refine Equiv.ext fun z => ?_
  refine deningerColimFrobenius_injective (X := X) (C := C) (ν := (ν' : ℕ) * (μ' : ℕ))
    (Submonoid.mul_mem N₀ ν'.2 μ'.2) ?_
  have hL : deningerColimFrobenius N₀ ((ν' : ℕ) * (μ' : ℕ)) (deningerColimFrac N₀ ν ν' z)
      = deningerColimFrobenius N₀ ((ν : ℕ) * (μ' : ℕ)) z := by
    rw [deningerColimFrac_apply, ← deningerColimFrobenius_comp,
      deningerColimFrobenius_commute (ν' : ℕ) (ν : ℕ), deningerColimFrobEquiv_apply_symm,
      deningerColimFrobenius_comp]
  have hR : deningerColimFrobenius N₀ ((ν' : ℕ) * (μ' : ℕ)) (deningerColimFrac N₀ μ μ' z)
      = deningerColimFrobenius N₀ ((μ : ℕ) * (ν' : ℕ)) z := by
    rw [deningerColimFrac_apply, ← deningerColimFrobenius_comp,
      deningerColimFrobenius_commute (μ' : ℕ) (ν' : ℕ),
      deningerColimFrobenius_commute (μ' : ℕ) (μ : ℕ), deningerColimFrobEquiv_apply_symm,
      deningerColimFrobenius_comp]
  rw [hL, hR, h]

/-- **Deninger, Theorem 5.2.**  `F_{ν/ν'}` fixes a point exactly when `F_ν` and `F_{ν'}` agree on
it. -/
theorem deningerColimFrac_eq_self_iff (ν ν' : N₀) (z : DeningerColimPoints N₀ X C) :
    deningerColimFrac N₀ ν ν' z = z
      ↔ deningerColimFrobenius N₀ (ν : ℕ) z = deningerColimFrobenius N₀ (ν' : ℕ) z := by
  constructor
  · intro h
    have h' := congrArg (deningerColimFrobenius N₀ (ν' : ℕ)) h
    rw [deningerColimFrac_apply, deningerColimFrobenius_commute,
      deningerColimFrobEquiv_apply_symm] at h'
    exact h'
  · intro h
    refine deningerColimFrobenius_injective (X := X) (C := C) (ν := (ν' : ℕ)) ν'.2 ?_
    rw [deningerColimFrac_apply, deningerColimFrobenius_commute,
      deningerColimFrobEquiv_apply_symm]
    exact h

/-- **Deninger, §3.**  `F_1 = id`. -/
theorem deningerColimFrac_self (ν : N₀) :
    deningerColimFrac (X := X) (C := C) N₀ ν ν = Equiv.refl _ := by
  refine Equiv.ext fun z => ?_
  refine deningerColimFrobenius_injective (X := X) (C := C) (ν := (ν : ℕ)) ν.2 ?_
  rw [deningerColimFrac_apply, deningerColimFrobenius_commute,
    deningerColimFrobEquiv_apply_symm]
  rfl

/-- **Deninger, §3.**  The fraction operators are multiplicative. -/
theorem deningerColimFrac_trans (ν ν' μ μ' : N₀) :
    (deningerColimFrac (X := X) (C := C) N₀ μ μ').trans (deningerColimFrac N₀ ν ν')
      = deningerColimFrac N₀ (ν * μ) (ν' * μ') := by
  refine Equiv.ext fun z => ?_
  refine deningerColimFrobenius_injective (X := X) (C := C) (ν := (ν' : ℕ) * (μ' : ℕ))
    (Submonoid.mul_mem N₀ ν'.2 μ'.2) ?_
  have hL : deningerColimFrobenius N₀ ((ν' : ℕ) * (μ' : ℕ))
        ((deningerColimFrac N₀ μ μ').trans (deningerColimFrac N₀ ν ν') z)
      = deningerColimFrobenius N₀ ((μ : ℕ) * (ν : ℕ)) z := by
    show deningerColimFrobenius N₀ ((ν' : ℕ) * (μ' : ℕ))
        (deningerColimFrac N₀ ν ν' (deningerColimFrac N₀ μ μ' z)) = _
    rw [deningerColimFrac_apply, deningerColimFrac_apply, ← deningerColimFrobenius_comp,
      deningerColimFrobenius_commute (ν' : ℕ) (ν : ℕ), deningerColimFrobEquiv_apply_symm,
      deningerColimFrobenius_commute (μ' : ℕ) (ν : ℕ),
      deningerColimFrobenius_commute (μ' : ℕ) (μ : ℕ), deningerColimFrobEquiv_apply_symm,
      deningerColimFrobenius_comp]
  have hR : deningerColimFrobenius N₀ ((ν' : ℕ) * (μ' : ℕ))
        (deningerColimFrac N₀ (ν * μ) (ν' * μ') z)
      = deningerColimFrobenius N₀ ((ν : ℕ) * (μ : ℕ)) z := by
    rw [deningerColimFrac_apply]
    show deningerColimFrobenius N₀ ((ν' * μ' : N₀) : ℕ)
        (deningerColimFrobenius N₀ ((ν * μ : N₀) : ℕ)
          ((deningerColimFrobEquiv N₀ (ν' * μ')).symm z))
      = deningerColimFrobenius N₀ ((ν : ℕ) * (μ : ℕ)) z
    rw [deningerColimFrobenius_commute, deningerColimFrobEquiv_apply_symm]
    rfl
  rw [hL, hR, Nat.mul_comm]

end RHTower
