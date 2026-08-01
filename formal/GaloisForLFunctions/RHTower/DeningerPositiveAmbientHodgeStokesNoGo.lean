import GaloisForLFunctions.RHTower.DeningerArithmeticPowerBar

/-!
# Positive ambient Hodge--Stokes no-go

Strict cup--Hodge positivity on the whole middle cochain space is incompatible with ordinary
Stokes descent whenever the incoming differential is nonzero and Hodge preserves cocycles.
Route L must therefore construct positivity after harmonic/relative reduction, rather than call
the unchanged positive coefficient pairing a cohomological cup.

This is unconditional chain-level algebra.  It uses no spectral divisor, Xi zero, numerical
computation, or RH premise.
-/

namespace RHTower

/-- Strict ambient cup--Hodge positivity and Stokes descent force every incoming boundary to
vanish whenever Hodge preserves cocycles. -/
theorem deningerPositiveAmbientHodge_stokes_forces_boundary_zero
    {E₀ E₁ E₂ : Type*}
    [AddCommGroup E₀] [AddCommGroup E₁] [AddCommGroup E₂]
    (d₀ : E₀ →+ E₁) (d₁ : E₁ →+ E₂)
    (J : E₁ → E₁) (cup : E₁ → E₁ → ℂ)
    (hcomplex : ∀ a, d₁ (d₀ a) = 0)
    (hJclosed : ∀ x, d₁ x = 0 → d₁ (J x) = 0)
    (hStokes : ∀ a z, d₁ z = 0 → cup (d₀ a) z = 0)
    (hpositive : ∀ {x}, x ≠ 0 → 0 < (cup x (J x)).re) :
    d₀ = 0 := by
  ext a
  by_contra hne
  have hclosed : d₁ (J (d₀ a)) = 0 := hJclosed _ (hcomplex a)
  have hcup : cup (d₀ a) (J (d₀ a)) = 0 := hStokes a _ hclosed
  have hpos := hpositive hne
  rw [hcup] at hpos
  simp at hpos

/-- If a nonzero boundary exists, its Hodge image is a closed witness against Stokes descent. -/
theorem deningerPositiveAmbientHodge_exists_stokes_defect
    {E₀ E₁ E₂ : Type*}
    [AddCommGroup E₀] [AddCommGroup E₁] [AddCommGroup E₂]
    (d₀ : E₀ →+ E₁) (d₁ : E₁ →+ E₂)
    (J : E₁ → E₁) (cup : E₁ → E₁ → ℂ)
    (hcomplex : ∀ a, d₁ (d₀ a) = 0)
    (hJclosed : ∀ x, d₁ x = 0 → d₁ (J x) = 0)
    (hpositive : ∀ {x}, x ≠ 0 → 0 < (cup x (J x)).re)
    {a : E₀} (ha : d₀ a ≠ 0) :
    ∃ b z : E₁,
      b ∈ Set.range d₀ ∧ d₁ z = 0 ∧ cup b z ≠ 0 := by
  refine ⟨d₀ a, J (d₀ a), ⟨a, rfl⟩, hJclosed _ (hcomplex a), ?_⟩
  intro hzero
  have hpos := hpositive ha
  rw [hzero] at hpos
  simp at hpos

end RHTower
