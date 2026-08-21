import GaloisForLFunctions.HTGeometry.AppellHumbertAutomorphicFactor
import GaloisForLFunctions.HTGeometry.PoincareTermJetGrowth

/-!
# The Poincaré term of a lower-automorphic seed decays with the difference form

For a seed transforming by a *lower* Appell--Humbert factor, the whole lattice dependence of the
Poincaré term `ψ(γ,·)⁻¹·seed(· + γ)` collapses: the translate of the seed is the lower factor times
the seed itself, so the term is `(upper/lower)(γ, z)⁻¹ · seed(z)` and the seed appears only at the
base point.  The ratio is again an Appell--Humbert expression, for the difference form, and its
inverse decays like `exp(−(π/4)·D(γ,γ))` when the difference is positive semidefinite.

This is the exact form of Abe positivity used by the damping estimate: no growth hypothesis on the
seed over the whole lattice is needed, only its size on one fixed ball.

* `IsHermitianForm.sub`;
* `norm_poincareTerm_appellHumbert_le` — **the Poincaré term's Gaussian bound**;
* `norm_multiIndexJetEvalCLM_poincareTerm_appellHumbert_le` — the packet-jet form of the same bound.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

namespace IsHermitianForm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H₁ H₂ : V → V → ℂ}

theorem sub (h₁ : IsHermitianForm H₁) (h₂ : IsHermitianForm H₂) :
    IsHermitianForm fun x y => H₁ x y - H₂ x y where
  add_left := fun x y z => by
    rw [h₁.add_left, h₂.add_left]
    ring
  smul_left := fun a x y => by
    rw [h₁.smul_left, h₂.smul_left]
    ring
  symm := fun x y => by
    rw [h₁.symm, h₂.symm, star_sub]

end IsHermitianForm

section Decay

variable {d : ℕ} {Hu Hl : (Fin d → ℂ) → (Fin d → ℂ) → ℂ}
variable {χu χl : (Fin d → ℂ) → ℂ}

/-- **The Poincaré term of a lower-automorphic seed decays like the difference form.** -/
theorem norm_poincareTerm_appellHumbert_le (hHu : IsHermitianForm Hu) (hHl : IsHermitianForm Hl)
    (hχu : ∀ γ, ‖χu γ‖ = 1) (hχl : ∀ γ, ‖χl γ‖ = 1)
    (hpos : ∀ w : Fin d → ℂ, 0 ≤ (Hu w w - Hl w w).re)
    {C : ℝ} (hC : 0 ≤ C) {z : Fin d → ℂ} (hz : (Hu z z - Hl z z).re ≤ C ^ 2)
    {Γ : AddSubgroup (Fin d → ℂ)}
    (hsemiu : ∀ γ γ' : Fin d → ℂ, χu (γ + γ')
      = χu γ * χu γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hu γ γ').im : ℝ))))
    (seed : MultivariateEntire d)
    (hseed : ∀ (γ : Γ) (x : Fin d → ℂ),
      seed.1 (x + γ.1) = appellHumbertFactor Hl χl γ.1 x * seed.1 x)
    (γ : Γ) :
    ‖poincareTerm (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ z‖
      ≤ Real.exp (Real.pi * C ^ 2)
          * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) * ‖seed.1 z‖ := by
  have hD : IsHermitianForm fun x y => Hu x y - Hl x y := hHu.sub hHl
  have hone : ∀ γ : Fin d → ℂ, ‖(1 : ℂ)‖ = 1 := fun _ => norm_one
  have hval : poincareTerm (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ z
      = (appellHumbertFactor Hu χu γ.1 z)⁻¹ * (appellHumbertFactor Hl χl γ.1 z * seed.1 z) := by
    rw [poincareTerm, hseed γ z]
    rfl
  have hnormu : ‖(appellHumbertFactor Hu χu γ.1 z)⁻¹‖
      = (Real.exp (Real.pi * (Hu z γ.1).re + Real.pi / 2 * (Hu γ.1 γ.1).re))⁻¹ := by
    rw [norm_inv, norm_appellHumbertFactor hHu hχu]
  have hnorml : ‖appellHumbertFactor Hl χl γ.1 z‖
      = Real.exp (Real.pi * (Hl z γ.1).re + Real.pi / 2 * (Hl γ.1 γ.1).re) :=
    norm_appellHumbertFactor hHl hχl _ _
  have hR : ‖(appellHumbertFactor (fun x y => Hu x y - Hl x y) (fun _ => 1) γ.1 z)⁻¹‖
      = Real.exp (-(Real.pi * (Hu z γ.1 - Hl z γ.1).re
          + Real.pi / 2 * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re)) := by
    rw [norm_inv, norm_appellHumbertFactor hD (fun _ => norm_one), ← Real.exp_neg]
  have hratio : ‖(appellHumbertFactor Hu χu γ.1 z)⁻¹‖ * ‖appellHumbertFactor Hl χl γ.1 z‖
      = ‖(appellHumbertFactor (fun x y => Hu x y - Hl x y) (fun _ => 1) γ.1 z)⁻¹‖ := by
    rw [hnormu, hnorml, hR, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    simp only [Complex.sub_re]
    ring
  have hbound : ‖(appellHumbertFactor (fun x y => Hu x y - Hl x y) (fun _ => 1) γ.1 z)⁻¹‖
      ≤ Real.exp (Real.pi * C ^ 2)
        * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) := by
    have h := norm_inv_appellHumbertFactor_le hD hpos (χ := fun _ => 1)
      (fun _ => norm_one) hC hz γ.1
    simpa using h
  rw [hval, norm_mul, norm_mul, ← mul_assoc, hratio]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-- **The packet-jet form of the same bound.**  This is the damping estimate's hypothesis with the
seed entering only through its size on one fixed ball. -/
theorem norm_multiIndexJetEvalCLM_poincareTerm_appellHumbert_le
    (hHu : IsHermitianForm Hu) (hHl : IsHermitianForm Hl)
    (hχu : ∀ γ, ‖χu γ‖ = 1) (hχl : ∀ γ, ‖χl γ‖ = 1)
    (hpos : ∀ w : Fin d → ℂ, 0 ≤ (Hu w w - Hl w w).re)
    {C : ℝ} (hC : 0 ≤ C) {Γ : AddSubgroup (Fin d → ℂ)}
    (hsemiu : ∀ γ γ' : Fin d → ℂ, χu (γ + γ')
      = χu γ * χu γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hu γ γ').im : ℝ))))
    (seed : MultivariateEntire d)
    (hseed : ∀ (γ : Γ) (x : Fin d → ℂ),
      seed.1 (x + γ.1) = appellHumbertFactor Hl χl γ.1 x * seed.1 x)
    (p : Fin d → ℂ) (a : Fin d →₀ ℕ) {ρ Ms : ℝ} (hρ : 0 < ρ)
    (hzsup : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ → (Hu y y - Hl y y).re ≤ C ^ 2)
    (hseedsup : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ → ‖seed.1 y‖ ≤ Ms)
    (γ : Γ) :
    ‖multiIndexJetEvalCLM p a
        (poincareTermEntire (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ)‖
      ≤ (Real.exp (Real.pi * C ^ 2) * Ms / ρ ^ (Fintype.card (MultiIndexSlot a)))
          * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) := by
  set E : ℝ := Real.exp (Real.pi * C ^ 2)
      * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) with hE
  have hEnonneg : 0 ≤ E := by positivity
  have hstep : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ →
        ‖(poincareTermEntire (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ).1 y‖
          ≤ E * Ms := by
    intro y hy
    have h1 : ‖poincareTerm (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ y‖
        ≤ E * ‖seed.1 y‖ :=
      norm_poincareTerm_appellHumbert_le hHu hHl hχu hχl hpos hC (hzsup y hy) hsemiu seed hseed γ
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_left (hseedsup y hy) hEnonneg
  have h := norm_multiIndexJetEvalCLM_le p a
    (poincareTermEntire (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ) hρ hstep
  refine le_trans h (le_of_eq ?_)
  rw [hE]
  field_simp

end Decay

end GaloisForLFunctions.HTGeometry
