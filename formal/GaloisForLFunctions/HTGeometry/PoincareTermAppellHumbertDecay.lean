import GaloisForLFunctions.HTGeometry.AppellHumbertAutomorphicFactor
import GaloisForLFunctions.HTGeometry.PoincareTermJetGrowth

/-!
# The Poincaré term of a seed of bounded normalised modulus

A seed for the complement Poincaré series is automorphic only for the *smaller* period group, so its
value at a complement translate `x + γ` is genuinely a new value and cannot be pulled back to the
base point.  What is invariant is the **normalised modulus** `|θ(y)|·exp(−(π/2)·Re H_l(y,y))`, which
is periodic for the lower period group; a seed of bounded normalised modulus therefore satisfies
`‖seed y‖ ≤ M·exp((π/2)·Re H_l(y,y))` globally.

With that bound the complement translate contributes `exp((π/2)·Re H_l(x+γ, x+γ))`, and expanding
the square cancels the lower form against the upper one:  the exponent is
`(π/2)·Re H_l(x,x) − π·Re D(x,γ) − (π/2)·D(γ,γ)` with `D = H_u − H_l`.  That is exactly the
exponent of the inverse Appell--Humbert factor of `D`, so Abe positivity gives the Gaussian decay.

* `re_hermitian_add_self`;
* `norm_poincareTerm_appellHumbert_le` — **the Poincaré term's Gaussian bound**;
* `norm_multiIndexJetEvalCLM_poincareTerm_appellHumbert_le` — its packet-jet form.
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

theorem re_add_self (h : IsHermitianForm H₁) (x y : V) :
    (H₁ (x + y) (x + y)).re = (H₁ x x).re + 2 * (H₁ x y).re + (H₁ y y).re := by
  rw [h.add_left, h.add_right, h.add_right]
  simp only [Complex.add_re]
  have := h.re_symm x y
  linarith

end IsHermitianForm

section Decay

variable {d : ℕ} {Hu Hl : (Fin d → ℂ) → (Fin d → ℂ) → ℂ}
variable {χu : (Fin d → ℂ) → ℂ}

/-- **The Poincaré term of a seed of bounded normalised modulus decays like the difference
form.** -/
theorem norm_poincareTerm_appellHumbert_le (hHu : IsHermitianForm Hu) (hHl : IsHermitianForm Hl)
    (hχu : ∀ γ, ‖χu γ‖ = 1)
    (hpos : ∀ w : Fin d → ℂ, 0 ≤ (Hu w w - Hl w w).re)
    {C : ℝ} (hC : 0 ≤ C) {z : Fin d → ℂ} (hz : (Hu z z - Hl z z).re ≤ C ^ 2)
    {Γ : AddSubgroup (Fin d → ℂ)}
    (hsemiu : ∀ γ γ' : Fin d → ℂ, χu (γ + γ')
      = χu γ * χu γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hu γ γ').im : ℝ))))
    (seed : MultivariateEntire d) {M : ℝ}
    (hseednorm : ∀ y : Fin d → ℂ, ‖seed.1 y‖ ≤ M * Real.exp (Real.pi / 2 * (Hl y y).re))
    (γ : Γ) :
    ‖poincareTerm (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ z‖
      ≤ M * Real.exp (Real.pi / 2 * (Hl z z).re) * Real.exp (Real.pi * C ^ 2)
          * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) := by
  have hD : IsHermitianForm fun x y => Hu x y - Hl x y := hHu.sub hHl
  have hM : 0 ≤ M := by
    have h := hseednorm z
    have h0 : (0 : ℝ) ≤ ‖seed.1 z‖ := norm_nonneg _
    nlinarith [Real.exp_pos (Real.pi / 2 * (Hl z z).re), h, h0]
  set A : ℝ := -(Real.pi * (Hu z γ.1).re + Real.pi / 2 * (Hu γ.1 γ.1).re) with hAdef
  set B : ℝ := Real.pi / 2 * ((Hl z z).re + 2 * (Hl z γ.1).re + (Hl γ.1 γ.1).re) with hBdef
  set P : ℝ := Real.pi / 2 * (Hl z z).re with hPdef
  set Q : ℝ := -(Real.pi * (Hu z γ.1 - Hl z γ.1).re
      + Real.pi / 2 * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) with hQdef
  have hval : poincareTerm (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ z
      = (appellHumbertFactor Hu χu γ.1 z)⁻¹ * seed.1 (z + γ.1) := rfl
  have hnormu : ‖(appellHumbertFactor Hu χu γ.1 z)⁻¹‖ = Real.exp A := by
    rw [norm_inv, norm_appellHumbertFactor hHu hχu, ← Real.exp_neg, hAdef]
  have hseedz : ‖seed.1 (z + γ.1)‖ ≤ M * Real.exp B := by
    have h := hseednorm (z + γ.1)
    rwa [hHl.re_add_self z γ.1] at h
  have hstep : ‖poincareTerm (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ z‖
      ≤ Real.exp A * (M * Real.exp B) := by
    rw [hval, norm_mul, hnormu]
    exact mul_le_mul_of_nonneg_left hseedz (Real.exp_nonneg _)
  have hexpsum : A + B = P + Q := by
    rw [hAdef, hBdef, hPdef, hQdef]
    simp only [Complex.sub_re]
    ring
  have hsplit : Real.exp A * (M * Real.exp B) = M * Real.exp P * Real.exp Q := by
    rw [show Real.exp A * (M * Real.exp B) = M * (Real.exp A * Real.exp B) from by ring,
      ← Real.exp_add, hexpsum, Real.exp_add]
    ring
  have hR : ‖(appellHumbertFactor (fun x y => Hu x y - Hl x y) (fun _ => 1) γ.1 z)⁻¹‖
      = Real.exp Q := by
    rw [norm_inv, norm_appellHumbertFactor hD (fun _ => norm_one), ← Real.exp_neg, hQdef]
  have hbound : Real.exp Q ≤ Real.exp (Real.pi * C ^ 2)
      * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) := by
    rw [← hR]
    have h := norm_inv_appellHumbertFactor_le hD hpos (χ := fun _ => 1)
      (fun _ => norm_one) hC hz γ.1
    simpa using h
  have hnn : (0 : ℝ) ≤ M * Real.exp P := by positivity
  rw [hsplit] at hstep
  refine le_trans hstep ?_
  calc M * Real.exp P * Real.exp Q
      ≤ M * Real.exp P * (Real.exp (Real.pi * C ^ 2)
          * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re)) :=
        mul_le_mul_of_nonneg_left hbound hnn
    _ = M * Real.exp P * Real.exp (Real.pi * C ^ 2)
          * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) := by ring

/-- **The packet-jet form of the same bound.** -/
theorem norm_multiIndexJetEvalCLM_poincareTerm_appellHumbert_le
    (hHu : IsHermitianForm Hu) (hHl : IsHermitianForm Hl) (hχu : ∀ γ, ‖χu γ‖ = 1)
    (hpos : ∀ w : Fin d → ℂ, 0 ≤ (Hu w w - Hl w w).re)
    {C : ℝ} (hC : 0 ≤ C) {Γ : AddSubgroup (Fin d → ℂ)}
    (hsemiu : ∀ γ γ' : Fin d → ℂ, χu (γ + γ')
      = χu γ * χu γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hu γ γ').im : ℝ))))
    (seed : MultivariateEntire d) {M : ℝ}
    (hseednorm : ∀ y : Fin d → ℂ, ‖seed.1 y‖ ≤ M * Real.exp (Real.pi / 2 * (Hl y y).re))
    (p : Fin d → ℂ) (a : Fin d →₀ ℕ) {ρ L : ℝ} (hρ : 0 < ρ)
    (hzsup : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ → (Hu y y - Hl y y).re ≤ C ^ 2)
    (hLsup : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ → (Hl y y).re ≤ L)
    (γ : Γ) :
    ‖multiIndexJetEvalCLM p a
        (poincareTermEntire (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ)‖
      ≤ (M * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C ^ 2)
            / ρ ^ (Fintype.card (MultiIndexSlot a)))
          * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) := by
  have hM : 0 ≤ M := by
    have h := hseednorm p
    have h0 : (0 : ℝ) ≤ ‖seed.1 p‖ := norm_nonneg _
    nlinarith [Real.exp_pos (Real.pi / 2 * (Hl p p).re), h, h0]
  set ψ := appellHumbertAutomorphicFactor hHu hχu hsemiu Γ with hψ
  set E : ℝ := Real.exp (Real.pi * C ^ 2)
      * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) with hE
  have hEnn : 0 ≤ E := by positivity
  have hstep : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ →
        ‖(poincareTermEntire ψ seed γ).1 y‖ ≤ M * Real.exp (Real.pi / 2 * L) * E := by
    intro y hy
    have h1 := norm_poincareTerm_appellHumbert_le hHu hHl hχu hpos hC (hzsup y hy) hsemiu
      seed hseednorm γ
    have hmono : Real.exp (Real.pi / 2 * (Hl y y).re) ≤ Real.exp (Real.pi / 2 * L) := by
      refine Real.exp_le_exp.mpr ?_
      have hL := hLsup y hy
      nlinarith [Real.pi_pos]
    have hle : M * Real.exp (Real.pi / 2 * (Hl y y).re) * E
        ≤ M * Real.exp (Real.pi / 2 * L) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hM) hEnn
    calc ‖(poincareTermEntire ψ seed γ).1 y‖
        ≤ M * Real.exp (Real.pi / 2 * (Hl y y).re) * Real.exp (Real.pi * C ^ 2)
            * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) := h1
      _ = M * Real.exp (Real.pi / 2 * (Hl y y).re) * E := by rw [hE]; ring
      _ ≤ M * Real.exp (Real.pi / 2 * L) * E := hle
  have h := norm_multiIndexJetEvalCLM_le p a (poincareTermEntire ψ seed γ) hρ hstep
  refine le_trans h (le_of_eq ?_)
  rw [hE]
  field_simp

end Decay

end GaloisForLFunctions.HTGeometry
