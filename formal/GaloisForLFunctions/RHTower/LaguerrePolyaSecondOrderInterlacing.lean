import GaloisForLFunctions.RHTower.LaguerrePolyaFirstOrderInterlacing

/-!
# Interlacing for the second-order Laguerre operator `1 − b²D²`

Let `ψ` be in the Laguerre–Pólya class, `b` real, and `F = ψ − b² ψ″ = (1 − bD)(1 + bD) ψ`, not
identically zero. If `F` has four distinct real zeros `γ₁ < γ₂ < γ₃ < γ₄`, then `ψ` vanishes in
`[γ₁, γ₄]`:
- `g = ψ + b ψ′` is in the Laguerre–Pólya class and `F = g − b g′`;
- first-order interlacing puts zeros of `g` in `[γ₁, γ₂]` and in `[γ₃, γ₄]`;
- first-order interlacing for `g = ψ − (−b) ψ′` puts a zero of `ψ` between them.

This is the interlacing step of the Poincaré route to the Laguerre–Pólya maximality of Ξ.
-/

open Set

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- **Second-order interlacing.** -/
theorem exists_zero_Icc_of_laguerrePolya_sub_sq_smul_deriv2 {ψ : ℂ → ℂ}
    (hψ : GaloisForLFunctions.HTGeometry.LaguerrePolya ψ) (b : ℝ)
    (hnz : ∃ z₀, ψ z₀ + (b : ℂ) * deriv ψ z₀ - (b : ℂ) * deriv (fun z => ψ z + (b : ℂ) *
      deriv ψ z) z₀ ≠ 0)
    {γ₁ γ₂ γ₃ γ₄ : ℝ} (h12 : γ₁ < γ₂) (h23 : γ₂ < γ₃) (h34 : γ₃ < γ₄)
    (hz : ∀ γ ∈ ({γ₁, γ₂, γ₃, γ₄} : Set ℝ),
      ψ γ + (b : ℂ) * deriv ψ γ - (b : ℂ) * deriv (fun z => ψ z + (b : ℂ) * deriv ψ z) γ = 0) :
    ∃ x ∈ Icc γ₁ γ₄, ψ x = 0 := by
  set g : ℂ → ℂ := fun z => ψ z + (b : ℂ) * deriv ψ z with hg
  have hgLP : GaloisForLFunctions.HTGeometry.LaguerrePolya g := by
    have := laguerrePolya_sub_smul_deriv hψ (-b)
    simpa [hg, sub_eq_add_neg, neg_mul] using this
  have hF : ∀ z, g z - (b : ℂ) * deriv g z =
      ψ z + (b : ℂ) * deriv ψ z - (b : ℂ) * deriv (fun z => ψ z + (b : ℂ) * deriv ψ z) z :=
    fun z => rfl
  have hnzg : ∃ z₀, g z₀ - (b : ℂ) * deriv g z₀ ≠ 0 := by
    obtain ⟨z₀, hz₀⟩ := hnz; exact ⟨z₀, by rw [hF]; exact hz₀⟩
  have hzF : ∀ γ ∈ ({γ₁, γ₂, γ₃, γ₄} : Set ℝ), g γ - (b : ℂ) * deriv g γ = 0 :=
    fun γ hγ => by rw [hF]; exact hz γ hγ
  obtain ⟨q₁, hq₁, hgq₁⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hgLP b hnzg h12
    (hzF γ₁ (by simp)) (hzF γ₂ (by simp))
  obtain ⟨q₂, hq₂, hgq₂⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hgLP b hnzg h34
    (hzF γ₃ (by simp)) (hzF γ₄ (by simp))
  have hq : q₁ < q₂ := by linarith [hq₁.2, hq₂.1]
  -- `g = ψ − (−b) ψ′` is not identically zero, since `F` is not
  have hnzψ : ∃ z₀, ψ z₀ - ((-b : ℝ) : ℂ) * deriv ψ z₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hg0 : g = 0 := by
      funext z; have := hall z; simp only [hg, Pi.zero_apply]; push_cast at this ⊢; linear_combination this
    obtain ⟨z₀, hz₀⟩ := hnzg
    apply hz₀
    rw [hg0]; simp
  have hzg : ∀ q : ℝ, g q = 0 → ψ q - ((-b : ℝ) : ℂ) * deriv ψ q = 0 := by
    intro q hq0; simp only [hg] at hq0; push_cast; linear_combination hq0
  obtain ⟨x, hx, hx0⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hψ (-b) hnzψ hq
    (hzg q₁ hgq₁) (hzg q₂ hgq₂)
  exact ⟨x, ⟨by linarith [hx.1, hq₁.1], by linarith [hx.2, hq₂.2]⟩, hx0⟩

end

end RHTower
