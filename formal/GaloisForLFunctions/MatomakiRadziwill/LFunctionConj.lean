import GaloisForLFunctions.MatomakiRadziwill.LFunctionZeroFree
import GaloisForLFunctions.RHTower.DirichletCompletedLConjugate

/-!
# Dirichlet `L`-functions under complex conjugation

For a nonprincipal character `χ`,

`L(s, χ⁻¹) = conj L(conj s, χ)`        (`LFunction_inv_eq_conj`),

since both sides are entire and agree on `Re s > 1` term by term (`conj χ(n) = χ⁻¹(n)`,
`conj (n^{conj s}) = n^s`).  Consequently `L'/L(s, χ⁻¹) = conj (L'/L(conj s, χ))`
(`logDeriv_LFunction_inv`), and the Vinogradov–Korobov region holds at negative heights as well
(`LFunction_ne_zero_vinogradovKorobov_abs`): heights `γ ≤ -γ₀` are the heights `-γ ≥ γ₀` of `χ⁻¹`.
-/

open Complex LSeries

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {q : ℕ} [NeZero q]

/-- `conj (n^{conj s}) = n^s` for a natural number `n`. -/
theorem conj_natCast_cpow_conj (n : ℕ) (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (starRingEnd ℂ) s) = (n : ℂ) ^ s := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_conj, Complex.conj_natCast]

/-- The `L`-series of `χ` at `conj s`, conjugated, is the `L`-series of `χ⁻¹` at `s`. -/
theorem conj_LSeries_conj (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (starRingEnd ℂ) (LSeries (fun n => χ n) ((starRingEnd ℂ) s)) =
      LSeries (fun n => χ⁻¹ n) s := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, term_of_ne_zero hn, map_div₀, conj_natCast_cpow_conj,
    RHTower.conj_dirichletCharacter_apply]

/-- **Reflection.**  `L(s, χ⁻¹) = conj L(conj s, χ)` for nonprincipal `χ`: both sides are entire
and agree on `Re s > 1`. -/
theorem LFunction_inv_eq_conj (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ s =
      (starRingEnd ℂ) (DirichletCharacter.LFunction χ ((starRingEnd ℂ) s)) := by
  have hχ' : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ DirichletCharacter.LFunction χ ∘ (starRingEnd ℂ) with hg
  have hd1 : Differentiable ℂ (DirichletCharacter.LFunction χ⁻¹) :=
    DirichletCharacter.differentiable_LFunction hχ'
  have hd2 : Differentiable ℂ g := by
    intro z
    have h := (DirichletCharacter.differentiable_LFunction hχ ((starRingEnd ℂ) z)).conj_conj
    rwa [Complex.conj_conj] at h
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {w : ℂ | 1 < w.re} := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have heq : DirichletCharacter.LFunction χ⁻¹ =ᶠ[nhds (2 : ℂ)] g := by
    filter_upwards [hopen.mem_nhds h2] with z hz
    have hz1 : 1 < z.re := hz
    have hz2 : 1 < ((starRingEnd ℂ) z).re := by rw [Complex.conj_re]; exact hz1
    rw [hg, Function.comp_apply, Function.comp_apply,
      DirichletCharacter.LFunction_eq_LSeries _ hz2, DirichletCharacter.LFunction_eq_LSeries _ hz1,
      conj_LSeries_conj]
  have h := (hd1.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hd2.differentiableOn.analyticOnNhd isOpen_univ) heq
  exact congrFun h s

/-- `L(s, χ) = conj L(conj s, χ⁻¹)` for nonprincipal `χ`. -/
theorem LFunction_eq_conj_inv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ s =
      (starRingEnd ℂ) (DirichletCharacter.LFunction χ⁻¹ ((starRingEnd ℂ) s)) := by
  have h := LFunction_inv_eq_conj χ⁻¹ (inv_ne_one.mpr hχ) s
  rwa [inv_inv] at h

/-- `L'/L(s, χ) = conj (L'/L(conj s, χ⁻¹))` for nonprincipal `χ`. -/
theorem logDeriv_LFunction_eq_conj_inv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.LFunction χ) s =
      (starRingEnd ℂ) (logDeriv (DirichletCharacter.LFunction χ⁻¹) ((starRingEnd ℂ) s)) := by
  have hfun : DirichletCharacter.LFunction χ =
      (starRingEnd ℂ) ∘ DirichletCharacter.LFunction χ⁻¹ ∘ (starRingEnd ℂ) :=
    funext fun w => LFunction_eq_conj_inv χ hχ w
  rw [logDeriv_apply, logDeriv_apply, hfun, deriv_conj_conj, map_div₀]
  simp only [Function.comp_apply]

/-- The point `σ + iγ` is the conjugate of `σ + i(-γ)`. -/
theorem conj_line (σ γ : ℝ) :
    (starRingEnd ℂ) ((σ : ℂ) + (γ : ℂ) * I) = (σ : ℂ) + ((-γ : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- **The Vinogradov–Korobov region at both signs of the height.** -/
theorem LFunction_ne_zero_vinogradovKorobov_abs (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ γ₀ : ℝ, ∀ β γ : ℝ, γ₀ ≤ |γ| →
      1 - Real.log |γ| ^ (-(2 : ℝ) / 3) * Real.log (Real.log |γ|) ^ (-(5 : ℝ) / 3) / 10 ^ 8 < β →
      DirichletCharacter.LFunction χ ((β : ℂ) + (γ : ℂ) * I) ≠ 0 := by
  obtain ⟨γ₁, h₁⟩ := LFunction_ne_zero_vinogradovKorobov χ hχ
  obtain ⟨γ₂, h₂⟩ := LFunction_ne_zero_vinogradovKorobov χ⁻¹ (inv_ne_one.mpr hχ)
  refine ⟨max (max γ₁ γ₂) 1, fun β γ hγ hβ => ?_⟩
  have hγ1 : γ₁ ≤ |γ| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hγ
  have hγ2 : γ₂ ≤ |γ| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hγ
  rcases le_or_gt 0 γ with h0 | h0
  · rw [abs_of_nonneg h0] at hγ1 hβ
    exact h₁ β γ hγ1 hβ
  · rw [abs_of_neg h0] at hγ2 hβ
    rw [LFunction_eq_conj_inv χ hχ, conj_line, map_ne_zero]
    exact h₂ β (-γ) hγ2 hβ

end

end GaloisForLFunctions.MatomakiRadziwill
