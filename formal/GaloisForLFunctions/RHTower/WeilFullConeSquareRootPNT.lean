import GaloisForLFunctions.RHTower.WeilFullConeBoundaryMeasure

/-!
# The square-root prime number theorem for every Weil-positive system

Let `lam` be full-cone Weil-positive and let `K = f ⋆ f̃` for a `C²` compactly supported `f`,
supported in `[−R, R]`.  For every `y > R` (think `y = log x`),

`‖e^{y/2} Σ_{n≥2} lam(n) n^{−1/2} K(log n − y) − e^{y} K̂(−i/2)‖ ≤ ‖K̂(i/2)‖ + e^{y/2} (A_f + B_f)`

(`norm_sqrt_pnt_sub_le`), where `A_f = (1/2π)∫ |K̂(r)| |γ(r)| dr` is the archimedean size of `K`
and `B_f = W_lam(f ⋆ f̃) = ∫ |f̂|² dμ_lam` is the Weil energy of `f` for `lam`.  In the variable
`x = e^y` and with `ψ(v) = v^{−1/2} K(log v)`, this reads

`Σ_n lam(n) ψ(n/x) = x ∫ψ + O(√x)`,

the smoothed prime number theorem with error exactly `O(√x)`: no `x^ε` loss, unconditionally, for
every Weil-positive system.  For `lam = Λ` (a producer exactly under RH) the constant `B_f` is the
zero sum `Σ_ρ |f̂(γ_ρ)|²`.

**Proof.**  The explicit formula is the definition of the Weil functional applied to the translated
test `K_y(u) = K(u − y)`:
`W_lam(K_y) = pole(K_y) − Σ_n lam(n) n^{−1/2}(K_y(log n) + K_y(−log n)) + arch(K_y)`.  The pole
part is `e^{−y/2}K̂(i/2) + e^{y/2}K̂(−i/2)`, the negative logarithms leave the support once
`y > R`, translation does not change `|K̂|` on the real line, and
`|W_lam(K_y)| = |charFun ν_f(y)| ≤ ν_f(ℝ) = W_lam(K)` by Bochner (`exists_spectralMeasure`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-- Past the support, the translated test vanishes at every `−log n`. -/
theorem transl_neg_log_eq_zero {K : ℝ → ℂ} {R y : ℝ} (hR : ∀ u, K u ≠ 0 → |u| ≤ R) (hy : R < y)
    (n : ℕ) : transl y K (-Real.log n) = 0 := by
  rw [transl]
  by_contra h
  have := (abs_le.mp (hR _ h)).1
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  linarith

/-- **The explicit formula on a translated test.**  Past the support, the prime sum minus its
main term equals `e^{−y/2}K̂(i/2) + arch(K_y) − W_lam(K_y)`. -/
theorem primeSum_transl_sub_main_eq (lam : ℕ → ℝ) {K : ℝ → ℂ} {R y : ℝ}
    (hR : ∀ u, K u ≠ 0 → |u| ≤ R) (hy : R < y) :
    (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * K (Real.log n - y)) -
        ((Real.exp (y / 2) : ℝ) : ℂ) * paperFT K (-I / 2) =
      ((Real.exp (-(y / 2)) : ℝ) : ℂ) * paperFT K (I / 2) + archPart (transl y K) -
        weilFullFunctional lam (transl y K) := by
  have hprime : primePart lam (transl y K) = ∑' n : ℕ,
      ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * K (Real.log n - y) := by
    rw [primePart]
    refine tsum_congr fun n => ?_
    rw [transl_neg_log_eq_zero hR hy n, add_zero, transl]
  have hpole : polePart (transl y K) = ((Real.exp (-(y / 2)) : ℝ) : ℂ) * paperFT K (I / 2) +
      ((Real.exp (y / 2) : ℝ) : ℂ) * paperFT K (-I / 2) := by
    rw [polePart, paperFT_transl, paperFT_transl]
    congr 2
    · rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
    · rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [← hprime, weilFullFunctional_eq_parts, hpole]
  ring

/-- Translation does not change the archimedean size. -/
theorem norm_archPart_transl_le (K : ℝ → ℂ) (y : ℝ) :
    ‖archPart (transl y K)‖ ≤
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT K r‖ * |EF.gammaBracket r| := by
  rw [archPart, norm_mul]
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [paperFT_transl, norm_mul, norm_mul, norm_cexp_I_mul_ofReal, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

/-- **The square-root prime number theorem for every Weil-positive system.** -/
theorem norm_sqrt_pnt_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ R C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, R < y →
      ‖((Real.exp (y / 2) : ℝ) : ℂ) * (∑' n : ℕ,
          ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * EF.weilTest f f (Real.log n - y))
        - ((Real.exp y : ℝ) : ℂ) * paperFT (EF.weilTest f f) (-I / 2)‖ ≤
        ‖paperFT (EF.weilTest f f) (I / 2)‖ + Real.exp (y / 2) * C := by
  set K := EF.weilTest f f with hKdef
  have hK := admissible_weilTest hf hfc
  obtain ⟨R, hR⟩ := exists_abs_bound_of_hasCompactSupport hK.supp
  obtain ⟨ν, hν, hνK⟩ := exists_spectralMeasure hW hf hfc
  set A : ℝ := (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT K r‖ * |EF.gammaBracket r| with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (by positivity) (integral_nonneg fun r => by positivity)
  refine ⟨R, A + ν.real univ, add_nonneg hA0 measureReal_nonneg, fun y hy => ?_⟩
  set Ky := transl y K with hKy
  have harch : ‖archPart Ky‖ ≤ A := norm_archPart_transl_le K y
  have hW : ‖weilFullFunctional lam Ky‖ ≤ ν.real univ := by
    have := hνK y
    rw [spectralKernel] at this
    rw [hKy, ← this]
    exact norm_charFun_le y
  have hkey : ((Real.exp (y / 2) : ℝ) : ℂ) * (∑' n : ℕ,
        ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * K (Real.log n - y)) -
      ((Real.exp y : ℝ) : ℂ) * paperFT K (-I / 2) =
      paperFT K (I / 2) + ((Real.exp (y / 2) : ℝ) : ℂ) * (archPart Ky - weilFullFunctional lam Ky) := by
    have h1 := primeSum_transl_sub_main_eq lam hR hy
    have he1 : ((Real.exp (y / 2) : ℝ) : ℂ) * ((Real.exp (-(y / 2)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    have he2 : ((Real.exp (y / 2) : ℝ) : ℂ) * ((Real.exp (y / 2) : ℝ) : ℂ) =
        ((Real.exp y : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_halves]
    linear_combination ((Real.exp (y / 2) : ℝ) : ℂ) * h1 + (paperFT K (I / 2)) * he1 +
      (paperFT K (-I / 2)) * he2
  rw [hkey]
  have hey : 0 ≤ Real.exp (y / 2) := (Real.exp_pos _).le
  calc ‖paperFT K (I / 2) + ((Real.exp (y / 2) : ℝ) : ℂ) *
        (archPart Ky - weilFullFunctional lam Ky)‖
      ≤ ‖paperFT K (I / 2)‖ + Real.exp (y / 2) * (‖archPart Ky‖ + ‖weilFullFunctional lam Ky‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hey]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hey
    _ ≤ ‖paperFT K (I / 2)‖ + Real.exp (y / 2) * (A + ν.real univ) := by
        gcongr

end RHTower.WeilSpectral

end
