import GaloisForLFunctions.RHTower.ThmEUniformArchimedean
import Zeta23.Chebyshev

/-!
# End effects of the prime-side Gram matrix, uniformly in the modulus

Alpöge–Furman's end-effect lemma for a general density `ν` (`Zeta23.PrimeSide.lem_ends_nu`) needs only
`|ν(τ)| ≤ B + log⁺(|τ|/4T)` with `B ≥ l`.  For `ν = μ_q + P_c`:

* `|P_c(τ)| ≤ √X` for every coefficient sequence with `|c(n)| ≤ 1` (`abs_PXc_le_uniform`);
* `|μ_q(τ)| ≤ (C₀ + log q) l + log⁺(|τ|/4T)` by the shift `μ_q = μ_1 + (log q)/2π`.

Hence (`prop_ends_uniform`)

`|tr G̃² − 𝓜[ν, ν]| ≤ C (1 + log q)² · L l log l · (l² + X)`

with `C` and the threshold for `T` independent of `q` and of the coefficients.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

/-- `|P_c(τ)| ≤ √X` uniformly in the coefficients. -/
theorem abs_PXc_le_uniform :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ 1) → ∀ X : ℝ, x₀ ≤ X → ∀ τ : ℝ,
      |PXc c X τ| ≤ Real.sqrt X := by
  obtain ⟨x₀, hx₀⟩ := Cheb.chebyshevMertens.cheb1b
  refine ⟨max x₀ 1, le_max_right _ _, fun c hc X hX τ => ?_⟩
  have hXx : x₀ ≤ X := (le_max_left _ _).trans hX
  have hπ3 : (3:ℝ) < π := Real.pi_gt_three
  unfold PXc
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
  have hsum : |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re|
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n / Real.sqrt n := by
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
    rw [norm_mul, norm_mul]
    have h1 : ‖((Λ n : ℝ) : ℂ)‖ = Λ n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h2 : ‖(n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)‖ = 1 / Real.sqrt n := by
      rw [Complex.norm_natCast_cpow_of_pos hn0]
      have hre : (-(1 / 2 : ℂ) - Complex.I * τ).re = -(1/2 : ℝ) := by simp
      rw [hre, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
    rw [h1, h2]
    calc Λ n * ‖c n‖ * (1 / Real.sqrt n) ≤ Λ n * 1 * (1 / Real.sqrt n) := by
          gcongr
          exact hc n
      _ = Λ n / Real.sqrt n := by ring
  calc 1 / π * |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re|
      ≤ 1 / π * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n / Real.sqrt n :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 1 / π * (3 * Real.sqrt X) := mul_le_mul_of_nonneg_left (hx₀ X hXx) (by positivity)
    _ ≤ Real.sqrt X := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith [Real.sqrt_nonneg X]

/-- The archimedean density of every modulus satisfies the `NuBound` shape with `C₀ + log q`. -/
theorem muq_nuBound_uniform :
    ∃ C₀ T₀ : ℝ, 1 ≤ C₀ ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ p : Setting, T₀ ≤ p.T → ∀ τ : ℝ,
      |muq κ q τ| ≤ (C₀ + Real.log q) * Zeta23.l p.T + max (Real.log (|τ| / (4 * p.T))) 0 := by
  obtain ⟨A, S, hA, hAb⟩ := muq_nuBound (κ := 0) (q := 1)
    (GammaChi.gammaFactsChi (by norm_num) le_rfl) le_rfl
  obtain ⟨B, R, hB, hBb⟩ := muq_nuBound (κ := 1) (q := 1) (GammaChi.gammaFactsChi le_rfl le_rfl)
    le_rfl
  refine ⟨A + B, max (max S R) (2 * π * Real.exp 1), by linarith,
    fun κ q hκ hq p hT τ => ?_⟩
  have hTe : 2 * π * Real.exp 1 ≤ p.T := (le_max_right _ _).trans hT
  have hl1 : 1 ≤ Zeta23.l p.T := by
    rw [Zeta23.l, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have h1 : |muq κ 1 τ| ≤ (A + B) * Zeta23.l p.T + max (Real.log (|τ| / (4 * p.T))) 0 := by
    have hl0 : 0 ≤ Zeta23.l p.T := by linarith
    interval_cases κ
    · have := hAb p ((le_max_left _ _).trans ((le_max_left _ _).trans hT)) τ
      nlinarith
    · have := hBb p ((le_max_right _ _).trans ((le_max_left _ _).trans hT)) τ
      nlinarith
  rw [muq_eq_muq_one_add κ q hq]
  have hc2 : 0 ≤ Real.log q / (2 * π) := div_nonneg hlq (by positivity)
  have hc3 : Real.log q / (2 * π) ≤ Real.log q * Zeta23.l p.T := by
    calc Real.log q / (2 * π) ≤ Real.log q := div_le_self hlq (by nlinarith [Real.pi_gt_three])
      _ ≤ Real.log q * Zeta23.l p.T := le_mul_of_one_le_right hlq hl1
  calc |muq κ 1 τ + Real.log q / (2 * π)| ≤ |muq κ 1 τ| + |Real.log q / (2 * π)| := abs_add_le _ _
    _ ≤ (A + B + Real.log q) * Zeta23.l p.T + max (Real.log (|τ| / (4 * p.T))) 0 := by
        rw [abs_of_nonneg hc2]; nlinarith

variable (cϱ : ℝ) in
/-- **[lem:ends] for `L(s, χ)`, uniformly in the modulus and the coefficients.** -/
theorem prop_ends_uniform {lam : ℝ} (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ c : ℕ → ℂ, CoeffOK q c →
      ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCore cϱ p F →
        |trGt2ChiA κ q c p F - MtotalChiA κ q c p F|
          ≤ C * (1 + Real.log q) ^ 2
            * (p.L * Zeta23.l p.T * Real.log (Zeta23.l p.T) * (Zeta23.l p.T ^ 2 + p.X)) := by
  obtain ⟨Cends, T₀e, hends⟩ := Zeta23.PrimeSide.lem_ends_nu (cϱ := cϱ) (lam := lam)
  obtain ⟨C₀, T₀μ, hC₀1, hμB⟩ := muq_nuBound_uniform
  obtain ⟨x₀, hx₀1, hPb⟩ := abs_PXc_le_uniform
  refine ⟨|Cends| * (2 * (C₀ + 1) ^ 2 + 2), max T₀e (max T₀μ (2 * π * Real.exp (|x₀| / lam))),
    by positivity, fun κ q hκ hq c hc p F hplam hT hF => ?_⟩
  have hTe : T₀e ≤ p.T := (le_max_left _ _).trans hT
  have hTμ : T₀μ ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hplam]; exact hTx)
  have hl1 : (1:ℝ) ≤ Zeta23.l p.T := hF.one_le_l
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hΓ := GammaChi.gammaFactsChi hκ hq
  set D : ℝ := C₀ + Real.log q with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  set B : ℝ := D * Zeta23.l p.T + Real.sqrt p.X with hB
  have hcont : Continuous (nuXc κ q c p.X) := by
    have h1 : (nuXc κ q c p.X) = fun τ => muq κ q τ + PXc c p.X τ := rfl
    rw [h1]
    exact (hΓ.smooth.continuous).add (PXc_continuous c p.X_pos)
  have hnu : Zeta23.PrimeSide.NuBound p B (nuXc κ q c p.X) := by
    intro τ
    have h1 : |nuXc κ q c p.X τ| ≤ |muq κ q τ| + |PXc c p.X τ| := abs_add_le _ _
    have h2 := hμB κ q hκ hq p hTμ τ
    have h3 := hPb c hc.norm_le p.X hX τ
    rw [hB]
    linarith
  have hlB : Zeta23.l p.T ≤ B := by
    rw [hB]
    nlinarith [Real.sqrt_nonneg p.X]
  have hmain := hends p F B (nuXc κ q c p.X) hplam hTe hF hcont hnu hlB
  have heq : trGt2ChiA κ q c p F - MtotalChiA κ q c p F
      = (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d,
          Zeta23.PrimeSide.GentryNu (nuXc κ q c p.X) p F k l ^ 2
        - Zeta23.PrimeSide.MtotalNu (nuXc κ q c p.X) p F := rfl
  rw [heq]
  refine hmain.trans ?_
  have hB2 : B ^ 2 ≤ (2 * D ^ 2 + 2) * (Zeta23.l p.T ^ 2 + p.X) := by
    have hsq : Real.sqrt p.X ^ 2 = p.X := Real.sq_sqrt (le_of_lt p.X_pos)
    rw [hB]
    nlinarith [sq_nonneg (D * Zeta23.l p.T - Real.sqrt p.X), sq_nonneg (Zeta23.l p.T),
      sq_nonneg (Real.sqrt p.X), mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ D)
        (by linarith : (0:ℝ) ≤ D)) (sq_nonneg (Zeta23.l p.T))]
  have hDle : 2 * D ^ 2 + 2 ≤ (2 * (C₀ + 1) ^ 2 + 2) * (1 + Real.log q) ^ 2 := by
    have h1 : D ≤ (C₀ + 1) * (1 + Real.log q) := by rw [hD]; nlinarith
    have h2 : D ^ 2 ≤ ((C₀ + 1) * (1 + Real.log q)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : (1 : ℝ) ≤ (1 + Real.log q) ^ 2 := by nlinarith
    nlinarith
  have hlog0 : 0 ≤ Real.log (Zeta23.l p.T) := Real.log_nonneg hl1
  have hL := hF.L_pos
  have hP0 : 0 ≤ p.L * Zeta23.l p.T * Real.log (Zeta23.l p.T) := by positivity
  have hQ0 : 0 ≤ Zeta23.l p.T ^ 2 + p.X := by have := p.X_pos; positivity
  calc Cends * (p.L * p.l * Real.log p.l * B ^ 2)
      ≤ |Cends| * (p.L * p.l * Real.log p.l * B ^ 2) := by
        apply mul_le_mul_of_nonneg_right (le_abs_self _)
        positivity
    _ ≤ |Cends| * (p.L * p.l * Real.log p.l
          * ((2 * (C₀ + 1) ^ 2 + 2) * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 + p.X))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hP0) (abs_nonneg _)
        exact hB2.trans (mul_le_mul_of_nonneg_right hDle hQ0)
    _ = |Cends| * (2 * (C₀ + 1) ^ 2 + 2) * (1 + Real.log q) ^ 2
        * (p.L * Zeta23.l p.T * Real.log (Zeta23.l p.T) * (Zeta23.l p.T ^ 2 + p.X)) := by
        ring

end RHTower
