/-
The per-frequency oscillatory integral of the reflected block, bounded uniformly in the frequency.

For the phase `g_n(x) = 2πn·x − τ·log x` and weight `x^{−σ−2} = exp((−σ−2)·log x)` — the shape each
Fourier mode of the Euler–Maclaurin `B₂` kernel contributes against `x^{−s−2}` (`s = σ + iτ`, `τ < 0`) —
the second-derivative van der Corput test gives `‖∫_1^N w·exp(i·g_n)‖ ≤ 10·N/√(−τ)`, a bound
independent of `n` because `g_n'' = τ/x²` does not involve `n`.  This `n`-uniformity is what lets the
`Σ 1/n²` Fourier coefficients close the mode sum. -/
import GaloisForLFunctions.RHTower.VanDerCorputWeightedSecondGeneral

open Complex intervalIntegral MeasureTheory Real
open scoped Interval

noncomputable section

namespace RHTower

theorem reflected_per_mode_bound {N : ℕ} (hN : 1 ≤ N) {σ τ : ℝ} (hσ : -2 ≤ σ) (hτ : τ < 0) (n : ℤ) :
    ‖∫ x in (1 : ℝ)..(N : ℝ),
        (Real.exp ((-σ - 2) * Real.log x) : ℂ)
          * Complex.exp (((2 * π * (n : ℝ)) * x - τ * Real.log x : ℝ) * I)‖
      ≤ 10 * (N : ℝ) / Real.sqrt (-τ) := by
  set w : ℝ → ℝ := fun x => Real.exp ((-σ - 2) * Real.log x) with hw_def
  set w' : ℝ → ℝ := fun x => Real.exp ((-σ - 2) * Real.log x) * ((-σ - 2) * x⁻¹) with hw'_def
  set g : ℝ → ℝ := fun x => (2 * π * (n : ℝ)) * x - τ * Real.log x with hg_def
  set g' : ℝ → ℝ := fun x => (2 * π * (n : ℝ)) - τ * x⁻¹ with hg'_def
  set g'' : ℝ → ℝ := fun x => τ * (x ^ 2)⁻¹ with hg''_def
  set lam : ℝ := -τ / (N : ℝ) ^ 2 with hlam_def
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlampos : 0 < lam := by rw [hlam_def]; exact div_pos (by linarith) (by positivity)
  have hxpos : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ), 0 < x := by
    intro x hx; rw [Set.uIcc_of_le hN1] at hx; linarith [hx.1]
  have hxne : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ), x ≠ 0 := fun x hx => (hxpos x hx).ne'
  -- derivative facts
  have hwD : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ), HasDerivAt w (w' x) x := by
    intro x hx
    have := ((Real.hasDerivAt_log (hxne x hx)).const_mul (-σ - 2)).exp
    simpa [hw_def, hw'_def, mul_comm] using this
  have hgD : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ), HasDerivAt g (g' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (2 * π * (n : ℝ)) * y) (2 * π * (n : ℝ)) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * π * (n : ℝ))
    have h2 : HasDerivAt (fun y : ℝ => τ * Real.log y) (τ * x⁻¹) x :=
      (Real.hasDerivAt_log (hxne x hx)).const_mul τ
    simpa [hg_def, hg'_def] using h1.sub h2
  have hg'D : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ), HasDerivAt g' (g'' x) x := by
    intro x hx
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv (hxne x hx)
    have h2 : HasDerivAt (fun y : ℝ => τ * y⁻¹) (τ * -(x ^ 2)⁻¹) x := hinv.const_mul τ
    have := (hasDerivAt_const x (2 * π * (n : ℝ))).sub h2
    simpa [hg'_def, hg''_def, mul_neg] using this
  -- continuity of w', g''
  have hcont_wg : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc (1 : ℝ) (N : ℝ)) :=
    ContinuousOn.inv₀ continuousOn_id (fun x hx => hxne x hx)
  have hlogc : ContinuousOn Real.log (Set.uIcc (1 : ℝ) (N : ℝ)) :=
    fun x hx => (Real.continuousAt_log (hxne x hx)).continuousWithinAt
  have hwc : ContinuousOn w (Set.uIcc (1 : ℝ) (N : ℝ)) := by
    rw [hw_def]; exact Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlogc)
  have hw'c : ContinuousOn w' (Set.uIcc (1 : ℝ) (N : ℝ)) := by
    rw [hw'_def]
    exact (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlogc)).mul
      (continuousOn_const.mul hcont_wg)
  have hg''c : ContinuousOn g'' (Set.uIcc (1 : ℝ) (N : ℝ)) := by
    rw [hg''_def]
    exact continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (hxne x hx)))
  -- hypotheses for the concave weighted second-derivative test
  have hwnn : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ), 0 ≤ w x := fun x _ => (Real.exp_pos _).le
  have hwanti : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ), w' x ≤ 0 := by
    intro x hx
    rw [hw'_def]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (inv_nonneg.mpr (hxpos x hx).le)
  have hg''ub : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ), g'' x ≤ -lam := by
    intro x hx
    rw [Set.uIcc_of_le hN1] at hx
    have hneglam : -lam = τ / (N : ℝ) ^ 2 := by rw [hlam_def]; ring
    rw [hg''_def, hneglam, div_eq_mul_inv]
    have hx2 : x ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith [hx.1, hx.2]
    have hxpos2 : (0 : ℝ) < x ^ 2 := pow_pos (by linarith [hx.1]) 2
    apply mul_le_mul_of_nonpos_left _ hτ.le
    exact inv_anti₀ hxpos2 hx2
  have hbound := norm_integral_weight_cexp_secondDeriv_neg (a := (1:ℝ)) (b := (N:ℝ))
    hN1 hlampos hwD hw'c hwnn hwanti hgD hg'D hg''c hg''ub
  -- w 1 = 1 and √lam = √(-τ)/N
  have hw1 : w 1 = 1 := by rw [hw_def]; simp
  have hsqrt : Real.sqrt lam = Real.sqrt (-τ) / (N : ℝ) := by
    rw [hlam_def, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hNpos.le]
  rw [hw1, hsqrt] at hbound
  calc ‖∫ x in (1 : ℝ)..(N : ℝ), (w x : ℂ) * Complex.exp ((g x : ℝ) * I)‖
      ≤ 10 * 1 / (Real.sqrt (-τ) / (N : ℝ)) := hbound
    _ = 10 * (N : ℝ) / Real.sqrt (-τ) := by
        rw [div_div_eq_mul_div]; ring

end RHTower
