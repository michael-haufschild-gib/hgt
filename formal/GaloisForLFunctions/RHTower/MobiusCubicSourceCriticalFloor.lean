import GaloisForLFunctions.RHTower.MobiusAbelPrefixFourierMultiplier
import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicFloor

/-!
# The critical endpoint of the cubic Möbius source is unbounded

Route L's cubic source `S_N(t) = Σ_{n ≤ N} μ(n) n² e^{-nt}` has, in the weighted norm of exponent
`δ`, the Mellin--Plancherel form

`‖S_N‖_δ² = (2π Γ(5+δ))⁻¹ ∫ |Γ((5+δ)/2 + iτ)|² |Σ_{n ≤ N} μ(n) n^{-(1+δ)/2 - iτ}|² dτ`

(`gammaEnergy_mobiusCubicSource_eq_mellin`).  At the critical endpoint `δ = 0` the Dirichlet
polynomial sits on `Re s = ½`, and `|Γ(5/2 + iτ)| = |3/2 + iτ| |1/2 + iτ| |Γ(1/2 + iτ)|` dominates
`(3/4) |Γ(1/2 + iτ)|`.  So `‖S_N‖_0² ≥ (3/128) Σ_{m,n ≤ N} μ(m)μ(n)/(m+n)`, and the logarithmic
floor of the Möbius Hilbert form gives `‖S_N‖_0² ≥ c log N` for every large `N`
(`exists_forall_mul_log_le_gammaEnergy_mobiusCubicSource_zero`).  No cutoff-uniform bound holds at
the critical endpoint.  For every `0 ≤ δ < 1` the same comparison gives
`‖S_N‖_δ² ≥ ((3+δ)(1+δ)/4)²/Γ(5+δ) · E_N(1+δ)`, so a zero of `ζ` with `Re ρ ≥ (1+δ)/2` forces
`‖S_N‖_δ → ∞` (`tendsto_gammaEnergy_mobiusCubicSource_atTop_of_riemannZeta_eq_zero`): a uniform
bound at level `δ` is a zero-free half-plane statement.
-/

open MeasureTheory Filter Finset Complex
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.CubicGamma

/-- `|Γ((5+δ)/2 + iτ)| ≥ ((3+δ)(1+δ)/4) |Γ((1+δ)/2 + iτ)|` for `δ ≥ 0`. -/
theorem norm_Gamma_shift_two_ge {δ : ℝ} (hδ : 0 ≤ δ) (τ : ℝ) :
    (3 + δ) * (1 + δ) / 4 * ‖Complex.Gamma (((1 + δ) / 2 : ℝ) + (τ : ℂ) * I)‖ ≤
      ‖Complex.Gamma (((5 + δ) / 2 : ℝ) + (τ : ℂ) * I)‖ := by
  set s : ℂ := (((1 + δ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hs
  have hsre : s.re = (1 + δ) / 2 := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hsre; linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    rw [Complex.add_re, hsre, Complex.one_re, Complex.zero_re] at this
    linarith
  have heq : (((5 + δ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I = s + 1 + 1 := by
    rw [hs]; push_cast; ring
  rw [heq, Complex.Gamma_add_one _ hs1, Complex.Gamma_add_one _ hs0, norm_mul, norm_mul]
  have h1 : (3 + δ) / 2 ≤ ‖s + 1‖ := by
    have := Complex.re_le_norm (s + 1)
    rw [Complex.add_re, hsre, Complex.one_re] at this
    linarith
  have h2 : (1 + δ) / 2 ≤ ‖s‖ := by
    have := Complex.re_le_norm s
    rw [hsre] at this
    exact this
  have hG := norm_nonneg (Complex.Gamma s)
  calc (3 + δ) * (1 + δ) / 4 * ‖Complex.Gamma s‖ =
        (3 + δ) / 2 * ((1 + δ) / 2 * ‖Complex.Gamma s‖) := by ring
    _ ≤ ‖s + 1‖ * (‖s‖ * ‖Complex.Gamma s‖) := by gcongr

/-- The Dirichlet polynomial of the cubic Mellin form is `edPoly mobCoeff`. -/
theorem cubic_sum_eq_edPoly (δ : ℝ) (N : ℕ) (τ : ℝ) :
    ∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 + δ) / 2 : ℝ) + (τ : ℂ) * I)) =
      edPoly mobCoeff (Icc 1 N) ((((1 + δ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I) := by
  unfold edPoly mobCoeff
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring_nf

/-- The line integrand of the cubic Mellin form is integrable. -/
theorem integrable_cubic_line {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    Integrable (fun τ : ℝ => ‖Complex.Gamma (((5 + δ) / 2 : ℝ) + (τ : ℂ) * I)‖ ^ 2 *
      ‖∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 + δ) / 2 : ℝ) + (τ : ℂ) * I))‖ ^ 2) := by
  set σ : ℝ := (5 + δ) / 2 with hσ_def
  have hσ : 0 < σ := by rw [hσ_def]; linarith
  set c : ℕ → ℝ := fun n => ((μ n : ℤ) : ℝ) * (n : ℝ) ^ 2 with hc
  set m : ℕ → ℝ := fun n => (n : ℝ) with hm
  set f : ℝ → ℂ := fun x => ((expDecaySum (Icc 1 N) c m x : ℝ) : ℂ) with hf
  have hm1 : ∀ n ∈ Icc 1 N, (1 : ℝ) ≤ m n := fun n hn => by
    simp only [hm]; exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hcont : Continuous f := by
    rw [hf]; exact Complex.continuous_ofReal.comp (continuous_expDecaySum _ _ _)
  have hbound : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ (∑ n ∈ Icc 1 N, |c n|) * Real.exp (-(1 * x)) := by
    intro x hx
    rw [hf, Complex.norm_real, Real.norm_eq_abs]
    exact abs_expDecaySum_le _ c m hm1 hx.le
  have h1 := integrable_logMellinLineSource_of_exp_bound hσ one_pos hcont hbound
  have h2 := memLp_two_logMellinLineSource_of_exp_bound hσ one_pos hcont hbound
  have hint := integrable_norm_sq_mellin_line_of_logMellinLineSource h1 h2
  refine hint.congr (Eventually.of_forall fun τ => ?_)
  have hre : 0 < ((σ : ℂ) + (τ : ℂ) * I).re := by simp; exact hσ
  have hsum : (∑ i ∈ Icc 1 N, (c i : ℂ) * (m i : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * I))) =
      ∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 + δ) / 2 : ℝ) + (τ : ℂ) * I)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    simp only [hc, hm]
    push_cast
    rw [mul_assoc]
    congr 1
    rw [show ((n : ℂ)) ^ 2 = (n : ℂ) ^ (2 : ℂ) by norm_cast, ← Complex.cpow_add _ _ hn0]
    congr 1
    rw [hσ_def]
    push_cast
    ring
  simp only
  rw [hf, mellin_expDecaySum _ c m (fun n hn => by linarith [hm1 n hn]) hre, norm_mul, mul_pow,
    hsum]

/-- **Plancherel for finite Möbius sections on `Re s = σ`.**
`∫ |Γ(σ+iu) Σ_{n≤N} μ(n) n^{-σ-iu}|² du = 2π E_N(2σ)`. -/
theorem integral_norm_sq_gamma_mul_edPoly_mobCoeff_line_sigma (N : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∫ u : ℝ, ‖Complex.Gamma ((σ : ℂ) + (u : ℂ) * I) *
        edPoly mobCoeff (Icc 1 N) ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 =
      2 * Real.pi * finiteMobiusGammaHankelEnergy N (2 * σ) := by
  have h1 := integrable_logMellinLineSource_mobiusDiscreteLaplaceFiniteSection N (sigma := σ) hσ
  have h2 : MemLp (logMellinLineSource (mobiusDiscreteLaplaceFiniteSection N) σ) 2 volume :=
    mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two N hσ
  have hP := integral_norm_sq_mellin_line_eq_logMellinLineSource h1 h2
  have hE := integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource N (sigma := σ) hσ
  have hm : ∀ y : ℝ, mellin (mobiusDiscreteLaplaceFiniteSection N) ((σ : ℂ) + (y : ℂ) * I) =
      Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * edPoly mobCoeff (Icc 1 N) ((σ : ℂ) + (y : ℂ) * I) := by
    intro y
    rw [mellin_mobiusDiscreteLaplaceFiniteSection N (by simpa using hσ)]
  simp_rw [hm] at hP
  rw [hP, ← hE]
  rfl

/-- **The cubic source dominates the Hilbert energy.**
`((3+δ)(1+δ)/4)² / Γ(5+δ) · E_N(1+δ) ≤ ‖S_N‖_δ²`. -/
theorem mul_energy_le_gammaEnergy_mobiusCubicSource {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    ((3 + δ) * (1 + δ) / 4) ^ 2 / Real.Gamma (5 + δ) * finiteMobiusGammaHankelEnergy N (1 + δ) ≤
      gammaEnergy δ (mobiusCubicSource N) := by
  have hmel := gammaEnergy_mobiusCubicSource_eq_mellin hδ N
  have hplan := integral_norm_sq_gamma_mul_edPoly_mobCoeff_line_sigma N
    (σ := (1 + δ) / 2) (by linarith)
  rw [show 2 * ((1 + δ) / 2) = 1 + δ by ring] at hplan
  have hΓ : 0 < Real.Gamma (5 + δ) := Real.Gamma_pos_of_pos (by linarith)
  set κ : ℝ := ((3 + δ) * (1 + δ) / 4) ^ 2 with hκ
  have hpt : ∀ τ : ℝ, κ * ‖Complex.Gamma ((((1 + δ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
      edPoly mobCoeff (Icc 1 N) ((((1 + δ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
      ‖Complex.Gamma (((5 + δ) / 2 : ℝ) + (τ : ℂ) * I)‖ ^ 2 *
        ‖∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) *
          (n : ℂ) ^ (-(((1 + δ) / 2 : ℝ) + (τ : ℂ) * I))‖ ^ 2 := by
    intro τ
    rw [cubic_sum_eq_edPoly, norm_mul, mul_pow, hκ]
    have h := norm_Gamma_shift_two_ge hδ τ
    have hsq := pow_le_pow_left₀ (by positivity) h 2
    have hP := sq_nonneg ‖edPoly mobCoeff (Icc 1 N) ((((1 + δ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖
    rw [mul_pow] at hsq
    nlinarith
  have hint := integral_mono_of_nonneg (Eventually.of_forall fun τ => by positivity)
    (integrable_cubic_line hδ N) (Eventually.of_forall hpt)
  rw [integral_const_mul, hplan] at hint
  rw [hmel]
  have hpi : 0 < Real.pi := Real.pi_pos
  calc κ / Real.Gamma (5 + δ) * finiteMobiusGammaHankelEnergy N (1 + δ) =
        (2 * Real.pi * Real.Gamma (5 + δ))⁻¹ *
          (κ * (2 * Real.pi * finiteMobiusGammaHankelEnergy N (1 + δ))) := by
        field_simp
    _ ≤ _ := by gcongr

/-- **Route L at level `δ` needs a zero-free half-plane.**  If `ζ` vanishes at some `ρ` with
`Re ρ ≥ (1+δ)/2`, `0 ≤ δ < 1`, then `‖S_N‖_δ → ∞`.  A cutoff-uniform bound for the cubic source at
level `δ` therefore implies that `ζ` has no zeros in `Re s ≥ (1+δ)/2`. -/
theorem tendsto_gammaEnergy_mobiusCubicSource_atTop_of_riemannZeta_eq_zero {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ : 1 + δ ≤ 2 * ρ.re) :
    Tendsto (fun N : ℕ => gammaEnergy δ (mobiusCubicSource N)) atTop atTop := by
  have hE := tendsto_finiteMobiusGammaHankelEnergy_atTop_of_riemannZeta_eq_zero hζ
    (r := 1 + δ) (by linarith) (by linarith) hρ
  have hc : 0 < ((3 + δ) * (1 + δ) / 4) ^ 2 / Real.Gamma (5 + δ) :=
    div_pos (by positivity) (Real.Gamma_pos_of_pos (by linarith))
  exact tendsto_atTop_mono (fun N => mul_energy_le_gammaEnergy_mobiusCubicSource hδ0 N)
    (hE.const_mul_atTop hc)

/-- **The critical cubic source is unbounded.**  For some `c > 0` and every large `N`,
`‖S_N‖_0² ≥ c log N`.  So Route L's Γ-weighted Mertens-prefix Fourier mass has no cutoff-uniform
bound at `δ = 0`. -/
theorem exists_forall_mul_log_le_gammaEnergy_mobiusCubicSource_zero :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * Real.log N ≤ gammaEnergy 0 (mobiusCubicSource N) := by
  obtain ⟨c, hc, N₀, hE⟩ := exists_forall_mul_log_le_finiteMobiusGammaHankelEnergy_one
  refine ⟨3 / 128 * c, by positivity, N₀, fun N hN => ?_⟩
  have h := mul_energy_le_gammaEnergy_mobiusCubicSource (le_refl (0 : ℝ)) N
  have hΓ5 : Real.Gamma (5 + 0) = 24 := by
    rw [add_zero, show (5 : ℝ) = (4 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [hΓ5, show (1 : ℝ) + 0 = 1 by norm_num] at h
  have hc' := hE N hN
  calc 3 / 128 * c * Real.log N = 3 / 128 * (c * Real.log N) := by ring
    _ ≤ 3 / 128 * finiteMobiusGammaHankelEnergy N 1 := by gcongr
    _ = ((3 + 0) * 1 / 4) ^ 2 / 24 * finiteMobiusGammaHankelEnergy N 1 := by norm_num
    _ ≤ _ := h
