import GaloisForLFunctions.RHTower.DirichletLRayLowerBound
import GaloisForLFunctions.HTGeometry.GammaLogGrowth
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# The completed Dirichlet L-function grows super-linearly on the real ray

Along the positive real axis the L-series factor is eventually at least `1/2` in modulus, so the
growth of the completed L-function is that of its Archimedean factor `Gammaℝ (s + d)`, where the
shift `d` is `0` for an even character and `1` for an odd one.  Evaluating at the arithmetic
progression `σ = 2(m+1) - d` turns that factor into `π^{-(m+1)} m!`, whose logarithm outgrows every
linear function of `m`.

This is the hypothesis of the Hadamard zero-existence criterion that no exponential majorant can
satisfy.
-/

open Complex Filter
open scoped Topology LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- The modulus of the real Archimedean factor. -/
theorem norm_Gammaℝ_ofReal {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gammaℝ (t : ℂ)‖ = Real.pi ^ (-t / 2) * Real.Gamma (t / 2) := by
  have hhalf : (0 : ℝ) < t / 2 := by linarith
  have hgam : Complex.Gamma ((t : ℂ) / 2) = ((Real.Gamma (t / 2) : ℝ) : ℂ) := by
    rw [show ((t : ℂ) / 2) = (((t / 2 : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.Gamma_ofReal _
  rw [Complex.Gammaℝ_def, norm_mul, hgam, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.Gamma_pos_of_pos hhalf)]
  congr 1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  rw [show (-(t : ℂ) / 2) = (((-t / 2 : ℝ)) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- The real Archimedean factor does not vanish on the positive ray. -/
theorem Gammaℝ_ofReal_ne_zero {t : ℝ} (ht : 0 < t) : Complex.Gammaℝ (t : ℂ) ≠ 0 := by
  intro h
  have hn : ‖Complex.Gammaℝ (t : ℂ)‖ = 0 := by rw [h, norm_zero]
  rw [norm_Gammaℝ_ofReal ht] at hn
  have hpos : 0 < Real.pi ^ (-t / 2) * Real.Gamma (t / 2) :=
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  linarith

/-- The logarithm of the real Archimedean factor. -/
theorem log_norm_Gammaℝ_ofReal {t : ℝ} (ht : 0 < t) :
    Real.log ‖Complex.Gammaℝ (t : ℂ)‖
      = -t / 2 * Real.log Real.pi + Real.log (Real.Gamma (t / 2)) := by
  rw [norm_Gammaℝ_ofReal ht,
    Real.log_mul (Real.rpow_pos_of_pos Real.pi_pos _).ne'
      (Real.Gamma_pos_of_pos (by linarith)).ne',
    Real.log_rpow Real.pi_pos]

/-- **Super-linear growth of the Archimedean factor on the shifted ray.**  For every slope `A`,
every threshold `T` and every shift `d ∈ [0,1]`, some `σ ≥ T` on the arithmetic progression
`2(m+1) - d` satisfies `A σ + log 2 < log ‖Gammaℝ (σ + d)‖`. -/
theorem exists_Gammaℝ_ray_growth (A T d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    ∃ σ : ℝ, T ≤ σ ∧ 1 ≤ σ ∧
      A * σ + Real.log 2 < Real.log ‖Complex.Gammaℝ ((σ + d : ℝ) : ℂ)‖ := by
  obtain ⟨m, ⟨hfact, hbig⟩, hT⟩ :=
    (((GaloisForLFunctions.HTGeometry.eventually_lt_log_factorial
        (2 * |A| + Real.log Real.pi + 1)).and
      (eventually_ge_atTop ⌈3 * |A| + Real.log Real.pi + Real.log 2⌉₊)).and
      (eventually_ge_atTop ⌈T⌉₊)).exists
  have hmB : 3 * |A| + Real.log Real.pi + Real.log 2 ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hbig)
  have hmT : T ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hT)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨2 * ((m : ℝ) + 1) - d, by linarith, by linarith, ?_⟩
  have harg : (2 * ((m : ℝ) + 1) - d + d) = 2 * ((m : ℝ) + 1) := by ring
  rw [harg]
  have hpos : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by linarith
  rw [log_norm_Gammaℝ_ofReal hpos]
  have hhalf : 2 * ((m : ℝ) + 1) / 2 = (m : ℝ) + 1 := by ring
  rw [hhalf, Real.Gamma_nat_eq_factorial m]
  have hAle : A * (2 * ((m : ℝ) + 1) - d) ≤ |A| * (2 * (m : ℝ) + 3) := by
    have h1 : A * (2 * ((m : ℝ) + 1) - d) ≤ |A| * |2 * ((m : ℝ) + 1) - d| := by
      calc A * (2 * ((m : ℝ) + 1) - d) ≤ |A * (2 * ((m : ℝ) + 1) - d)| := le_abs_self _
        _ = |A| * |2 * ((m : ℝ) + 1) - d| := abs_mul _ _
    have h2 : |2 * ((m : ℝ) + 1) - d| ≤ 2 * (m : ℝ) + 3 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg A))
  have hAbs : 0 ≤ |A| := abs_nonneg A
  have hlogpi : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.two_le_pi])
  nlinarith [hfact, hAle, hmB, hm0, hAbs, hlogpi]

/-- Ray growth of the completed L-function, given the parity shift of the Gamma factor. -/
theorem completedLFunction_ray_growth_aux {χ : DirichletCharacter ℂ N} (A d : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hgf : ∀ σ : ℝ, DirichletCharacter.gammaFactor χ (σ : ℂ)
      = Complex.Gammaℝ ((σ + d : ℝ) : ℂ)) :
    ∃ σ : ℝ, 1 ≤ σ ∧
      A * σ < Real.log ‖DirichletCharacter.completedLFunction χ (σ : ℂ)‖ := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (eventually_half_le_norm_LSeries χ)
  obtain ⟨σ, hσT, hσ1, hgrow⟩ := exists_Gammaℝ_ray_growth A (max T₀ 2) d hd0 hd1
  have hσ2 : (2 : ℝ) ≤ σ := le_trans (le_max_right T₀ 2) hσT
  have hσT₀ : T₀ ≤ σ := le_trans (le_max_left T₀ 2) hσT
  refine ⟨σ, hσ1, ?_⟩
  have hgfne : DirichletCharacter.gammaFactor χ (σ : ℂ) ≠ 0 := by
    rw [hgf σ]; exact Gammaℝ_ofReal_ne_zero (by linarith)
  have hre : 1 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; linarith
  have hLeq : DirichletCharacter.LFunction χ (σ : ℂ) = L ↗χ (σ : ℂ) :=
    DirichletCharacter.LFunction_eq_LSeries χ hre
  have hLlow : (1 / 2 : ℝ) ≤ ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ := by
    rw [hLeq]; exact hT₀ σ hσT₀
  have hLne : ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ ≠ 0 := by
    intro h; rw [h] at hLlow; linarith
  have hσne : ((σ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro h; rw [h] at hσ2; linarith
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ (σ : ℂ) (Or.inl hσne)
  have hfac : DirichletCharacter.completedLFunction χ (σ : ℂ)
      = DirichletCharacter.LFunction χ (σ : ℂ) * DirichletCharacter.gammaFactor χ (σ : ℂ) := by
    rw [hdiv, div_mul_cancel₀ _ hgfne]
  have hGnorm : 0 < ‖DirichletCharacter.gammaFactor χ (σ : ℂ)‖ := norm_pos_iff.mpr hgfne
  rw [hfac, norm_mul, Real.log_mul hLne hGnorm.ne']
  have hlog2 : Real.log (1 / 2 : ℝ) ≤ Real.log ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ :=
    Real.log_le_log (by norm_num) hLlow
  have hlog2' : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hlog2'] at hlog2
  rw [hgf σ]
  linarith

/-- **Super-linear ray growth of the completed L-function.**  For every slope `A` there is a real
`σ ≥ 1` with `A σ < log ‖Λ(σ, χ)‖`. -/
theorem completedLFunction_ray_growth {χ : DirichletCharacter ℂ N} (A : ℝ) :
    ∃ σ : ℝ, 1 ≤ σ ∧
      A * σ < Real.log ‖DirichletCharacter.completedLFunction χ (σ : ℂ)‖ := by
  rcases χ.even_or_odd with hev | hod
  · refine completedLFunction_ray_growth_aux A 0 le_rfl (by norm_num) fun σ => ?_
    rw [hev.gammaFactor_def]
    norm_num
  · refine completedLFunction_ray_growth_aux A 1 (by norm_num) le_rfl fun σ => ?_
    rw [hod.gammaFactor_def]
    congr 1
    push_cast
    ring

end RHTower
