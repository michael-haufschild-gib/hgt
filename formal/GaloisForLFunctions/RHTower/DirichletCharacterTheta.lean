import GaloisForLFunctions.RHTower.DirichletCharacterUnsmoothing
import GaloisForLFunctions.RHTower.ChebyshevThetaPowerLog

/-!
# Actual character prime sums

Removing proper prime powers from the proved character von Mangoldt estimate
preserves its power-log decay. Every prime up to the physical endpoint is retained.
-/

noncomputable section
namespace RHTower
open ArithmeticFunction Complex
variable {Q : ℕ}

/-- The actual prime sum with its Dirichlet character and logarithmic weight. -/
def characterChebyshevTheta (χ : DirichletCharacter ℂ Q) (x : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, χ p * (Real.log p : ℂ)

/-- Removing the proper prime powers costs at most their ordinary positive mass. -/
theorem norm_characterChebyshevPsi_sub_theta (χ : DirichletCharacter ℂ Q) (x : ℝ) :
    ‖characterChebyshevPsi χ ⌊x⌋₊ - characterChebyshevTheta χ x‖ ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  classical
  have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [characterChebyshevPsi, characterChebyshevTheta, hset,
    Finset.sum_filter, ← Finset.sum_sub_distrib,
    Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
  apply (norm_sum_le _ _).trans
  refine Finset.sum_le_sum fun n hn => ?_
  by_cases hp : n.Prime
  · simp [hp, vonMangoldt_apply_prime hp]
  · simp only [hp, ↓reduceIte, sub_zero]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)

/-- Every actual nonprincipal character has quantitative cancellation in its full
prime sum. No prime-distribution estimate is assumed. -/
theorem exists_characterChebyshevTheta_power_log [NeZero Q]
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ‖characterChebyshevTheta χ x‖ ≤
        C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, C, X, hc, hC, hX, hpsi⟩ := exists_characterChebyshevPsi_power_log hχ
  obtain ⟨Y, hY, hdecay⟩ := sqrt_log_le_power_log_decay hc
  refine ⟨c, C + 1, max X Y, hc, by positivity, hX.trans (le_max_left _ _), fun x hx => ?_⟩
  have hxX := (le_max_left X Y).trans hx
  have hxY := (le_max_right X Y).trans hx
  have hx1 : 1 ≤ x := by linarith only [hX, hxX]
  have hdef := (norm_characterChebyshevPsi_sub_theta χ x).trans
    ((Chebyshev.psi_sub_theta_le hx1).trans (hdecay x hxY))
  have htri := norm_sub_norm_le (characterChebyshevTheta χ x) (characterChebyshevPsi χ ⌊x⌋₊)
  rw [norm_sub_rev] at htri
  have hp := hpsi x hxX
  linarith only [hdef, htri, hp]

/-- The principal character removes only prime divisors of its modulus. -/
theorem norm_characterChebyshevTheta_principal_sub_theta [NeZero Q] (x : ℝ) :
    ‖characterChebyshevTheta (1 : DirichletCharacter ℂ Q) x - (Chebyshev.theta x : ℂ)‖ ≤
      Chebyshev.theta Q := by
  classical
  let s := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hnorm (p : ℕ) (hp : p ∈ s) :
      ‖(1 : DirichletCharacter ℂ Q) p * (Real.log p : ℂ) - (Real.log p : ℂ)‖ =
        if p ∣ Q then Real.log p else 0 := by
    have hprime := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
    by_cases hd : p ∣ Q
    · have hn : ¬ IsUnit (p : ZMod Q) := by
        rw [ZMod.isUnit_iff_coprime]
        exact hprime.dvd_iff_not_coprime.mp hd
      rw [MulChar.map_nonunit _ hn, zero_mul, zero_sub, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog, if_pos hd]
    · have hu : IsUnit (p : ZMod Q) :=
        (ZMod.isUnit_iff_coprime p Q).mpr (hprime.coprime_iff_not_dvd.mpr hd)
      rw [MulChar.one_apply hu, one_mul, sub_self, norm_zero, if_neg hd]
  have hsub : s.filter (fun p => p ∣ Q) ⊆ (Finset.Ioc 0 Q).filter Nat.Prime := by
    intro p hp
    obtain ⟨hs, hd⟩ := Finset.mem_filter.mp hp
    have hprime := (Finset.mem_filter.mp hs).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨hprime.pos, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne Q)) hd⟩, hprime⟩
  calc
    _ = ‖∑ p ∈ s, ((1 : DirichletCharacter ℂ Q) p * (Real.log p : ℂ) - (Real.log p : ℂ))‖ := by
      rw [Finset.sum_sub_distrib]
      simp only [s, characterChebyshevTheta, Chebyshev.theta, Complex.ofReal_sum]
    _ ≤ ∑ p ∈ s, ‖(1 : DirichletCharacter ℂ Q) p * (Real.log p : ℂ) - (Real.log p : ℂ)‖ := norm_sum_le _ _
    _ = ∑ p ∈ s.filter (fun p => p ∣ Q), Real.log p := by
      conv_rhs => rw [Finset.sum_filter]
      exact Finset.sum_congr rfl hnorm
    _ ≤ ∑ p ∈ (Finset.Ioc 0 Q).filter Nat.Prime, Real.log p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => Real.log_nonneg
        (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
    _ = Chebyshev.theta Q := by simp only [Chebyshev.theta, Nat.floor_natCast]

/-- Every character has its actual prime main term and a quantitative error. -/
theorem exists_characterChebyshevTheta_main_power_log [NeZero Q]
    (χ : DirichletCharacter ℂ Q) :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ‖characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤
        C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    obtain ⟨c, C, X, hc, hC, hX, htheta⟩ := exists_chebyshev_theta_power_log
    obtain ⟨Y, hY, hdecay⟩ := sqrt_log_le_power_log_decay hc
    refine ⟨c, C + Chebyshev.theta Q, max X (max Y (Real.exp 1)), hc,
      add_nonneg hC (Chebyshev.theta_nonneg _), hX.trans (le_max_left _ _), fun x hx => ?_⟩
    have hxX := (le_max_left X (max Y (Real.exp 1))).trans hx
    have hxY := (le_max_left Y (Real.exp 1)).trans ((le_max_right X _).trans hx)
    have hxe := (le_max_right Y (Real.exp 1)).trans ((le_max_right X _).trans hx)
    have hx1 : 1 ≤ x := by linarith only [hX, hxX]
    have hlog : 1 ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
    have hsqrt := Real.one_le_sqrt.mpr hx1
    have hfloor : 1 ≤ x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
      have hb : 1 ≤ 2 * Real.sqrt x * Real.log x := by nlinarith only [hsqrt, hlog]
      exact hb.trans (hdecay x hxY)
    have hfixed := mul_le_mul_of_nonneg_left hfloor (Chebyshev.theta_nonneg Q)
    have hp := htheta x hxX
    have hdef := norm_characterChebyshevTheta_principal_sub_theta (Q := Q) x
    have htri := norm_add_le
      (characterChebyshevTheta (1 : DirichletCharacter ℂ Q) x - (Chebyshev.theta x : ℂ))
      ((Chebyshev.theta x : ℂ) - (x : ℂ))
    rw [sub_add_sub_cancel, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htri
    simp only [↓reduceIte]
    linarith only [htri, hdef, hp, hfixed]
  · simpa only [hχ, ↓reduceIte, sub_zero] using exists_characterChebyshevTheta_power_log hχ

end RHTower
