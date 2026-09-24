import GaloisForLFunctions.RHTower.EstermannGrowth
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# Polynomial growth of Estermann's zeta function on the left

The archimedean factor of the Estermann functional equation is `Γ(s)² cos(π s)`.  The square of
the Gamma factor decays like `e^{-π|t|}` uniformly on a vertical strip and the cosine grows like
`e^{π|t|}`, so the two exponentials cancel exactly and only a power of the height survives.
Since the Dirichlet series is bounded right of the abscissa, one constant and one exponent bound
`D(1-s, a/q)` for every abscissa `2 ≤ Re s ≤ M` above unit height.
-/

open Complex

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The shifted `p`-series is monotone decreasing in the exponent. -/
theorem shiftedPSeries_le_two {σ : ℝ} (hσ : 2 ≤ σ) :
    (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ σ)
      ≤ ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ (2 : ℝ) := by
  refine (summable_shiftedPSeries (by linarith)).tsum_le_tsum (fun n => ?_)
    (summable_shiftedPSeries (by norm_num))
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  have hmono : (((n + 1 : ℕ) : ℝ)) ^ (2 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) ^ σ :=
    Real.rpow_le_rpow_of_exponent_le h1 hσ
  have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith) _
  exact one_div_le_one_div_of_le hpos hmono

/-- **Polynomial growth of `D(·, a/q)` on the left.**  One constant and one exponent serve every
abscissa `2 ≤ Re s ≤ M` above unit height. -/
theorem exists_bound_norm_estermannZeta_one_sub (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (M : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, 2 ≤ σ → σ ≤ M → 1 ≤ |t| →
      ‖estermannZeta q ((a : ZMod q)) (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ≤ C * |t| ^ N := by
  classical
  obtain ⟨CΓ, NΓ, hCΓ0, hCΓ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := (2 : ℝ)) (by norm_num) (max M 2)
  set Z : ℝ := ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ (2 : ℝ) with hZ
  have hZ0 : 0 ≤ Z := shiftedPSeries_nonneg _
  set Q : ℝ := (q : ℝ) ^ (2 * max M 2) with hQ
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  refine ⟨4 * Q * CΓ ^ (2 : ℕ) * Z ^ (2 : ℕ), 2 * NΓ, by positivity, ?_⟩
  intro σ t hσ2 hσM ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by rw [hs]; simp
  have him : s.im = t := by rw [hs]; simp
  have hsre : 1 < s.re := by rw [hre]; linarith
  have hpole : ∀ n : ℕ, s ≠ 1 - (n : ℂ) := by
    intro n hcon
    have hc := congrArg Complex.re hcon
    rw [hre] at hc
    simp only [Complex.sub_re, Complex.one_re, Complex.natCast_re] at hc
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hbase := norm_estermannZeta_one_sub_le a hsre hpole
  rw [hre] at hbase
  -- the four factors
  have hQfac : (q : ℝ) ^ (2 * σ - 1) ≤ Q := by
    rw [hQ]
    refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
    have : σ ≤ max M 2 := le_trans hσM (le_max_left _ _)
    linarith
  have hpi : (2 * Real.pi) ^ (-(2 * σ)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
    linarith [Real.pi_gt_three]
  have hΓ : ‖Complex.Gamma s‖ ≤ CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2)) := by
    have h := hCΓ σ t hσ2 (le_trans hσM (le_max_left _ _)) ht
    rw [hs]; exact h
  have hΓ2 : ‖Complex.Gamma s‖ ^ (2 : ℕ)
      ≤ (CΓ * |t| ^ NΓ) ^ (2 : ℕ) * Real.exp (-(Real.pi * |t|)) := by
    have hnn : (0 : ℝ) ≤ CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2)) := by positivity
    have hsq := mul_le_mul hΓ hΓ (norm_nonneg _) hnn
    calc ‖Complex.Gamma s‖ ^ (2 : ℕ) = ‖Complex.Gamma s‖ * ‖Complex.Gamma s‖ := by ring
      _ ≤ (CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2)))
          * (CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2))) := hsq
      _ = (CΓ * |t| ^ NΓ) ^ (2 : ℕ)
            * (Real.exp (-(Real.pi * |t| / 2)) * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ = (CΓ * |t| ^ NΓ) ^ (2 : ℕ) * Real.exp (-(Real.pi * |t|)) := by
          rw [← Real.exp_add]; congr 2; ring
  have hcos : (1 : ℝ) + ‖Complex.cos ((Real.pi : ℂ) * s)‖ ≤ 2 * Real.exp (Real.pi * |t|) := by
    have h := norm_cos_le_exp_abs_im ((Real.pi : ℂ) * s)
    have him2 : ((Real.pi : ℂ) * s).im = Real.pi * t := by
      simp [Complex.mul_im, hs]
    rw [him2] at h
    have habs : |Real.pi * t| = Real.pi * |t| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [habs] at h
    have h1 : (1 : ℝ) ≤ Real.exp (Real.pi * |t|) := by
      refine Real.one_le_exp ?_
      have := abs_nonneg t
      positivity
    linarith
  have htsum : (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ σ) ≤ Z := shiftedPSeries_le_two hσ2
  have htsum0 : (0 : ℝ) ≤ ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ σ := shiftedPSeries_nonneg _
  -- assemble
  refine hbase.trans ?_
  have hexp : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
    rw [← Real.exp_add]; simp
  have hstep : (2 : ℝ) * (q : ℝ) ^ (2 * σ - 1) * (2 * Real.pi) ^ (-(2 * σ))
        * ‖Complex.Gamma s‖ ^ (2 : ℕ) * (1 + ‖Complex.cos ((Real.pi : ℂ) * s)‖)
        * ((∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ σ)
            * (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ σ))
      ≤ 2 * Q * 1 * ((CΓ * |t| ^ NΓ) ^ (2 : ℕ) * Real.exp (-(Real.pi * |t|)))
          * (2 * Real.exp (Real.pi * |t|)) * (Z * Z) := by
    gcongr
  refine hstep.trans (le_of_eq ?_)
  have hpow : (CΓ * |t| ^ NΓ) ^ (2 : ℕ) = CΓ ^ (2 : ℕ) * |t| ^ (2 * NΓ) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm NΓ 2]
  rw [hpow]
  calc 2 * Q * 1 * (CΓ ^ (2 : ℕ) * |t| ^ (2 * NΓ) * Real.exp (-(Real.pi * |t|)))
          * (2 * Real.exp (Real.pi * |t|)) * (Z * Z)
      = (4 * Q * CΓ ^ (2 : ℕ) * Z ^ (2 : ℕ) * |t| ^ (2 * NΓ))
          * (Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|)) := by ring
    _ = 4 * Q * CΓ ^ (2 : ℕ) * Z ^ (2 : ℕ) * |t| ^ (2 * NΓ) := by rw [hexp]; ring

end

end RHTower
