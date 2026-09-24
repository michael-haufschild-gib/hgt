import GaloisForLFunctions.RHTower.EstermannRectangleIdentity
import GaloisForLFunctions.RHTower.EstermannConvexity
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay

/-!
# The horizontal edges of the Estermann rectangle vanish

On the segment `Re s ∈ [½, 2]` at height `±T` the three factors of `x^{-s} Γ(s) D(s, a/q)` are
bounded by a constant, by `C T^N e^{-πT/2}` and by `C(1+T)^N`.  The Gamma decay beats the
convexity bound, so the horizontal edge integrals tend to zero as `T → ∞`.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- A polynomial against a genuine exponential decays. -/
theorem tendsto_poly_mul_exp_neg_zero (K : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => (1 + T) ^ K * Real.exp (-(c * T))) atTop (nhds 0) := by
  have hshift : Tendsto (fun T : ℝ => c * (1 + T)) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop hc ?_
    exact tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp hshift
  have hconst := hbase.const_mul (Real.exp c / c ^ K)
  rw [mul_zero] at hconst
  refine hconst.congr (fun T => ?_)
  have hcK : (c : ℝ) ^ K ≠ 0 := pow_ne_zero K hc.ne'
  simp only [Function.comp_apply]
  rw [mul_pow, show -(c * (1 + T)) = -c + -(c * T) by ring, Real.exp_add]
  field_simp
  rw [mul_right_comm, ← Real.exp_add]
  norm_num

/-- The exponential weight is bounded on the abscissa segment. -/
theorem rpow_neg_le_of_mem {x u : ℝ} (hx : 0 < x) (h1 : 1 / 2 ≤ u) (h2 : u ≤ 2) :
    x ^ (-u) ≤ x ^ (-(1 / 2 : ℝ)) + x ^ (-(2 : ℝ)) := by
  have hp1 : (0 : ℝ) < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx _
  have hp2 : (0 : ℝ) < x ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hx _
  rcases le_total 1 x with hb | hb
  · have := Real.rpow_le_rpow_of_exponent_le hb (by linarith : -u ≤ -(1 / 2 : ℝ))
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hx hb (by linarith : -(2 : ℝ) ≤ -u)
    linarith

/-- **A uniform bound on the horizontal edges.** -/
theorem exists_bound_norm_estermannMellinIntegrand_horizontal (q : ℕ) [NeZero q] (a : (ZMod q)ˣ)
    {x : ℝ} (hx : 0 < x) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ u T : ℝ, 1 / 2 ≤ u → u ≤ 2 → 1 ≤ |T| →
      ‖estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + (T : ℂ) * I)‖
        ≤ C * (1 + |T|) ^ N * Real.exp (-(Real.pi * |T| / 2)) := by
  obtain ⟨CΓ, NΓ, hCΓ0, hCΓ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := (1 : ℝ) / 2) (by norm_num) 2
  obtain ⟨CD, ND, hCD0, hCD⟩ := exists_bound_norm_estermannZeta_strip q a
  set Mx : ℝ := x ^ (-(1 / 2 : ℝ)) + x ^ (-(2 : ℝ)) with hMx
  have hMx0 : 0 ≤ Mx := by rw [hMx]; positivity
  refine ⟨Mx * CΓ * CD, NΓ + ND, by positivity, fun u T h1 h2 hT => ?_⟩
  set s : ℂ := (u : ℂ) + (T : ℂ) * I with hs
  have hre : s.re = u := by rw [hs]; simp
  have him : s.im = T := by rw [hs]; simp
  have hxb : ‖((x : ℝ) : ℂ) ^ (-s)‖ ≤ Mx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.neg_re, hre]
    exact rpow_neg_le_of_mem hx h1 h2
  have hΓb : ‖Complex.Gamma s‖ ≤ CΓ * |T| ^ NΓ * Real.exp (-(Real.pi * |T| / 2)) := by
    have h := hCΓ u T h1 h2 hT
    rw [hs]; exact h
  have hDb : ‖estermannZeta q ((a : ZMod q)) s‖ ≤ CD * (1 + |T|) ^ ND := by
    have h := hCD s (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hT)
    rw [him] at h
    exact h
  have hTnn : (0 : ℝ) ≤ |T| := abs_nonneg T
  have hpow : |T| ^ NΓ ≤ (1 + |T|) ^ NΓ := pow_le_pow_left₀ hTnn (by linarith) NΓ
  have hΓb' : ‖Complex.Gamma s‖ ≤ CΓ * (1 + |T|) ^ NΓ * Real.exp (-(Real.pi * |T| / 2)) := by
    refine hΓb.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCΓ0)
      (Real.exp_pos _).le
  rw [estermannMellinIntegrand, norm_mul, norm_mul]
  calc ‖((x : ℝ) : ℂ) ^ (-s)‖ * ‖Complex.Gamma s‖ * ‖estermannZeta q ((a : ZMod q)) s‖
      ≤ Mx * (CΓ * (1 + |T|) ^ NΓ * Real.exp (-(Real.pi * |T| / 2))) * (CD * (1 + |T|) ^ ND) := by
        refine mul_le_mul (mul_le_mul hxb hΓb' (norm_nonneg _) hMx0) hDb (norm_nonneg _) ?_
        positivity
    _ = Mx * CΓ * CD * (1 + |T|) ^ (NΓ + ND) * Real.exp (-(Real.pi * |T| / 2)) := by
        rw [pow_add]; ring

/-- **The horizontal edges of the rectangle vanish.**  Both are covered: the bound is in `|T|`. -/
theorem tendsto_horizontal_estermannMellin (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u in (1 / 2 : ℝ)..2,
        estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (nhds 0) := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_estermannMellinIntegrand_horizontal q a hx
  have hεabs : ∀ T : ℝ, 0 ≤ T → |ε * T| = T := by
    intro T hT
    rcases hε with rfl | rfl <;> simp [abs_of_nonneg hT]
  have hg : Tendsto (fun T : ℝ => 3 / 2 * C * ((1 + T) ^ N * Real.exp (-(Real.pi / 2 * T))))
      atTop (nhds 0) := by
    have h := (tendsto_poly_mul_exp_neg_zero N (c := Real.pi / 2) (by positivity)).const_mul
      (3 / 2 * C)
    rwa [mul_zero] at h
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have habs : |ε * T| = T := hεabs T hT0
  have hbound : ∀ u ∈ Set.uIoc (1 / 2 : ℝ) 2,
      ‖estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ C * (1 + T) ^ N * Real.exp (-(Real.pi * T / 2)) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 2)] at hu
    have h := hC u (ε * T) (le_of_lt hu.1) hu.2 (by rw [habs]; exact hT)
    rwa [habs] at h
  have hlen : |(2 : ℝ) - 1 / 2| = 3 / 2 := by norm_num
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hlen] at hint
  calc ‖∫ u in (1 / 2 : ℝ)..2,
        estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ C * (1 + T) ^ N * Real.exp (-(Real.pi * T / 2)) * (3 / 2) := hint
    _ = 3 / 2 * C * ((1 + T) ^ N * Real.exp (-(Real.pi / 2 * T))) := by
        rw [show -(Real.pi * T / 2) = -(Real.pi / 2 * T) by ring]; ring

end

end RHTower
