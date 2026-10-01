import GaloisForLFunctions.RHTower.WindowTransformSamplingParseval

/-!
# The exact equal-ordinate overlap cost of a sampled window

For a simple on-line zero at ordinate `γ` and an off-line zero at the same ordinate and horizontal
distance `ε`, the sampled real vectors `f_k = Re φ̂(γ − τ_k)/√c` and
`g_k = Re φ̂(γ − iε − τ_k)/√c` (`c = aL²`) satisfy

`2J²/(I₀I₂) − 1 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²`   (`shift_overlap_cost_exact`),

`I₀ = ∫φ²`, `J = ∫φ² cosh(εu)`, `I₂ = ∫φ² cosh²(εu)` over `[−L/2, L/2]`.

On the full grid, `⟨f,g⟩ = LJ/c` and `‖g‖² = LI₂/c` (sampled Parseval,
`hasSum_re_mul_re_paperFT_grid`, `hasSum_norm_sq_paperFT_grid`), with `c = LI₀`. The overlap
criterion transfers the full-grid value to the truncated grid (`overlap_criterion`). Unlike
`shift_overlap_cost`, no restriction on `ε` is needed.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

/-- **Exact equal-ordinate overlap cost.** -/
theorem shift_overlap_cost_exact (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hc : Continuous (Q.phi T)) (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0)
    (hconj : Zeta23.ZeroSide.PhiHatConj T Q) (hreal : Zeta23.ZeroSide.PhiHatReal T Q)
    (ha : 0 < Q.a T) (γ ε : ℝ) :
    2 * (∫ u in (-(Q.L T / 2))..(Q.L T / 2), Q.phi T u ^ 2 * Real.cosh (ε * u)) ^ 2
        / ((∫ u in (-(Q.L T / 2))..(Q.L T / 2), Q.phi T u ^ 2)
          * ∫ u in (-(Q.L T / 2))..(Q.L T / 2), (Q.phi T u * Real.cosh (ε * u)) ^ 2) - 1
      ≤ 1 + 2 * (∑ k : Fin (Q.d T),
          (Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)
            * ((Q.phiHat T ((γ : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2))) ^ 2
        / (∑ k : Fin (Q.d T),
          ((Q.phiHat T ((γ : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)) ^ 2)
      - 2 * ∑ k : Fin (Q.d T),
          ((Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt (Q.a T * Q.L T ^ 2)) ^ 2 := by
  set L := Q.L T with hLdef
  set φ := Q.phi T with hφ
  set c := Q.a T * L ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  -- the partner window `φ cosh(ε·)`
  set b : ℝ → ℂ := fun u => ((φ u * Real.cosh (ε * u) : ℝ) : ℂ) with hb
  have hbc : Continuous b := by simp only [hb]; fun_prop
  have hbs : ∀ u, L / 2 ≤ |u| → b u = 0 := fun u hu => by
    simp only [hb]; rw [show φ u = 0 from hsupp u hu, zero_mul, Complex.ofReal_zero]
  have hbre : ∀ u, (b u).re = φ u * Real.cosh (ε * u) := fun u => by
    simp only [hb]; exact Complex.ofReal_re _
  have hbnorm : ∀ u, ‖b u‖ ^ 2 = (φ u * Real.cosh (ε * u)) ^ 2 := fun u => by
    simp only [hb, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  set I₀ := ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 with hI₀
  set J := ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 * Real.cosh (ε * u) with hJ
  set I₂ := ∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2 with hI₂
  have hcI : c = L * I₀ := a_mul_L_sq_eq Q T hL hsupp
  have hI₀pos : 0 < I₀ := by
    have : 0 < L * I₀ := hcI ▸ hc0
    exact pos_of_mul_pos_right this hL.le
  set w : ℤ → ℝ := fun j => γ - (T + j * (2 * Real.pi / L)) with hw
  set F : ℤ → ℝ := fun j => (Zeta23.paperFT (fun u => (φ u : ℂ)) (w j)).re / Real.sqrt c with hF
  set G : ℤ → ℝ := fun j => (Zeta23.paperFT b (w j)).re / Real.sqrt c with hG
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  have hsqc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
  have hbgrid : ∀ j : ℤ, Zeta23.paperFT b ((w j : ℝ) : ℂ)
      = ((Q.phiHat T (((w j : ℝ) : ℂ) - ε * I)).re : ℂ) :=
    fun j => paperFT_cosh_eq_re Q T hc hsupp hconj (w j) ε
  have hFt : ∀ t : Finset ℤ, ∑ j ∈ t, F j ^ 2 ≤ 1 := by
    intro t
    have h := sum_norm_sq_paperFT_grid_le (ψ := fun u => (φ u : ℂ)) hL (by fun_prop)
      (fun u hu => by simp [show φ u = 0 from hsupp u hu]) γ T t
    have hI : ∫ u in (-(L / 2))..(L / 2), ‖(φ u : ℂ)‖ ^ 2 = I₀ :=
      intervalIntegral.integral_congr fun u _ => by simp [Complex.norm_real, sq_abs]
    rw [hI, ← hcI] at h
    simp only [hF, div_pow, hsqc, ← Finset.sum_div]
    rw [div_le_one hc0]
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) h
    have := Complex.abs_re_le_norm (Zeta23.paperFT (fun u => (φ u : ℂ)) (w j))
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hreal' : ∀ j : ℤ, (Zeta23.paperFT (fun u => (φ u : ℂ)) ((w j : ℝ) : ℂ)).im = 0 := by
    intro j
    have := hreal (w j)
    change Q.phiHat T (w j) = _ at this
    change (Q.phiHat T (w j)).im = 0
    rw [this, Complex.ofReal_im]
  have hJeq : (∫ u in (-(L / 2))..(L / 2), φ u * (b u).re) = J := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hbre]; ring
  have hFG : HasSum (fun j => F j * G j) (L * J / c) := by
    have h := (hasSum_re_mul_re_paperFT_grid hL hc hbc hsupp hbs γ T hreal').div_const c
    rw [hJeq] at h
    refine h.congr_fun fun j => ?_
    simp only [hF, hG]
    rw [div_mul_div_comm, hsq]
  have hGG : HasSum (fun j => G j ^ 2) (L * I₂ / c) := by
    have h := (hasSum_norm_sq_paperFT_grid (ψ := b) hL hbc hbs γ T).div_const c
    have hI : ∫ u in (-(L / 2))..(L / 2), ‖b u‖ ^ 2 = I₂ :=
      intervalIntegral.integral_congr fun u _ => by simp only [hbnorm]
    rw [hI] at h
    refine h.congr_fun fun j => ?_
    simp only [hG, div_pow, hsqc]
    congr 1
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have him : (Zeta23.paperFT b ((w j : ℝ) : ℂ)).im = 0 := by
      rw [hbgrid j, Complex.ofReal_im]
    rw [him]
    ring
  -- positivity of `J` and `I₂`
  have hI0J : I₀ ≤ J := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u => φ u ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => φ u ^ 2 * Real.cosh (ε * u)).intervalIntegrable _ _
    intro u _
    have := Real.one_le_cosh (ε * u)
    nlinarith [sq_nonneg (φ u)]
  have hI0I2 : I₀ ≤ I₂ := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u => φ u ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => (φ u * Real.cosh (ε * u)) ^ 2).intervalIntegrable _ _
    intro u _
    have := Real.one_le_cosh (ε * u)
    have h1 : 1 ≤ Real.cosh (ε * u) ^ 2 := by nlinarith
    have e : (φ u * Real.cosh (ε * u)) ^ 2 = φ u ^ 2 * Real.cosh (ε * u) ^ 2 := by ring
    rw [e]
    nlinarith [sq_nonneg (φ u)]
  have hJpos : 0 < J := lt_of_lt_of_le hI₀pos hI0J
  have hI₂pos : 0 < I₂ := lt_of_lt_of_le hI₀pos hI0I2
  have hKpos : 0 < L * J / c := by positivity
  set s : Finset ℤ := Finset.univ.image (fun k : Fin (Q.d T) => ((k : ℕ) : ℤ)) with hs
  have hinj : Function.Injective (fun k : Fin (Q.d T) => ((k : ℕ) : ℤ)) := by
    intro a b h; simp only [Nat.cast_inj] at h; exact Fin.ext h
  have hcrit := overlap_criterion hFt hFG hGG hKpos s
  have hFk : ∀ k : Fin (Q.d T), F ((k : ℕ) : ℤ)
      = (Q.phiHat T ((γ : ℂ) - Q.tau T k)).re / Real.sqrt c := by
    intro k
    have : ((w ((k : ℕ) : ℤ) : ℝ) : ℂ) = (γ : ℂ) - Q.tau T k := by
      simp only [hw, Zeta23.Params.tau, Zeta23.Params.hgrid, hLdef]; push_cast; ring
    simp only [hF]
    rw [this]; rfl
  have hGk : ∀ k : Fin (Q.d T), G ((k : ℕ) : ℤ)
      = (Q.phiHat T ((γ : ℂ) - ε * I - Q.tau T k)).re / Real.sqrt c := by
    intro k
    have : (γ : ℂ) - ε * I - Q.tau T k = (((w ((k : ℕ) : ℤ)) : ℝ) : ℂ) - ε * I := by
      simp only [hw, Zeta23.Params.tau, Zeta23.Params.hgrid, hLdef]; push_cast; ring
    simp only [hG]
    rw [this, hbgrid, Complex.ofReal_re]
  rw [Finset.sum_image (fun a _ b _ h => hinj h), Finset.sum_image (fun a _ b _ h => hinj h),
    Finset.sum_image (fun a _ b _ h => hinj h)] at hcrit
  simp only [hFk, hGk] at hcrit
  have hval : 2 * (L * J / c) ^ 2 / (L * I₂ / c) = 2 * J ^ 2 / (I₀ * I₂) := by
    rw [hcI]; field_simp
  rw [hval] at hcrit
  exact hcrit

end

end RHTower
