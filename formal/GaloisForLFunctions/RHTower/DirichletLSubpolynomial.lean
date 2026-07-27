import GaloisForLFunctions.RHTower.DirichletLDiscBound
import GaloisForLFunctions.RHTower.DirichletLLineLowerBound
import GaloisForLFunctions.RHTower.DirichletZeroAbscissa
import GaloisForLFunctions.HTGeometry.ThreeCircles

/-!
# A logarithmic-power lower bound for the L-function

Right of the zero abscissa the L-function is bounded below by `exp(-c (1 + log(2+|t|))^θ)` with
`θ < 1` strictly.

The three circles are centred at `σ₀ + 1 + it`.  The inner disc stays right of `Re s = 2`, where
the L-function is bounded above by an absolute constant and below by `1/2`; the outer disc reaches
`Re s = Θ + δ/4`, still inside the zero-free half-plane, where the cubic bound gives
`log(M/m) = O(log(2+|t|))`.  On the target line `Re s ≥ Θ + δ` the interpolation weight is bounded
by a constant `< 1` because the outer radius overshoots the target by `δ/2`.
-/

open Complex Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Three-circles lower bound.**  Right of `Θ + δ` the L-function is at least
`(1/2) exp(-B (K (1 + log (2+|t|)))^θ)` with `θ < 1`. -/
theorem exists_three_circles_lower_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ B K θ : ℝ, 0 < B ∧ 0 < K ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ s : ℂ, zeroAbscissa χ + δ ≤ s.re →
      (1 : ℝ) / 2 * Real.exp (-(B * (K * (1 + Real.log (2 + |s.im|))) ^ θ))
        ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  obtain ⟨σ₀, hσ₀2, hline⟩ := exists_line_lower_bound χ
  obtain ⟨C₁, hC₁, hright⟩ := exists_bound_LFunction_of_two_le_re χ
  have hΘ1' : zeroAbscissa χ ≤ 1 := zeroAbscissa_le_one hχ hprim
  have hΘhalf' : (1 : ℝ) / 2 ≤ zeroAbscissa χ := half_le_zeroAbscissa hχ hprim
  obtain ⟨Θ, hΘ⟩ : ∃ T : ℝ, zeroAbscissa χ = T := ⟨_, rfl⟩
  rw [hΘ] at hΘ1' hΘhalf'
  have hΘ1 : Θ ≤ 1 := hΘ1'
  have hΘhalf : (1 : ℝ) / 2 ≤ Θ := hΘhalf'
  rw [hΘ]
  -- the geometry
  set a : ℝ := σ₀ + 1 with ha
  set r₃ : ℝ := a - (Θ + δ / 2) with hr₃
  set R : ℝ := a - (Θ + δ / 4) with hR
  have hr₃big : (3 : ℝ) / 2 ≤ r₃ := by rw [hr₃, ha]; linarith
  have hRbig : r₃ < R := by rw [hr₃, hR]; linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hRlow : (-2 : ℝ) ≤ a - R := by rw [hR]; linarith
  have hr₁ρ : (1 : ℝ) / 4 < 1 / 2 := by norm_num
  have hρR : (1 : ℝ) / 2 ≤ R := by linarith
  have hr₁r₃ : (1 : ℝ) / 4 < r₃ := by linarith
  obtain ⟨E₀, hE₀, hdisc₀⟩ := exists_bound_LFunction_disc hχ hprim hR0 hRlow
  set E : ℝ := max E₀ 1 with hE
  have hE1 : (1 : ℝ) ≤ E := le_max_right _ _
  have hE0 : (0 : ℝ) < E := by linarith
  have hdisc : ∀ t : ℝ, ∀ z : ℂ, ‖z - ((a : ℂ) + (t : ℝ) * I)‖ ≤ R →
      ‖DirichletCharacter.LFunction χ z‖ ≤ E * (2 + |t|) ^ 3 := by
    intro t z hz
    refine le_trans (hdisc₀ t z hz) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- `C₁` is at least `1/2`, since it dominates a value of modulus at least `1/2`
  have hC₁half : (1 : ℝ) / 2 ≤ C₁ := by
    have hval := hline ((σ₀ : ℂ) + 1) (by simp)
    exact le_trans hval (hright _ (by simp; linarith))
  -- the two Borel–Carathéodory constants
  set B : ℝ := 2 * (Real.log (C₁ / (1 / 2)) + 1) * (1 / 4) / (1 / 2 - 1 / 4) with hB
  have hlogC : 0 ≤ Real.log (C₁ / (1 / 2)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hB]
    have hsimp : 2 * (Real.log (C₁ / (1 / 2)) + 1) * (1 / 4) / (1 / 2 - 1 / 4)
        = 2 * (Real.log (C₁ / (1 / 2)) + 1) := by ring
    rw [hsimp]
    linarith
  have hB0 : (0 : ℝ) < B := by linarith
  set K : ℝ := 8 * r₃ / δ * (Real.log (2 * E) + 4) with hK
  have hlogE : (0 : ℝ) ≤ Real.log (2 * E) := Real.log_nonneg (by linarith)
  have hlog2E : 0 < Real.log (2 * E) + 4 := by linarith
  have hK0 : (0 : ℝ) < K := by rw [hK]; positivity
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hK]
    have h1 : (6 : ℝ) ≤ 8 * r₃ / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith
    nlinarith [h1, hlogE]
  -- the interpolation weight is bounded away from `1`
  set θ : ℝ := (Real.log (a - Θ - δ) - Real.log (1 / 4)) / (Real.log r₃ - Real.log (1 / 4))
    with hθ
  have hgap : (1 : ℝ) / 4 < a - Θ - δ := by rw [ha]; linarith
  have hgap2 : a - Θ - δ < r₃ := by rw [hr₃]; linarith
  have hden : 0 < Real.log r₃ - Real.log (1 / 4) := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4) hr₁r₃
    linarith
  have hnum : 0 ≤ Real.log (a - Θ - δ) - Real.log (1 / 4) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hgap.le
    linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg hnum hden.le
  clear_value θ K B E R r₃ a
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hden]
    have := Real.log_lt_log (by linarith : (0 : ℝ) < a - Θ - δ) hgap2
    linarith
  refine ⟨B, K, θ, hB0, hK0, hθ0, hθ1, fun s hs => ?_⟩
  set t : ℝ := s.im with ht
  have hbase : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hlogbase : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg hbase
  have hone : (1 : ℝ) ≤ 1 + Real.log (2 + |t|) := by linarith
  have hKpos : (0 : ℝ) ≤ K * (1 + Real.log (2 + |t|)) :=
    mul_nonneg hK0.le (by linarith only [hlogbase])
  have hexpnn : 0 ≤ B * (K * (1 + Real.log (2 + |t|))) ^ θ :=
    mul_nonneg hB0.le (Real.rpow_nonneg hKpos _)
  -- to the right of `a - 1/4` the direct line bound already suffices
  rcases le_or_gt s.re (a - 1 / 4) with hleft | hrightside
  · -- the three-circles regime
    set c : ℂ := (a : ℂ) + (t : ℝ) * I with hc
    have hcre : c.re = a := by rw [hc]; simp
    have hcim : c.im = t := by rw [hc]; simp
    have hsc : s - c = (((s.re - a : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp [hc, ht]
    have hscnorm : ‖s - c‖ = a - s.re := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hz1 : (1 : ℝ) / 4 ≤ ‖s - c‖ := by rw [hscnorm]; linarith
    have hz3 : ‖s - c‖ ≤ r₃ := by
      rw [hscnorm, hr₃]
      linarith
    -- hypotheses of the two-radius bound
    have hballre : ∀ z ∈ ball c R, a - R < z.re := by
      intro z hz
      have hd : ‖z - c‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre] at hre
      have h2 := abs_lt.mp (lt_of_le_of_lt hre hd)
      linarith [h2.1]
    have hne : ∀ z ∈ ball c R, DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz
      refine LFunction_ne_zero_of_zeroAbscissa_lt hχ ?_
      have hb := hballre z hz
      rw [hΘ]
      have hAR : a - R = Θ + δ / 4 := by rw [hR]; ring
      rw [hAR] at hb
      linarith only [hb, hδ]
    have hf : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (ball c R) :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    have hMi : ∀ z ∈ ball c (1 / 2), ‖DirichletCharacter.LFunction χ z‖ ≤ C₁ := by
      intro z hz
      have hd : ‖z - c‖ < 1 / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre] at hre
      have h2 := abs_lt.mp (lt_of_le_of_lt hre hd)
      refine hright z ?_
      rw [ha] at h2
      linarith [h2.1]
    have hmc : (1 : ℝ) / 2 ≤ ‖DirichletCharacter.LFunction χ c‖ := by
      refine hline c ?_
      rw [hcre, ha]
      linarith
    have hM : ∀ z ∈ ball c R, ‖DirichletCharacter.LFunction χ z‖ ≤ E * (2 + |t|) ^ 3 := by
      intro z hz
      have hd : ‖z - c‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      exact hdisc t z hd.le
    have hmain := norm_lower_bound_of_two_radii (by norm_num : (0 : ℝ) < 1 / 4) hr₁ρ hρR hr₁r₃
      hRbig hf hne hMi (by norm_num : (0 : ℝ) < 1 / 2) hmc hM (by norm_num : (0 : ℝ) < 1 / 2) hmc
      hz1 hz3
    -- compare the exponents
    set w : ℝ := (Real.log ‖s - c‖ - Real.log (1 / 4)) / (Real.log r₃ - Real.log (1 / 4)) with hw
    have hw0 : 0 ≤ w := by
      rw [hw]
      have hnum' := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hz1
      exact div_nonneg (by linarith) hden.le
    have hwθ : w ≤ θ := by
      rw [hw, hθ, div_le_div_iff_of_pos_right hden]
      have hle : ‖s - c‖ ≤ a - Θ - δ := by rw [hscnorm]; linarith
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hz1
      have h2 := Real.log_le_log (by linarith : (0 : ℝ) < ‖s - c‖) hle
      linarith
    -- the outer constant is at most `K (1 + log (2+|t|))`
    have hMm : E * (2 + |t|) ^ 3 / (1 / 2) = 2 * E * (2 + |t|) ^ 3 := by ring
    have hlogsplit : Real.log (2 * E * (2 + |t|) ^ 3)
        = Real.log (2 * E) + 3 * Real.log (2 + |t|) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    have hr₃0 : (0 : ℝ) < r₃ := by linarith
    have hRr : R - r₃ = δ / 4 := by rw [hR, hr₃]; ring
    have hRr0 : (0 : ℝ) < R - r₃ := by rw [hRr]; linarith only [hδ]
    have hfac : (0 : ℝ) < 8 * r₃ / δ := div_pos (by linarith only [hr₃0]) hδ
    have houter : 2 * (Real.log (E * (2 + |t|) ^ 3 / (1 / 2)) + 1) * r₃ / (R - r₃)
        ≤ K * (1 + Real.log (2 + |t|)) := by
      rw [hMm, hlogsplit, hRr, hK]
      have hkey : Real.log (2 * E) + 3 * Real.log (2 + |t|) + 1
          ≤ (Real.log (2 * E) + 4) * (1 + Real.log (2 + |t|)) := by
        have hexpand : (Real.log (2 * E) + 4) * (1 + Real.log (2 + |t|))
            = Real.log (2 * E) + 3 * Real.log (2 + |t|) + 1
              + (Real.log (2 * E) * Real.log (2 + |t|) + Real.log (2 + |t|) + 3) := by ring
        rw [hexpand]
        have h0 : 0 ≤ Real.log (2 * E) * Real.log (2 + |t|) := mul_nonneg hlogE hlogbase
        linarith only [h0, hlogbase]
      calc 2 * (Real.log (2 * E) + 3 * Real.log (2 + |t|) + 1) * r₃ / (δ / 4)
          = 8 * r₃ / δ * (Real.log (2 * E) + 3 * Real.log (2 + |t|) + 1) := by
            field_simp
            ring
        _ ≤ 8 * r₃ / δ * ((Real.log (2 * E) + 4) * (1 + Real.log (2 + |t|))) :=
            mul_le_mul_of_nonneg_left hkey hfac.le
        _ = 8 * r₃ / δ * (Real.log (2 * E) + 4) * (1 + Real.log (2 + |t|)) := by ring
    have houter1 : (1 : ℝ) ≤ K * (1 + Real.log (2 + |t|)) := by
      calc (1 : ℝ) ≤ K := hK1
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * (1 + Real.log (2 + |t|)) := mul_le_mul_of_nonneg_left hone hK0.le
    have hlogM : (0 : ℝ) ≤ Real.log (E * (2 + |t|) ^ 3 / (1 / 2)) := by
      rw [hMm]
      refine Real.log_nonneg ?_
      have h1 : (1 : ℝ) ≤ (2 + |t|) ^ 3 := one_le_pow₀ hbase
      have h3 : (0 : ℝ) ≤ 2 * E := by linarith only [hE1]
      calc (1 : ℝ) ≤ 2 * E * 1 := by linarith only [hE1]
        _ ≤ 2 * E * (2 + |t|) ^ 3 := mul_le_mul_of_nonneg_left h1 h3
    have hbase0 : (0 : ℝ) ≤ 2 * (Real.log (E * (2 + |t|) ^ 3 / (1 / 2)) + 1) * r₃ / (R - r₃) := by
      have hnum0 : (0 : ℝ) ≤ 2 * (Real.log (E * (2 + |t|) ^ 3 / (1 / 2)) + 1) * r₃ :=
        mul_nonneg (by linarith only [hlogM]) hr₃0.le
      exact div_nonneg hnum0 hRr0.le
    -- monotonicity of the interpolated exponent
    have hpow1 : B ^ (1 - w) ≤ B := by
      calc B ^ (1 - w) ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
        _ = B := Real.rpow_one B
    have hpow3 : (2 * (Real.log (E * (2 + |t|) ^ 3 / (1 / 2)) + 1) * r₃ / (R - r₃)) ^ w
        ≤ (K * (1 + Real.log (2 + |t|))) ^ θ :=
      le_trans (Real.rpow_le_rpow hbase0 houter hw0)
        (Real.rpow_le_rpow_of_exponent_le houter1 hwθ)
    have hprod : B ^ (1 - w) *
        (2 * (Real.log (E * (2 + |t|) ^ 3 / (1 / 2)) + 1) * r₃ / (R - r₃)) ^ w
          ≤ B * (K * (1 + Real.log (2 + |t|))) ^ θ :=
      mul_le_mul hpow1 hpow3 (Real.rpow_nonneg hbase0 _) hB0.le
    rw [← hB] at hmain
    calc (1 : ℝ) / 2 * Real.exp (-(B * (K * (1 + Real.log (2 + |t|))) ^ θ))
        ≤ 1 / 2 * Real.exp (-(B ^ (1 - w) *
            (2 * (Real.log (E * (2 + |t|) ^ 3 / (1 / 2)) + 1) * r₃ / (R - r₃)) ^ w)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hprod]))
            (by norm_num)
      _ ≤ ‖DirichletCharacter.LFunction χ c‖ * Real.exp (-(B ^ (1 - w) *
            (2 * (Real.log (E * (2 + |t|) ^ 3 / (1 / 2)) + 1) * r₃ / (R - r₃)) ^ w)) :=
          mul_le_mul_of_nonneg_right hmc (Real.exp_pos _).le
      _ ≤ ‖DirichletCharacter.LFunction χ s‖ := hmain
  · -- far to the right the line bound applies directly
    have hge : σ₀ ≤ s.re := by rw [ha] at hrightside; linarith
    have hval := hline s hge
    calc (1 : ℝ) / 2 * Real.exp (-(B * (K * (1 + Real.log (2 + |t|))) ^ θ))
        ≤ 1 / 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = 1 / 2 := by ring
      _ ≤ ‖DirichletCharacter.LFunction χ s‖ := hval

/-- **Subpolynomial lower bound.**  Right of `Θ + δ` the L-function is bounded below by
`κ (2+|t|)^{-ε}` for **every** `ε > 0` — equivalently, `1/L` grows slower than any fixed power of
the height.  This is the strengthening of `exists_lower_bound_right_of_abscissa`, whose exponent is
a fixed large constant, that the smoothed Perron argument needs. -/
theorem exists_lower_bound_subpolynomial {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, zeroAbscissa χ + δ ≤ s.re →
      κ * (2 + |s.im|) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  obtain ⟨B, K, θ, hB, hK, hθ0, hθ1, hbd⟩ := exists_three_circles_lower_bound hχ hprim hδ hδ1
  have hbasepos : ∀ u : ℝ, 2 ≤ u → 0 < K * (1 + Real.log u) :=
    fun u hu => mul_pos hK (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ u)])
  have hcont : ContinuousOn (fun u : ℝ => Real.exp (ε * Real.log u -
      B * (K * (1 + Real.log u)) ^ θ)) (Set.Ici 2) := by
    refine Real.continuous_exp.comp_continuousOn (ContinuousOn.sub ?_ ?_)
    · refine continuousOn_const.mul (Real.continuousOn_log.mono ?_)
      intro u hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have h2 : (2 : ℝ) ≤ u := hu
      linarith
    · refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ ?_)
      · refine continuousOn_const.mul (continuousOn_const.add (Real.continuousOn_log.mono ?_))
        intro u hu
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h2 : (2 : ℝ) ≤ u := hu
        linarith
      · exact fun u hu => Or.inl (ne_of_gt (hbasepos u hu))
  have hlim : Filter.Tendsto (fun u : ℝ => Real.exp (ε * Real.log u -
      B * (K * (1 + Real.log u)) ^ θ)) Filter.atTop Filter.atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    have hinner : Filter.Tendsto (fun L : ℝ => ε * L - B * (K * (1 + L)) ^ θ)
        Filter.atTop Filter.atTop := by
      have hhalf : Filter.Tendsto (fun L : ℝ => ε / 2 * L) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by linarith) Filter.tendsto_id
      refine Filter.tendsto_atTop_mono' _ ?_ hhalf
      have hc := eventually_const_mul_rpow_le (c := B * (K ^ θ * 2 ^ θ)) hθ1
        (show (0 : ℝ) < ε / 2 by linarith)
      filter_upwards [hc, Filter.eventually_ge_atTop (1 : ℝ)] with L hL hL1
      have hsplit : (K * (1 + L)) ^ θ = K ^ θ * (1 + L) ^ θ :=
        Real.mul_rpow hK.le (by linarith)
      have h2L : (1 + L) ^ θ ≤ (2 * L) ^ θ :=
        Real.rpow_le_rpow (by linarith) (by linarith) hθ0
      have h2L' : (2 * L) ^ θ = 2 ^ θ * L ^ θ := Real.mul_rpow (by norm_num) (by linarith)
      have hKθ : (0 : ℝ) ≤ K ^ θ := Real.rpow_nonneg hK.le _
      have hchain : B * (K * (1 + L)) ^ θ ≤ B * (K ^ θ * 2 ^ θ) * L ^ θ := by
        rw [hsplit]
        have hmid : K ^ θ * (1 + L) ^ θ ≤ K ^ θ * (2 ^ θ * L ^ θ) := by
          rw [← h2L']
          exact mul_le_mul_of_nonneg_left h2L hKθ
        nlinarith [hB.le, hmid]
      linarith
    exact hinner.comp Real.tendsto_log_atTop
  obtain ⟨κ, hκ0, hκ⟩ := exists_pos_lower_bound_of_tendsto_atTop hcont
    (fun u _ => Real.exp_pos _) hlim
  refine ⟨κ / 2, by linarith, fun s hs => ?_⟩
  have h1 := hbd s hs
  set u : ℝ := 2 + |s.im| with hu
  have hu2 : (2 : ℝ) ≤ u := by rw [hu]; linarith [abs_nonneg s.im]
  have hupos : (0 : ℝ) < u := by linarith
  have hκu := hκ u hu2
  have hrpow : u ^ (-ε) = Real.exp (-(ε * Real.log u)) := by
    rw [Real.rpow_def_of_pos hupos]
    ring_nf
  rw [hrpow]
  refine le_trans ?_ h1
  have hstep : κ * Real.exp (-(ε * Real.log u))
      ≤ Real.exp (-(B * (K * (1 + Real.log u)) ^ θ)) := by
    calc κ * Real.exp (-(ε * Real.log u))
        ≤ Real.exp (ε * Real.log u - B * (K * (1 + Real.log u)) ^ θ) *
            Real.exp (-(ε * Real.log u)) :=
          mul_le_mul_of_nonneg_right hκu (Real.exp_pos _).le
      _ = Real.exp (-(B * (K * (1 + Real.log u)) ^ θ)) := by
          rw [← Real.exp_add]
          ring_nf
  linarith [hstep]

end RHTower
