import GaloisForLFunctions.FrustratedArithmeticDirichletForms.SoftEntryInEveryStageFibre

/-!
# The entry constant is one

`TheEntryIsLogarithmicallySoft` bounds an entering weight by `√n₀(A log(1/δ) + B)`,
`δ = 2c − log n₀`, with a leading constant `A` lost to Cauchy–Schwarz between the two sites and to the
support length of a site. Keeping the exact pair energy of two separated atoms (SSHA
`levyEnergy_atom_pair`, the cross term reading `ω` at the distance) and the exact mass of a site gives
the sharp leading constant.

* **Two-site energy** (`levyEnergy_twoSite_eq`): `𝒥(F_ε) = 2𝒥(φ_r) − 2εX`, with the archimedean cross
  term `|X| ≤ 2ω(ℓ − 2r)(2r)²` (`abs_atomCrossTerm_siteBump_le`).
* **Outer law with constant one** (`abs_calibration_coord_le_log_add`): for small `δ` every
  `λ ∈ 𝒜(c)` has `|λ(n₀)| ≤ √n₀(log(1/δ) + B)`. The reading of the two-site test pays `2‖φ_r‖²/√n₀`
  per unit of weight, its energy is `2‖φ_r‖² log(1/δ) + O(r)`, and `θ′(0) < 0` only helps.
* **Inner law with constant one half** (`levyTail_ge_half_log`): `Ω(δ) ≥ ½log(1/δ) − ¼`, so with a
  Lévy margin `η` the stage fibre contains every `t` with `|t − λ(n₀)| ≤ √n₀η(½log(1/δ) − ¼)`
  (`stageFibre_sharp`).

The leading constant of the logarithmic entry thus lies between `η/2` inside and `1` outside.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower _root_.Zeta23

/-! ### The inner constant: `Ω(δ) ≥ ½log(1/δ) − ¼` -/

/-- `ω(x) ≥ 1/(2x) − 1/4` on `(0, 1]` integrates to `Ω(δ) ≥ ½log(1/δ) − ¼`. -/
theorem levyTail_ge_half_log {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (1 / δ) / 2 - 1 / 4 ≤ ∫ x in Ioi δ, archLevyDensity x := by
  have hint : IntegrableOn archLevyDensity (Ioi δ) :=
    WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ
  have hsub : (∫ x in Ioc δ 1, archLevyDensity x) ≤ ∫ x in Ioi δ, archLevyDensity x :=
    setIntegral_mono_set hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        (archLevyDensity_pos (lt_trans hδ hx)).le)
      (Eventually.of_forall fun x hx => hx.1)
  have hinvI : IntervalIntegrable (fun x : ℝ => x⁻¹) volume δ 1 := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun x hx => ?_)
    rw [uIcc_of_le hδ1] at hx
    exact (lt_of_lt_of_le hδ hx.1).ne'
  have hval : ∫ x in δ..1, ((1 / 2) * x⁻¹ - 1 / 4) = Real.log (1 / δ) / 2 - (1 - δ) / 4 := by
    rw [intervalIntegral.integral_sub (hinvI.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_inv_of_pos hδ one_pos,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hlow : ∫ x in δ..1, ((1 / 2) * x⁻¹ - 1 / 4) ≤ ∫ x in Ioc δ 1, archLevyDensity x := by
    rw [← intervalIntegral.integral_of_le hδ1]
    refine intervalIntegral.integral_mono_on hδ1 ((hinvI.const_mul _).sub intervalIntegrable_const)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ1).mpr
        (hint.mono_set Ioc_subset_Ioi_self)) fun x hx => ?_
    have hx0 : 0 < x := lt_of_lt_of_le hδ hx.1
    have h1 := Real.add_one_le_exp (-x / 2)
    have h2 := SignedWindowCriticality.PrimeThreeEntry.exp_neg_half_div_le_archLevyDensity hx0
    have e : (1 / 2) * x⁻¹ - 1 / 4 = (-x / 2 + 1) / (2 * x) := by
      field_simp
      ring
    rw [e]
    exact (div_le_div_of_nonneg_right h1 (by positivity)).trans h2
  linarith

/-! ### The exact energy of a two-site test -/

theorem siteBump_shift_vanish {r : ℝ} (hr : 0 < r) :
    ∀ u, u ∉ Icc 0 (2 * r) → siteBump r hr (u - r) = 0 := fun u hu =>
  siteBump_eq_zero hr (by
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith)

/-- The Lévy energy of a site bump with its exact mass:
`𝒥(φ_r) ≤ (log(1/(2r)) + C₀)‖φ_r‖² + 4e^{1/2}Kr`. -/
theorem levyEnergy_siteBump_le_mass :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, ∀ hr : 0 < r, r ≤ 1 / 2 →
      levyEnergy (siteBump r hr) ≤
        (Real.log (1 / (2 * r)) + SpacingScaleHarmonicAnalysis.selfEnergyConstant) *
            (∫ u, siteBump r hr u ^ 2) + 4 * Real.exp (1 / 2) * K * r := by
  obtain ⟨C, hC⟩ := ((siteBump 1 one_pos).contDiff (n := 1)).lipschitzWith_of_hasCompactSupport
    (siteBump 1 one_pos).hasCompactSupport (by norm_num)
  refine ⟨C, C.2, fun r hr hr2 => ?_⟩
  set g : ℝ → ℝ := fun u => siteBump r hr (u - r)
  have hg : ContDiff ℝ 2 g := (siteBump r hr).contDiff.comp (contDiff_id.sub contDiff_const)
  have hgsupp : ∀ u, u ∉ Icc 0 (2 * r) → g u = 0 := siteBump_shift_vanish hr
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * r)) hgsupp
  have hlip : ∀ u v, |g u - g v| ≤ (C / r) * |u - v| := by
    intro u v
    simp only [g]
    rw [siteBump_eq_unit hr, siteBump_eq_unit hr]
    have h := hC.dist_le_mul ((u - r) / r) ((v - r) / r)
    rw [Real.dist_eq, Real.dist_eq] at h
    calc |siteBump 1 one_pos ((u - r) / r) - siteBump 1 one_pos ((v - r) / r)|
        ≤ C * |(u - r) / r - (v - r) / r| := h
      _ = (C / r) * |u - v| := by
          rw [show (u - r) / r - (v - r) / r = (u - v) / r by ring, abs_div, abs_of_pos hr]
          ring
  have hK0 : 0 ≤ (C : ℝ) / r := div_nonneg C.2 hr.le
  have h := SpacingScaleHarmonicAnalysis.levyEnergy_atom_le hg hgc hgsupp (by linarith)
    (by linarith) hK0 hlip
  have htr : levyEnergy g = levyEnergy (siteBump r hr) :=
    SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := siteBump r hr) r
  have hsq : (∫ u, g u ^ 2) = ∫ u, siteBump r hr u ^ 2 :=
    integral_sub_right_eq_self (μ := volume) (fun u => siteBump r hr u ^ 2) r
  have habs : (∫ u, |g u|) = ∫ u, siteBump r hr u := by
    rw [integral_sub_right_eq_self (μ := volume) (fun u => |siteBump r hr u|) r]
    exact integral_congr_ae (Eventually.of_forall fun u => abs_of_nonneg (siteBump_nonneg hr u))
  rw [htr, hsq, habs] at h
  have e2 : Real.exp (1 / 2) * (C / r) * (2 * r) * (∫ u, siteBump r hr u) ≤
      4 * Real.exp (1 / 2) * C * r := by
    have : Real.exp (1 / 2) * (C / r) * (2 * r) = 2 * Real.exp (1 / 2) * C := by field_simp
    rw [this]
    calc 2 * Real.exp (1 / 2) * C * (∫ u, siteBump r hr u) ≤ 2 * Real.exp (1 / 2) * C * (2 * r) :=
          mul_le_mul_of_nonneg_left (integral_siteBump_le hr) (by positivity)
      _ = 4 * Real.exp (1 / 2) * C * r := by ring
  linarith

/-- **The two-site energy**: `𝒥(F_ε) = 2𝒥(φ_r) − 2εX` for `ε = ±1`, `X` the archimedean cross term
of two atoms at distance `ℓ > 2r`. -/
theorem levyEnergy_twoSite_eq {ℓ r : ℝ} (hr : 0 < r) (hrℓ : 2 * r < ℓ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    levyEnergy (twoSiteTestAt ℓ r hr ε) = 2 * levyEnergy (siteBump r hr) -
      2 * ε * SpacingScaleHarmonicAnalysis.atomCrossTerm (fun u => siteBump r hr (u - r)) ℓ := by
  set g : ℝ → ℝ := fun u => siteBump r hr (u - r)
  have hg : ContDiff ℝ 2 g := (siteBump r hr).contDiff.comp (contDiff_id.sub contDiff_const)
  have hgsupp : ∀ u, u ∉ Icc 0 (2 * r) → g u = 0 := siteBump_shift_vanish hr
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * r)) hgsupp
  have hgs : ContDiff ℝ 2 fun u => g (u - ℓ) := hg.comp (contDiff_id.sub contDiff_const)
  have hgsc : HasCompactSupport fun u => g (u - ℓ) := hgc.comp_homeomorph (Homeomorph.subRight ℓ)
  have hpair := SpacingScaleHarmonicAnalysis.levyEnergy_atom_pair hg hgc hgsupp hrℓ
  have h1 := SpacingScaleHarmonicAnalysis.levyEnergy_smul_add hg hgc hgs hgsc 1
  have hε' := SpacingScaleHarmonicAnalysis.levyEnergy_smul_add hg hgc hgs hgsc ε
  simp only [one_mul, mul_one] at h1
  have htr : levyEnergy (fun u => g (u - ℓ)) = levyEnergy g :=
    SpacingScaleHarmonicAnalysis.levyEnergy_translate ℓ
  have hgφ : levyEnergy g = levyEnergy (siteBump r hr) :=
    SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := siteBump r hr) r
  have hmix : ∫ y in Ioi 0, SpacingScaleHarmonicAnalysis.levyMixed g (fun u => g (u - ℓ)) y =
      -SpacingScaleHarmonicAnalysis.atomCrossTerm g ℓ := by
    rw [htr] at h1; linarith
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hF : twoSiteTestAt ℓ r hr ε =
      fun u => (fun v => ε * g v + g (v - ℓ)) (u - -(ℓ / 2 + r)) := by
    funext u
    simp only [twoSiteTestAt, g]
    rw [show u - -(ℓ / 2 + r) - r = u + ℓ / 2 by ring,
      show u - -(ℓ / 2 + r) - ℓ - r = u - ℓ / 2 by ring]
    ring
  have hT := SpacingScaleHarmonicAnalysis.levyEnergy_translate
    (g := fun v => ε * g v + g (v - ℓ)) (-(ℓ / 2 + r))
  rw [hF, hT, hε', htr, hmix, hε2, hgφ]
  ring

/-- The cross term of two sites: `|X| ≤ 2ω(ℓ − 2r)(2r)²`. -/
theorem abs_atomCrossTerm_siteBump_le {ℓ r : ℝ} (hr : 0 < r) (hrℓ : 2 * r < ℓ) :
    |SpacingScaleHarmonicAnalysis.atomCrossTerm (fun u => siteBump r hr (u - r)) ℓ| ≤
      2 * archLevyDensity (ℓ - 2 * r) * (2 * r) ^ 2 := by
  set g : ℝ → ℝ := fun u => siteBump r hr (u - r)
  have hg : ContDiff ℝ 2 g := (siteBump r hr).contDiff.comp (contDiff_id.sub contDiff_const)
  have hgsupp : ∀ u, u ∉ Icc 0 (2 * r) → g u = 0 := siteBump_shift_vanish hr
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * r)) hgsupp
  have h := SpacingScaleHarmonicAnalysis.abs_crossTerm_sub_le hg.continuous hgc hgsupp
    (by linarith) hrℓ
  set X := SpacingScaleHarmonicAnalysis.atomCrossTerm g ℓ
  have habs : (∫ u, |g u|) = ∫ u, siteBump r hr u := by
    rw [integral_sub_right_eq_self (μ := volume) (fun u => |siteBump r hr u|) r]
    exact integral_congr_ae (Eventually.of_forall fun u => abs_of_nonneg (siteBump_nonneg hr u))
  set A := ∫ u, |g u|
  have hA : A ≤ 2 * r := habs ▸ integral_siteBump_le hr
  have hA0 : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hI : |∫ u, g u| ≤ A := abs_integral_le_integral_abs
  have hsq : (∫ u, g u) ^ 2 ≤ A ^ 2 := by
    nlinarith [abs_nonneg (∫ u, g u), sq_abs (∫ u, g u)]
  have hℓ0 : 0 < ℓ := by linarith
  have hω1 : archLevyDensity ℓ ≤ archLevyDensity (ℓ - 2 * r) :=
    SpacingScaleHarmonicAnalysis.archLevyDensity_antitoneOn (show ℓ - 2 * r ∈ Ioi (0 : ℝ) by
      simp only [mem_Ioi]; linarith) (show ℓ ∈ Ioi (0 : ℝ) from hℓ0) (by linarith)
  have hω0 : 0 ≤ archLevyDensity ℓ := (archLevyDensity_pos hℓ0).le
  have hω2 : 0 ≤ archLevyDensity (ℓ + 2 * r) := (archLevyDensity_pos (by linarith)).le
  have hA2 : A ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have t1 : archLevyDensity ℓ * (∫ u, g u) ^ 2 ≤ archLevyDensity (ℓ - 2 * r) * A ^ 2 :=
    mul_le_mul hω1 hsq (sq_nonneg _) (hω0.trans hω1)
  have t2 : 0 ≤ archLevyDensity ℓ * (∫ u, g u) ^ 2 := mul_nonneg hω0 (sq_nonneg _)
  have t3 : archLevyDensity (ℓ - 2 * r) * A ^ 2 ≤ archLevyDensity (ℓ - 2 * r) * (2 * r) ^ 2 :=
    mul_le_mul_of_nonneg_left hA2 (hω0.trans hω1)
  have t4 : 0 ≤ archLevyDensity (ℓ + 2 * r) * A ^ 2 := mul_nonneg hω2 (sq_nonneg _)
  have h' := abs_sub_abs_le_abs_sub X (archLevyDensity ℓ * (∫ u, g u) ^ 2)
  rw [abs_of_nonneg t2] at h'
  nlinarith

/-! ### The outer constant -/

/-- **The entry constant is one.** For an acting `n₀` there are `δ₀ > 0` and `B` such that on every
window with sliver `δ = 2c − log n₀ ≤ δ₀`, every `λ ∈ 𝒜(c)` has `|λ(n₀)| ≤ √n₀(log(1/δ) + B)`. -/
theorem abs_calibration_coord_le_log_add {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    ∃ δ₀ B : ℝ, 0 < δ₀ ∧ ∀ c : ℝ, Real.log n₀ < 2 * c → 2 * c - Real.log n₀ ≤ δ₀ →
      ∀ lam ∈ calibration c,
        |lam n₀| ≤ Real.sqrt n₀ * (Real.log (1 / (2 * c - Real.log n₀)) + B) := by
  obtain ⟨g, hg0, hg⟩ := exists_log_gap n₀ hn₀
  obtain ⟨K, hK0, hK⟩ := levyEnergy_siteBump_le_mass
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log n₀ :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn₀)
  set m₁ := ∫ x, siteBump 1 one_pos x ^ 2
  have hm₁ : 0 < m₁ := integral_siteBump_sq_pos one_pos
  set C₀ := SpacingScaleHarmonicAnalysis.selfEnergyConstant
  set Ch := Real.cosh ((Real.log n₀ + 1) / 4)
  set ω₀ := archLevyDensity (Real.log 2 / 2)
  have hω₀ : 0 ≤ ω₀ := (archLevyDensity_pos (by positivity)).le
  refine ⟨min g (min (Real.log 2) 1),
    Real.log 2 + C₀ + (4 * Real.exp (1 / 2) * K + 8 * ω₀ + 16 * Ch ^ 2) / m₁,
    lt_min hg0 (lt_min hl2 one_pos), fun c hc hδ lam hlam => ?_⟩
  set δ := 2 * c - Real.log n₀ with hδdef
  have hδ0 : 0 < δ := by linarith
  have hδg : δ ≤ g := hδ.trans (min_le_left _ _)
  have hδ2 : δ ≤ Real.log 2 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  set r := δ / 4
  have hr : 0 < r := by positivity
  have hrg : 2 * r ≤ g := by simp only [r]; linarith
  have hr2 : 2 * r ≤ Real.log 2 := by simp only [r]; linarith
  have hrc : Real.log n₀ / 2 + r ≤ c := by simp only [r]; linarith
  have hrhalf : r ≤ 1 / 2 := by simp only [r]; linarith
  have hr1 : r ≤ 1 := by linarith
  have hrℓ : 2 * r < Real.log n₀ := by simp only [r]; linarith
  have hr4 : 2 * r ≤ Real.log 2 / 2 := by simp only [r]; linarith
  have hm : ∫ t, siteBump r hr t ^ 2 = r * m₁ := integral_siteBump_sq_eq hr
  have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have hc0 : 0 < c := by linarith
  set Q' := 8 * Real.exp (1 / 2) * K + 16 * ω₀ * r + 32 * Ch ^ 2 * r
  -- the energy bound for both signs
  have hA : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (weilFullFunctional (fun _ => 0)
        (EF.weilTest (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ))
          (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ)))).re ≤
        2 * (Real.log (1 / (2 * r)) + C₀) * (r * m₁) + r * Q' := by
    intro ε hε
    have hε2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    set F := twoSiteTestAt (Real.log n₀) r hr ε
    rw [archPolar_twoSite_eq hn₀ hr hg hrg hr2 ε]
    have hJ := levyEnergy_twoSite_eq hr hrℓ hε
    have hX := abs_atomCrossTerm_siteBump_le hr hrℓ
    set X := SpacingScaleHarmonicAnalysis.atomCrossTerm (fun u => siteBump r hr (u - r))
      (Real.log n₀)
    have hω : archLevyDensity (Real.log n₀ - 2 * r) ≤ ω₀ :=
      SpacingScaleHarmonicAnalysis.archLevyDensity_antitoneOn
        (show Real.log 2 / 2 ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; positivity)
        (show Real.log n₀ - 2 * r ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith) (by linarith)
    have hX' : |X| ≤ 8 * ω₀ * r ^ 2 := by
      have := mul_le_mul_of_nonneg_right hω (sq_nonneg (2 * r))
      linarith
    have hεX : -(2 * ε * X) ≤ 2 * |X| := by
      rcases hε with h | h <;> rw [h]
      · linarith [neg_abs_le X]
      · linarith [le_abs_self X]
    have hφ := hK r hr hrhalf
    rw [hm] at hφ
    have hF1 := integral_abs_twoSite_le (Real.log n₀) hr hε2
    have hsupp : SpacingScaleHarmonicAnalysis.SupportedIn c F := fun u hu => by
      have h := tsupport_twoSiteTestAt_subset (Real.log_nonneg (by exact_mod_cast
        (by omega : 1 ≤ n₀))) hr ε hrc
      by_contra hne
      have hmem : u ∈ tsupport (fun u => (F u : ℂ)) := subset_tsupport _ (by simpa using hne)
      have := h hmem
      exact absurd (abs_le.mpr ⟨this.1, this.2⟩) (not_le.mpr hu)
    have hC := SpacingScaleHarmonicAnalysis.abs_moment_le (contDiff_twoSiteTestAt _ hr ε).continuous
      (hasCompactSupport_twoSiteTestAt _ hr ε) hsupp (φ := fun u => Real.cosh (u / 2))
      (by fun_prop) fun u hu => SpacingScaleHarmonicAnalysis.abs_cosh_half_le hu
    have hCh : Real.cosh (c / 2) ≤ Ch := by
      rw [Real.cosh_le_cosh, abs_of_pos (by linarith), abs_of_pos (by
        have : 0 ≤ Real.log n₀ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n₀))
        linarith)]
      linarith
    have hcosh : coshHalfMoment F ^ 2 ≤ 16 * Ch ^ 2 * r ^ 2 := by
      have h1 : |coshHalfMoment F| ≤ Ch * (4 * r) := by
        refine (show |coshHalfMoment F| ≤ Real.cosh (c / 2) * ∫ u, |F u| from hC).trans ?_
        exact mul_le_mul hCh hF1 (integral_nonneg fun _ => abs_nonneg _) (by positivity)
      have h0 := abs_nonneg (coshHalfMoment F)
      nlinarith [sq_abs (coshHalfMoment F)]
    have hθ : 2 * gammaHardyPhaseRate 0 * (∫ u, F u ^ 2) ≤ 0 := by
      have hθ0 := gammaHardyPhaseRate_zero_neg
      have hM0 : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun _ => sq_nonneg _
      nlinarith [mul_nonneg (neg_nonneg.mpr hθ0.le) hM0]
    have hQ : 2 * (4 * Real.exp (1 / 2) * K * r) + 2 * (8 * ω₀ * r ^ 2) +
        2 * (16 * Ch ^ 2 * r ^ 2) = r * Q' := by simp only [Q']; ring
    have hS := sq_nonneg (sinhHalfMoment F)
    linarith
  have hplus := twoSite_reading hn₀ hr hg hrg hr2 hrc hlam 1
  have hminus := twoSite_reading hn₀ hr hg hrg hr2 hrc hlam (-1)
  have hAplus := hA 1 (Or.inl rfl)
  have hAminus := hA (-1) (Or.inr rfl)
  rw [hm] at hplus hminus
  set L := Real.log (1 / δ)
  have hlog : Real.log (1 / (2 * r)) = Real.log 2 + L := by
    rw [show 1 / (2 * r) = 2 * (1 / δ) by simp only [r]; field_simp; ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hpos : 0 < 2 * (r * m₁) / Real.sqrt n₀ := by positivity
  have hw : |lam n₀| * (2 * (r * m₁) / Real.sqrt n₀) ≤
      2 * (Real.log (1 / (2 * r)) + C₀) * (r * m₁) + r * Q' := by
    rcases abs_cases (lam n₀) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have h1 : |lam n₀| ≤ (2 * (Real.log (1 / (2 * r)) + C₀) * (r * m₁) + r * Q') /
      (2 * (r * m₁) / Real.sqrt n₀) :=
    (le_div_iff₀ hpos).mpr hw
  have h2 : (2 * (Real.log (1 / (2 * r)) + C₀) * (r * m₁) + r * Q') /
      (2 * (r * m₁) / Real.sqrt n₀) =
      Real.sqrt n₀ * ((Real.log (1 / (2 * r)) + C₀) + Q' / (2 * m₁)) := by
    field_simp
  have h3 : Q' / (2 * m₁) ≤ (4 * Real.exp (1 / 2) * K + 8 * ω₀ + 16 * Ch ^ 2) / m₁ := by
    rw [div_le_div_iff₀ (by positivity) hm₁]
    simp only [Q']
    have hCh0 : 0 ≤ Ch ^ 2 := sq_nonneg _
    have t1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 hω₀) hm₁.le
    have t2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 hCh0) hm₁.le
    linarith
  rw [h2] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hsq.le)
  rw [hlog]
  linarith

/-- **The sharp two-sided entry law.** For an acting `n₀` there are `δ₀ > 0` and `B` such that on
every window with sliver `δ ≤ δ₀` and for all weights with Lévy margin `η`, the stage fibre contains
the interval of radius `√n₀η(½log(1/δ) − ¼)` about `λ(n₀)` and lies in the interval of radius
`√n₀(log(1/δ) + B)` about `0`. -/
theorem stageFibre_sharp {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    ∃ δ₀ B : ℝ, 0 < δ₀ ∧ ∀ c : ℝ, Real.log n₀ < 2 * c → 2 * c - Real.log n₀ ≤ δ₀ →
      ∀ (η : ℝ) (lam : ℕ → ℝ), 0 ≤ η →
      (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c →
        η * levyEnergy f ≤
          (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) →
      Icc (lam n₀ - Real.sqrt n₀ * η *
            (Real.log (1 / (2 * c - Real.log n₀)) / 2 - 1 / 4))
          (lam n₀ + Real.sqrt n₀ * η *
            (Real.log (1 / (2 * c - Real.log n₀)) / 2 - 1 / 4)) ⊆
        {t | withWeight lam n₀ t ∈ calibration c} ∧
      {t | withWeight lam n₀ t ∈ calibration c} ⊆
        Icc (-(Real.sqrt n₀ * (Real.log (1 / (2 * c - Real.log n₀)) + B)))
          (Real.sqrt n₀ * (Real.log (1 / (2 * c - Real.log n₀)) + B)) := by
  obtain ⟨δ₀, B, hδ₀, hout⟩ := abs_calibration_coord_le_log_add hn₀
  refine ⟨min δ₀ 1, B, lt_min hδ₀ one_pos, fun c hc hδ η lam hη hmargin => ⟨?_, ?_⟩⟩
  · intro t ht
    rw [mem_setOf_eq, ← realCalibration_eq_calibration]
    have hsq : 0 ≤ Real.sqrt n₀ := Real.sqrt_nonneg _
    have hab : |t - lam n₀| ≤
        Real.sqrt n₀ * η * (Real.log (1 / (2 * c - Real.log n₀)) / 2 - 1 / 4) :=
      abs_sub_le_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine withWeight_mem_realCalibration_of_margin hn₀ hc hη hmargin (hab.trans ?_)
    exact mul_le_mul_of_nonneg_left
      (levyTail_ge_half_log (by linarith) (hδ.trans (min_le_right _ _))) (mul_nonneg hsq hη)
  · intro t ht
    have h := hout c hc (hδ.trans (min_le_left _ _)) _ ht
    rw [withWeight, Function.update_self] at h
    exact abs_le.mp h

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
