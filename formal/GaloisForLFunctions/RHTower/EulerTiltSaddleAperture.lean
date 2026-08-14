import GaloisForLFunctions.RHTower.EulerTiltSaddle
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

/-!
# The canonical cofinal aperture and the saddle tilt

At physical scale `x = e^{-L}` the canonical cofinal aperture is `Y = 2L/x = 2L e^{L}`, whose
logarithm is exactly `ℓ = L + log L + log 2`.  The tilt equation `μ(1+δ, Y) = log((1+δ)/x)` then
has exactly one solution in `(0, 1]` for all large `L`, and that solution obeys

```text
δ = 2(ℓ - L)/ℓ² + O(1/ℓ² + (ℓ - L)²/ℓ³),
```

which is the source-faithful central tilt.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The canonical cofinal aperture attached to the physical scale `x = e^{-L}`. -/
def cofinalAperture (L : ℝ) : ℝ := 2 * L * Real.exp L

/-- The logarithmic width of the aperture over the physical scale. -/
def cofinalApertureWidth (L : ℝ) : ℝ := Real.log 2 + Real.log L

theorem cofinalAperture_pos {L : ℝ} (hL : 0 < L) : 0 < cofinalAperture L := by
  rw [cofinalAperture]
  positivity

theorem log_cofinalAperture {L : ℝ} (hL : 0 < L) :
    Real.log (cofinalAperture L) = cofinalApertureWidth L + L := by
  rw [cofinalAperture, cofinalApertureWidth,
    Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos L)),
    Real.log_mul (by norm_num) (ne_of_gt hL), Real.log_exp]

theorem two_le_cofinalAperture {L : ℝ} (hL : 1 ≤ L) : 2 ≤ cofinalAperture L := by
  have h1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp (by linarith)
  rw [cofinalAperture]
  nlinarith

theorem log_inv_exp_neg (L : ℝ) : Real.log (1 / Real.exp (-L)) = L := by
  rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]

/-! ## Continuity of the saddle defect -/

theorem continuous_eulerTiltMeanEnergy_shift (Y : ℝ) :
    Continuous (fun δ : ℝ => eulerTiltMeanEnergy (1 + δ) Y) := by
  have hfun : (fun δ : ℝ => eulerTiltMeanEnergy (1 + δ) Y)
      = fun δ : ℝ => ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
        (p : ℝ) ^ (-(1 + δ)) * Real.log p / (1 + (p : ℝ) ^ (-(1 + δ))) := rfl
  rw [hfun]
  refine continuous_finsetSum _ fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hbase : Continuous (fun δ : ℝ => (p : ℝ) ^ (-(1 + δ))) :=
    (Real.continuous_const_rpow (ne_of_gt hp0)).comp (by fun_prop)
  have hden : ∀ δ : ℝ, (1 : ℝ) + (p : ℝ) ^ (-(1 + δ)) ≠ 0 := by
    intro δ
    have h : (0 : ℝ) < (p : ℝ) ^ (-(1 + δ)) := Real.rpow_pos_of_pos hp0 _
    linarith
  exact (hbase.mul continuous_const).div (continuous_const.add hbase) hden

theorem continuousOn_eulerTiltSaddleDefect {Y x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun δ : ℝ => eulerTiltSaddleDefect δ Y x) (Ici 0) := by
  have hcentre : ContinuousOn (fun δ : ℝ => Real.log ((1 + δ) / x)) (Ici 0) := by
    intro δ hδ
    have hδ0 : (0 : ℝ) ≤ δ := hδ
    have hpos : (0 : ℝ) < (1 + δ) / x := div_pos (by linarith) hx
    refine ContinuousAt.continuousWithinAt ?_
    have hinner : ContinuousAt (fun t : ℝ => (1 + t) / x) δ := by
      have h1 : ContinuousAt (fun t : ℝ => 1 + t) δ := by fun_prop
      exact h1.div_const x
    exact hinner.log (ne_of_gt hpos)
  exact ((continuous_eulerTiltMeanEnergy_shift Y).continuousOn).sub hcentre

/-! ## Two-sided bounds on the saddle defect -/

theorem saddleDefect_le {δ L : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hL : 1 ≤ L) :
    eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L))
      ≤ cofinalApertureWidth L - δ * Real.log (cofinalAperture L) ^ 2 / 2
        + δ ^ 2 * Real.log (cofinalAperture L) ^ 3 / 6 + eulerTiltEnergyConst := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hY := two_le_cofinalAperture hL
  have hx : (0 : ℝ) < Real.exp (-L) := Real.exp_pos _
  have hlaw := abs_eulerTiltMeanEnergy_sub_expansion_le (Y := cofinalAperture L) hδ0 hδ1 hY
  have hcentre : Real.log ((1 + δ) / Real.exp (-L))
      = Real.log (1 + δ) + L := by
    rw [Real.log_div (by linarith) (ne_of_gt hx), Real.log_exp]
    ring
  have hlogδ : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  have hwidth : Real.log (cofinalAperture L) = cofinalApertureWidth L + L :=
    log_cofinalAperture hL0
  have hb := abs_le.mp hlaw
  rw [eulerTiltSaddleDefect, hcentre]
  nlinarith [hb.1, hb.2, hlogδ, hwidth]

theorem le_saddleDefect {δ L : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hL : 1 ≤ L) :
    cofinalApertureWidth L - δ * Real.log (cofinalAperture L) ^ 2 / 2
        - δ ^ 2 * Real.log (cofinalAperture L) ^ 3 / 6 - (eulerTiltEnergyConst + 1)
      ≤ eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hY := two_le_cofinalAperture hL
  have hx : (0 : ℝ) < Real.exp (-L) := Real.exp_pos _
  have hlaw := abs_eulerTiltMeanEnergy_sub_expansion_le (Y := cofinalAperture L) hδ0 hδ1 hY
  have hcentre : Real.log ((1 + δ) / Real.exp (-L))
      = Real.log (1 + δ) + L := by
    rw [Real.log_div (by linarith) (ne_of_gt hx), Real.log_exp]
    ring
  have hlogδ1 : Real.log (1 + δ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + δ by linarith)
    linarith
  have hwidth : Real.log (cofinalAperture L) = cofinalApertureWidth L + L :=
    log_cofinalAperture hL0
  have hb := abs_le.mp hlaw
  rw [eulerTiltSaddleDefect, hcentre]
  nlinarith [hb.1, hb.2, hlogδ1, hwidth]

/-! ## Existence and uniqueness of the saddle tilt -/

/-- **The tilt equation has exactly one solution** once the aperture is wide enough. -/
theorem exists_unique_saddle_root {L : ℝ} (hL : 1 ≤ L)
    (hwidth : 0 < cofinalApertureWidth L)
    (h1 : 4 * cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2 ≤ 1)
    (h2 : (eulerTiltEnergyConst + 1)
        + cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L))
      < cofinalApertureWidth L / 2)
    (h3 : 16 * cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L))
        + eulerTiltEnergyConst < cofinalApertureWidth L) :
    ∃! δ : ℝ, δ ∈ Ioc (0 : ℝ) 1
      ∧ eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) = 0 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hY := two_le_cofinalAperture hL
  have hx : (0 : ℝ) < Real.exp (-L) := Real.exp_pos _
  set A := cofinalApertureWidth L with hA
  set ℓ := Real.log (cofinalAperture L) with hℓ
  have hℓpos : 0 < ℓ := by
    rw [hℓ]
    exact Real.log_pos (by linarith)
  set dLow := A / ℓ ^ 2 with hdLow
  set dHigh := 4 * A / ℓ ^ 2 with hdHigh
  have hdLow0 : 0 < dLow := by
    rw [hdLow]
    positivity
  have hdHighle : dHigh ≤ 1 := by
    rw [hdHigh]
    exact h1
  have hdLowlt : dLow < dHigh := by
    rw [hdLow, hdHigh]
    have hden : (0 : ℝ) < ℓ ^ 2 := by positivity
    rw [div_lt_div_iff_of_pos_right hden]
    linarith
  have hdHigh0 : 0 < dHigh := lt_trans hdLow0 hdLowlt
  have hdLowle : dLow ≤ 1 := le_trans hdLowlt.le hdHighle
  -- the defect is positive at the lower endpoint
  have hpos : 0 < eulerTiltSaddleDefect dLow (cofinalAperture L) (Real.exp (-L)) := by
    have hlow := le_saddleDefect hdLow0 hdLowle hL
    have hval : A - dLow * ℓ ^ 2 / 2 - dLow ^ 2 * ℓ ^ 3 / 6 - (eulerTiltEnergyConst + 1)
        = A / 2 - A ^ 2 / (6 * ℓ) - (eulerTiltEnergyConst + 1) := by
      rw [hdLow]
      field_simp
      ring
    rw [hval] at hlow
    linarith [h2]
  -- the defect is negative at the upper endpoint
  have hneg : eulerTiltSaddleDefect dHigh (cofinalAperture L) (Real.exp (-L)) < 0 := by
    have hup := saddleDefect_le hdHigh0 hdHighle hL
    have hval : A - dHigh * ℓ ^ 2 / 2 + dHigh ^ 2 * ℓ ^ 3 / 6 + eulerTiltEnergyConst
        = -A + 16 * A ^ 2 / (6 * ℓ) + eulerTiltEnergyConst := by
      rw [hdHigh]
      field_simp
      ring
    rw [hval] at hup
    linarith [h3]
  -- intermediate value
  have hcont : ContinuousOn (fun δ : ℝ => eulerTiltSaddleDefect δ (cofinalAperture L)
      (Real.exp (-L))) (Icc dLow dHigh) :=
    (continuousOn_eulerTiltSaddleDefect hx).mono (fun t ht => le_trans hdLow0.le ht.1)
  have hmem : (0 : ℝ) ∈ Icc (eulerTiltSaddleDefect dHigh (cofinalAperture L) (Real.exp (-L)))
      (eulerTiltSaddleDefect dLow (cofinalAperture L) (Real.exp (-L))) := ⟨hneg.le, hpos.le⟩
  obtain ⟨δ, hδmem, hδroot⟩ := intermediate_value_Icc' hdLowlt.le hcont hmem
  refine ⟨δ, ⟨⟨lt_of_lt_of_le hdLow0 hδmem.1, le_trans hδmem.2 hdHighle⟩, hδroot⟩, ?_⟩
  rintro δ' ⟨⟨hδ'0, hδ'1⟩, hδ'root⟩
  exact eulerTiltSaddleDefect_injOn hY hx hδ'0.le
    (lt_of_lt_of_le hdLow0 hδmem.1).le hδ'root hδroot

/-! ## The saddle expansion -/

/-- **The source-faithful central tilt.**  Any solution of the tilt equation in `(0,1]` satisfies
`δ = 2(ℓ - L)/ℓ² + O(1/ℓ² + (ℓ - L)²/ℓ³)`. -/
theorem abs_saddle_root_sub_expansion_le {δ L : ℝ} (hL : 1 ≤ L)
    (hwidth : 0 < cofinalApertureWidth L)
    (h1 : 4 * cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2 ≤ 1)
    (h3 : 16 * cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L))
        + eulerTiltEnergyConst < cofinalApertureWidth L)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hroot : eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) = 0) :
    |δ - 2 * cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2|
      ≤ 2 * (eulerTiltEnergyConst + 1) / Real.log (cofinalAperture L) ^ 2
        + 16 * cofinalApertureWidth L ^ 2 / (3 * Real.log (cofinalAperture L) ^ 3) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hY := two_le_cofinalAperture hL
  have hx : (0 : ℝ) < Real.exp (-L) := Real.exp_pos _
  set A := cofinalApertureWidth L with hA
  set ℓ := Real.log (cofinalAperture L) with hℓ
  have hℓpos : 0 < ℓ := by
    rw [hℓ]
    exact Real.log_pos (by linarith)
  set dHigh := 4 * A / ℓ ^ 2 with hdHigh
  have hdHigh0 : 0 < dHigh := by
    rw [hdHigh]
    positivity
  have hdHighle : dHigh ≤ 1 := h1
  -- the root is below the upper endpoint
  have hupper : δ < dHigh := by
    by_contra hcon
    rw [not_lt] at hcon
    have hup := saddleDefect_le hdHigh0 hdHighle hL
    have hval : A - dHigh * ℓ ^ 2 / 2 + dHigh ^ 2 * ℓ ^ 3 / 6 + eulerTiltEnergyConst
        = -A + 16 * A ^ 2 / (6 * ℓ) + eulerTiltEnergyConst := by
      rw [hdHigh]
      field_simp
      ring
    rw [hval] at hup
    have hneg : eulerTiltSaddleDefect dHigh (cofinalAperture L) (Real.exp (-L)) < 0 := by
      linarith [h3]
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [heq, hroot] at hneg
      exact absurd hneg (lt_irrefl 0)
    · have hmono := eulerTiltSaddleDefect_strictAnti hY hx hdHigh0.le hlt
      rw [hroot] at hmono
      linarith
  -- the cofactor relation
  have hcof := abs_saddle_sub_cofactor_le hδ0 hδ1 hY hx hroot
  have hlogx : Real.log (1 / Real.exp (-L)) = L := log_inv_exp_neg L
  rw [hlogx] at hcof
  have hwidth' : ℓ - L = A := by
    rw [hℓ, log_cofinalAperture hL0, hA]
    ring
  rw [hwidth'] at hcof
  -- the cubic remainder is controlled by the upper endpoint
  have hcube : δ ^ 2 * ℓ ^ 3 / 6 ≤ 16 * A ^ 2 / (6 * ℓ) := by
    have hsq : δ ^ 2 ≤ dHigh ^ 2 := by nlinarith [hδ0, hupper, hdHigh0]
    have hval : dHigh ^ 2 * ℓ ^ 3 / 6 = 16 * A ^ 2 / (6 * ℓ) := by
      rw [hdHigh]
      field_simp
      ring
    calc δ ^ 2 * ℓ ^ 3 / 6 ≤ dHigh ^ 2 * ℓ ^ 3 / 6 := by
          have : (0 : ℝ) < ℓ ^ 3 / 6 := by positivity
          nlinarith [hsq]
      _ = 16 * A ^ 2 / (6 * ℓ) := hval
  have hC : |δ * ℓ ^ 2 / 2 - A| ≤ (eulerTiltEnergyConst + 1) + 16 * A ^ 2 / (6 * ℓ) := by
    refine le_trans hcof ?_
    linarith [hcube]
  have hℓ2 : (0 : ℝ) < ℓ ^ 2 := by positivity
  have hfac : (0 : ℝ) < 2 / ℓ ^ 2 := by positivity
  have hkey : δ - 2 * A / ℓ ^ 2 = (δ * ℓ ^ 2 / 2 - A) * (2 / ℓ ^ 2) := by
    field_simp
  rw [hkey, abs_mul, abs_of_pos hfac]
  calc |δ * ℓ ^ 2 / 2 - A| * (2 / ℓ ^ 2)
      ≤ ((eulerTiltEnergyConst + 1) + 16 * A ^ 2 / (6 * ℓ)) * (2 / ℓ ^ 2) :=
        mul_le_mul_of_nonneg_right hC hfac.le
    _ = 2 * (eulerTiltEnergyConst + 1) / ℓ ^ 2 + 16 * A ^ 2 / (3 * ℓ ^ 3) := by
        field_simp
        ring

/-! ## The aperture limits -/

theorem tendsto_cofinalApertureWidth : Tendsto cofinalApertureWidth atTop atTop := by
  have h : Tendsto (fun L : ℝ => Real.log 2 + Real.log L) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop (Real.log 2) Real.tendsto_log_atTop
  exact h

theorem tendsto_logPow_div_id (k : ℕ) :
    Tendsto (fun L : ℝ => Real.log L ^ k / L) atTop (nhds 0) := by
  have h := HTGeometry.tendsto_logPow_div_rpow (a := (1 : ℝ)) one_pos k
  refine h.congr fun L => ?_
  rw [Real.rpow_one]

theorem tendsto_widthSq_div_logAperture :
    Tendsto (fun L : ℝ => cofinalApertureWidth L ^ 2 / Real.log (cofinalAperture L)) atTop
      (nhds 0) := by
  have hmaj : Tendsto (fun L : ℝ =>
      2 * Real.log 2 ^ 2 / L + 2 * (Real.log L ^ 2 / L)) atTop (nhds 0) := by
    have h1 : Tendsto (fun L : ℝ => 2 * Real.log 2 ^ 2 / L) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (tendsto_logPow_div_id 2).const_mul (2 : ℝ)
    rw [mul_zero] at h2
    have h := h1.add h2
    rwa [add_zero] at h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hlog : Real.log (cofinalAperture L) = cofinalApertureWidth L + L :=
      log_cofinalAperture hL0
    have hw : 0 ≤ cofinalApertureWidth L := by
      rw [cofinalApertureWidth]
      have : 0 ≤ Real.log L := Real.log_nonneg hL
      have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    rw [hlog]
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hlog : Real.log (cofinalAperture L) = cofinalApertureWidth L + L :=
      log_cofinalAperture hL0
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hw : 0 ≤ cofinalApertureWidth L := by
      rw [cofinalApertureWidth]
      linarith
    have hsq : cofinalApertureWidth L ^ 2 ≤ 2 * Real.log 2 ^ 2 + 2 * Real.log L ^ 2 := by
      rw [cofinalApertureWidth]
      nlinarith [sq_nonneg (Real.log 2 - Real.log L)]
    have hden : L ≤ cofinalApertureWidth L + L := by linarith
    have hdpos : (0 : ℝ) < cofinalApertureWidth L + L := by linarith
    rw [hlog]
    calc cofinalApertureWidth L ^ 2 / (cofinalApertureWidth L + L)
        ≤ (2 * Real.log 2 ^ 2 + 2 * Real.log L ^ 2) / (cofinalApertureWidth L + L) :=
          div_le_div_of_nonneg_right hsq hdpos.le
      _ ≤ (2 * Real.log 2 ^ 2 + 2 * Real.log L ^ 2) / L := by
          refine div_le_div_of_nonneg_left ?_ hL0 hden
          positivity
      _ = 2 * Real.log 2 ^ 2 / L + 2 * (Real.log L ^ 2 / L) := by
          field_simp

theorem tendsto_width_div_logAperture_sq :
    Tendsto (fun L : ℝ => cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2) atTop
      (nhds 0) := by
  have hmaj : Tendsto (fun L : ℝ => Real.log 2 / L + Real.log L / L) atTop (nhds 0) := by
    have h1 : Tendsto (fun L : ℝ => Real.log 2 / L) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := tendsto_logPow_div_id 1
    have h2' : Tendsto (fun L : ℝ => Real.log L / L) atTop (nhds 0) := by
      refine h2.congr fun L => ?_
      rw [pow_one]
    have h := h1.add h2'
    rwa [add_zero] at h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hlog : Real.log (cofinalAperture L) = cofinalApertureWidth L + L :=
      log_cofinalAperture hL0
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hw : 0 ≤ cofinalApertureWidth L := by
      rw [cofinalApertureWidth]
      linarith
    rw [hlog]
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hlog : Real.log (cofinalAperture L) = cofinalApertureWidth L + L :=
      log_cofinalAperture hL0
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hw : 0 ≤ cofinalApertureWidth L := by
      rw [cofinalApertureWidth]
      linarith
    have hdpos : (0 : ℝ) < cofinalApertureWidth L + L := by linarith
    have hsq : L ^ 2 ≤ (cofinalApertureWidth L + L) ^ 2 := by nlinarith
    have hLsq : L ≤ L ^ 2 := by nlinarith
    rw [hlog]
    calc cofinalApertureWidth L / (cofinalApertureWidth L + L) ^ 2
        ≤ cofinalApertureWidth L / L ^ 2 := by
          refine div_le_div_of_nonneg_left hw (by positivity) hsq
      _ ≤ cofinalApertureWidth L / L := by
          refine div_le_div_of_nonneg_left hw hL0 hLsq
      _ = Real.log 2 / L + Real.log L / L := by
          rw [cofinalApertureWidth]
          field_simp

/-! ## The unconditional aperture law -/

theorem eventually_saddle_conditions :
    ∀ᶠ L in atTop, 1 ≤ L ∧ 0 < cofinalApertureWidth L
      ∧ 4 * cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2 ≤ 1
      ∧ (eulerTiltEnergyConst + 1)
          + cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L))
        < cofinalApertureWidth L / 2
      ∧ 16 * cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L))
          + eulerTiltEnergyConst < cofinalApertureWidth L := by
  have hA := tendsto_cofinalApertureWidth
  have hq := tendsto_widthSq_div_logAperture
  have hr := tendsto_width_div_logAperture_sq
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hA.eventually_ge_atTop (4 * (|eulerTiltEnergyConst| + 4)),
    hq.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with L hL hAge hqlt hrlt
  have habs : eulerTiltEnergyConst ≤ |eulerTiltEnergyConst| := le_abs_self _
  have habs0 : 0 ≤ |eulerTiltEnergyConst| := abs_nonneg _
  have hwpos : 0 < cofinalApertureWidth L := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogpos : 0 < Real.log (cofinalAperture L) := by
    rw [log_cofinalAperture hL0]
    linarith
  refine ⟨hL, hwpos, ?_, ?_, ?_⟩
  · have h : 4 * (cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2) < 1 := by
      linarith
    calc 4 * cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2
        = 4 * (cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2) := by ring
      _ ≤ 1 := h.le
  · have hsmall : cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L)) < 1 := by
      have hval : cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L))
          = (cofinalApertureWidth L ^ 2 / Real.log (cofinalAperture L)) / 6 := by
        field_simp
      rw [hval]
      linarith
    linarith
  · have hsmall : 16 * cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L)) < 3 := by
      have hval : 16 * cofinalApertureWidth L ^ 2 / (6 * Real.log (cofinalAperture L))
          = 16 * (cofinalApertureWidth L ^ 2 / Real.log (cofinalAperture L)) / 6 := by
        field_simp
      rw [hval]
      linarith
    linarith

/-- **The source-faithful central tilt.**  For every sufficiently wide canonical aperture the tilt
equation has exactly one solution in `(0,1]`, and it equals `2(ℓ - L)/ℓ²` up to
`O(1/ℓ² + (ℓ - L)²/ℓ³)`. -/
theorem eventually_saddle_root_expansion :
    ∀ᶠ L in atTop,
      (∃! δ : ℝ, δ ∈ Ioc (0 : ℝ) 1
        ∧ eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) = 0)
      ∧ ∀ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
          eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) = 0 →
          |δ - 2 * cofinalApertureWidth L / Real.log (cofinalAperture L) ^ 2|
            ≤ 2 * (eulerTiltEnergyConst + 1) / Real.log (cofinalAperture L) ^ 2
              + 16 * cofinalApertureWidth L ^ 2 / (3 * Real.log (cofinalAperture L) ^ 3) := by
  filter_upwards [eventually_saddle_conditions] with L hcond
  obtain ⟨hL, hw, h1, h2, h3⟩ := hcond
  exact ⟨exists_unique_saddle_root hL hw h1 h2 h3,
    fun δ hδ hroot => abs_saddle_root_sub_expansion_le hL hw h1 h3 hδ.1 hδ.2 hroot⟩

end

end RHTower
