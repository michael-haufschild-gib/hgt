import GaloisForLFunctions.HTGeometry.PoissonSuperpositionSaturationProperness
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet

/-!
# The reflected prime history reserve

The reflected odds `p^{t-1}` and `p^{-t-1}` of a prime give two Poisson formation rates whose
Boolean occupancy reports are exactly the adaptive reflected Bernoulli laws.  The information
erased by Boolean support projection is the vertical history reserve.  This module computes its
sharp small-odds asymptotic `t (log p) p^{-2(1-t)}` and the exact all-prime summability threshold
at half aperture.
-/

namespace GaloisForLFunctions.HTGeometry

open Real Filter Topology
open scoped NNReal ENNReal

noncomputable section

/-! ## A two-sided cubic sandwich for `log (1 + x)` -/

/-- `log (1 + x) > x - x²/2` for `x > 0`. -/
theorem log_one_add_gt_quadratic {x : ℝ} (hx : 0 < x) : x - x ^ 2 / 2 < Real.log (1 + x) := by
  have key : StrictMonoOn (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) (Set.Ici (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · refine ContinuousOn.add (ContinuousOn.sub ?_ continuousOn_id) (by fun_prop)
      refine ContinuousOn.log (by fun_prop) fun t ht => ?_
      simp only [Set.mem_Ici] at ht
      linarith
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      have ht1 : (0 : ℝ) < 1 + t := by linarith
      have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹ * 1) t :=
        (Real.hasDerivAt_log ht1.ne').comp t (by simpa using (hasDerivAt_id t).const_add (1 : ℝ))
      have h3 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 : ℝ) * t ^ 1 / 2) t := by
        simpa using (hasDerivAt_pow 2 t).div_const 2
      have hd : HasDerivAt (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
          ((1 + t)⁻¹ * 1 - 1 + (2 : ℝ) * t ^ 1 / 2) t :=
        (h2.sub (hasDerivAt_id t)).add h3
      rw [hd.deriv, show (1 + t)⁻¹ * 1 - 1 + (2 : ℝ) * t ^ 1 / 2 = t ^ 2 / (1 + t) from by
        field_simp; ring]
      positivity
  have := key Set.self_mem_Ici (Set.mem_Ici.2 hx.le) hx
  norm_num at this
  linarith

/-- `log (1 + x) < x - x²/2 + x³/3` for `x > 0`. -/
theorem log_one_add_lt_cubic {x : ℝ} (hx : 0 < x) :
    Real.log (1 + x) < x - x ^ 2 / 2 + x ^ 3 / 3 := by
  have key : StrictMonoOn (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t))
      (Set.Ici (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · refine ContinuousOn.sub (by fun_prop) ?_
      refine ContinuousOn.log (by fun_prop) fun t ht => ?_
      simp only [Set.mem_Ici] at ht
      linarith
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      have ht1 : (0 : ℝ) < 1 + t := by linarith
      have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹ * 1) t :=
        (Real.hasDerivAt_log ht1.ne').comp t (by simpa using (hasDerivAt_id t).const_add (1 : ℝ))
      have h3 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 : ℝ) * t ^ 1 / 2) t := by
        simpa using (hasDerivAt_pow 2 t).div_const 2
      have h4 : HasDerivAt (fun t : ℝ => t ^ 3 / 3) ((3 : ℝ) * t ^ 2 / 3) t := by
        simpa using (hasDerivAt_pow 3 t).div_const 3
      have hd : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t))
          (1 - (2 : ℝ) * t ^ 1 / 2 + (3 : ℝ) * t ^ 2 / 3 - (1 + t)⁻¹ * 1) t :=
        (((hasDerivAt_id t).sub h3).add h4).sub h2
      rw [hd.deriv, show 1 - (2 : ℝ) * t ^ 1 / 2 + (3 : ℝ) * t ^ 2 / 3 - (1 + t)⁻¹ * 1
          = t ^ 3 / (1 + t) from by field_simp; ring]
      positivity
  have := key Set.self_mem_Ici (Set.mem_Ici.2 hx.le) hx
  norm_num at this
  linarith

/-! ## The occupancy defect -/

/-- Poisson formation rate attached to an odds parameter. -/
def oddsRate (x : ℝ) : ℝ := Real.log (1 + x)

/-- Boolean occupancy attached to an odds parameter. -/
def oddsOccupancy (x : ℝ) : ℝ := x / (1 + x)

/-- The occupancy defect: rate minus occupancy. -/
def oddsDefect (x : ℝ) : ℝ := oddsRate x - oddsOccupancy x

theorem oddsDefect_bounds {x : ℝ} (hx : 0 < x) :
    x ^ 2 * (1 / (1 + x) - 1 / 2) < oddsDefect x ∧
      oddsDefect x < x ^ 2 * (1 / (1 + x) - 1 / 2 + x / 3) := by
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  have hocc : oddsOccupancy x = x - x ^ 2 / (1 + x) := by
    rw [oddsOccupancy]
    field_simp
    ring
  have hl := log_one_add_gt_quadratic hx
  have hu := log_one_add_lt_cubic hx
  rw [oddsDefect, oddsRate, hocc]
  constructor
  · have : x ^ 2 * (1 / (1 + x) - 1 / 2) = (x - x ^ 2 / 2) - (x - x ^ 2 / (1 + x)) := by
      field_simp
      ring
    rw [this]
    linarith
  · have : x ^ 2 * (1 / (1 + x) - 1 / 2 + x / 3)
        = (x - x ^ 2 / 2 + x ^ 3 / 3) - (x - x ^ 2 / (1 + x)) := by
      field_simp
      ring
    rw [this]
    linarith

theorem oddsDefect_div_sq_bounds {x : ℝ} (hx : 0 < x) :
    1 / (1 + x) - 1 / 2 < oddsDefect x / x ^ 2 ∧
      oddsDefect x / x ^ 2 < 1 / (1 + x) - 1 / 2 + x / 3 := by
  obtain ⟨h1, h2⟩ := oddsDefect_bounds hx
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hx2]
    linarith [h1]
  · rw [div_lt_iff₀ hx2]
    linarith [h2]

theorem oddsDefect_div_sq_nonneg_le_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ oddsDefect x / x ^ 2 ∧ oddsDefect x / x ^ 2 ≤ 1 := by
  obtain ⟨h1, h2⟩ := oddsDefect_div_sq_bounds hx
  have hden : (0 : ℝ) < 1 + x := by linarith
  have hlow : (0 : ℝ) ≤ 1 / (1 + x) - 1 / 2 := by
    rw [sub_nonneg, div_le_div_iff₀ (by norm_num) hden]
    linarith
  have hhigh : 1 / (1 + x) - 1 / 2 + x / 3 ≤ 1 := by
    have : 1 / (1 + x) ≤ 1 := by
      rw [div_le_one hden]
      linarith
    linarith
  exact ⟨by linarith, by linarith⟩

/-! ## The logarithmic shape factor -/

/-- The shape factor `log (1 + x) / x`. -/
def oddsShape (x : ℝ) : ℝ := oddsRate x / x

theorem abs_log_oddsShape_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (oddsShape x)| ≤ x := by
  have hx1' : (0 : ℝ) < 1 + x := by linarith
  have hup : Real.log (1 + x) < x := by
    have := Real.add_one_le_exp (Real.log (1 + x))
    have hexp : Real.exp (Real.log (1 + x)) = 1 + x := Real.exp_log hx1'
    rw [hexp] at this
    rcases lt_or_eq_of_le this with h | h
    · linarith
    · exfalso
      have hlt := log_one_add_lt_cubic hx
      nlinarith [log_one_add_gt_quadratic hx]
  have hlow : 1 - x / 2 < oddsShape x := by
    rw [oddsShape, oddsRate, lt_div_iff₀ hx]
    nlinarith [log_one_add_gt_quadratic hx]
  have hshapeUp : oddsShape x < 1 := by
    rw [oddsShape, oddsRate, div_lt_one hx]
    exact hup
  have hpos : 0 < oddsShape x := by
    rw [oddsShape, oddsRate]
    exact div_pos (Real.log_pos (by linarith)) hx
  have hlogneg : Real.log (oddsShape x) < 0 := Real.log_neg hpos hshapeUp
  have hhalf : (0 : ℝ) < 1 - x / 2 := by linarith
  have hlogge : -x ≤ Real.log (1 - x / 2) := by
    have h1 : Real.log ((1 - x / 2)⁻¹) ≤ (1 - x / 2)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at h1
    have hmul : (1 - x / 2)⁻¹ * (1 - x / 2) = 1 := inv_mul_cancel₀ hhalf.ne'
    have hinvpos : (0 : ℝ) < (1 - x / 2)⁻¹ := inv_pos.2 hhalf
    have h3 : (1 - x / 2)⁻¹ - 1 ≤ x := by nlinarith [hmul, hinvpos]
    linarith
  have := Real.log_le_log hhalf hlow.le
  rw [abs_of_neg hlogneg]
  linarith

/-- The occupancy defect has exact quadratic order `1/2` at zero odds. -/
theorem tendsto_oddsDefect_div_sq :
    Tendsto (fun x : ℝ => oddsDefect x / x ^ 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hc : ContinuousAt (fun x : ℝ => 1 / (1 + x) - 1 / 2) 0 := by
    refine ContinuousAt.sub (ContinuousAt.div continuousAt_const (by fun_prop) ?_)
      continuousAt_const
    norm_num
  have hlow : Tendsto (fun x : ℝ => 1 / (1 + x) - 1 / 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have h : Tendsto (fun x : ℝ => 1 / (1 + x) - 1 / 2) (𝓝[>] (0 : ℝ))
        (𝓝 (1 / (1 + (0 : ℝ)) - 1 / 2)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have hval : 1 / (1 + (0 : ℝ)) - 1 / 2 = 1 / 2 := by norm_num
    rwa [hval] at h
  have hhigh : Tendsto (fun x : ℝ => 1 / (1 + x) - 1 / 2 + x / 3) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have hid : Tendsto (fun x : ℝ => x / 3) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => x / 3) (𝓝 (0 : ℝ)) (𝓝 (0 / 3)) :=
        (continuous_id.div_const 3).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using hlow.add hid
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (oddsDefect_div_sq_bounds hx).1.le
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (oddsDefect_div_sq_bounds hx).2.le

/-! ## The prime history reserve -/

/-- Reflected odds of a prime at aperture `t`. -/
def reflectedOdds (p : Nat.Primes) (t : ℝ) : ℝ := (p : ℝ) ^ (t - 1)

theorem primeReal_pos (p : Nat.Primes) : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos

theorem primeReal_one_lt (p : Nat.Primes) : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt

theorem reflectedOdds_pos (p : Nat.Primes) (t : ℝ) : 0 < reflectedOdds p t :=
  Real.rpow_pos_of_pos (primeReal_pos p) _

theorem reflectedOdds_eq_exp (p : Nat.Primes) (t : ℝ) :
    reflectedOdds p t = Real.exp ((t - 1) * Real.log (p : ℝ)) := by
  rw [reflectedOdds, Real.rpow_def_of_pos (primeReal_pos p)]
  ring_nf

theorem coe_reflectedSourceRate_eq_oddsRate (p : Nat.Primes) (t : ℝ) :
    (reflectedSourceRate p t : ℝ) = oddsRate (reflectedOdds p t) := rfl

/-- The vertical history reserve erased by Boolean support projection. -/
def primeHistoryReserve (p : Nat.Primes) (t : ℝ) : ℝ :=
  hiddenHistoryWork (reflectedSourceRate p t) (reflectedSourceRate p (-t))

/-- **The reserve is the exact Poisson-minus-Boolean information difference.** -/
theorem primeHistoryReserve_eq (p : Nat.Primes) (t : ℝ) :
    primeHistoryReserve p t
      = (oddsRate (reflectedOdds p t) - oddsRate (reflectedOdds p (-t))) *
          Real.log (oddsRate (reflectedOdds p t) / oddsRate (reflectedOdds p (-t)))
        - (oddsOccupancy (reflectedOdds p t) - oddsOccupancy (reflectedOdds p (-t))) *
          Real.log (reflectedOdds p t / reflectedOdds p (-t)) := by
  set a := reflectedOdds p t with ha
  set b := reflectedOdds p (-t) with hb
  have ha0 : 0 < a := reflectedOdds_pos p t
  have hb0 : 0 < b := reflectedOdds_pos p (-t)
  have hA : (reflectedSourceRate p t : ℝ) = Real.log (1 + a) := rfl
  have hB : (reflectedSourceRate p (-t) : ℝ) = Real.log (1 + b) := rfl
  rw [primeHistoryReserve,
    hiddenHistoryWork_eq (reflectedSourceRate_pos p t) (reflectedSourceRate_pos p (-t)),
    hA, hB]
  have hea : Real.exp (Real.log (1 + a)) = 1 + a := Real.exp_log (by linarith)
  have heb : Real.exp (Real.log (1 + b)) = 1 + b := Real.exp_log (by linarith)
  have hnega : Real.exp (-Real.log (1 + a)) = (1 + a)⁻¹ := by
    rw [Real.exp_neg, hea]
  have hnegb : Real.exp (-Real.log (1 + b)) = (1 + b)⁻¹ := by
    rw [Real.exp_neg, heb]
  rw [hea, heb, hnega, hnegb, oddsRate, oddsRate, oddsOccupancy, oddsOccupancy,
    show (1 : ℝ) + a - 1 = a from by ring, show (1 : ℝ) + b - 1 = b from by ring]
  congr 2
  field_simp
  ring

theorem log_reflectedOdds_ratio (p : Nat.Primes) (t : ℝ) :
    Real.log (reflectedOdds p t / reflectedOdds p (-t)) = 2 * t * Real.log (p : ℝ) := by
  rw [reflectedOdds_eq_exp, reflectedOdds_eq_exp, ← Real.exp_sub, Real.log_exp]
  ring

theorem oddsRate_pos {x : ℝ} (hx : 0 < x) : 0 < oddsRate x :=
  Real.log_pos (by linarith)

theorem oddsShape_pos {x : ℝ} (hx : 0 < x) : 0 < oddsShape x :=
  div_pos (oddsRate_pos hx) hx

theorem oddsRate_eq_mul_shape {x : ℝ} (hx : 0 < x) : oddsRate x = x * oddsShape x := by
  rw [oddsShape]
  field_simp

/-- **Split of the reserve** into an occupancy-defect term and a shape-drift term. -/
theorem primeHistoryReserve_split (p : Nat.Primes) (t : ℝ) :
    primeHistoryReserve p t
      = (oddsDefect (reflectedOdds p t) - oddsDefect (reflectedOdds p (-t))) *
          (2 * t * Real.log (p : ℝ))
        + (oddsRate (reflectedOdds p t) - oddsRate (reflectedOdds p (-t))) *
          Real.log (oddsShape (reflectedOdds p t) / oddsShape (reflectedOdds p (-t))) := by
  set a := reflectedOdds p t with hadef
  set b := reflectedOdds p (-t) with hbdef
  have ha0 : 0 < a := reflectedOdds_pos p t
  have hb0 : 0 < b := reflectedOdds_pos p (-t)
  have hsa := oddsShape_pos ha0
  have hsb := oddsShape_pos hb0
  have hsplit : Real.log (oddsRate a / oddsRate b)
      = Real.log (a / b) + Real.log (oddsShape a / oddsShape b) := by
    rw [oddsRate_eq_mul_shape ha0, oddsRate_eq_mul_shape hb0,
      show a * oddsShape a / (b * oddsShape b) = (a / b) * (oddsShape a / oddsShape b) from by
        field_simp,
      Real.log_mul (by positivity) (by positivity)]
  rw [primeHistoryReserve_eq, hsplit, ← log_reflectedOdds_ratio p t, ← hadef, ← hbdef, oddsDefect,
    oddsDefect]
  ring

/-! ## The sharp prime reserve asymptotic -/

theorem tendsto_reflectedOdds_nhdsGT {t : ℝ} (ht1 : t < 1) :
    Tendsto (fun p : Nat.Primes => reflectedOdds p t) cofinite (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Filter.Eventually.of_forall fun p => reflectedOdds_pos p t)
  have hexp : Tendsto (fun p : Nat.Primes => (t - 1) * Real.log (p : ℝ)) cofinite atBot := by
    have hneg : (0 : ℝ) < 1 - t := by linarith
    have h : Tendsto (fun p : Nat.Primes => (1 - t) * Real.log (p : ℝ)) cofinite atTop :=
      Filter.Tendsto.const_mul_atTop hneg tendsto_primeRealLog_cofinite_atTop
    refine (tendsto_neg_atTop_atBot.comp h).congr fun p => ?_
    simp only [Function.comp_apply]
    ring
  refine (Real.tendsto_exp_atBot.comp hexp).congr fun p => ?_
  rw [Function.comp_apply, reflectedOdds_eq_exp]

theorem tendsto_reflectedOdds_ratio_zero {t : ℝ} (ht0 : 0 < t) :
    Tendsto (fun p : Nat.Primes => reflectedOdds p (-t) / reflectedOdds p t) cofinite (𝓝 0) := by
  have hexp : Tendsto (fun p : Nat.Primes => -(2 * t) * Real.log (p : ℝ)) cofinite atBot := by
    have h : Tendsto (fun p : Nat.Primes => 2 * t * Real.log (p : ℝ)) cofinite atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0:ℝ) < 2 * t)
        tendsto_primeRealLog_cofinite_atTop
    refine (tendsto_neg_atTop_atBot.comp h).congr fun p => ?_
    simp only [Function.comp_apply]
    ring
  refine (Real.tendsto_exp_atBot.comp hexp).congr fun p => ?_
  rw [Function.comp_apply, reflectedOdds_eq_exp, reflectedOdds_eq_exp, ← Real.exp_sub]
  congr 1
  ring

theorem reflectedOdds_le {t : ℝ} (ht0 : 0 ≤ t) (p : Nat.Primes) :
    reflectedOdds p (-t) ≤ reflectedOdds p t := by
  rw [reflectedOdds_eq_exp, reflectedOdds_eq_exp, Real.exp_le_exp]
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (primeReal_one_lt p).le
  nlinarith

/-- **Sharp prime reserve asymptotic**, normalized form. -/
theorem tendsto_primeHistoryReserve_ratio {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun p : Nat.Primes =>
        primeHistoryReserve p t / (reflectedOdds p t ^ 2 * (2 * t * Real.log (p : ℝ))))
      cofinite (𝓝 (1 / 2)) := by
  have hA := tendsto_reflectedOdds_nhdsGT ht1
  have hB := tendsto_reflectedOdds_nhdsGT (show -t < 1 by linarith)
  have hBA := tendsto_reflectedOdds_ratio_zero ht0
  have hLtop : Tendsto (fun p : Nat.Primes => 2 * t * Real.log (p : ℝ)) cofinite atTop := by
    have h := Filter.Tendsto.const_mul_atTop (by positivity : (0:ℝ) < 2 * t)
      tendsto_primeRealLog_cofinite_atTop
    exact h.congr fun p => by ring
  -- small-odds regime
  have hsmall : ∀ᶠ p : Nat.Primes in cofinite,
      reflectedOdds p t ≤ 1 ∧ reflectedOdds p (-t) ≤ 1 := by
    have h1 := hA (Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1))
    have h2 := hB (Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1))
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1.2.le, hp2.2.le⟩
  -- first term
  have hT1a : Tendsto (fun p : Nat.Primes =>
      oddsDefect (reflectedOdds p t) / reflectedOdds p t ^ 2) cofinite (𝓝 (1 / 2)) :=
    tendsto_oddsDefect_div_sq.comp hA
  have hT1b : Tendsto (fun p : Nat.Primes =>
      oddsDefect (reflectedOdds p (-t)) / reflectedOdds p t ^ 2) cofinite (𝓝 0) := by
    have hsq : Tendsto (fun p : Nat.Primes =>
        (reflectedOdds p (-t) / reflectedOdds p t) ^ 2) cofinite (𝓝 0) := by
      simpa using hBA.pow 2
    refine squeeze_zero' ?_ ?_ hsq
    · filter_upwards [hsmall] with p hp
      have hb0 := reflectedOdds_pos p (-t)
      have ha0 := reflectedOdds_pos p t
      have := (oddsDefect_div_sq_nonneg_le_one hb0 hp.2).1
      have hbb : (0 : ℝ) ≤ oddsDefect (reflectedOdds p (-t)) := by
        have hy : (0 : ℝ) < reflectedOdds p (-t) ^ 2 := by positivity
        rw [le_div_iff₀ hy] at this
        linarith
      positivity
    · filter_upwards [hsmall] with p hp
      have hb0 := reflectedOdds_pos p (-t)
      have ha0 := reflectedOdds_pos p t
      obtain ⟨hnn, hle⟩ := oddsDefect_div_sq_nonneg_le_one hb0 hp.2
      rw [div_pow]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hdb : oddsDefect (reflectedOdds p (-t)) ≤ reflectedOdds p (-t) ^ 2 := by
        rw [div_le_one (by positivity)] at hle
        exact hle
      nlinarith [sq_nonneg (reflectedOdds p t)]
  -- second term
  have hT2 : Tendsto (fun p : Nat.Primes =>
      (oddsRate (reflectedOdds p t) - oddsRate (reflectedOdds p (-t))) *
        Real.log (oddsShape (reflectedOdds p t) / oddsShape (reflectedOdds p (-t))) /
        (reflectedOdds p t ^ 2 * (2 * t * Real.log (p : ℝ)))) cofinite (𝓝 0) := by
    have hbound : Tendsto (fun p : Nat.Primes => 2 / (2 * t * Real.log (p : ℝ)))
        cofinite (𝓝 0) := Filter.Tendsto.div_atTop tendsto_const_nhds hLtop
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hsmall, hLtop.eventually_gt_atTop 0] with p hp hL
    obtain ⟨hpa, hpb⟩ := hp
    have ha0 := reflectedOdds_pos p t
    have hb0 := reflectedOdds_pos p (-t)
    have hba := reflectedOdds_le ht0.le p
    have hra : oddsRate (reflectedOdds p t) ≤ reflectedOdds p t := by
      rw [oddsRate]
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + reflectedOdds p t by linarith)
      linarith
    have hrb : 0 < oddsRate (reflectedOdds p (-t)) := oddsRate_pos hb0
    have hmono : oddsRate (reflectedOdds p (-t)) ≤ oddsRate (reflectedOdds p t) := by
      rw [oddsRate, oddsRate]
      exact Real.log_le_log (by linarith) (by linarith)
    have hnum : |oddsRate (reflectedOdds p t) - oddsRate (reflectedOdds p (-t))|
        ≤ reflectedOdds p t := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hlog : |Real.log (oddsShape (reflectedOdds p t) / oddsShape (reflectedOdds p (-t)))|
        ≤ 2 * reflectedOdds p t := by
      rw [Real.log_div (oddsShape_pos ha0).ne' (oddsShape_pos hb0).ne']
      calc |Real.log (oddsShape (reflectedOdds p t)) - Real.log (oddsShape (reflectedOdds p (-t)))|
          ≤ |Real.log (oddsShape (reflectedOdds p t))|
            + |Real.log (oddsShape (reflectedOdds p (-t)))| := abs_sub _ _
        _ ≤ reflectedOdds p t + reflectedOdds p (-t) :=
            add_le_add (abs_log_oddsShape_le ha0 hpa) (abs_log_oddsShape_le hb0 hpb)
        _ ≤ 2 * reflectedOdds p t := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (show (0:ℝ) <
      reflectedOdds p t ^ 2 * (2 * t * Real.log (p : ℝ)) by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hprod : |oddsRate (reflectedOdds p t) - oddsRate (reflectedOdds p (-t))| *
        |Real.log (oddsShape (reflectedOdds p t) / oddsShape (reflectedOdds p (-t)))|
        ≤ reflectedOdds p t * (2 * reflectedOdds p t) :=
      mul_le_mul hnum hlog (abs_nonneg _) ha0.le
    nlinarith [hprod, sq_nonneg (reflectedOdds p t)]
  have hsum := ((hT1a.sub hT1b).add hT2)
  rw [sub_zero, add_zero] at hsum
  refine hsum.congr fun p => ?_
  have ha0 := reflectedOdds_pos p t
  have hLne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (primeReal_one_lt p)).ne'
  rw [primeHistoryReserve_split]
  field_simp

theorem reflectedOdds_sq (p : Nat.Primes) (t : ℝ) :
    reflectedOdds p t ^ 2 = (p : ℝ) ^ (-(2 * (1 - t))) := by
  rw [reflectedOdds_eq_exp, ← Real.exp_nat_mul, Real.rpow_def_of_pos (primeReal_pos p)]
  congr 1
  push_cast
  ring

/-- **Sharp prime reserve asymptotic** (card (4.5)). -/
theorem isEquivalent_primeHistoryReserve {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Asymptotics.IsEquivalent cofinite (fun p : Nat.Primes => primeHistoryReserve p t)
      (fun p : Nat.Primes => t * Real.log (p : ℝ) * (p : ℝ) ^ (-(2 * (1 - t)))) := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have h := (tendsto_primeHistoryReserve_ratio ht0 ht1).const_mul 2
  rw [show (2 : ℝ) * (1 / 2) = 1 from by norm_num] at h
  refine h.congr fun p => ?_
  have ha0 : 0 < reflectedOdds p t := reflectedOdds_pos p t
  have hLne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (primeReal_one_lt p)).ne'
  have ht0' : t ≠ 0 := ht0.ne'
  simp only [Pi.div_def]
  rw [← reflectedOdds_sq]
  field_simp

/-- **Positivity of the reserve** (card (4.4)). -/
theorem primeHistoryReserve_pos {t : ℝ} (ht : t ≠ 0) (p : Nat.Primes) :
    0 < primeHistoryReserve p t := by
  refine lt_of_le_of_ne (hiddenHistoryWork_nonneg _ _) ?_
  intro h
  have hzero : hiddenHistoryWork (reflectedSourceRate p t) (reflectedSourceRate p (-t)) = 0 :=
    h.symm
  have := (hiddenHistoryWork_eq_zero_iff (reflectedSourceRate_pos p t)
    (reflectedSourceRate_pos p (-t))).1 hzero
  exact ht ((reflectedSourceRate_eq_iff p t).1 this)

@[simp] theorem primeHistoryReserve_zero (p : Nat.Primes) : primeHistoryReserve p 0 = 0 := by
  simp [primeHistoryReserve]

/-! ## The exact all-prime threshold -/

theorem summable_primeRpow_neg {β : ℝ} (hβ : 1 < β) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-β) := by
  have hnat : Summable fun n : ℕ => 1 / (n : ℝ) ^ β := Real.summable_one_div_nat_rpow.2 hβ
  have hsub := hnat.comp_injective Nat.Primes.coe_nat_injective
  refine hsub.congr fun p => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (le_of_lt (primeReal_pos p)), one_div]

theorem log_le_rpow_div {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x ^ ε / ε := by
  have hpow : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx ε
  have h := Real.log_le_sub_one_of_pos hpow
  rw [Real.log_rpow hx] at h
  rw [le_div_iff₀ hε]
  nlinarith

theorem summable_reserveModel_of_lt_half {t : ℝ} (ht0 : 0 < t) (ht : t < 1 / 2) :
    Summable fun p : Nat.Primes => t * Real.log (p : ℝ) * (p : ℝ) ^ (-(2 * (1 - t))) := by
  have hα : (1 : ℝ) < 2 * (1 - t) := by linarith
  set ε : ℝ := (2 * (1 - t) - 1) / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    linarith
  have hαε : (1 : ℝ) < 2 * (1 - t) - ε := by
    rw [hεdef]
    linarith
  have hbase : Summable fun p : Nat.Primes => ε⁻¹ * ((p : ℕ) : ℝ) ^ (-(2 * (1 - t) - ε)) :=
    (summable_primeRpow_neg hαε).mul_left _
  refine Summable.of_nonneg_of_le ?_ (fun p => ?_) hbase
  · intro p
    have h1 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (primeReal_one_lt p).le
    have h2 : (0 : ℝ) < ((p : ℝ)) ^ (-(2 * (1 - t))) := Real.rpow_pos_of_pos (primeReal_pos p) _
    positivity
  · have hp0 : (0 : ℝ) < (p : ℝ) := primeReal_pos p
    have hlog := log_le_rpow_div hε hp0
    have hpow : (0 : ℝ) < ((p : ℝ)) ^ (-(2 * (1 - t))) := Real.rpow_pos_of_pos hp0 _
    have hsplit : ((p : ℝ)) ^ ε * ((p : ℝ)) ^ (-(2 * (1 - t)))
        = ((p : ℝ)) ^ (-(2 * (1 - t) - ε)) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    calc t * Real.log (p : ℝ) * ((p : ℝ)) ^ (-(2 * (1 - t)))
        ≤ t * (((p : ℝ)) ^ ε / ε) * ((p : ℝ)) ^ (-(2 * (1 - t))) := by
          have : t * Real.log (p : ℝ) ≤ t * (((p : ℝ)) ^ ε / ε) := by
            exact mul_le_mul_of_nonneg_left hlog ht0.le
          exact mul_le_mul_of_nonneg_right this hpow.le
      _ = t * ε⁻¹ * (((p : ℝ)) ^ ε * ((p : ℝ)) ^ (-(2 * (1 - t)))) := by
          field_simp
      _ = t * ε⁻¹ * ((p : ℝ)) ^ (-(2 * (1 - t) - ε)) := by rw [hsplit]
      _ ≤ ε⁻¹ * ((p : ℝ)) ^ (-(2 * (1 - t) - ε)) := by
          have hle : t * ε⁻¹ ≤ ε⁻¹ := by
            have hεi : (0 : ℝ) < ε⁻¹ := by positivity
            nlinarith
          have hpos : (0 : ℝ) ≤ ((p : ℝ)) ^ (-(2 * (1 - t) - ε)) :=
            (Real.rpow_pos_of_pos hp0 _).le
          exact mul_le_mul_of_nonneg_right hle hpos

theorem not_summable_reserveModel_of_half_le {t : ℝ} (ht0 : 0 < t) (ht : 1 / 2 ≤ t) :
    ¬ Summable fun p : Nat.Primes => t * Real.log (p : ℝ) * (p : ℝ) ^ (-(2 * (1 - t))) := by
  intro hsum
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) < t * Real.log 2 := by positivity
  refine Nat.Primes.not_summable_one_div ?_
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hsum.mul_left (t * Real.log 2)⁻¹)
  · have := primeReal_pos p
    positivity
  · have hp0 : (0 : ℝ) < (p : ℝ) := primeReal_pos p
    have hp1 : (1 : ℝ) < (p : ℝ) := primeReal_one_lt p
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    have hlogp : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
    have hexp : ((p : ℝ)) ^ (-(1 : ℝ)) ≤ ((p : ℝ)) ^ (-(2 * (1 - t))) := by
      refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
      linarith
    have hinv : ((p : ℝ)) ^ (-(1 : ℝ)) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, one_div]
    have hkey : t * Real.log 2 * (1 / (p : ℝ))
        ≤ t * Real.log (p : ℝ) * ((p : ℝ)) ^ (-(2 * (1 - t))) := by
      rw [← hinv]
      have h1 : t * Real.log 2 ≤ t * Real.log (p : ℝ) := by nlinarith
      have h2 : (0 : ℝ) ≤ ((p : ℝ)) ^ (-(1 : ℝ)) := (Real.rpow_pos_of_pos hp0 _).le
      calc t * Real.log 2 * ((p : ℝ)) ^ (-(1 : ℝ))
          ≤ t * Real.log (p : ℝ) * ((p : ℝ)) ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ t * Real.log (p : ℝ) * ((p : ℝ)) ^ (-(2 * (1 - t))) := by
            have hnn : (0 : ℝ) ≤ t * Real.log (p : ℝ) := by
              have := Real.log_nonneg hp1.le
              positivity
            exact mul_le_mul_of_nonneg_left hexp hnn
    rw [← le_div_iff₀' hc] at hkey
    simpa [div_eq_inv_mul] using hkey

/-- **Exact all-prime threshold** (card (4.11)). -/
theorem summable_primeHistoryReserve_iff {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Summable (fun p : Nat.Primes => primeHistoryReserve p t) ↔ t < 1 / 2 := by
  rw [(isEquivalent_primeHistoryReserve ht0 ht1).summable_iff]
  constructor
  · intro h
    by_contra hge
    exact not_summable_reserveModel_of_half_le ht0 (not_lt.1 hge) h
  · intro h
    exact summable_reserveModel_of_lt_half ht0 h

end

end GaloisForLFunctions.HTGeometry
