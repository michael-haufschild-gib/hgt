import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTripleBoxTypeII
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedScheduleCount

/-!
# Paper-width dilation budget

Using width `δ_(A+1)` leaves one full logarithmic power reserve.  Uniformly through the source's
cubic terminal depth, every block product used by the Type-I, Type-I/II, and Type-II constructors
therefore lies inside a dyadic interval.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A nonnegative relative width whose total exponent is at most one half has dyadic dilation. -/
theorem one_add_pow_le_two_of_nat_mul_le_half
    {delta : ℝ} (hdelta : 0 ≤ delta) (R : ℕ)
    (hbudget : (R : ℝ) * delta ≤ 1 / 2) :
    (1 + delta) ^ R ≤ 2 := by
  calc
    (1 + delta) ^ R ≤ (Real.exp delta) ^ R :=
      pow_le_pow_left₀ (by linarith) (by
        simpa [add_comm] using Real.add_one_le_exp delta) R
    _ = Real.exp ((R : ℝ) * delta) := (Real.exp_nat_mul delta R).symm
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hbudget
    _ ≤ 2 := by
      have hlog : (1 : ℝ) / 2 < Real.log 2 := by
        linarith [Real.log_two_gt_d9]
      have h := Real.exp_lt_exp.mpr hlog
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
      exact h.le

/-- One successor in the paper parameter leaves enough width to absorb two endpoint roundings. -/
theorem eventually_three_mul_mtPaperWidth_succ_le (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      3 * mtPaperWidth (A + 1) X ≤ mtPaperWidth A X := by
  have hexponent :
      (-((10 * (A + 1) : ℕ) : ℝ)) < -((10 * A : ℕ) : ℝ) := by
    push_cast
    linarith
  have hkey := eventually_const_mul_rpow_polylog_le_rpow
    (C := (3 : ℝ))
    (α := -((10 * (A + 1) : ℕ) : ℝ))
    (β := -((10 * A : ℕ) : ℝ)) 0 hexponent
  have hkeyX := Real.tendsto_log_atTop.eventually hkey
  filter_upwards [hkeyX] with X hX
  simpa [mtPaperWidth] using hX

/-- Two successive endpoint roundings at width `δ_(A+1)` fit inside one width `δ_A`. -/
theorem eventually_one_add_mtPaperWidth_succ_sq_le (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (1 + mtPaperWidth (A + 1) X) ^ 2 ≤ 1 + mtPaperWidth A X := by
  filter_upwards [eventually_three_mul_mtPaperWidth_succ_le A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hwidth hX
  have hlog : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hsucc0 : 0 ≤ mtPaperWidth (A + 1) X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hsucc1 : mtPaperWidth (A + 1) X ≤ 1 := by
    rw [mtPaperWidth]
    calc
      (Real.log X) ^ (-((10 * (A + 1) : ℕ) : ℝ)) ≤
          (Real.log X) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog (neg_nonpos.mpr (Nat.cast_nonneg _))
      _ = 1 := by simp
  nlinarith [mul_nonneg hsucc0 (sub_nonneg.mpr hsucc1)]

/-- Uniform dyadic dilation through terminal depth plus the five outer/adically split factors. -/
theorem eventually_mtPaperWidth_succ_depthDilation_le_two (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ Y R : ℕ,
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      R ≤ Nat.floor (Real.log (Y : ℝ) /
          Real.log (mtLowerCutoffNat X : ℝ)) + 5 →
      (1 + mtPaperWidth (A + 1) X) ^ R ≤ 2 := by
  let e : ℝ := -((10 * (A + 1) : ℕ) : ℝ)
  have he : e < 0 := by
    dsimp [e]
    have hnat : 0 < 10 * (A + 1) := by omega
    have hcast : (0 : ℝ) < ((10 * (A + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hlim := tendsto_logRpow_mul_logLogPow (e := e) he 3
  have hsmall := hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [eventually_mtLogDepth_le_two_mul_log_log_cube,
    hsmall, Filter.eventually_ge_atTop (Real.exp (Real.exp 1))]
      with X hdepth hsmallX hX
  intro Y R hY hYX hR
  let u := Real.log (Real.log X)
  let delta := mtPaperWidth (A + 1) X
  have hlogXLower : Real.exp 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos (Real.exp 1)) hX
    simpa only [Real.log_exp] using hmono
  have hu : 1 ≤ u := by
    dsimp [u]
    have hmono := Real.log_le_log (Real.exp_pos 1) hlogXLower
    simpa only [Real.log_exp] using hmono
  have hlogX0 : 0 ≤ Real.log X :=
    (Real.exp_pos 1).le.trans hlogXLower
  have hdelta : 0 ≤ delta := by
    exact Real.rpow_nonneg hlogX0 _
  have hsmallPaper : delta * u ^ 3 ≤ 1 / 16 := by
    simpa [delta, u, mtPaperWidth, e] using hsmallX
  have hdeltaSmall : delta ≤ 1 / 16 := by
    have huCube : 1 ≤ u ^ 3 := one_le_pow₀ hu
    calc
      delta = delta * 1 := by ring
      _ ≤ delta * u ^ 3 := mul_le_mul_of_nonneg_left huCube hdelta
      _ ≤ 1 / 16 := hsmallPaper
  have hdepthX := hdepth Y hY hYX
  have hRreal : (R : ℝ) ≤ 2 * u ^ 3 + 5 := by
    have hRcast : (R : ℝ) ≤
        (Nat.floor (Real.log (Y : ℝ) /
          Real.log (mtLowerCutoffNat X : ℝ)) : ℝ) + 5 := by
      exact_mod_cast hR
    dsimp [u]
    linarith
  have hbudget : (R : ℝ) * delta ≤ 1 / 2 := by
    calc
      (R : ℝ) * delta ≤ (2 * u ^ 3 + 5) * delta :=
        mul_le_mul_of_nonneg_right hRreal hdelta
      _ = 2 * (delta * u ^ 3) + 5 * delta := by ring
      _ ≤ 2 * (1 / 16) + 5 * (1 / 16) := by gcongr
      _ ≤ 1 / 2 := by norm_num
  exact one_add_pow_le_two_of_nat_mul_le_half hdelta R hbudget

/-- On `[0,1/2]`, the exponential is bounded by its linear majorant `1+2x`. -/
theorem Real.exp_le_one_add_two_mul_of_nonneg_of_le_half
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have h1 : (1 : ℝ) - x ≤ Real.exp (-x) := by
    linarith [Real.add_one_le_exp (-x)]
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hE : (0 : ℝ) < Real.exp x := Real.exp_pos _
  nlinarith

/-- The complete depth dilation at literal width `δ_A` fits inside one preceding paper width.
This is the scale collar used when boxes outside `(Y/2,4Y]` are moved into the error. -/
theorem eventually_mtPaperWidth_depthDilation_le_prev
    (A : ℕ) (hA : 1 ≤ A) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ Y R : ℕ,
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      R ≤ Nat.floor (Real.log (Y : ℝ) /
          Real.log (mtLowerCutoffNat X : ℝ)) + 5 →
      (1 + mtPaperWidth A X) ^ R ≤ 1 + mtPaperWidth (A - 1) X := by
  have hlim := tendsto_logRpow_mul_logLogPow (e := (-10 : ℝ)) (by norm_num) 3
  have hsmall := hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 56)
  filter_upwards [eventually_mtLogDepth_le_two_mul_log_log_cube,
    hsmall, Filter.eventually_ge_atTop (Real.exp (Real.exp 1))]
      with X hdepth hsmallX hX
  intro Y R hY hYX hR
  let u := Real.log (Real.log X)
  let delta := mtPaperWidth A X
  let previous := mtPaperWidth (A - 1) X
  have hlogXLower : Real.exp 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos (Real.exp 1)) hX
    simpa only [Real.log_exp] using hmono
  have hu : 1 ≤ u := by
    dsimp [u]
    have hmono := Real.log_le_log (Real.exp_pos 1) hlogXLower
    simpa only [Real.log_exp] using hmono
  have hlogX0 : 0 ≤ Real.log X := (Real.exp_pos 1).le.trans hlogXLower
  have hlogX : 0 < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogXLower
  have hlogXOne : 1 ≤ Real.log X := by
    have hexp : (1 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp (1 : ℝ)]
    exact hexp.trans hlogXLower
  have hdelta0 : 0 ≤ delta := by
    exact Real.rpow_nonneg hlogX0 _
  have hprevious0 : 0 ≤ previous := by
    exact Real.rpow_nonneg hlogX0 _
  have hpreviousOne : previous ≤ 1 := by
    dsimp [previous, mtPaperWidth]
    exact (Real.rpow_le_rpow_of_exponent_le hlogXOne
      (neg_nonpos.mpr (Nat.cast_nonneg _))).trans_eq (by simp)
  have hratio : delta = previous * (Real.log X) ^ (-10 : ℝ) := by
    dsimp [delta, previous, mtPaperWidth]
    rw [← Real.rpow_add hlogX]
    congr 1
    have hsub : A - 1 + 1 = A := Nat.sub_add_cancel hA
    have hsubR : ((A - 1 : ℕ) : ℝ) + 1 = (A : ℝ) := by exact_mod_cast hsub
    push_cast
    linarith
  have hsmallRatio : (Real.log X) ^ (-10 : ℝ) * u ^ 3 ≤ 1 / 56 := by
    simpa [u] using hsmallX
  have hdepthX := hdepth Y hY hYX
  have hRreal : (R : ℝ) ≤ 2 * u ^ 3 + 5 := by
    have hRcast : (R : ℝ) ≤
        (Nat.floor (Real.log (Y : ℝ) /
          Real.log (mtLowerCutoffNat X : ℝ)) : ℝ) + 5 := by
      exact_mod_cast hR
    dsimp [u]
    linarith
  have hRcoarse : (R : ℝ) ≤ 7 * u ^ 3 := by
    have huCube : 1 ≤ u ^ 3 := one_le_pow₀ hu
    linarith
  have hbudget : (R : ℝ) * delta ≤ previous / 8 := by
    rw [hratio]
    calc
      (R : ℝ) * (previous * (Real.log X) ^ (-10 : ℝ)) =
          previous * ((R : ℝ) * (Real.log X) ^ (-10 : ℝ)) := by ring
      _ ≤ previous * (7 * u ^ 3 * (Real.log X) ^ (-10 : ℝ)) := by
        gcongr
      _ = previous * (7 * ((Real.log X) ^ (-10 : ℝ) * u ^ 3)) := by ring
      _ ≤ previous * (7 * (1 / 56)) := by gcongr
      _ = previous / 8 := by ring
  have hhalf : (R : ℝ) * delta ≤ 1 / 2 := by
    exact hbudget.trans (by linarith)
  calc
    (1 + delta) ^ R ≤ (Real.exp delta) ^ R :=
      pow_le_pow_left₀ (by linarith) (by
        simpa [add_comm] using Real.add_one_le_exp delta) R
    _ = Real.exp ((R : ℝ) * delta) := (Real.exp_nat_mul delta R).symm
    _ ≤ 1 + 2 * ((R : ℝ) * delta) :=
      Real.exp_le_one_add_two_mul_of_nonneg_of_le_half
        (mul_nonneg (Nat.cast_nonneg _) hdelta0) hhalf
    _ ≤ 1 + previous := by linarith

end

end RHTower.Sieve
