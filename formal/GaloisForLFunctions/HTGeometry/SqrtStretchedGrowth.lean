import GaloisForLFunctions.HTGeometry.StretchedExponentialMagnitudeHypertranscendence
import GaloisForLFunctions.HTGeometry.FactorialProfileGrowth

/-!
# The square-root stretched-exponential family has order zero

The magnitudes `ρ n = exp (−exp √n)` decay faster than `exp (−n²/24)`, because the fourth term of
the exponential series already gives `exp (√n) ≥ n²/24`.  Splitting the series at `24 (log r + 1)`
bounds the sum by `(24 log r + 25) · exp (24 (log r)² + 25 log r) + 2`, which is below `exp (ε r)`
for every `ε > 0` once `r` is large: the logarithm squared is negligible against the radius.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section


/-- The fourth term of the exponential series: `exp √n ≥ n²/24`. -/
theorem sq_div_le_exp_sqrt (n : ℕ) : ((n : ℝ) ^ 2) / 24 ≤ Real.exp (Real.sqrt n) := by
  have hnn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsum := Real.sum_le_exp_of_nonneg hnn 5
  have hterm : (Real.sqrt n) ^ 4 / 24
      ≤ ∑ i ∈ Finset.range 5, (Real.sqrt n) ^ i / (i.factorial : ℝ) := by
    have hmem : (4 : ℕ) ∈ Finset.range 5 := by decide
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun i : ℕ => (Real.sqrt n) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) hmem)
    norm_num [Nat.factorial]
  have hsq : (Real.sqrt n) ^ 4 = (n : ℝ) ^ 2 := by
    have h := Real.sq_sqrt (show (0:ℝ) ≤ (n : ℝ) by positivity)
    calc (Real.sqrt n) ^ 4 = ((Real.sqrt n) ^ 2) ^ 2 := by ring
      _ = (n : ℝ) ^ 2 := by rw [h]
  rw [hsq] at hterm
  exact le_trans hterm hsum

/-- The magnitudes of the family are dominated by a Gaussian profile. -/
theorem sqrtStretched_coeff_le (n : ℕ) :
    Real.exp (-Real.exp (Real.sqrt n)) ≤ Real.exp (-((n : ℝ) ^ 2 / 24)) := by
  refine Real.exp_le_exp.mpr ?_
  have := sq_div_le_exp_sqrt n
  linarith

/-- Each term of the series is bounded by the Gaussian term. -/
theorem sqrtStretched_term_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Real.exp (-Real.exp (Real.sqrt n)) * r ^ n
      ≤ Real.exp (-((n : ℝ) ^ 2 / 24) + n * Real.log r) := by
  have hpow : r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [hpow, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := sq_div_le_exp_sqrt n
  linarith

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- The magnitude series of the family converges for every radius. -/
theorem summable_sqrtStretched_term {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun n : ℕ => Real.exp (-Real.exp (Real.sqrt n)) * r ^ n) := by
  classical
  set p := FormalMultilinearSeries.ofScalars ℂ
    (GaloisForLFunctions.stretchedExponentialPhaseCoeff 1 (1/2) (fun _ => 0)) with hp
  have hrad : p.radius = ⊤ :=
    GaloisForLFunctions.stretchedExponentialPhaseSeries_radius_eq_top (by norm_num) (by norm_num)
      (by norm_num) (fun _ => 0)
  have hlt : ((Real.toNNReal r : NNReal) : ENNReal) < p.radius := by
    rw [hrad]
    exact ENNReal.coe_lt_top
  have hsum := p.summable_norm_mul_pow hlt
  have hcoe : ((Real.toNNReal r : NNReal) : ℝ) = r := Real.coe_toNNReal r hr
  rw [hcoe] at hsum
  refine hsum.congr fun n => ?_
  have hnorm : ‖p n‖ = Real.exp (-Real.exp (Real.sqrt n)) := by
    rw [hp]
    simp only [FormalMultilinearSeries.ofScalars_norm]
    rw [GaloisForLFunctions.norm_stretchedExponentialPhaseCoeff,
      GaloisForLFunctions.stretchedExp_oneHalf_eq_exp_sqrt]
    norm_num
  rw [hnorm]

/-- The head-plus-tail bound for the magnitude series. -/
theorem sqrtStretched_sum_le {r : ℝ} (hr : Real.exp 1 ≤ r) :
    ∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * r ^ n
      ≤ (24 * Real.log r + 25) * Real.exp (24 * Real.log r ^ 2 + 25 * Real.log r) + 2 := by
  classical
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (Real.exp_pos 1) hr
  have hL1 : (1 : ℝ) ≤ Real.log r := by
    have := Real.log_le_log (Real.exp_pos 1) hr
    rwa [Real.log_exp] at this
  set L : ℝ := Real.log r with hLdef
  set N : ℕ := ⌈24 * (L + 1)⌉₊ with hNdef
  have hNge : 24 * (L + 1) ≤ (N : ℝ) := Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 24 * L + 25 := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 24 * (L + 1) by nlinarith)
    linarith
  have hsummable := summable_sqrtStretched_term (le_of_lt hrpos)
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun n : ℕ =>
    Real.exp (-Real.exp (Real.sqrt n)) * r ^ n) N hsummable
  -- head
  have hhead : (∑ n ∈ Finset.range N, Real.exp (-Real.exp (Real.sqrt n)) * r ^ n)
      ≤ (24 * L + 25) * Real.exp (24 * L ^ 2 + 25 * L) := by
    have hterm : ∀ n ∈ Finset.range N, Real.exp (-Real.exp (Real.sqrt n)) * r ^ n
        ≤ Real.exp (24 * L ^ 2 + 25 * L) := by
      intro n hn
      refine le_trans (sqrtStretched_term_le hrpos n) ?_
      refine Real.exp_le_exp.mpr ?_
      have hnlt : (n : ℝ) ≤ 24 * L + 25 := by
        have : (n : ℝ) < (N : ℝ) := by exact_mod_cast Finset.mem_range.mp hn
        linarith
      have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 24 := by positivity
      nlinarith [hL1, Nat.cast_nonneg (α := ℝ) n]
    calc (∑ n ∈ Finset.range N, Real.exp (-Real.exp (Real.sqrt n)) * r ^ n)
        ≤ ∑ _n ∈ Finset.range N, Real.exp (24 * L ^ 2 + 25 * L) :=
          Finset.sum_le_sum hterm
      _ = (N : ℝ) * Real.exp (24 * L ^ 2 + 25 * L) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (24 * L + 25) * Real.exp (24 * L ^ 2 + 25 * L) := by
          exact mul_le_mul_of_nonneg_right hNle (le_of_lt (Real.exp_pos _))
  -- tail
  have hle : ∀ n : ℕ,
      (fun k : ℕ => Real.exp (-Real.exp (Real.sqrt k)) * r ^ k) (n + N)
        ≤ Real.exp (-(n : ℝ)) := by
    intro n
    refine le_trans (sqrtStretched_term_le hrpos (n + N)) ?_
    refine Real.exp_le_exp.mpr ?_
    have hcast : ((n + N : ℕ) : ℝ) = (n : ℝ) + (N : ℝ) := by push_cast; ring
    rw [hcast]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hNn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith [hNge, hL1, hnn, hNn]
  have hgeoFun : (fun n : ℕ => Real.exp (-(n : ℝ))) = fun n : ℕ => (Real.exp (-1)) ^ n := by
    funext n
    rw [← Real.exp_nat_mul]
    ring_nf
  have hexphalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    nlinarith [Real.exp_one_gt_d9]
  have hgeo : Summable (fun n : ℕ => Real.exp (-(n : ℝ))) := by
    rw [hgeoFun]
    exact summable_geometric_of_lt_one (le_of_lt (Real.exp_pos _)) (by linarith)
  have hshift : Summable (fun n : ℕ =>
      (fun k : ℕ => Real.exp (-Real.exp (Real.sqrt k)) * r ^ k) (n + N)) :=
    hsummable.comp_injective (add_left_injective N)
  have htailsum : (∑' n : ℕ,
      (fun k : ℕ => Real.exp (-Real.exp (Real.sqrt k)) * r ^ k) (n + N))
      ≤ ∑' n : ℕ, Real.exp (-(n : ℝ)) := Summable.tsum_le_tsum hle hshift hgeo
  have hval : ∑' n : ℕ, Real.exp (-(n : ℝ)) = (1 - Real.exp (-1))⁻¹ := by
    rw [hgeoFun, tsum_geometric_of_lt_one (le_of_lt (Real.exp_pos _)) (by linarith)]
  have hpos : (0 : ℝ) < 1 - Real.exp (-1) := by linarith
  have htail : (∑' n : ℕ,
      (fun k : ℕ => Real.exp (-Real.exp (Real.sqrt k)) * r ^ k) (n + N)) ≤ 2 := by
    refine le_trans htailsum ?_
    rw [hval, inv_le_iff_one_le_mul₀ hpos]
    linarith
  linarith [hsplit, hhead, htail]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Asymptotics


theorem isLittleO_log_sq_id : (fun x : ℝ => Real.log x ^ 2) =o[atTop] fun x : ℝ => x := by
  have hlog : Real.log =o[atTop] fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hmul := hlog.mul hlog
  refine hmul.congr' (Eventually.of_forall fun x => by ring) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)]
  norm_num

/-- The logarithmic terms are eventually negligible against a linear function. -/
theorem eventually_log_poly_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, 24 * Real.log r ^ 2 + 49 * Real.log r + 26 ≤ ε * r := by
  have h1 : ∀ᶠ r : ℝ in atTop, ‖Real.log r ^ 2‖ ≤ (ε / 72) * ‖r‖ :=
    isLittleO_log_sq_id.bound (by positivity)
  have h2 : ∀ᶠ r : ℝ in atTop, ‖Real.log r‖ ≤ (ε / 147) * ‖r‖ :=
    Real.isLittleO_log_id_atTop.bound (by positivity)
  filter_upwards [h1, h2, eventually_ge_atTop (78 / ε), eventually_ge_atTop (1 : ℝ)]
    with r hr1 hr2 hr3 hr4
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr4
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hrpos] at hr1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hrpos] at hr2
  have hsq : Real.log r ^ 2 ≤ (ε / 72) * r := le_trans (le_abs_self _) hr1
  have hlin : Real.log r ≤ (ε / 147) * r := le_trans (le_abs_self _) hr2
  have hconst : (26 : ℝ) ≤ ε * r / 3 := by
    rw [div_le_iff₀ hε] at hr3
    linarith
  have h24 : 24 * Real.log r ^ 2 ≤ ε * r / 3 := by nlinarith [hsq, hε, hrpos]
  have h49 : 49 * Real.log r ≤ ε * r / 3 := by nlinarith [hlin, hε, hrpos]
  linarith

/-- **The family has order zero.**  Its magnitude series is eventually below `exp (ε r)`. -/
theorem sqrtStretched_growth {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop,
      ∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * r ^ n ≤ Real.exp (ε * r) := by
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_log_poly_le hε,
    eventually_ge_atTop (2 / ε), eventually_ge_atTop (1 : ℝ)] with r hr hpoly hbig hr1
  set L : ℝ := Real.log r with hL
  have hsum := sqrtStretched_sum_le hr
  have hLpos : (1 : ℝ) ≤ L := by
    have := Real.log_le_log (Real.exp_pos 1) hr
    rwa [Real.log_exp] at this
  have hlin : 24 * L + 25 ≤ Real.exp (24 * L + 25) := by
    have := Real.add_one_le_exp (24 * L + 25)
    linarith
  have hstep : (24 * L + 25) * Real.exp (24 * L ^ 2 + 25 * L)
      ≤ Real.exp (24 * L ^ 2 + 49 * L + 25) := by
    calc (24 * L + 25) * Real.exp (24 * L ^ 2 + 25 * L)
        ≤ Real.exp (24 * L + 25) * Real.exp (24 * L ^ 2 + 25 * L) :=
          mul_le_mul_of_nonneg_right hlin (le_of_lt (Real.exp_pos _))
      _ = Real.exp (24 * L ^ 2 + 49 * L + 25) := by
          rw [← Real.exp_add]
          ring_nf
  have hexp1 : Real.exp (24 * L ^ 2 + 49 * L + 25) ≤ Real.exp (ε * r - 1) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hεr : (2 : ℝ) ≤ ε * r := by
    rw [div_le_iff₀ hε] at hbig
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp (ε * r) * (1 - Real.exp (-1)) := by
    have hexpge : Real.exp (2 : ℝ) ≤ Real.exp (ε * r) := Real.exp_le_exp.mpr hεr
    have h2 : (7 : ℝ) ≤ Real.exp 2 := by
      have h := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [h]
    have hsmall : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      nlinarith [Real.exp_one_gt_d9]
    nlinarith [hexpge, h2, hsmall, Real.exp_pos (ε * r)]
  have hdiv : Real.exp (ε * r - 1) = Real.exp (ε * r) * Real.exp (-1) := by
    rw [← Real.exp_add]
    ring_nf
  calc ∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * r ^ n
      ≤ (24 * L + 25) * Real.exp (24 * L ^ 2 + 25 * L) + 2 := hsum
    _ ≤ Real.exp (ε * r - 1) + 2 := by linarith [hstep, hexp1]
    _ ≤ Real.exp (ε * r) * Real.exp (-1) + Real.exp (ε * r) * (1 - Real.exp (-1)) := by
        rw [hdiv]
        linarith [htwo]
    _ = Real.exp (ε * r) := by ring

end

end GaloisForLFunctions.HTGeometry
