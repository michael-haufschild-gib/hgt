import GaloisForLFunctions.BiScaleUncertainty.PrimeShellMellinMassBudget
import GaloisForLFunctions.HTGeometry.WeightedPowerWindowAsymptotics
import GaloisForLFunctions.RHTower.JointAncestryDampedShellArithmetic
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap

/-!
# A finite power-window criterion on square prime shells

RH is equivalent to subpower growth of the literal arithmetic Riesz shell sums,
on infinitely many square shells, for only the powers
`m < k ≤ m + m/log(m+1)`. Failure of RH produces a violating power in this window
on every sufficiently large square shell. The loud-rank budget comes from the
actual prime-shell half-mass; the weight cone comes from the completed endpoint
source height gap. No maximal off-line zero or zero-density assumption is used.
-/

open Complex Filter
open scoped Topology
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The completed endpoint source supplies a fixed cone for every actual Xi weight. -/
theorem half_norm_xiWeilWeight_le_re (q : XiZeroCopy) :
    ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ / 2 ≤
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
  half_norm_weight_le_re_of_height (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
    (xiZeroCopy_one_lt_abs_im q).le

private theorem tendsto_nat_square_atTop :
    Tendsto (fun m : ℕ => m ^ 2) atTop atTop := by
  refine tendsto_atTop.mpr fun N => ?_
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with m hm hm1
  nlinarith

private theorem eventually_squareShell_mode_large (q : XiZeroCopy)
    (hq : 1 / 2 < (q.1 : ℂ).re) :
    ∀ᶠ m : ℕ in atTop,
      2 * (m : ℝ) ^ ((q.1 : ℂ).re - 1 / 2) ≤
        ‖jasShellDampedSum (m ^ 2) (q.1 : ℂ)‖ := by
  let δ : ℝ := (q.1 : ℂ).re - 1 / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hplus : (q.1 : ℂ) + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith [xiZeroCopy_re_pos q]
  have hc : 0 < ‖(q.1 : ℂ) + 1‖ ^ 2 := pow_pos (norm_pos_iff.mpr hplus) 2
  have hU := tendsto_nat_square_atTop.eventually
    (eventually_lt_norm_jasShellUniformSum q
      (show 0 ≤ 3 * δ / 4 by positivity) (show 3 * δ / 4 < (q.1 : ℂ).re - 1 / 2 by
        change 3 * δ / 4 < δ; linarith))
  have hp : Tendsto (fun m : ℕ => (m : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < δ / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hU, hp.eventually (eventually_ge_atTop (2 * ‖(q.1 : ℂ) + 1‖ ^ 2)),
    eventually_ge_atTop 1] with m hU hp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have he : (((m ^ 2 : ℕ) : ℝ)) ^ (3 * δ / 4) =
      (m : ℝ) ^ δ * (m : ℝ) ^ (δ / 2) := by
    push_cast
    rw [← Real.rpow_natCast_mul hm0.le, ← Real.rpow_add hm0]
    congr 1
    norm_num
    ring
  rw [he] at hU
  change 2 * (m : ℝ) ^ δ ≤ ‖jasShellDampedSum (m ^ 2) (q.1 : ℂ)‖
  rw [jasShellDampedSum, norm_div, norm_pow, le_div_iff₀ hc]
  have hprod := mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hm0 δ).le
  nlinarith

/-- Every failure of RH produces an arithmetic violation in the explicit finite power window
on every sufficiently large square shell. -/
theorem exists_eventually_large_squareShellRiesz_of_not_riemannHypothesis
    (hRH : ¬RiemannHypothesis) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      m < k ∧ (k : ℝ) ≤ (m : ℝ) + (m : ℝ) / Real.log ((m : ℝ) + 1) ∧
      (m : ℝ) ^ (ε * k) < ‖jasShellRieszSum (m ^ 2) k‖ := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
  let δ : ℝ := (q.1 : ℂ).re - 1 / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let w : XiZeroCopy → ℂ := fun r => 1 / ((r.1 : ℂ) * (1 - (r.1 : ℂ)))
  let b : ℕ → XiZeroCopy → ℂ := fun m r => jasShellDampedSum (m ^ 2) (r.1 : ℂ)
  let W : ℝ := ∑' r, ‖w r‖
  have hw : Summable fun r => ‖w r‖ := summable_inv_mul_one_sub.norm
  have hW : 0 < W := Summable.tsum_pos hw (fun _ => norm_nonneg _) q
    (norm_pos_iff.mpr (inv_mul_one_sub_ne_zero q))
  have hbig : ∀ᶠ m : ℕ in atTop, ∃ r, 2 * (m : ℝ) ^ δ ≤ ‖b m r‖ :=
    (eventually_squareShell_mode_large q hq).mono fun _ h => ⟨q, h⟩
  have hwindow := eventually_exists_short_weighted_power_window b w hw hW
    half_norm_xiWeilWeight_le_re
    (fun m hm r => norm_jasShellDampedSum_square_le_weight hm
      (xiZeroCopy_re_pos r) (xiZeroCopy_re_lt_one r)) hδ hbig
  have hp : Tendsto (fun m : ℕ => (m : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < δ / 2)).comp tendsto_natCast_atTop_atTop
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [hwindow, hp.eventually (eventually_gt_atTop (1 / (2 * W))),
    eventually_ge_atTop 1] with m hm hp hm1
  obtain ⟨k, hk0, hk1, hk2⟩ := hm
  have hk : 1 ≤ k := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < m := by linarith
  have ha : 1 ≤ (m : ℝ) ^ (δ / 2) := Real.one_le_rpow hmR (by positivity)
  have hpow : (m : ℝ) ^ (δ / 2) ≤ ((m : ℝ) ^ (δ / 2)) ^ k := by
    simpa using pow_le_pow_right₀ ha hk
  have hcoef : 1 < 2 * W * ((m : ℝ) ^ (δ / 2)) ^ k := by
    have hp' := (div_lt_iff₀ (show 0 < 2 * W by positivity)).mp hp
    nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * W by positivity)]
  have he : (m : ℝ) ^ δ = (m : ℝ) ^ (δ / 2) * (m : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add hm0]
    congr 1
    ring
  have hstrict : (m : ℝ) ^ (δ / 2 * k) < 2 * W * ((m : ℝ) ^ δ) ^ k := by
    rw [Real.rpow_mul_natCast hm0.le, he, mul_pow]
    have hpos : 0 < ((m : ℝ) ^ (δ / 2)) ^ k :=
      pow_pos (Real.rpow_pos_of_pos hm0 _) _
    nlinarith [mul_lt_mul_of_pos_right hcoef hpos]
  have hident : (∑' r, w r * b m r ^ k) = jasShellRieszSum (m ^ 2) k := by
    rw [← jasShellDampedPowerSum_eq_rieszSum (m ^ 2) hk]
    unfold jasShellDampedPowerSum
    apply tsum_congr
    intro r
    dsimp [w, b]
    ring
  rw [hident] at hk2
  exact ⟨k, hk0, hk1, hstrict.trans_le hk2⟩

private theorem norm_squareShellRiesz_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) (m k : ℕ) (hk : 1 ≤ k) :
    ‖jasShellRieszSum (m ^ 2) k‖ ≤
      ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [← jasShellDampedPowerSum_eq_rieszSum (m ^ 2) hk, jasShellDampedPowerSum]
  refine (norm_tsum_le_tsum_norm (summable_jasShellDampedPowerSum_terms (m ^ 2) k).norm).trans ?_
  refine Summable.tsum_le_tsum (fun q => ?_)
    (summable_jasShellDampedPowerSum_terms (m ^ 2) k).norm summable_inv_mul_one_sub.norm
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _)
      (norm_jasShellDampedSum_le_one_of_riemannHypothesis hRH (m ^ 2) q))

/-- RH is equivalent to subpower growth of the literal Riesz source on infinitely many
square shells, checking only the finite interval `m < k ≤ m + m/log(m+1)`. -/
theorem riemannHypothesis_iff_squareShellRiesz_finitePowerWindow :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ᶠ m : ℕ in atTop,
      ∀ k : ℕ, m < k →
        (k : ℝ) ≤ (m : ℝ) + (m : ℝ) / Real.log ((m : ℝ) + 1) →
        ‖jasShellRieszSum (m ^ 2) k‖ ≤ (m : ℝ) ^ (ε * k) := by
  constructor
  · intro hRH ε hε
    let W : ℝ := ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
    have hp : Tendsto (fun m : ℕ => (m : ℝ) ^ ε) atTop atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    apply Filter.Eventually.frequently
    filter_upwards [hp.eventually (eventually_ge_atTop W), eventually_ge_atTop 1] with m hp hm
    intro k hk _
    have hk1 : 1 ≤ k := by omega
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc
      ‖jasShellRieszSum (m ^ 2) k‖ ≤ W :=
        norm_squareShellRiesz_le_of_riemannHypothesis hRH m k hk1
      _ ≤ (m : ℝ) ^ ε := hp
      _ ≤ (m : ℝ) ^ (ε * k) := by
        rw [Real.rpow_mul_natCast (by positivity)]
        simpa using pow_le_pow_right₀ (Real.one_le_rpow hmR hε.le) hk1
  · intro h
    by_contra hRH
    obtain ⟨ε, hε, hbad⟩ := exists_eventually_large_squareShellRiesz_of_not_riemannHypothesis hRH
    obtain ⟨m, hgood, hbad⟩ := ((h ε hε).and_eventually hbad).exists
    obtain ⟨k, hk0, hk1, hk2⟩ := hbad
    exact (not_lt_of_ge (hgood k hk0 hk1)) hk2

end

end RHTower
