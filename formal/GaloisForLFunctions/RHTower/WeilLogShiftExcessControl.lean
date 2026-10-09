import GaloisForLFunctions.RHTower.WeilLogShiftPotentialCone

/-!
# One-sided excess controls mixed-sign log-shift potentials

Asymptotic log-shift positivity and finite total normalized excess bound every
normalized deviation by one hundred times that excess. This gives summability
and fixed-shift convergence of the signed kernel potential without assuming
summable deficit. The necessary potential inequalities therefore survive with
only one-sided summability and the countable log-shift family.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open RHTower.WeilExcess

noncomputable section

namespace RHTower

/-- Even approximate positivity of late panels bounds every normalized deviation
by the total positive excess, without a deficit-summability premise. -/
theorem abs_weilDeviation_le_total_excess_of_logShiftAsymptoticPositive {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam))
    (n : ℕ) : |weilDeviation lam n| ≤ 100 * ∑' j, deviationExcess lam j := by
  let E := ∑' j, deviationExcess lam j
  have hE : 0 ≤ E := tsum_nonneg fun j => deviationExcess_nonneg lam j
  have hup : weilDeviation lam n ≤ E :=
    (le_max_left _ _).trans (hexc.le_tsum n fun j _ => deviationExcess_nonneg lam j)
  rw [abs_le]
  constructor
  · by_cases ha : 0 ≤ weilDeviation lam n
    · linarith only [ha, hE]
    have hd : 0 < -weilDeviation lam n := by linarith only [ha]
    have hn : 2 ≤ n := by
      by_contra h
      have hz : weilDeviation lam n = 0 := by simp only [weilDeviation, if_neg h]
      exact ha (hz ▸ le_rfl)
    have hq : n - 2 + 2 = n := Nat.sub_add_cancel hn
    have hsmall : -weilDeviation lam n / 100 ≤ E := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hK : 0 < 4 * riemannAutocorr 0 := mul_pos (by norm_num) riemannAutocorr_zero_pos
      obtain ⟨Np, hp⟩ := hpos (ε * (4 * riemannAutocorr 0)) (mul_pos hε hK)
      obtain ⟨Nb, hb⟩ := exists_uniform_finiteBlock_excessMass_budget (n - 2)
        (Real.log (-weilDeviation lam n))
      let k := max Np Nb
      have hgap : Real.exp (Real.log (-weilDeviation lam n)) ≤
          ((ArithmeticFunction.vonMangoldt (n - 2 + 2) : ℝ) - lam (n - 2 + 2)) /
            Real.sqrt (n - 2 + 2 : ℕ) := by
        rw [Real.exp_log hd, hq, weilDeviation, if_pos hn]
        exact le_of_eq (by ring)
      have hbudget := hb k (le_max_right _ _) (ε * (4 * riemannAutocorr 0))
        ⟨hp k (le_max_left _ _), hgap⟩
      change max (Real.exp (Real.log (-weilDeviation lam n)) / 100 -
        (ε * (4 * riemannAutocorr 0)) / (4 * riemannAutocorr 0)) 0 ≤
          weilFiniteBlockExcessMass k lam at hbudget
      have hmass : weilFiniteBlockExcessMass k lam ≤ E :=
        hexc.sum_le_tsum _ fun j _ => deviationExcess_nonneg lam j
      have h := ((le_max_left _ _).trans hbudget).trans hmass
      rw [Real.exp_log hd, mul_div_cancel_right₀ _ hK.ne'] at h
      linarith only [h]
    linarith only [hsmall]
  · linarith only [hup, hE]

private theorem deviation_log_bound {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |weilDeviation lam n| ≤ 2 * Real.log n + C := by
  refine ⟨100 * ∑' j, deviationExcess lam j,
    mul_nonneg (by norm_num) (tsum_nonneg fun j => deviationExcess_nonneg lam j), fun n => ?_⟩
  have h := abs_weilDeviation_le_total_excess_of_logShiftAsymptoticPositive hpos hexc n
  linarith only [h, Real.log_natCast_nonneg n]

/-- Every signed potential series converges under finite excess and asymptotic
log-shift positivity, even when the unweighted deficit series is not summable. -/
theorem summable_potential_of_logShiftAsymptoticPositive {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) (y : ℝ) :
    Summable fun n : ℕ => weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := deviation_log_bound hpos hexc
  obtain ⟨D, _, hD⟩ := exists_riemannAutocorr_le
  exact summable_potential_term riemannAutocorr_nonneg hD hC (weilDeviation_zero lam) hC0 y

private theorem norm_truncated_potential_term_le (lam : ℕ → ℝ) (L y : ℝ) (n : ℕ) :
    ‖weilDeviation lam n * (truncatedRiemannAutocorr L (y + Real.log n) +
      truncatedRiemannAutocorr L (y - Real.log n))‖ ≤
    ‖weilDeviation lam n * (riemannAutocorr (y + Real.log n) +
      riemannAutocorr (y - Real.log n))‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (add_nonneg (truncatedRiemannAutocorr_nonneg _ _)
      (truncatedRiemannAutocorr_nonneg _ _)),
    abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (truncatedRiemannAutocorr_le_riemannAutocorr _ _)
      (truncatedRiemannAutocorr_le_riemannAutocorr _ _)) (abs_nonneg _)

/-- Every truncated potential series has finite support, for arbitrary
coefficients and arbitrary real cutoff and shift. -/
theorem summable_truncated_potential_term (a : ℕ → ℝ) (L y : ℝ) :
    Summable fun n => a n *
      (truncatedRiemannAutocorr L (y + Real.log n) +
        truncatedRiemannAutocorr L (y - Real.log n)) := by
  refine summable_of_ne_finset_zero
    (s := Finset.range (⌊Real.exp (2 * |L| + |y|)⌋₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (⌊Real.exp (2 * |L| + |y|)⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hlog : 2 * |L| + |y| < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).mpr ((Nat.lt_floor_add_one _).trans_le hnR)
  have hplus : 2 * L ≤ |y + Real.log n| := by
    linarith only [hlog, le_abs_self L, neg_le_abs y, le_abs_self (y + Real.log n)]
  have hminus : 2 * L ≤ |y - Real.log n| := by
    linarith only [hlog, le_abs_self L, le_abs_self y, neg_le_abs (y - Real.log n)]
  rw [truncatedRiemannAutocorr_eq_zero hplus, truncatedRiemannAutocorr_eq_zero hminus,
    add_zero, mul_zero]

/-- Convergence at this single shift suffices for the truncated potential limit;
no coefficient-growth bound or log-shift positivity is required. -/
theorem tendsto_truncatedPotential_of_summable_potential {lam : ℕ → ℝ} {y : ℝ}
    (hs : Summable fun n => weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) :
    Tendsto (fun L : ℝ => truncatedDeviationPotential lam L y) atTop
      (𝓝 (deviationPotential lam y)) := by
  refine tendsto_tsum_of_dominated_convergence hs.norm (fun n => ?_)
    (Eventually.of_forall fun L => norm_truncated_potential_term_le lam L y)
  exact ((tendsto_truncatedRiemannAutocorr _).add (tendsto_truncatedRiemannAutocorr _)).const_mul _

/-- Fixed-shift potential convergence needs only finite excess once asymptotic
log-shift positivity supplies the missing coefficient bound. -/
theorem tendsto_truncatedPotential_of_logShiftAsymptoticPositive {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) (y : ℝ) :
    Tendsto (fun L : ℝ => truncatedDeviationPotential lam L y) atTop
      (𝓝 (deviationPotential lam y)) :=
  tendsto_truncatedPotential_of_summable_potential
    (summable_potential_of_logShiftAsymptoticPositive hpos hexc y)

/-- The real-shift probe identity is unconditional: all truncated sums are finite. -/
theorem logShift_probe_potential_identity (lam : ℕ → ℝ) (L c : ℝ) :
    (weilFullFunctional lam (EF.weilTest (logShiftRiemannDifference L c)
      (logShiftRiemannDifference L c))).re =
      (zetaZeroConfig.W (logShiftRiemannDifference L c) (logShiftRiemannDifference L c)).re +
        2 * (truncatedDeviationPotential lam L c - truncatedDeviationPotential lam L 0) := by
  let f := logShiftRiemannDifference L c
  have hfc : HasCompactSupport f := hasCompactSupport_logShiftRiemannDifference _ _
  have hgc := EF.weilTest_hasCompactSupport hfc hfc
  have hterms := summable_primeAtoms (weilDeviation lam) hgc
  have hp0 := summable_truncated_potential_term (weilDeviation lam) L 0
  have hpc := summable_truncated_potential_term (weilDeviation lam) L c
  have hsum : (∑' n : ℕ, ((weilDeviation lam n : ℝ) : ℂ) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re =
      2 * truncatedDeviationPotential lam L 0 - 2 * truncatedDeviationPotential lam L c := by
    rw [Complex.re_tsum hterms]
    have heq (n : ℕ) : (((weilDeviation lam n : ℝ) : ℂ) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re =
        2 * (weilDeviation lam n * (truncatedRiemannAutocorr L (0 + Real.log n) +
          truncatedRiemannAutocorr L (0 - Real.log n))) -
        2 * (weilDeviation lam n * (truncatedRiemannAutocorr L (c + Real.log n) +
          truncatedRiemannAutocorr L (c - Real.log n))) := by
      rw [show EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n) =
        ((4 * truncatedRiemannAutocorr L (Real.log n) -
          2 * truncatedRiemannAutocorr L (Real.log n + c) -
          2 * truncatedRiemannAutocorr L (Real.log n - c) : ℝ) : ℂ) from
        logShiftRiemannPair_eq _ _ _, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [zero_add, zero_sub, truncatedRiemannAutocorr_neg,
        show c - Real.log n = -(Real.log n - c) by ring, truncatedRiemannAutocorr_neg,
        add_comm c (Real.log n)]
      ring
    rw [tsum_congr heq, (hp0.mul_left 2).tsum_sub (hpc.mul_left 2),
      tsum_mul_left, tsum_mul_left]
    rfl
  change (weilFullFunctional lam (EF.weilTest f f)).re = _
  rw [weilFullFunctional_eq_sub lam hgc, ← weilFullFunctional_vonMangoldt,
    ← zeta_W_eq_weilFullFunctional (contDiff_logShiftRiemannDifference _ _) hfc, Complex.sub_re]
  change (zetaZeroConfig.W f f).re -
    (∑' n : ℕ, ((weilDeviation lam n : ℝ) : ℂ) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re = _
  rw [hsum]
  ring

/-- The zero-side contribution of every fixed integer-log probe vanishes. -/
theorem tendsto_logShift_zeroSide (m : ℕ) :
    Tendsto (fun L : ℝ => (zetaZeroConfig.W
      (logShiftRiemannDifference L (Real.log m))
      (logShiftRiemannDifference L (Real.log m))).re) atTop (𝓝 0) := by
  obtain ⟨Λ, _, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine squeeze_zero_norm (fun L => ?_)
    (by simpa only [mul_zero] using
      (tendsto_nearRadicalEnergy.const_mul ((1 + Real.exp (Real.log m / 2)) ^ 2)))
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans
    (norm_W_logShiftRiemannDifference_le L (Real.log_natCast_nonneg m) hΛ)

/-- A fixed integer-log probe has its exact potential-gap limit whenever the
potential series converge at the origin and at that probe. -/
theorem tendsto_logShift_probe_of_summable_potential {lam : ℕ → ℝ} (m : ℕ)
    (hp0 : Summable fun n => weilDeviation lam n *
      (riemannAutocorr (0 + Real.log n) + riemannAutocorr (0 - Real.log n)))
    (hpm : Summable fun n => weilDeviation lam n *
      (riemannAutocorr (Real.log m + Real.log n) +
        riemannAutocorr (Real.log m - Real.log n))) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (Real.log m))
      (logShiftRiemannDifference L (Real.log m)))).re) atTop
      (𝓝 (2 * (deviationPotential lam (Real.log m) - deviationPotential lam 0))) := by
  have hp := ((tendsto_truncatedPotential_of_summable_potential hpm).sub
    (tendsto_truncatedPotential_of_summable_potential hp0)).const_mul 2
  have h := (tendsto_logShift_zeroSide m).add hp
  rw [zero_add] at h
  exact h.congr fun L => (logShift_probe_potential_identity lam L (Real.log m)).symm

/-- Exact fixed-probe limit under one-sided summability and asymptotic positivity. -/
theorem tendsto_logShift_probe_of_summable_excess {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) (m : ℕ) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (Real.log m))
      (logShiftRiemannDifference L (Real.log m)))).re) atTop
      (𝓝 (2 * (deviationPotential lam (Real.log m) - deviationPotential lam 0))) :=
  tendsto_logShift_probe_of_summable_potential m
    (summable_potential_of_logShiftAsymptoticPositive hpos hexc 0)
    (summable_potential_of_logShiftAsymptoticPositive hpos hexc (Real.log m))

/-- Finite excess suffices for every necessary potential inequality; absolute
summability of the signed deviation is not assumed. -/
theorem logShiftAsymptotic_potential_le_of_summable_excess {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam))
    (m : ℕ) (hm : 2 ≤ m) : deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN⟩ := hpos (2 * ε) (by positivity)
  have ht := (tendsto_logShift_probe_of_summable_excess hpos hexc m).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor : ∀ᶠ k : ℕ in atTop,
      -(2 * ε) ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (Real.log m))
        (logShiftRiemannDifference k (Real.log m)))).re := by
    filter_upwards [eventually_ge_atTop (max N ⌈Real.log m / 2⌉₊)] with k hk
    have hNk : N ≤ k := (le_max_left _ _).trans hk
    have hlog : Real.log m / 2 ≤ (k : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (show ⌈Real.log m / 2⌉₊ ≤ k from (le_max_right _ _).trans hk))
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmE : (m : ℝ) ≤ Real.exp (2 * (k : ℝ)) :=
      (Real.log_le_iff_le_exp hmpos).mp (by linarith only [hlog])
    exact hN k hNk ⟨m, Finset.mem_Icc.mpr ⟨hm, Nat.le_floor hmE⟩⟩
  have h := ge_of_tendsto ht hfloor
  linarith only [h]

/-- The original countable test predicate with raw summable excess supplies the
same potential inequalities, without full Weil positivity or summable deficit. -/
theorem logShiftTests_potential_le_of_summable_excess {lam : ℕ → ℝ}
    (hpos : WeilLogShiftTestsPositive lam)
    (hexc : Summable fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 / Real.sqrt n) :
    ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
  have ha : WeilLogShiftAsymptoticPositive lam := by
    intro ε hε
    refine ⟨0, fun k _ m => ?_⟩
    have hm2 := (Finset.mem_Icc.mp m.2).1
    have hmN := (Finset.mem_Icc.mp m.2).2
    have hmE : (m.1 : ℝ) ≤ Real.exp (2 * (k : ℝ)) :=
      (by exact_mod_cast hmN : (m.1 : ℝ) ≤ (⌊Real.exp (2 * (k : ℝ))⌋₊ : ℝ)).trans
        (Nat.floor_le (Real.exp_pos _).le)
    exact (neg_nonpos.mpr hε.le).trans (hpos k m.1 hm2 hmE)
  exact logShiftAsymptotic_potential_le_of_summable_excess ha (summable_deviationExcess hexc)

/-- Finite excess controls the deficit potential without full Weil positivity:
its series converges at every real shift and is uniformly bounded at integer logarithms. -/
theorem deficit_potential_control_of_summable_excess {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) :
    (∀ y : ℝ, Summable fun n : ℕ => deviationDeficit lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) ∧
    ∀ m : ℕ, 2 ≤ m → kernelPotential (deviationDeficit lam) (Real.log m) ≤
      2 * riemannAutocorr 0 * (∑' n, deviationExcess lam n) - deviationPotential lam 0 := by
  let E := ∑' n, deviationExcess lam n
  have hE0 : 0 ≤ E := tsum_nonneg fun n => deviationExcess_nonneg lam n
  have hB0 : 0 ≤ 100 * E := mul_nonneg (by norm_num) hE0
  have hdef (n : ℕ) : |deviationDeficit lam n| ≤ 2 * Real.log n + 100 * E := by
    rw [abs_of_nonneg (deviationDeficit_nonneg _ _)]
    have ha := abs_weilDeviation_le_total_excess_of_logShiftAsymptoticPositive hpos hexc n
    have hv : deviationDeficit lam n ≤ 100 * E :=
      max_le ((neg_le_abs _).trans ha) hB0
    linarith only [hv, Real.log_natCast_nonneg n]
  obtain ⟨D, _, hD⟩ := exists_riemannAutocorr_le
  have hsD (y : ℝ) : Summable fun n : ℕ => deviationDeficit lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) :=
    summable_potential_term riemannAutocorr_nonneg hD hdef (deviationDeficit_zero lam) hB0 y
  have hterm (y : ℝ) (n : ℕ) : deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) ≤
      deviationExcess lam n * (2 * riemannAutocorr 0) := by
    apply mul_le_mul_of_nonneg_left _ (deviationExcess_nonneg _ _)
    linarith only [riemannAutocorr_le_zero (y + Real.log n), riemannAutocorr_le_zero (y - Real.log n)]
  have hsE (y : ℝ) : Summable fun n : ℕ => deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
    refine (hexc.mul_right (2 * riemannAutocorr 0)).of_norm_bounded fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (deviationExcess_nonneg _ _)
      (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _)))]
    exact hterm y n
  have hupper (y : ℝ) : kernelPotential (deviationExcess lam) y ≤ 2 * riemannAutocorr 0 * E := by
    calc _ ≤ ∑' n, deviationExcess lam n * (2 * riemannAutocorr 0) :=
        (hsE y).tsum_le_tsum (hterm y) (hexc.mul_right _)
      _ = _ := by rw [tsum_mul_right]; dsimp only [E]; ring
  have hsplit (y : ℝ) : deviationPotential lam y =
      kernelPotential (deviationExcess lam) y - kernelPotential (deviationDeficit lam) y := by
    unfold deviationPotential kernelPotential
    rw [← (hsE y).tsum_sub (hsD y)]
    refine tsum_congr fun n => ?_
    rw [weilDeviation_eq_sub]
    ring
  refine ⟨hsD, fun m hm => ?_⟩
  have h := logShiftAsymptotic_potential_le_of_summable_excess hpos hexc m hm
  rw [hsplit (Real.log m)] at h
  have he := hupper (Real.log m)
  linarith only [h, he]

end RHTower

end
