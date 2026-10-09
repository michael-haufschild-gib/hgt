import GaloisForLFunctions.RHTower.WeilLogShiftSignedDivergence
import GaloisForLFunctions.RHTower.WeilLogShiftPointwiseCriterion

/-!
# Pointwise positivity recovers convergence with finite excess

Actual probe lower bounds exclude divergent deficit potentials. Consequently,
finite positive excess alone permits the pointwise-to-uniform quantifier
exchange and guarantees a persistent fixed witness whenever positivity fails.
-/

open Filter Topology Zeta23

noncomputable section

namespace RHTower

open WeilExcess

private theorem not_eventually_bounded_below_of_atBot {f : ℝ → ℝ}
    (ht : Tendsto f atTop atBot) :
    ¬ ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → b ≤ f k := by
  rintro ⟨b, N, hN⟩
  have hev := (ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_atBot (b - 1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  have hlow := hN (max N M) (le_max_left _ _)
  have hupp := hM (max N M) (le_max_right _ _)
  change f (max N M : ℕ) ≤ b - 1 at hupp
  linarith only [hlow, hupp]

/-- A lower bound on one fixed log-shift probe of size at least four already
forces origin deficit summability, assuming only finite positive excess. -/
theorem summable_deficit_origin_of_probe_bounded_below {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) {m : ℕ} (hm : 4 ≤ Real.log m)
    (hbounded : ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (Real.log m))
        (logShiftRiemannDifference k (Real.log m)))).re) :
    Summable fun n => deviationDeficit lam n * riemannAutocorr (Real.log n) := by
  by_contra hbad
  exact not_eventually_bounded_below_of_atBot
    (tendsto_logShift_probe_atBot_of_nonsummable_deficit_origin hexc hbad hm) hbounded

/-- With finite origin deficit moment, a lower bound on any fixed probe forces
convergence of the signed potential at that probe. -/
theorem summable_potential_of_probe_bounded_below {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam))
    (horigin : Summable fun n => deviationDeficit lam n * riemannAutocorr (Real.log n))
    (m : ℕ)
    (hbounded : ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (Real.log m))
        (logShiftRiemannDifference k (Real.log m)))).re) :
    Summable fun n => weilDeviation lam n *
      (riemannAutocorr (Real.log m + Real.log n) +
        riemannAutocorr (Real.log m - Real.log n)) := by
  apply (summable_potential_iff_summable_deficit hexc (Real.log m)).mpr
  by_contra hbad
  exact not_eventually_bounded_below_of_atBot
    (tendsto_logShift_probe_atBot_of_nonsummable_deficit_sample hexc horigin m hbad) hbounded

private theorem summable_origin_potential_of_deficit {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam))
    (horigin : Summable fun n => deviationDeficit lam n * riemannAutocorr (Real.log n)) :
    Summable fun n => weilDeviation lam n *
      (riemannAutocorr (0 + Real.log n) + riemannAutocorr (0 - Real.log n)) := by
  apply (summable_potential_iff_summable_deficit hexc 0).mpr
  refine (horigin.mul_left 2).congr fun n => ?_
  rw [zero_add, zero_sub, riemannAutocorr_neg]
  ring

/-- Finite excess alone permits the probe/cutoff quantifier exchange. Pointwise
approximate positivity supplies all required convergence automatically. -/
theorem weilLogShiftAsymptoticPositive_iff_pointwise_of_summable_excess
    {lam : ℕ → ℝ} (hexc : Summable (deviationExcess lam)) :
    WeilLogShiftAsymptoticPositive lam ↔
      ∀ m : ℕ, 2 ≤ m → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        -ε ≤ (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re := by
  constructor
  · intro hpos
    exact (weilLogShiftAsymptoticPositive_iff_pointwise_of_summable_potential hexc
      (summable_potential_of_logShiftAsymptoticPositive hpos hexc 0)
      (fun m _ => summable_potential_of_logShiftAsymptoticPositive hpos hexc (Real.log m))).mp hpos
  · intro hpoint
    have hbound (m : ℕ) (hm : 2 ≤ m) : ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        b ≤ (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re := by
      obtain ⟨N, hN⟩ := hpoint m hm 1 (by norm_num)
      exact ⟨-1, N, hN⟩
    let m0 : ℕ := ⌊Real.exp (4 : ℝ)⌋₊ + 1
    have hm0 : 2 ≤ m0 := (integer_log_probe_bounds 4).1
    have hmc : 4 ≤ Real.log m0 := (integer_log_probe_bounds 4).2.1
    have hs0 := summable_deficit_origin_of_probe_bounded_below hexc hmc (hbound m0 hm0)
    exact (weilLogShiftAsymptoticPositive_iff_pointwise_of_summable_potential hexc
      (summable_origin_potential_of_deficit hexc hs0)
      (fun m hm => summable_potential_of_probe_bounded_below hexc hs0 m (hbound m hm))).mpr hpoint

private theorem fixed_separation_of_eventually_negative {lam : ℕ → ℝ} {m : ℕ}
    (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η)
    (hev : ∀ᶠ k : ℕ in atTop, (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference k (Real.log m))
      (logShiftRiemannDifference k (Real.log m)))).re ≤ -η) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (m : ℝ) ≤ Real.exp (2 * (k : ℝ)) ∧
        (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re ≤ -η := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨m, hm, η, hη, max N ⌈Real.log m / 2⌉₊, ?_⟩
  intro k hk
  constructor
  · have hlog : Real.log m / 2 ≤ (k : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (show ⌈Real.log m / 2⌉₊ ≤ k from (le_max_right _ _).trans hk))
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact (Real.log_le_iff_le_exp hmpos).mp (by linarith only [hlog])
  · exact hN k ((le_max_left _ _).trans hk)

/-- Every failure of asymptotic log-shift positivity with finite excess has a
persistent fixed negative witness; no coefficient sign or convergence is assumed. -/
theorem exists_persistent_fixed_logShift_negative_of_summable_excess
    {lam : ℕ → ℝ} (hexc : Summable (deviationExcess lam))
    (hnot : ¬ WeilLogShiftAsymptoticPositive lam) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (m : ℝ) ≤ Real.exp (2 * (k : ℝ)) ∧
        (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re ≤ -η := by
  by_cases hs0 : Summable fun n => deviationDeficit lam n * riemannAutocorr (Real.log n)
  · by_cases hsample : ∀ m : ℕ, 2 ≤ m → Summable fun n => deviationDeficit lam n *
        (riemannAutocorr (Real.log m + Real.log n) +
          riemannAutocorr (Real.log m - Real.log n))
    · have hpm (m : ℕ) (hm : 2 ≤ m) :=
        (summable_potential_iff_summable_deficit hexc (Real.log m)).mpr (hsample m hm)
      have hp0 := summable_origin_potential_of_deficit hexc hs0
      have hpotential : ¬ ∀ m : ℕ, 2 ≤ m →
          deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
        intro h
        exact hnot ((weilLogShiftAsymptoticPositive_iff_sampled_potential hexc).mpr
          (fun m hm => ⟨hpm m hm, h m hm⟩))
      push Not at hpotential
      obtain ⟨m, hm, hgap⟩ := hpotential
      let d := 2 * (deviationPotential lam (Real.log m) - deviationPotential lam 0)
      have hd : d < 0 := by dsimp only [d]; linarith only [hgap]
      have ht := (tendsto_logShift_probe_of_summable_potential m hp0 (hpm m hm)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      have hev := (tendsto_order.mp ht).2 (d / 2) (by change d < d / 2; linarith only [hd])
      apply fixed_separation_of_eventually_negative hm (-d / 2) (by linarith only [hd])
      filter_upwards [hev] with k hk
      change (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (Real.log m))
        (logShiftRiemannDifference k (Real.log m)))).re < d / 2 at hk
      linarith only [hk]
    · push Not at hsample
      obtain ⟨m, hm, hbad⟩ := hsample
      have ht := tendsto_logShift_probe_atBot_of_nonsummable_deficit_sample hexc hs0 m hbad
      exact fixed_separation_of_eventually_negative hm 1 (by norm_num)
        ((ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_atBot (-1))
  · let m0 : ℕ := ⌊Real.exp (4 : ℝ)⌋₊ + 1
    have hm0 : 2 ≤ m0 := (integer_log_probe_bounds 4).1
    have hmc : 4 ≤ Real.log m0 := (integer_log_probe_bounds 4).2.1
    have ht := tendsto_logShift_probe_atBot_of_nonsummable_deficit_origin hexc hs0 hmc
    exact fixed_separation_of_eventually_negative hm0 1 (by norm_num)
      ((ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_atBot (-1))

end RHTower
