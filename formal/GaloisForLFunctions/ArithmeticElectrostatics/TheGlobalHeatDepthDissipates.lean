import GaloisForLFunctions.ArithmeticElectrostatics.TheSimpleHeatPacketDissipatesDepth
import GaloisForLFunctions.ArithmeticElectrostatics.TheGlobalHeatDepthHasItsZeroVelocityDerivative
import GaloisForLFunctions.HTGeometry.ForwardRegularIntervalComparison

/-!
# Global dissipation of squared heat-zero depth

For positive times, the full multiplicity-weighted squared-depth energy
satisfies `E(b) + 2∫_a^b N(t)dt ≤ E(a)`. Its continuity and the short
forward simple-zero intervals extend the reciprocal-field dissipation
through every collision. No initial-time energy assumption is made.
-/

open Complex Filter Topology Set MeasureTheory Metric
open RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.EntireZeroDivisor
namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section


/-- The nonreal count is constant immediately to the right of each positive time. -/
private theorem exists_nonrealZeroCount_forward_eq {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, ∀ s ∈ Ioo t (t + δ), nonrealZeroCount s = nonrealZeroCount t := by
  by_cases ht8 : t < 1 / 8
  · obtain ⟨δ, hδ, hlo, hhi⟩ := exists_local_nonrealZeroCount ht ht8
    refine ⟨δ, hδ, fun s hs => le_antisymm (hhi s hs.1 hs.2) ?_⟩
    apply hlo s _ (ht.trans hs.1)
    rw [abs_of_pos (sub_pos.mpr hs.1)]
    linarith only [hs.2]
  · refine ⟨1, one_pos, fun s hs => ?_⟩
    rw [nonrealZeroCount_eq_zero_of_le (le_of_not_gt ht8),
      nonrealZeroCount_eq_zero_of_le ((le_of_not_gt ht8).trans hs.1.le)]

/-- Integrating the count primitive carries the derivative inequality through collisions. -/
private theorem integral_heatCount_le_of_forward_drift {E : ℝ → ℝ}
    (hc : ContinuousOn E (Ioi 0))
    (hd : ∀ t : ℝ, 0 < t → ∃ δ > 0, ∀ s ∈ Ioo t (t + δ),
      ∃ D : ℝ, HasDerivWithinAt E D (Ici s) s ∧ D ≤ -2 * (nonrealZeroCount s : ℝ))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    E b + 2 * (∫ s in a..b, (nonrealZeroCount s : ℝ)) ≤ E a := by
  -- Clamp below the comparison interval to obtain a globally integrable monotone count.
  let N : ℝ → ℝ := fun s => (nonrealZeroCount (max s (a / 2)) : ℝ)
  have hNanti : Antitone N := by
    intro s t hst
    change (nonrealZeroCount (max t (a / 2)) : ℝ) ≤
      (nonrealZeroCount (max s (a / 2)) : ℝ)
    exact_mod_cast nonrealZeroCount_antitoneOn
      ((half_pos ha).trans_le (le_max_right s (a / 2)))
      ((half_pos ha).trans_le (le_max_right t (a / 2))) (max_le_max hst le_rfl)
  have hNmeas : StronglyMeasurable N := hNanti.measurable.stronglyMeasurable
  have hNc : ContinuousOn (fun x => ∫ s in a..x, N s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' (hNanti.intervalIntegrable (a := a) (b := b))
        left_mem_uIcc
  have hF : ContinuousOn (fun s => E s + 2 * ∫ x in a..s, N x) (Icc a b) :=
    (hc.mono fun s hs => ha.trans_le hs.1).add (continuousOn_const.mul hNc)
  have h := le_initial_of_forward_intervals_interior hab hF (by
    intro t ht
    obtain ⟨δ, hδ, hder⟩ := hd t (ha.trans ht.1)
    obtain ⟨ε, hε, hcount⟩ := exists_nonrealZeroCount_forward_eq (ha.trans ht.1)
    refine ⟨min δ ε, lt_min hδ hε, fun s hs _ => ?_⟩
    have hsδ : s ∈ Ioo t (t + δ) := ⟨hs.1, by linarith only [hs.2, min_le_left δ ε]⟩
    have hsε : s ∈ Ioo t (t + ε) := ⟨hs.1, by linarith only [hs.2, min_le_right δ ε]⟩
    have hsN : N s = (nonrealZeroCount s : ℝ) := by
      dsimp only [N]
      rw [max_eq_left (by linarith only [ha, ht.1, hs.1])]
    have hev : N =ᶠ[𝓝 s] (fun _ => (nonrealZeroCount t : ℝ)) := by
      filter_upwards [Ioo_mem_nhds hsε.1 hsε.2] with u hu
      dsimp only [N]
      rw [max_eq_left (by linarith only [ha, ht.1, hu.1]), hcount u hu]
    have hcont : ContinuousAt N s := continuousAt_const.congr hev.symm
    have hP := intervalIntegral.integral_hasDerivAt_right
      (hNanti.intervalIntegrable (a := a) (b := s))
      hNmeas.stronglyMeasurableAtFilter hcont
    obtain ⟨D, hD, hbound⟩ := hder s hsδ
    refine ⟨D + 2 * N s, hD.add (hP.const_mul 2).hasDerivWithinAt, ?_⟩
    rw [hsN]
    linarith only [hbound])
  have hInt : (∫ s in a..b, N s) = ∫ s in a..b, (nonrealZeroCount s : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only [N]
    rw [uIcc_of_le hab] at hs
    rw [max_eq_left (by linarith only [ha, hs.1])]
  simpa only [intervalIntegral.integral_same, mul_zero, add_zero, hInt] using h

/-- Every positive time has a punctured forward interval of global energy dissipation. -/
theorem heatGlobalVerticalEnergy_forward_derivative :
    ∀ t : ℝ, 0 < t → ∃ δ > 0, ∀ s ∈ Ioo t (t + δ),
      ∃ D : ℝ, HasDerivWithinAt heatGlobalVerticalEnergy D (Ici s) s ∧
        D ≤ -2 * (nonrealZeroCount s : ℝ) := by
  classical
  intro t ht
  obtain ⟨R, hR⟩ := exists_heat_nonreal_norm_bound ht
  obtain ⟨δ, hδ, hreg⟩ := exists_compact_simple_riemannHeat_zeros_forward ht
    (isCompact_closedBall (0 : ℂ) R)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hs0 : 0 < s := ht.trans hs.1
  have han : AnalyticOnNhd ℂ (riemannHeat s) (closedBall 0 R) :=
    fun z _ => (riemannHeat_analytic hs0.le) z (mem_univ z)
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top hs0.le z (analyticOrderAt_eq_top.mpr h))
  let S := hfin.toFinset
  have hpacket (a : ℂ) : a ∈ S ↔ riemannHeat s a = 0 ∧ ‖a‖ ≤ R := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_closedBall,
      dist_zero_right, and_comm]
  have hsimple (a : ℂ) (ha : a ∈ S) : deriv (riemannHeat s) a ≠ 0 := by
    obtain ⟨hz, hn⟩ := (hpacket a).mp ha
    exact (hreg s hs.1 hs.2 a (by simpa only [mem_closedBall, dist_zero_right] using hn) hz).1
  have hconf : ∀ u, s ≤ u → ∀ z, riemannHeat u z = 0 → z.im ≠ 0 → ‖z‖ ≤ R :=
    fun u hu z hz hi => (hR u (hs.1.le.trans hu) z hz hi).le
  have hder := heatGlobalVerticalEnergy_hasDerivWithinAt_of_simple hs0 hconf hpacket hsimple
  let D := ∑ a ∈ S, 2 * a.im *
    (deriv (deriv (riemannHeat s)) a / deriv (riemannHeat s) a).im
  have hder' : HasDerivWithinAt (fun h => heatGlobalVerticalEnergy (s + h))
      D (Ici 0) (s - s) := by simpa only [D, sub_self] using hder
  have hg : HasDerivWithinAt (fun r : ℝ => r - s) 1 (Ici s) s :=
    ((hasDerivAt_id s).sub_const s).hasDerivWithinAt
  have hc := hder'.comp (h := fun r : ℝ => r - s) s hg (by
    intro r hr
    change 0 ≤ r - s
    exact sub_nonneg.mpr hr)
  have hfun : (fun r => heatGlobalVerticalEnergy (s + (r - s))) = heatGlobalVerticalEnergy := by
    funext r
    congr 1
    ring
  have hactual : HasDerivWithinAt heatGlobalVerticalEnergy D (Ici s) s := by
    change HasDerivWithinAt (fun r => heatGlobalVerticalEnergy (s + (r - s))) (D * 1) (Ici s) s at hc
    rwa [hfun, mul_one] at hc
  refine ⟨D, hactual, heatGlobalPacket_drift_le hs0
    (fun a ha => ((hpacket a).mp ha).1) hsimple
    (fun a hz hi => (hpacket a).mpr ⟨hz, hconf s le_rfl a hz hi⟩) ?_⟩
  intro a ha
  obtain ⟨hz, hn⟩ := (hpacket a).mp ha
  apply (hpacket (starRingEnd ℂ a)).mpr
  constructor
  · rw [riemannHeat_conj hs0.le, hz, map_zero]
  · simpa only [Complex.norm_conj] using hn

/-- The full nonreal count is paid by the decrease in global squared depth. -/
theorem heatGlobalVerticalEnergy_add_integral_count_le {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    heatGlobalVerticalEnergy b + 2 * (∫ s in a..b, (nonrealZeroCount s : ℝ)) ≤
      heatGlobalVerticalEnergy a :=
  integral_heatCount_le_of_forward_drift continuousOn_heatGlobalVerticalEnergy
    heatGlobalVerticalEnergy_forward_derivative ha hab

/-- The actual global heat energy is nonincreasing on positive times. -/
theorem antitoneOn_heatGlobalVerticalEnergy :
    AntitoneOn heatGlobalVerticalEnergy (Ioi 0) := by
  intro a ha b hb hab
  have h := heatGlobalVerticalEnergy_add_integral_count_le ha hab
  have hn : 0 ≤ ∫ s in a..b, (nonrealZeroCount s : ℝ) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Nat.cast_nonneg _)
  linarith only [h, hn]

#print axioms heatGlobalVerticalEnergy_add_integral_count_le
#print axioms antitoneOn_heatGlobalVerticalEnergy

/-- The energy vanishes exactly when every zero of the heat function is real. -/
theorem heatGlobalVerticalEnergy_eq_zero_iff {t : ℝ} (ht : 0 < t) :
    heatGlobalVerticalEnergy t = 0 ↔ ∀ z : ℂ, riemannHeat t z = 0 → z.im = 0 := by
  classical
  constructor
  · intro hE z hz
    by_contra hi
    obtain ⟨q, hq⟩ := exists_zeroCopy_of_eq_zero (riemannHeat_analytic ht.le)
      (RHTower.riemannHeat_zero_ne ht.le) hz
    have hmem : q ∈ heatNonrealCopies t := (mem_heatNonrealCopies ht q).mpr (by rwa [hq])
    have hs := Finset.single_le_sum
      (f := fun q => (zeroCopyPoint (riemannHeat t) q).im ^ 2)
      (fun _ _ => sq_nonneg _) hmem
    change (zeroCopyPoint (riemannHeat t) q).im ^ 2 ≤
      heatGlobalVerticalEnergy t at hs
    rw [hq, hE] at hs
    exact (not_le_of_gt (sq_pos_of_ne_zero hi)) hs
  · intro hreal
    unfold heatGlobalVerticalEnergy
    apply Finset.sum_eq_zero
    intro q _
    rw [hreal _ (apply_zeroCopyPoint (riemannHeat_analytic ht.le) q), zero_pow two_ne_zero]

#print axioms heatGlobalVerticalEnergy_eq_zero_iff


end

end GaloisForLFunctions.ArithmeticElectrostatics
