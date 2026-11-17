import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatCHMDMassCoercivity

/-!
# Negative arithmetic energy forces a flat mass residual

The negative part of the signed source energy is bounded by source mass.
Sharp nonlinear mass coercivity and tangent support therefore give a
quantitative first-variation barrier. On the nonpositive signed-energy
region the mass also controls graph norm, so convex secants strengthen
the barrier without any external norm bound.
-/

open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
open _root_.RHTower.CHMDDoobGraph
noncomputable section

private theorem potential_sqrt_mono {a b : ℝ} (hab : a ≤ b) :
    potential (Real.sqrt a) ≤ potential (Real.sqrt b) := by
  have h := evenPotential_le_of_abs_le (x := Real.sqrt a) (y := Real.sqrt b)
    (by simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sqrt_le_sqrt hab)
  simpa only [evenPotential_eq_potential_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h

private theorem negative_part_le_mass (p : SourceGraph) :
    max 0 (-sourceEnergy p) ≤ ‖p.val.fst‖ ^ 2 := by
  apply max_le (sq_nonneg _)
  change -(‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2) ≤ ‖p.val.fst‖ ^ 2
  nlinarith only [sq_nonneg ‖p.val.snd‖]

/-- Negative signed energy is controlled by the actual nonlinear source mass loss. -/
theorem negativeSourceEnergy_flatMass_bound (p : SourceGraph) :
    potential (Real.sqrt (2 * max 0 (-sourceEnergy p))) ≤ 2 * flatMassEnergy p := by
  exact (potential_sqrt_mono (mul_le_mul_of_nonneg_left (negative_part_le_mass p) (by norm_num))).trans
    (flatMassEnergy_coercivity p)

/-- Tangent support bounds the flat mass loss by the operator norm of its actual derivative. -/
theorem flatMassEnergy_le_derivative_norm (p : SourceGraph) :
    flatMassEnergy p ≤ ‖fderiv ℝ flatMassEnergy p‖ * ‖p‖ := by
  rw [(flatMassEnergy_hasFDerivAt p).fderiv]
  have hs : flatMassEnergy p ≤ flatMassFirstVariation p p :=
    evenIntegralEnergy_le_inner_gradient (sourceMap p)
  have hn : flatMassFirstVariation p p ≤ ‖flatMassFirstVariation p‖ * ‖p‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      (flatMassFirstVariation p).le_opNorm p)
  exact hs.trans hn

/-- A negative Weil-energy direction must carry a quantitatively nonzero nonlinear mass residual. -/
theorem negativeSourceEnergy_derivative_barrier (p : SourceGraph) :
    potential (Real.sqrt (2 * max 0 (-sourceEnergy p))) ≤
      2 * ‖fderiv ℝ flatMassEnergy p‖ * ‖p‖ := by
  have h := mul_le_mul_of_nonneg_left (flatMassEnergy_le_derivative_norm p) (by norm_num : (0 : ℝ) ≤ 2)
  exact (negativeSourceEnergy_flatMass_bound p).trans (by simpa only [mul_assoc] using h)

/-- On negative signed-energy directions, the graph norm is already controlled by source mass. -/
private theorem graph_norm_le_source_amplitude (p : SourceGraph) (he : sourceEnergy p ≤ 0) :
    ‖p‖ ≤ Real.sqrt (2 * ‖p.val.fst‖ ^ 2) := by
  have hi := sourceEnergy_add_two_mass p
  have hs := Real.sq_sqrt (show 0 ≤ 2 * ‖p.val.fst‖ ^ 2 by positivity)
  nlinarith only [hi, hs, he, norm_nonneg p, Real.sqrt_nonneg (2 * ‖p.val.fst‖ ^ 2)]

private theorem source_amplitude_secant_bound (p : SourceGraph) (he : sourceEnergy p ≤ 0)
    (hb : 0 < Real.sqrt (2 * ‖p.val.fst‖ ^ 2)) :
    potential (Real.sqrt (2 * ‖p.val.fst‖ ^ 2)) / Real.sqrt (2 * ‖p.val.fst‖ ^ 2) ≤
      2 * ‖fderiv ℝ flatMassEnergy p‖ := by
  have hm := flatMassEnergy_coercivity p
  have hs := flatMassEnergy_le_derivative_norm p
  have hg := mul_le_mul_of_nonneg_left (graph_norm_le_source_amplitude p he)
    (norm_nonneg (fderiv ℝ flatMassEnergy p))
  apply (div_le_iff₀ hb).mpr
  nlinarith only [hm, hs, hg]

/-- The negative signed-energy amplitude gives a residual bound independent of graph norm. -/
theorem negativeSourceEnergy_uniform_derivative_barrier (p : SourceGraph) :
    potential (Real.sqrt (2 * max 0 (-sourceEnergy p))) /
        (2 * Real.sqrt (2 * max 0 (-sourceEnergy p))) ≤
      ‖fderiv ℝ flatMassEnergy p‖ := by
  by_cases he : sourceEnergy p < 0
  · have hn : max 0 (-sourceEnergy p) = -sourceEnergy p := max_eq_right (by linarith only [he])
    have ha : 0 < Real.sqrt (2 * max 0 (-sourceEnergy p)) := by
      rw [hn]
      exact Real.sqrt_pos.mpr (mul_pos (by norm_num) (neg_pos.mpr he))
    have hab : Real.sqrt (2 * max 0 (-sourceEnergy p)) ≤ Real.sqrt (2 * ‖p.val.fst‖ ^ 2) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (negative_part_le_mass p) (by norm_num))
    have hb := ha.trans_le hab
    have hsec := potential_convex.secant_mono (mem_univ (0 : ℝ))
      (mem_univ (Real.sqrt (2 * max 0 (-sourceEnergy p))))
      (mem_univ (Real.sqrt (2 * ‖p.val.fst‖ ^ 2))) ha.ne' hb.ne' hab
    rw [potential_zero, sub_zero, sub_zero, sub_zero, sub_zero] at hsec
    have hratio := source_amplitude_secant_bound p he.le hb
    have hbound := (div_le_iff₀ ha).mp (hsec.trans hratio)
    apply (div_le_iff₀ (mul_pos (by norm_num) ha)).mpr
    nlinarith only [hbound]
  · have hn : max 0 (-sourceEnergy p) = 0 := max_eq_left (by linarith only [le_of_not_gt he])
    simp only [hn, mul_zero, Real.sqrt_zero, potential_zero, div_zero]
    exact norm_nonneg (fderiv ℝ flatMassEnergy p)

/-- The nonpositive signed-energy cone has a uniform flat mass residual away from its vertex. -/
theorem nonpositiveSourceEnergy_residual_threshold {ε : ℝ} (hε : 0 < ε) (p : SourceGraph)
    (he : sourceEnergy p ≤ 0) (hp : ε ≤ ‖p‖) :
    potential ε / (2 * ε) ≤ ‖fderiv ℝ flatMassEnergy p‖ := by
  have hab := hp.trans (graph_norm_le_source_amplitude p he)
  have hb := hε.trans_le hab
  have hs := potential_convex.secant_mono (mem_univ (0 : ℝ)) (mem_univ ε)
    (mem_univ (Real.sqrt (2 * ‖p.val.fst‖ ^ 2))) hε.ne' hb.ne' hab
  rw [potential_zero, sub_zero, sub_zero, sub_zero, sub_zero] at hs
  have hh := (div_le_iff₀ hε).mp (hs.trans (source_amplitude_secant_bound p he hb))
  apply (div_le_iff₀ (mul_pos (by norm_num) hε)).mpr
  nlinarith only [hh]

/-- Every flat mass critical sequence in the nonpositive energy cone converges in the full graph norm. -/
theorem nonpositiveSourceEnergy_critical_sequence_converges (p : ℕ → SourceGraph)
    (he : ∀ n, sourceEnergy (p n) ≤ 0)
    (hd : Tendsto (fun n => ‖fderiv ℝ flatMassEnergy (p n)‖) atTop (𝓝 0)) :
    Tendsto p atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hp : 0 < potential ε := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) (potential_bounds ε).1
    exact (not_le_of_gt hε) ((potential_zero_iff _).mp hz)
  have hc := div_pos hp (mul_pos (by norm_num : (0 : ℝ) < 2) hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hd.eventually (gt_mem_nhds hc))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  by_contra hsmall
  exact (not_le_of_gt (hN n hn))
    (nonpositiveSourceEnergy_residual_threshold hε (p n) (he n) (le_of_not_gt hsmall))

/-- Every fixed negative signed-energy margin forces a fixed strictly positive residual threshold. -/
theorem negativeSourceEnergy_residual_threshold {ε : ℝ} (hε : 0 < ε) (p : SourceGraph)
    (he : sourceEnergy p ≤ -ε) :
    potential (Real.sqrt (2 * ε)) / (2 * Real.sqrt (2 * ε)) ≤
      ‖fderiv ℝ flatMassEnergy p‖ := by
  have ha : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hε)
  have hm : ε ≤ max 0 (-sourceEnergy p) :=
    (by linarith only [he] : ε ≤ -sourceEnergy p).trans (le_max_right _ _)
  have hab := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2))
  have hb := ha.trans_le hab
  have hs := potential_convex.secant_mono (mem_univ (0 : ℝ))
    (mem_univ (Real.sqrt (2 * ε))) (mem_univ (Real.sqrt (2 * max 0 (-sourceEnergy p))))
    ha.ne' hb.ne' hab
  rw [potential_zero, sub_zero, sub_zero, sub_zero, sub_zero] at hs
  have hhalf := div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2)
  have hratio : potential (Real.sqrt (2 * ε)) / (2 * Real.sqrt (2 * ε)) ≤
      potential (Real.sqrt (2 * max 0 (-sourceEnergy p))) /
        (2 * Real.sqrt (2 * max 0 (-sourceEnergy p))) := by
    simpa only [div_div, mul_comm _ (2 : ℝ)] using hhalf
  exact hratio.trans (negativeSourceEnergy_uniform_derivative_barrier p)

/-- Vanishing flat mass residual removes the full negative signed-energy component, without boundedness. -/
theorem flatMass_residual_zero_negative_energy_tendsto (p : ℕ → SourceGraph)
    (hd : Tendsto (fun n => ‖fderiv ℝ flatMassEnergy (p n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (-sourceEnergy (p n))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ha : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hε)
  have hp : 0 < potential (Real.sqrt (2 * ε)) := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) (potential_bounds (Real.sqrt (2 * ε))).1
    exact (not_le_of_gt ha) ((potential_zero_iff _).mp hz)
  have hc := div_pos hp (mul_pos (by norm_num : (0 : ℝ) < 2) ha)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hd.eventually (gt_mem_nhds hc))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)]
  by_contra hsmall
  have hm : ε ≤ max 0 (-sourceEnergy (p n)) := le_of_not_gt hsmall
  have he : sourceEnergy (p n) ≤ -ε := by
    by_cases hsign : sourceEnergy (p n) ≤ 0
    · rw [max_eq_right (neg_nonneg.mpr hsign)] at hm
      linarith only [hm]
    · rw [max_eq_left (by linarith only [le_of_not_ge hsign])] at hm
      exact False.elim ((not_le_of_gt hε) hm)
  exact (not_le_of_gt (hN n hn)) (negativeSourceEnergy_residual_threshold hε (p n) he)

/-- Bounded graph critical sequences converge strongly in source mass; no edge compactness is asserted. -/
theorem flatMass_critical_sequence_source_converges (p : ℕ → SourceGraph) (R : ℝ)
    (hR : ∀ n, ‖p n‖ ≤ R)
    (hd : Tendsto (fun n => ‖fderiv ℝ flatMassEnergy (p n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => sourceMap (p n)) atTop (𝓝 0) := by
  have hb (n : ℕ) : potential (Real.sqrt (2 * ‖(p n).val.fst‖ ^ 2)) ≤
      2 * R * ‖fderiv ℝ flatMassEnergy (p n)‖ := by
    have he := flatMassEnergy_coercivity (p n)
    have hf := flatMassEnergy_le_derivative_norm (p n)
    have hn := mul_le_mul_of_nonneg_left (hR n)
      (norm_nonneg (fderiv ℝ flatMassEnergy (p n)))
    nlinarith only [he, hf, hn]
  have hlim : Tendsto (fun n => 2 * R * ‖fderiv ℝ flatMassEnergy (p n)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hd
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hc : 0 < potential (Real.sqrt (2 * ε ^ 2)) := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) (potential_bounds (Real.sqrt (2 * ε ^ 2))).1
    exact (not_le_of_gt (Real.sqrt_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hε))))
      ((potential_zero_iff _).mp hz)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hc))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  by_contra hsmall
  have hs : ε ≤ ‖(p n).val.fst‖ := le_of_not_gt hsmall
  have hs2 := mul_le_mul hs hs hε.le (norm_nonneg _)
  have hm := potential_sqrt_mono (by nlinarith only [hs2] :
    2 * ε ^ 2 ≤ 2 * ‖(p n).val.fst‖ ^ 2)
  exact (not_le_of_gt (hN n hn)) (hm.trans (hb n))

/-- A unit graph critical sequence can escape only at the upper signed-energy boundary. -/
theorem unit_flatMass_critical_sequence_energy_tendsto (p : ℕ → SourceGraph)
    (hp : ∀ n, ‖p n‖ = 1)
    (hd : Tendsto (fun n => ‖fderiv ℝ flatMassEnergy (p n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => sourceEnergy (p n)) atTop (𝓝 1) := by
  have hs := flatMass_critical_sequence_source_converges p 1 (fun n => (hp n).le) hd
  have hm : Tendsto (fun n => ‖sourceMap (p n)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hs.norm.pow 2
  have he : Tendsto (fun n => 1 - 2 * ‖sourceMap (p n)‖ ^ 2) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hm)
  convert he using 1
  funext n
  have hi := sourceEnergy_add_two_mass (p n)
  rw [hp n, one_pow] at hi
  change sourceEnergy (p n) + 2 * ‖sourceMap (p n)‖ ^ 2 = 1 at hi
  linarith only [hi]

/-- Uniformly negative signed energy cannot coexist with vanishing flat mass residual. -/
theorem no_negative_flatMass_critical_sequence :
    ¬ ∃ (p : ℕ → SourceGraph) (ε : ℝ), 0 < ε ∧
      (∀ n, sourceEnergy (p n) ≤ -ε) ∧
      Tendsto (fun n => ‖fderiv ℝ flatMassEnergy (p n)‖) atTop (𝓝 0) := by
  rintro ⟨p, ε, hε, hE, hd⟩
  have hlim := flatMass_residual_zero_negative_energy_tendsto p hd
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  have he : ε ≤ max 0 (-sourceEnergy (p N)) :=
    (by linarith only [hE N] : ε ≤ -sourceEnergy (p N)).trans (le_max_right _ _)
  exact (not_le_of_gt (hN N le_rfl)) he

#print axioms negativeSourceEnergy_flatMass_bound
#print axioms flatMassEnergy_le_derivative_norm
#print axioms negativeSourceEnergy_derivative_barrier
#print axioms negativeSourceEnergy_uniform_derivative_barrier
#print axioms nonpositiveSourceEnergy_residual_threshold
#print axioms nonpositiveSourceEnergy_critical_sequence_converges
#print axioms negativeSourceEnergy_residual_threshold
#print axioms flatMass_residual_zero_negative_energy_tendsto
#print axioms flatMass_critical_sequence_source_converges
#print axioms unit_flatMass_critical_sequence_energy_tendsto
#print axioms no_negative_flatMass_critical_sequence
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
