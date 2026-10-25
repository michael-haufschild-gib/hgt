import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceConeBoundaryRigidity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceRiemannRochAwayFromTheLowFrequencyDivisor

/-!
# Riemann–Roch and ampleness do not give Bézout on the same source cone

At every positive aperture the low-frequency-blind test space has a positive coercive Weil
floor. Taking half that floor gives a convex source cone with Riemann–Roch and ampleness on
the original scaling subsurface. Nevertheless its strict interior contains a negative-square
cycle. Thus even all nonnegative fibre-linear degree tests, together with RR and ampleness,
do not prove Bézout for the chosen cone.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A nonzero continuous compactly supported real test has positive square integral. -/
theorem integral_sq_pos_of_realTest_ne_zero (f : realTests) (hf : f ≠ 0) :
    0 < ∫ u : ℝ, (f.1 u) ^ 2 := by
  have hnn : 0 ≤ ∫ u : ℝ, (f.1 u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rcases hnn.eq_or_lt with h | h
  · exact (hf (Subtype.ext (eq_zero_of_integral_sq_eq_zero_of_mem_realTests f.2 h.symm))).elim
  · exact h

/-- Every positive aperture has an ample RR source cone whose strict interior violates Bézout. -/
theorem lowBlind_halfCoercivity_riemannRoch_ample_and_negative_square {a : ℝ} (ha : 0 < a) :
    (scalingSubsurface (lowBlindTests a)).RiemannRochAxiom
        (l2SourceCone (lowBlindCoercivity a / 2) (lowBlindTests a)) ∧
      (scalingSubsurface (lowBlindTests a)).AmpleAxiom
        (l2SourceCone (lowBlindCoercivity a / 2) (lowBlindTests a)) ∧
      ∃ x ∈ strictL2SourceCone (lowBlindCoercivity a / 2) (lowBlindTests a),
        (scalingSubsurface (lowBlindTests a)).pair x x < 0 := by
  have hc := lowBlindCoercivity_pos a
  have hc2 : 0 < lowBlindCoercivity a / 2 := by positivity
  refine ⟨(l2SourceCone_riemannRoch_iff_weilPair_ge hc2 _).mpr ?_,
    l2SourceCone_ample hc2 _, ?_⟩
  · intro f
    have hfloor := lowBlindCoercivity_le_weilPair ha.le f
    have hmass : 0 ≤ ∫ u : ℝ, (f.1.1 u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hprod := mul_nonneg hc.le hmass
    linarith only [hfloor, hprod]
  · obtain ⟨f, hf⟩ := exists_ne_zero_mem_lowBlindTests ha
    have hmass := integral_sq_pos_of_realTest_ne_zero f.1 hf
    have hfloor := lowBlindCoercivity_le_weilPair ha.le f
    apply exists_strictL2SourceCone_negative_square hc2.le (lowBlindTests a) f
    have hprod := mul_pos hc hmass
    linarith only [hfloor, hprod]

theorem lowBlind_halfCoercivity_not_bezout {a : ℝ} (ha : 0 < a) :
    ¬ (scalingSubsurface (lowBlindTests a)).BezoutAxiom
        (l2SourceCone (lowBlindCoercivity a / 2) (lowBlindTests a)) ∧
      ¬ (scalingSubsurface (lowBlindTests a)).BezoutAxiom
        (strictL2SourceCone (lowBlindCoercivity a / 2) (lowBlindTests a)) := by
  obtain ⟨-, -, x, hx, hxx⟩ :=
    lowBlind_halfCoercivity_riemannRoch_ample_and_negative_square ha
  have hx' : x ∈ l2SourceCone (lowBlindCoercivity a / 2) (lowBlindTests a) :=
    (scalingSubsurface (lowBlindTests a)).strictSourceCone_subset_sourceCone _ hx
  exact ⟨fun hB => (not_lt_of_ge (hB x hx' x hx')) hxx,
    fun hB => (not_lt_of_ge (hB x hx x hx)) hxx⟩

/-- These counterexamples pass every nonnegative linear degree test from the two fibres. -/
theorem lowBlind_halfCoercivity_nonneg_degrees {a : ℝ} (x : ℝ × ℝ × lowBlindTests a)
    (hx : x ∈ l2SourceCone (lowBlindCoercivity a / 2) (lowBlindTests a))
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (scalingSubsurface (lowBlindTests a)).pair x
      (u • (scalingSubsurface (lowBlindTests a)).H +
        v • (scalingSubsurface (lowBlindTests a)).V) :=
  (scalingSubsurface (lowBlindTests a)).sourceCone_nonneg_fibre_degrees hx hu hv

/-- Even on the certified subsurface, nonnegative fibre degrees alone fail Bézout. -/
theorem lowBlind_fibre_degree_cone_not_bezout {a : ℝ} (ha : 0 < a) :
    ¬ (scalingSubsurface (lowBlindTests a)).BezoutAxiom
      ((scalingSubsurface (lowBlindTests a)).sourceCone (fun _ => 0)) := by
  intro hB
  obtain ⟨-, -, -, f, hf⟩ := lowBlindTests_effectivity ha
  have hz := (scalingSubsurface (lowBlindTests a)).sourceCone_zero_bezout_iff.mp hB (0, 0, f)
  rw [scalingSubsurface_defect_self] at hz
  exact hf.ne' hz

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
