import GaloisForLFunctions.HTGeometry.SupportEscapeDescentLaw

/-!
# Bounded weighted descents and escaping capacities both exist

The support–escape law pits a uniformly bounded weighted descent against a coordinate whose
evaluation escapes every bound at bounded source capacity, and concludes that the weight vanishes
there.  Neither side had a producer.

The zero weight is a bounded descent with constant zero, and a weight bounded in modulus against an
evaluation dominated by the capacity is bounded with the product constant.  On the other side, the
identity evaluation at constant zero capacity escapes, so the law's conclusion is not vacuous: both
hypotheses are simultaneously satisfiable, which forces the zero weight.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The zero weight is a bounded weighted descent, with constant zero. -/
theorem weightedDescentBounded_zero {S I : Type*} (capacity : S → ℝ)
    (evaluation : I → S → ℂ) :
    WeightedDescentBounded capacity evaluation (fun _ => 0) := by
  refine ⟨0, le_rfl, fun u i => ?_⟩
  simp

/-- **A capacity-dominated evaluation with a bounded weight is a bounded descent.** -/
theorem weightedDescentBounded_of_bounds {S I : Type*} {capacity : S → ℝ}
    {evaluation : I → S → ℂ} {weight : I → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hcap : ∀ (u : S) (i : I), ‖evaluation i u‖ ≤ capacity u)
    (hweight : ∀ i, ‖weight i‖ ≤ M) :
    WeightedDescentBounded capacity evaluation weight := by
  refine ⟨M, hM, fun u i => ?_⟩
  rw [norm_mul]
  have hcapnn : 0 ≤ capacity u := le_trans (norm_nonneg _) (hcap u i)
  calc ‖evaluation i u‖ * ‖weight i‖ ≤ capacity u * M :=
        mul_le_mul (hcap u i) (hweight i) (norm_nonneg _) hcapnn
    _ = M * capacity u := by ring

/-- **Capacity escape is realized.**  With constant zero capacity the identity evaluation exceeds
every bound. -/
theorem capacityEscapesAt_id {I : Type*} (i : I) :
    CapacityEscapesAt (fun _ : ℂ => (0 : ℝ)) (fun _ : I => fun u : ℂ => u) i := by
  refine ⟨0, le_rfl, fun M => ⟨((M + 1 : ℝ) : ℂ), le_rfl, ?_⟩⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  have : M < |M + 1| := by
    rcases abs_cases (M + 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  exact this

end GaloisForLFunctions.HTGeometry
