import GaloisForLFunctions.HTGeometry.HilbertSphereTransport
import GaloisForLFunctions.HTGeometry.SphereBlockTail

/-!
# Small-block probability from sphere distances

Apply the Hilbert specialization of Tingley's extension theorem to the corpus's
`SphereBlockTail`: every boundary isometry preserves the entire block-tail
distribution and its block-dimension power law.
-/

open Metric MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E U V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The block event can be pulled back using sphere distances alone. -/
theorem hilbertSphereIsometry_block_event
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : BlockSpace U V) 1) (x : ℝ) :
    blockSmallOf U V (hilbertSphereExtension f) x = f ⁻¹' blockSmall U V x := by
  ext u
  simp only [blockSmallOf, blockSmall, Set.mem_setOf_eq, Set.mem_preimage,
    hilbertSphereExtension_unit]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace U] [BorelSpace U] [FiniteDimensional ℝ U]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- A sphere isometry transports block-event mass without an ambient splitting as input. -/
theorem hilbertSphereIsometry_block_mass
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : BlockSpace U V) 1) (x : ℝ) :
    (volume : Measure E).toSphere (f ⁻¹' blockSmall U V x) =
      (volume : Measure (BlockSpace U V)).toSphere (blockSmall U V x) := by
  rw [← hilbertSphereIsometry_block_event]
  exact toSphere_blockSmallOf U V (hilbertSphereExtension f) x

/-- The entire normalized block-tail distribution is determined by sphere isometry. -/
theorem hilbertSphereIsometry_block_probability
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : BlockSpace U V) 1) (x : ℝ) :
    ((volume : Measure E).toSphere (f ⁻¹' blockSmall U V x)).toReal /
        ((volume : Measure E).toSphere univ).toReal =
      shellProb U V (blockSmall U V x) := by
  rw [← hilbertSphereIsometry_block_event]
  exact shellProb_blockSmallOf U V (hilbertSphereExtension f) x

/-- Boundary-distance data retains the exact small-block power law from the corpus. -/
theorem hilbertSphereIsometry_block_power_law [Nontrivial V]
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : BlockSpace U V) 1) :
    ∃ C c : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : Set.Icc (0 : ℝ) 1,
      c * (t : ℝ) ^ Module.finrank ℝ U ≤
        ((volume : Measure E).toSphere (f ⁻¹' blockSmall U V t)).toReal /
          ((volume : Measure E).toSphere univ).toReal ∧
      ((volume : Measure E).toSphere (f ⁻¹' blockSmall U V t)).toReal /
          ((volume : Measure E).toSphere univ).toReal ≤
        C * (t : ℝ) ^ Module.finrank ℝ U := by
  obtain ⟨C, c, hc, hC, hup, hlo⟩ := exists_blockTail_bounds U V (hilbertSphereExtension f)
  refine ⟨C, c, hc, hC, fun t => ?_⟩
  rw [← hilbertSphereIsometry_block_event]
  exact ⟨hlo t t.property.1 t.property.2, hup t t.property.1⟩

end

end GaloisForLFunctions.HTGeometry
