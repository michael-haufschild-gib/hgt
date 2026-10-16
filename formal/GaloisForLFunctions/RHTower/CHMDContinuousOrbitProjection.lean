import GaloisForLFunctions.RHTower.CHMDUniversalCardinalPairing

/-!
# Continuous signed projections onto individual Xi zero orbits

Every actual cardinal orbit splits off from the complete source graph. The
projection preserves its literal cosine sample, kills the signed radical,
and leaves a signed-orthogonal residual. A nonreal orbit gives the exact
rank-two hyperbolic block; a real orbit gives a positive rank-one block.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph

def graphCosineReadoutCLM (a : ℂ) : SourceGraph →L[ℝ] ℂ where
  toFun p := graphCosineReadout p a
  map_add' p q := graphCosineReadout_add p q a
  map_smul' c p := by simpa only [RingHom.id_apply, real_smul] using graphCosineReadout_smul c p a
  cont := continuous_graphCosineReadout a

def CardinalGraphFrame.orbitProjection {a : ℂ} (F : CardinalGraphFrame a) :
    SourceGraph →L[ℝ] SourceGraph :=
  if a.im = 0 then (Complex.reCLM.comp (graphCosineReadoutCLM a)).smulRight F.reVector
  else (2 : ℝ) • (Complex.reCLM.comp (graphCosineReadoutCLM a)).smulRight F.reVector +
    (-2 : ℝ) • (Complex.imCLM.comp (graphCosineReadoutCLM a)).smulRight F.imVector

theorem CardinalGraphFrame.orbitProjection_real {a : ℂ} (F : CardinalGraphFrame a)
    (hi : a.im = 0) (p : SourceGraph) :
    F.orbitProjection p = (graphCosineReadout p a).re • F.reVector := by
  simp [CardinalGraphFrame.orbitProjection, hi, graphCosineReadoutCLM]

theorem CardinalGraphFrame.orbitProjection_nonreal {a : ℂ} (F : CardinalGraphFrame a)
    (hi : a.im ≠ 0) (p : SourceGraph) :
    F.orbitProjection p = (2*(graphCosineReadout p a).re) • F.reVector +
      (-2*(graphCosineReadout p a).im) • F.imVector := by
  simp [CardinalGraphFrame.orbitProjection, hi, graphCosineReadoutCLM, smul_smul]

theorem CardinalGraphFrame.orbitProjection_readout {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p : SourceGraph) :
    graphCosineReadout (F.orbitProjection p) a = graphCosineReadout p a := by
  by_cases hi : a.im = 0
  · rw [F.orbitProjection_real hi, graphCosineReadout_smul, (F.real_samples ha hz hi).1, mul_one]
    apply Complex.ext <;> simp [graphCosineReadout_real hi]
  · rw [F.orbitProjection_nonreal hi, graphCosineReadout_add,
      graphCosineReadout_smul, graphCosineReadout_smul,
      (F.nonreal_samples ha hz hi).1, (F.nonreal_samples ha hz hi).2]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    <;> ring

theorem CardinalGraphFrame.orbitProjection_idempotent {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p : SourceGraph) :
    F.orbitProjection (F.orbitProjection p) = F.orbitProjection p := by
  by_cases hi : a.im = 0
  · rw [F.orbitProjection_real hi (F.orbitProjection p), F.orbitProjection_readout ha hz,
      F.orbitProjection_real hi p]
  · rw [F.orbitProjection_nonreal hi (F.orbitProjection p), F.orbitProjection_readout ha hz,
      F.orbitProjection_nonreal hi p]

theorem CardinalGraphFrame.orbitProjection_re {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) : F.orbitProjection F.reVector = F.reVector := by
  by_cases hi : a.im = 0
  · rw [F.orbitProjection_real hi, (F.real_samples ha hz hi).1]
    simp
  · rw [F.orbitProjection_nonreal hi, (F.nonreal_samples ha hz hi).1]
    norm_num

theorem CardinalGraphFrame.orbitProjection_im {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im ≠ 0) :
    F.orbitProjection F.imVector = F.imVector := by
  rw [F.orbitProjection_nonreal hi, (F.nonreal_samples ha hz hi).2]
  norm_num

theorem CardinalGraphFrame.orbitProjection_nonreal_range {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im ≠ 0) (q : SourceGraph) :
    (∃ p, F.orbitProjection p = q) ↔ ∃ r s : ℝ, r • F.reVector + s • F.imVector = q := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨2*(graphCosineReadout p a).re, -2*(graphCosineReadout p a).im,
      (F.orbitProjection_nonreal hi p).symm⟩
  · rintro ⟨r, s, rfl⟩
    refine ⟨r • F.reVector + s • F.imVector, ?_⟩
    rw [map_add, map_smul, map_smul, F.orbitProjection_re ha hz, F.orbitProjection_im ha hz hi]

theorem CardinalGraphFrame.orbitProjection_real_range {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im = 0) (q : SourceGraph) :
    (∃ p, F.orbitProjection p = q) ↔ ∃ r : ℝ, r • F.reVector = q := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(graphCosineReadout p a).re, (F.orbitProjection_real hi p).symm⟩
  · rintro ⟨r, rfl⟩
    refine ⟨r • F.reVector, ?_⟩
    rw [map_smul, F.orbitProjection_re ha hz]

theorem CardinalGraphFrame.orbitProjection_primitive {a : ℂ} (F : CardinalGraphFrame a)
    (p : SourceGraph) : sourcePair (constantLift 1) (F.orbitProjection p) = 0 := by
  by_cases hi : a.im = 0
  · rw [F.orbitProjection_real hi, sourcePair_symm, sourcePair_smul_left,
      sourcePair_symm F.reVector, F.re_primitive, mul_zero]
  · rw [F.orbitProjection_nonreal hi]
    exact F.primitive _ _

theorem CardinalGraphFrame.residual_readout {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p : SourceGraph) :
    graphCosineReadout (p-F.orbitProjection p) a = 0 := by
  change graphCosineReadoutCLM a (p-F.orbitProjection p) = 0
  rw [map_sub]
  change graphCosineReadout p a - graphCosineReadout (F.orbitProjection p) a = 0
  rw [F.orbitProjection_readout ha hz, sub_self]

theorem CardinalGraphFrame.residual_pair {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p : SourceGraph) :
    sourcePair (p-F.orbitProjection p) F.reVector = 0 ∧
      sourcePair (p-F.orbitProjection p) F.imVector = 0 := by
  rw [F.pair_re ha hz, F.pair_im ha hz, F.residual_readout ha hz]
  simp

theorem CardinalGraphFrame.residual_pair_plane {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p : SourceGraph) (r s : ℝ) :
    sourcePair (p-F.orbitProjection p) (r • F.reVector + s • F.imVector) = 0 := by
  rw [sourcePair_symm, sourcePair_add_left, sourcePair_smul_left, sourcePair_smul_left,
    sourcePair_symm F.reVector, sourcePair_symm F.imVector,
    (F.residual_pair ha hz p).1, (F.residual_pair ha hz p).2]
  simp

theorem CardinalGraphFrame.residual_pair_projection {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p q : SourceGraph) :
    sourcePair (p-F.orbitProjection p) (F.orbitProjection q) = 0 := by
  by_cases hi : a.im = 0
  · rw [F.orbitProjection_real hi q, sourcePair_symm, sourcePair_smul_left,
      sourcePair_symm F.reVector, (F.residual_pair ha hz p).1, mul_zero]
  · rw [F.orbitProjection_nonreal hi q]
    exact F.residual_pair_plane ha hz p (2*(graphCosineReadout q a).re)
      (-2*(graphCosineReadout q a).im)

theorem CardinalGraphFrame.orbitProjection_signed_symmetric {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p q : SourceGraph) :
    sourcePair (F.orbitProjection p) q = sourcePair p (F.orbitProjection q) := by
  have hp := F.residual_pair_projection ha hz p q
  have hq := F.residual_pair_projection ha hz q p
  rw [sourcePair_sub_left] at hp hq
  rw [sourcePair_symm q, sourcePair_symm (F.orbitProjection q)] at hq
  linarith

/-- The split is orthogonal for the actual signed arithmetic form. -/
theorem CardinalGraphFrame.orbitProjection_energy_split {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (p : SourceGraph) :
    sourceEnergy p = sourceEnergy (F.orbitProjection p) + sourceEnergy (p-F.orbitProjection p) := by
  have h := sourceEnergy_linearCombination_of_pair_zero
    (F.residual_pair_projection ha hz p p) 1 1
  simp only [one_smul, one_pow, one_mul, sub_add_cancel] at h
  exact h.trans (add_comm _ _)

theorem CardinalGraphFrame.orbitProjection_nonreal_energy {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hi : a.im ≠ 0) (p : SourceGraph) :
    sourceEnergy (F.orbitProjection p) = 4 * cardinalPositiveMass a *
      ((graphCosineReadout p a).re^2 - (graphCosineReadout p a).im^2) := by
  rw [F.orbitProjection_nonreal hi, F.nonreal_energy ha hi]
  ring

theorem CardinalGraphFrame.orbitProjection_real_energy {a : ℂ} (F : CardinalGraphFrame a)
    (hi : a.im = 0) (p : SourceGraph) :
    sourceEnergy (F.orbitProjection p) = cardinalPositiveMass a * (graphCosineReadout p a).re^2 := by
  have h := F.real_energy hi (graphCosineReadout p a).re 0
  simpa only [zero_smul, add_zero, F.orbitProjection_real hi] using h

theorem CardinalGraphFrame.orbitProjection_radical {a : ℂ} (F : CardinalGraphFrame a)
    (hz : XiC a = 0) {p : SourceGraph} (hp : p ∈ signedRadical) : F.orbitProjection p = 0 := by
  by_cases hi : a.im = 0
  · rw [F.orbitProjection_real hi, radical_graphCosineReadout_zero hp hz]
    simp
  · rw [F.orbitProjection_nonreal hi, radical_graphCosineReadout_zero hp hz]
    simp

theorem CardinalGraphFrame.orbitProjection_outside_readout {a b : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hb : XiC b = 0) (ho : b ∉ cardinalOrbit a)
    (p : SourceGraph) : graphCosineReadout (F.orbitProjection p) b = 0 := by
  obtain ⟨hr, hi⟩ := F.readouts_outside_orbit ha hz hb ho
  by_cases hreal : a.im = 0
  · rw [F.orbitProjection_real hreal, graphCosineReadout_smul, hr, mul_zero]
  · rw [F.orbitProjection_nonreal hreal, graphCosineReadout_add,
      graphCosineReadout_smul, graphCosineReadout_smul, hr, hi]
    simp

theorem CardinalGraphFrame.orbitProjection_annihilates {a b : ℂ}
    (F : CardinalGraphFrame a) (G : CardinalGraphFrame b)
    (ha : 0 < a.re) (hz : XiC a = 0) (hb : XiC b = 0) (ho : b ∉ cardinalOrbit a)
    (p : SourceGraph) : G.orbitProjection (F.orbitProjection p) = 0 := by
  by_cases hi : b.im = 0
  · rw [G.orbitProjection_real hi, F.orbitProjection_outside_readout ha hz hb ho]
    simp
  · rw [G.orbitProjection_nonreal hi, F.orbitProjection_outside_readout ha hz hb ho]
    simp

theorem CardinalGraphFrame.distinct_orbit_projections {a b : ℂ}
    (F : CardinalGraphFrame a) (G : CardinalGraphFrame b)
    (ha : 0 < a.re) (hza : XiC a = 0) (hb : 0 < b.re) (hzb : XiC b = 0)
    (ho : b ∉ cardinalOrbit a) (p : SourceGraph) :
    G.orbitProjection (F.orbitProjection p) = 0 ∧
      F.orbitProjection (G.orbitProjection p) = 0 := by
  exact ⟨F.orbitProjection_annihilates G ha hza hzb ho p,
    G.orbitProjection_annihilates F hb hzb hza (fun h => ho (cardinalOrbit_mem_reverse h)) p⟩

/-- The real rank-one splitting has an unconditional nonzero instance. -/
theorem exists_nonzero_real_orbitProjection :
    ∃ (a : ℝ) (F : CardinalGraphFrame (a : ℂ)), 0 < a ∧ XiC (a : ℂ) = 0 ∧
      F.orbitProjection F.reVector = F.reVector ∧ F.reVector ≠ 0 := by
  obtain ⟨a, F, ha, hz, hpos, _, _⟩ := exists_positive_primitive_cardinal_frame
  refine ⟨a, F, ha, hz, ?_, ?_⟩
  · rw [F.orbitProjection_real (by simp), (F.real_samples ha hz (by simp)).1]
    simp
  · intro heq
    rw [heq, ← sourcePair_self] at hpos
    simp [sourcePair] at hpos

/-- Actual positive-half-plane Xi zeros, with their membership proofs retained. -/
def PositiveXiZero := {a : ℂ // 0 < a.re ∧ XiC a = 0}

def literalOrbitFrame (a : PositiveXiZero) : CardinalGraphFrame a.val :=
  Classical.choice (exists_cardinalGraphFrame a.property.1 a.property.2)

/-- A concrete continuous operator for every actual zero orbit; no frame is assumed. -/
def literalOrbitProjection (a : PositiveXiZero) : SourceGraph →L[ℝ] SourceGraph :=
  (literalOrbitFrame a).orbitProjection

theorem literalOrbitProjection_splitting (a : PositiveXiZero) (p : SourceGraph) :
    graphCosineReadout (literalOrbitProjection a p) a.val = graphCosineReadout p a.val ∧
      literalOrbitProjection a (literalOrbitProjection a p) = literalOrbitProjection a p ∧
      sourcePair (constantLift 1) (literalOrbitProjection a p) = 0 ∧
      sourceEnergy p = sourceEnergy (literalOrbitProjection a p) +
        sourceEnergy (p-literalOrbitProjection a p) := by
  exact ⟨(literalOrbitFrame a).orbitProjection_readout a.property.1 a.property.2 p,
    (literalOrbitFrame a).orbitProjection_idempotent a.property.1 a.property.2 p,
    (literalOrbitFrame a).orbitProjection_primitive p,
    (literalOrbitFrame a).orbitProjection_energy_split a.property.1 a.property.2 p⟩

theorem literalOrbitProjection_kills_radical (a : PositiveXiZero) (p : signedRadical) :
    literalOrbitProjection a p.val = 0 :=
  (literalOrbitFrame a).orbitProjection_radical a.property.2 p.property

theorem exists_nonzero_literalOrbitProjection :
    ∃ a : PositiveXiZero, literalOrbitProjection a ≠ 0 := by
  obtain ⟨a, _, ha, hz, _, _, _⟩ := exists_positive_primitive_cardinal_frame
  let z : PositiveXiZero := ⟨(a : ℂ), ha, hz⟩
  refine ⟨z, ?_⟩
  intro h
  have he := (literalOrbitFrame z).orbitProjection_re z.property.1 z.property.2
  change literalOrbitProjection z (literalOrbitFrame z).reVector = _ at he
  rw [h, zero_apply] at he
  have hpos : 0 < sourceEnergy (literalOrbitFrame z).reVector := by
    rw [(literalOrbitFrame z).re_energy]
    exact cardinalPositiveMass_pos_of_zero z.property.2
  rw [← he, ← sourcePair_self] at hpos
  simp [sourcePair] at hpos

end RHTower.CHMDDoobGraph
