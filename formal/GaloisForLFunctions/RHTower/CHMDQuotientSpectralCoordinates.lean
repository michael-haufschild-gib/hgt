import GaloisForLFunctions.RHTower.CHMDSignedRadicalQuotient
import GaloisForLFunctions.RHTower.CHMDFullSpectralNullspace
import GaloisForLFunctions.RHTower.CHMDContinuousOrbitProjection

/-!
# Spectral coordinates and cardinal orbit projections on the signed quotient

Actual Xi-zero and pole evaluations descend to continuous linear readouts and
separate quotient classes. Each literal cardinal orbit projection descends to
a continuous idempotent with closed range, preserving signed symmetry and the
exact energy decomposition. No resolvent eigenspace identification is asserted.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower.CHMDDoobGraph

/-- The actual divisor and the two pole nodes detected by the signed form. -/
def QuotientSpectralNode := {z : ℂ // XiC z = 0 ∨ z = I / 2 ∨ z = -I / 2}

theorem QuotientSpectralNode.strip (z : QuotientSpectralNode) : |z.val.im| ≤ 1 / 2 := by
  rcases z.property with hz | hz | hz
  · exact (abs_im_lt_half_of_XiC_eq_zero hz).le
  · rw [hz]; norm_num
  · rw [hz]; norm_num

theorem QuotientSpectralNode.radical_zero (z : QuotientSpectralNode) (k : signedRadical) :
    graphFourierReadout k z.val = 0 := by
  rcases z.property with hz | hz | hz
  · exact radical_graphFourierReadout_zero k.property hz
  · rw [hz]
    exact (radical_graphFourierReadout_poles_zero k.property).1
  · rw [hz]
    exact (radical_graphFourierReadout_poles_zero k.property).2

def quotientSpectralReadout (z : QuotientSpectralNode) : SignedQuotient →L[ℝ] ℂ :=
  (graphFourierReadoutCLM z.val z.strip).comp signedQuotientRepresentative

@[simp] theorem quotientSpectralReadout_mk (z : QuotientSpectralNode) (p : SourceGraph) :
    quotientSpectralReadout z (signedQuotientMk p) = graphFourierReadout p z.val := by
  change graphFourierReadoutCLM z.val z.strip
    (signedQuotientRepresentative (signedQuotientMk p)) = _
  rw [signedQuotientRepresentative_mk, graphFourierReadoutCLM_apply]
  change graphFourierReadout (p - criticalProjection p) z.val = _
  rw [graphFourierReadout_sub _ _ z.strip,
    z.radical_zero ⟨criticalProjection p, criticalProjection_mem p⟩, sub_zero]

theorem mem_signedRadical_iff_spectral_nodes (p : SourceGraph) :
    p ∈ signedRadical ↔ ∀ z : QuotientSpectralNode, graphFourierReadout p z.val = 0 := by
  constructor
  · intro hp z
    exact z.radical_zero ⟨p, hp⟩
  · intro h
    apply (full_radical_iff_samples_zero p).mpr
    exact ⟨fun z hz => h ⟨z, Or.inl hz⟩,
      h ⟨I / 2, Or.inr (Or.inl rfl)⟩,
      h ⟨-I / 2, Or.inr (Or.inr rfl)⟩⟩

/-- Equality of quotient classes is exactly equality of all divisor and pole readings. -/
theorem signedQuotientMk_eq_iff_spectral_nodes (p q : SourceGraph) :
    signedQuotientMk p = signedQuotientMk q ↔
      ∀ z : QuotientSpectralNode, graphFourierReadout p z.val = graphFourierReadout q z.val := by
  rw [signedQuotientMk_eq_iff, mem_signedRadical_iff_spectral_nodes]
  constructor
  · intro h z
    have hz := h z
    rw [graphFourierReadout_sub _ _ z.strip, sub_eq_zero] at hz
    exact hz
  · intro h z
    rw [graphFourierReadout_sub _ _ z.strip, h z, sub_self]

theorem quotientSpectralReadout_ext (x y : SignedQuotient) :
    (∀ z, quotientSpectralReadout z x = quotientSpectralReadout z y) ↔ x = y := by
  obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
  obtain ⟨q, rfl⟩ := signedQuotientMk_surjective y
  simp only [quotientSpectralReadout_mk]
  exact (signedQuotientMk_eq_iff_spectral_nodes p q).symm

/-- The literal cardinal orbit projector acting on the Hilbert quotient. -/
def quotientOrbitProjection (a : PositiveXiZero) : SignedQuotient →L[ℝ] SignedQuotient :=
  signedQuotientMk.comp ((literalOrbitProjection a).comp signedQuotientRepresentative)

@[simp] theorem quotientOrbitProjection_mk (a : PositiveXiZero) (p : SourceGraph) :
    quotientOrbitProjection a (signedQuotientMk p) =
      signedQuotientMk (literalOrbitProjection a p) := by
  change signedQuotientMk (literalOrbitProjection a
    (signedQuotientRepresentative (signedQuotientMk p))) = _
  rw [signedQuotientRepresentative_mk]
  change signedQuotientMk ((literalOrbitFrame a).orbitProjection (p - criticalProjection p)) = _
  rw [map_sub, (literalOrbitFrame a).orbitProjection_radical a.property.2
    (criticalProjection_mem p), sub_zero]
  rfl

theorem quotientOrbitProjection_idempotent (a : PositiveXiZero) (x : SignedQuotient) :
    quotientOrbitProjection a (quotientOrbitProjection a x) = quotientOrbitProjection a x := by
  obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
  rw [quotientOrbitProjection_mk, quotientOrbitProjection_mk]
  change signedQuotientMk ((literalOrbitFrame a).orbitProjection
    ((literalOrbitFrame a).orbitProjection p)) = _
  rw [(literalOrbitFrame a).orbitProjection_idempotent a.property.1 a.property.2]
  rfl

/-- Every cardinal orbit has closed range in the actual quotient topology. -/
theorem isClosed_range_quotientOrbitProjection (a : PositiveXiZero) :
    IsClosed (Set.range (quotientOrbitProjection a)) := by
  have he : Set.range (quotientOrbitProjection a) =
      {x | quotientOrbitProjection a x = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact quotientOrbitProjection_idempotent a y
    · intro hx
      exact ⟨x, hx⟩
  rw [he]
  exact isClosed_eq (quotientOrbitProjection a).continuous continuous_id

theorem quotientOrbitProjection_signed_symmetric (a : PositiveXiZero) (x y : SignedQuotient) :
    quotientPair (quotientOrbitProjection a x) y =
      quotientPair x (quotientOrbitProjection a y) := by
  obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
  obtain ⟨q, rfl⟩ := signedQuotientMk_surjective y
  rw [quotientOrbitProjection_mk, quotientOrbitProjection_mk, quotientPair_mk, quotientPair_mk]
  exact (literalOrbitFrame a).orbitProjection_signed_symmetric a.property.1 a.property.2 p q

theorem quotientOrbitProjection_energy_split (a : PositiveXiZero) (x : SignedQuotient) :
    quotientEnergy x = quotientEnergy (quotientOrbitProjection a x) +
      quotientEnergy (x - quotientOrbitProjection a x) := by
  obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
  rw [quotientOrbitProjection_mk, ← map_sub, quotientEnergy_mk, quotientEnergy_mk,
    quotientEnergy_mk]
  exact (literalOrbitFrame a).orbitProjection_energy_split a.property.1 a.property.2 p

end RHTower.CHMDDoobGraph
