import GaloisForLFunctions.RHTower.CHMDQuotientWeilForm
import GaloisForLFunctions.RHTower.CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality

/-!
# Parity and coercivity on the actual signed quotient

Reflection descends to an isometric involution. Its even and odd eigenspaces are
closed Hilbert spaces; the Weil form has its exact parity corrections and zero
cross terms. Every original source-domain coercivity statement transfers using
reduced graph mass. Raw source mass cannot descend, and the full Weil form cannot
be represented as an injective Hilbert norm because its ground class is nonzero.
-/

open MeasureTheory Set Topology
open scoped InnerProductSpace
noncomputable section


namespace RHTower.CHMDDoobGraph
open CHMDPolar CHMDClosedJump

theorem reflectGraph_mem_signedRadical {p : SourceGraph} (hp : p ∈ signedRadical) :
    reflectGraph p ∈ signedRadical := by
  intro q
  have h := sourcePair_reflectGraph p (reflectGraph q)
  rw [reflectGraph_reflectGraph] at h
  exact h.trans (hp (reflectGraph q))

theorem reflectGraph_mem_radical_orthogonal {p : SourceGraph} (hp : p ∈ signedRadicalᗮ) :
    reflectGraph p ∈ signedRadicalᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro k hk
  rw [← inner_reflectGraph]
  exact (Submodule.mem_orthogonal _ _).mp hp _ (reflectGraph_mem_signedRadical hk)

def quotientReflection : SignedQuotient →L[ℝ] SignedQuotient :=
  signedQuotientMk.comp (reflectGraphₗᵢ.toContinuousLinearMap.comp signedQuotientRepresentative)

theorem representative_quotientReflection (x : SignedQuotient) :
    signedQuotientRepresentative (quotientReflection x) =
      reflectGraph (signedQuotientRepresentative x) :=
  signedQuotientRepresentative_mk_of_mem
    (reflectGraph_mem_radical_orthogonal (signedQuotientRepresentative_mem x))

@[simp] theorem quotientReflection_mk (p : SourceGraph) :
    quotientReflection (signedQuotientMk p) = signedQuotientMk (reflectGraph p) := by
  change signedQuotientMk (reflectGraph (signedQuotientRepresentative (signedQuotientMk p))) = _
  rw [signedQuotientRepresentative_mk]
  apply (signedQuotientMk_eq_iff _ _).mpr
  rw [← reflectGraph_sub]
  apply reflectGraph_mem_signedRadical
  have h : reducedSource p - p = -criticalProjection p := by
    change (p - criticalProjection p) - p = -criticalProjection p
    abel
  rw [h]
  exact signedRadical.neg_mem (criticalProjection_mem p)

@[simp] theorem quotientReflection_involutive (x : SignedQuotient) :
    quotientReflection (quotientReflection x) = x := by
  obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
  rw [quotientReflection_mk, quotientReflection_mk, reflectGraph_reflectGraph]

theorem norm_quotientReflection (x : SignedQuotient) : ‖quotientReflection x‖ = ‖x‖ := by
  rw [← norm_signedQuotientRepresentative, representative_quotientReflection,
    norm_reflectGraph, norm_signedQuotientRepresentative]

/-- Literal parity reflection as an involutive isometric equivalence of the actual quotient. -/
def quotientReflectionEquiv : SignedQuotient ≃ₗᵢ[ℝ] SignedQuotient where
  toLinearEquiv :=
    { quotientReflection.toLinearMap with
      invFun := quotientReflection
      left_inv := quotientReflection_involutive
      right_inv := quotientReflection_involutive }
  norm_map' := norm_quotientReflection

theorem quotientPair_reflection (x y : SignedQuotient) :
    quotientPair (quotientReflection x) (quotientReflection y) = quotientPair x y := by
  obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
  obtain ⟨q, rfl⟩ := signedQuotientMk_surjective y
  rw [quotientReflection_mk, quotientReflection_mk, quotientPair_mk, quotientPair_mk,
    sourcePair_reflectGraph]

@[simp] theorem quotientCoshMoment_reflection (x : SignedQuotient) :
    quotientCoshMoment (quotientReflection x) = quotientCoshMoment x := by
  obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
  rw [quotientReflection_mk, quotientCoshMoment_mk, quotientCoshMoment_mk,
    reflectGraph_fst, inner_reflectMass, reflectMass_oneL]

@[simp] theorem quotientSinhMoment_reflection (x : SignedQuotient) :
    quotientSinhMoment (quotientReflection x) = -quotientSinhMoment x := by
  obtain ⟨p, rfl⟩ := signedQuotientMk_surjective x
  rw [quotientReflection_mk, quotientSinhMoment_mk, quotientSinhMoment_mk,
    reflectGraph_fst, inner_reflectMass, reflectMass_tanhL, inner_neg_right]

def quotientEvenSpace : Submodule ℝ SignedQuotient :=
  (quotientReflection - ContinuousLinearMap.id ℝ SignedQuotient).ker

def quotientOddSpace : Submodule ℝ SignedQuotient :=
  (quotientReflection + ContinuousLinearMap.id ℝ SignedQuotient).ker

@[simp] theorem mem_quotientEvenSpace (x : SignedQuotient) :
    x ∈ quotientEvenSpace ↔ quotientReflection x = x := by
  change quotientReflection x - x = 0 ↔ _
  exact sub_eq_zero

@[simp] theorem mem_quotientOddSpace (x : SignedQuotient) :
    x ∈ quotientOddSpace ↔ quotientReflection x = -x := by
  change quotientReflection x + x = 0 ↔ _
  exact eq_neg_iff_add_eq_zero.symm

theorem isClosed_quotientEvenSpace : IsClosed (quotientEvenSpace : Set SignedQuotient) :=
  (quotientReflection - ContinuousLinearMap.id ℝ SignedQuotient).isClosed_ker

theorem isClosed_quotientOddSpace : IsClosed (quotientOddSpace : Set SignedQuotient) :=
  (quotientReflection + ContinuousLinearMap.id ℝ SignedQuotient).isClosed_ker

instance quotientEvenSpace_complete : CompleteSpace quotientEvenSpace :=
  @IsClosed.completeSpace_coe SignedQuotient inferInstance signedQuotient_complete
    (quotientEvenSpace : Set SignedQuotient) isClosed_quotientEvenSpace

instance quotientOddSpace_complete : CompleteSpace quotientOddSpace :=
  @IsClosed.completeSpace_coe SignedQuotient inferInstance signedQuotient_complete
    (quotientOddSpace : Set SignedQuotient) isClosed_quotientOddSpace

theorem quotientSinhMoment_even (x : quotientEvenSpace) : quotientSinhMoment x = 0 := by
  have h := quotientSinhMoment_reflection x
  rw [(mem_quotientEvenSpace x).mp x.property] at h
  linarith

theorem quotientCoshMoment_odd (x : quotientOddSpace) : quotientCoshMoment x = 0 := by
  have h := quotientCoshMoment_reflection x
  rw [(mem_quotientOddSpace x).mp x.property] at h
  have hn : quotientCoshMoment (-x.val) = -quotientCoshMoment x.val := by
    rw [← neg_one_smul ℝ x.val, quotientCoshMoment_smul, neg_one_mul]
  rw [hn] at h
  linarith

theorem quotientWeilForm_even (x : quotientEvenSpace) :
    quotientWeilForm x = quotientEnergy x + 2 * quotientCoshMoment x ^ 2 := by
  simp only [quotientWeilForm, quotientWeilPair, quotientSinhMoment_even,
    quotientEnergy]
  ring

theorem quotientWeilForm_odd (x : quotientOddSpace) :
    quotientWeilForm x = quotientEnergy x - 2 * quotientSinhMoment x ^ 2 := by
  simp only [quotientWeilForm, quotientWeilPair, quotientCoshMoment_odd,
    quotientEnergy]
  ring

theorem quotientPair_even_odd (x : quotientEvenSpace) (y : quotientOddSpace) :
    quotientPair x y = 0 := by
  have h := quotientPair_reflection x y
  rw [(mem_quotientEvenSpace x).mp x.property, (mem_quotientOddSpace y).mp y.property] at h
  have hn : quotientPair x.val (-y.val) = -quotientPair x.val y.val := by
    rw [← neg_one_smul ℝ y.val, quotientPair_smul_right, neg_one_mul]
  rw [hn] at h
  linarith

theorem quotientWeilPair_even_odd (x : quotientEvenSpace) (y : quotientOddSpace) :
    quotientWeilPair x y = 0 := by
  simp [quotientWeilPair, quotientPair_even_odd, quotientSinhMoment_even,
    quotientCoshMoment_odd]

/-- Exact coercivity transport for every literal source domain, including window and parity
domains that need not be saturated under addition of radical vectors. -/
theorem quotientWeil_coercivity_on_image_iff (S : Set SourceGraph) (c : ℝ) :
    (∀ x ∈ signedQuotientMk '' S, c * ‖x‖ ^ 2 ≤ quotientWeilForm x) ↔
      ∀ p ∈ S, c * ‖reducedSource p‖ ^ 2 ≤ weilForm p := by
  constructor
  · intro h p hp
    simpa only [norm_signedQuotientMk, quotientWeilForm_mk] using h _ ⟨p, hp, rfl⟩
  · rintro h x ⟨p, hp, rfl⟩
    simpa only [norm_signedQuotientMk, quotientWeilForm_mk] using h p hp

theorem quotientEnergy_coercivity_on_image_iff (S : Set SourceGraph) (c : ℝ) :
    (∀ x ∈ signedQuotientMk '' S, c * ‖x‖ ^ 2 ≤ quotientEnergy x) ↔
      ∀ p ∈ S, c * ‖reducedSource p‖ ^ 2 ≤ sourceEnergy p := by
  constructor
  · intro h p hp
    simpa only [norm_signedQuotientMk, quotientEnergy_mk] using h _ ⟨p, hp, rfl⟩
  · rintro h x ⟨p, hp, rfl⟩
    simpa only [norm_signedQuotientMk, quotientEnergy_mk] using h p hp

/-- Original source mass does not define a function of the radical quotient. -/
theorem not_sourceMass_descends :
    ¬ ∃ m : SignedQuotient → ℝ, ∀ p : SourceGraph,
      m (signedQuotientMk p) = ‖p.val.fst‖ ^ 2 := by
  rintro ⟨m, hm⟩
  let k : SourceGraph := (criticalBandSequence 0).val
  have hk : signedQuotientMk k = 0 := (signedQuotientMk_eq_zero k).mpr (criticalBandSequence 0).property
  have hnorm : ‖k.val.fst‖ ^ 2 = 0 := by
    rw [← hm, hk, ← map_zero signedQuotientMk, hm]
    simp
  have hmass : k.val.fst = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg k.val.fst])
  have hzero : k = 0 := source_projection_injective hmass
  exact criticalBandSequence_linearIndependent.ne_zero 0 (Subtype.ext hzero)

/-- The full Weil form on this quotient cannot be the squared norm of an injective
linear realization: its nonzero ground class still lies in its polar radical. -/
theorem not_injective_quotientWeil_norm_representation (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] :
    ¬ ∃ L : SignedQuotient →ₗ[ℝ] H, Function.Injective L ∧
      ∀ x, ‖L x‖ ^ 2 = quotientWeilForm x := by
  rintro ⟨L, hL, hnorm⟩
  have hz := hnorm (signedQuotientMk (constantLift 1))
  rw [quotientWeilForm_ground] at hz
  have hzero : L (signedQuotientMk (constantLift 1)) = 0 :=
    norm_eq_zero.mp (by nlinarith [norm_nonneg (L (signedQuotientMk (constantLift 1)))])
  exact signedQuotientMk_ground_ne_zero (hL (hzero.trans L.map_zero.symm))

end RHTower.CHMDDoobGraph
