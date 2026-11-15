import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.BinaryCSSDistance
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.FiberPullbackCodes

/-!
# Exact distance two for binary fiber CSS groups

Even fibers make the full pullback code self-orthogonal. Orthogonality
to the constant word excludes logical operators of weight one. If one
fiber has more than two points, its two-point indicators are cycles;
a third point proves that they are not constant on that fiber, hence
not boundaries. Their Pauli encodings attain distance two.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Quantum.Stabilizer.Homological
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β]

omit [DecidableEq ι] in
/-- Orthogonality to the constant binary word forces positive even weight. -/
theorem binaryDual_weight_ge_two (C : Submodule (ZMod 2) (ι → ZMod 2))
    (h1 : (fun _ => 1) ∈ C) (c : ι → ZMod 2) (hc : c ≠ 0)
    (horth : ∀ d ∈ C, twistedPair (RingHom.id _) c d = 0) : 2 ≤ weight c := by
  have hsum : (∑ x, c x) = 0 := by
    simpa only [twistedPair, RingHom.id_apply, mul_one] using horth _ h1
  rw [binary_sum_eq_weight] at hsum
  have heven := (CharP.cast_eq_zero_iff (ZMod 2) 2 (weight c)).mp hsum
  have hpos : 0 < weight c := by
    obtain ⟨x, hx⟩ : ∃ x, c x ≠ 0 := by
      by_contra! h
      exact hc (funext h)
    apply Finset.card_pos.mpr
    refine ⟨x, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx
  obtain ⟨k, hk⟩ := heven
  omega

/-- The binary indicator of two coordinates. -/
def binaryPairIndicator (a b : ι) : ι → ZMod 2 :=
  fun i => if i = a ∨ i = b then 1 else 0

/-- Distinct coordinates give weight exactly two. -/
theorem binaryPairIndicator_weight (a b : ι) (hab : a ≠ b) :
    weight (binaryPairIndicator a b) = 2 := by
  unfold weight
  calc
    _ = ({a, b} : Finset ι).card := by
      apply congrArg Finset.card
      ext i
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        simp [binaryPairIndicator, hia, hib]
    _ = 2 := Finset.card_pair hab

/-- Pairing a two-point indicator reads the sum of its two coordinates. -/
theorem binaryPairIndicator_pairing (a b : ι) (hab : a ≠ b) (d : ι → ZMod 2) :
    twistedPair (RingHom.id _) (binaryPairIndicator a b) d = d a + d b := by
  unfold twistedPair
  simp only [RingHom.id_apply]
  have hs : (∑ i ∈ ({a, b} : Finset ι), binaryPairIndicator a b i * d i) =
      ∑ i, binaryPairIndicator a b i * d i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hi' : ¬ (i = a ∨ i = b) := by simpa only [Finset.mem_insert,
      Finset.mem_singleton] using hi
    simp only [binaryPairIndicator, if_neg hi', zero_mul]
  rw [← hs, Finset.sum_pair hab]
  simp only [binaryPairIndicator, true_or, or_true, if_true, one_mul]

omit [Fintype β] in
/-- Equal fiber values cancel in characteristic two. -/
theorem binaryPairIndicator_fiber_orthogonal (π : ι → β) (a b : ι)
    (hab : a ≠ b) (hπ : π a = π b) (d : ι → ZMod 2) (hd : d ∈ fiberCode π) :
    twistedPair (RingHom.id _) (binaryPairIndicator a b) d = 0 := by
  obtain ⟨f, rfl⟩ := hd
  rw [binaryPairIndicator_pairing a b hab]
  change f (π a) + f (π b) = 0
  rw [hπ, CharTwo.add_self_eq_zero]

omit [Fintype ι] [Fintype β] in
/-- A third point in the fiber witnesses failure to be a pullback. -/
theorem binaryPairIndicator_not_mem_fiberCode (π : ι → β) (a b t : ι)
    (hta : t ≠ a) (htb : t ≠ b) (hπ : π t = π a) :
    binaryPairIndicator a b ∉ fiberCode π := by
  rintro ⟨f, hf⟩
  have ha := congrFun hf a
  have ht := congrFun hf t
  change f (π a) = binaryPairIndicator a b a at ha
  change f (π t) = binaryPairIndicator a b t at ht
  have hzero : f (π a) = 0 := by
    simpa only [binaryPairIndicator, hπ, hta, htb, false_or, if_false] using ht
  have hone : f (π a) = 1 := by
    simpa only [binaryPairIndicator, true_or, if_true] using ha
  exact zero_ne_one (hzero.symm.trans hone)

#print axioms binaryPairIndicator_fiber_orthogonal

omit [Fintype β] in
/-- A fiber with at least three points supplies a weight-two dual word outside the code. -/
theorem fiberCode_exists_weight_two_nonboundary (π : ι → β) (b : β)
    (hbig : 2 < Nat.card {i // π i = b}) :
    ∃ c : ι → ZMod 2,
      (∀ d ∈ fiberCode π, twistedPair (RingHom.id _) c d = 0) ∧
        c ∉ fiberCode π ∧ weight c = 2 := by
  letI : Fintype {i // π i = b} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hbig
  obtain ⟨a, d, t, had, hat, hdt⟩ := Fintype.two_lt_card_iff.mp hbig
  have had' : a.val ≠ d.val := fun h => had (Subtype.ext h)
  have hta' : t.val ≠ a.val := fun h => hat (Subtype.ext h.symm)
  have htd' : t.val ≠ d.val := fun h => hdt (Subtype.ext h.symm)
  refine ⟨binaryPairIndicator a.val d.val, ?_, ?_, binaryPairIndicator_weight _ _ had'⟩
  · exact binaryPairIndicator_fiber_orthogonal π _ _ had' (a.property.trans d.property.symm)
  · exact binaryPairIndicator_not_mem_fiberCode π _ _ _ hta' htd'
      (t.property.trans a.property.symm)

#print axioms fiberCode_exists_weight_two_nonboundary

/-- A self-orthogonal binary code containing the constant word has no weight-one logicals. -/
theorem unitalBinaryHomologicalCode_logical_weight_ge_two
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (hC : SelfOrthogonal (RingHom.id _) C)
    (h1 : (fun _ => 1) ∈ C)
    (g : Quantum.NQubitPauliGroupElement (selfOrthogonalHomologicalCode C hC).numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      (selfOrthogonalHomologicalCode C hC).homologicalStabilizerGroup) :
    2 ≤ Quantum.NQubitPauliGroupElement.weight g := by
  apply selfOrthogonalHomologicalCode_logical_weight_ge C hC 2 ?_ g hg
  intro c hc hb
  apply binaryDual_weight_ge_two C h1 c
  · intro hz
    apply hb
    rw [hz]
    exact Submodule.zero_mem _
  · exact (binaryCheckSyndrome_eq_zero_iff C c).mp hc

/-- Even fibers and one fiber larger than two give exact Pauli distance two. -/
theorem fiberHomologicalCode_distance_two (π : ι → β)
    (hπ : ∀ b, 2 ∣ Nat.card {i // π i = b}) (b : β)
    (hbig : 2 < Nat.card {i // π i = b}) :
    let X := selfOrthogonalHomologicalCode (fiberCode π)
      (fiberCode_selfOrthogonal 2 π hπ (RingHom.id (ZMod 2)))
    (∀ g : Quantum.NQubitPauliGroupElement X.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g X.homologicalStabilizerGroup →
        2 ≤ Quantum.NQubitPauliGroupElement.weight g) ∧
    ∃ g : Quantum.NQubitPauliGroupElement X.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g X.homologicalStabilizerGroup ∧
        Quantum.NQubitPauliGroupElement.weight g = 2 := by
  dsimp only
  constructor
  · exact unitalBinaryHomologicalCode_logical_weight_ge_two _ _ (one_mem_fiberCode π)
  · apply homological_exists_logical_weight
    obtain ⟨c, hc, hb, hw⟩ := fiberCode_exists_weight_two_nonboundary π b hbig
    refine ⟨c, (binaryCheckSyndrome_eq_zero_iff (fiberCode π) c).mpr hc, ?_, hw⟩
    rwa [selfOrthogonalHomologicalCode_boundaries]

#print axioms fiberHomologicalCode_distance_two
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
