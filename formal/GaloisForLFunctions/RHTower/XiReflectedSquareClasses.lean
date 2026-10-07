import GaloisForLFunctions.RHTower.XiReflectedFactorSeparation
import GaloisForLFunctions.RHTower.XiSignedFactorSquareClasses
import GaloisForLFunctions.HTGeometry.EntireOddFactorPackets

open Complex Filter Topology
noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

theorem reflected_factor_packet_not_isSquare (S T : Finset ℕ) (e : ℕ)
    (hne : T.Nonempty) (hS : ∀ n ∈ S, 2 ≤ n) (hT : ∀ n ∈ T, 2 ≤ n) :
    ¬ IsSquare (xiElement ^ e * (∏ n ∈ S, factorElement n) *
      ∏ n ∈ T, reflectedElement n) := by
  classical
  obtain ⟨n, hn⟩ := hne
  obtain ⟨z, hz, hodd⟩ := exists_odd_zero_reflectedFactor (hT n hn)
  have hu : packet S e z ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (xi_ne_zero_of_reflectedFactor_zero hz))
    exact Finset.prod_ne_zero_iff.mpr fun m hm =>
      deletionFactor_ne_zero_of_reflectedFactor_zero (hS m hm) (hT n hn) hz
  have hothers (m : ℕ) (hm : m ∈ T) (hmn : m ≠ n) : reflectedFactor m z ≠ 0 := by
    intro hmz
    exact hmn (reflectedFactor_label_injective_at_zero
      (by have := hT m hm; omega) (by have := hT n hn; omega) hmz hz)
  have hns := entire_packet_not_isSquare_of_odd_factor reflectedFactor
    reflectedFactor_differentiable (packet_differentiable S e) T hn hodd hu hothers
  change ¬ IsSquare (packetElement S e * ∏ n ∈ T, reflectedElement n) at hns
  rwa [packetElement_eq] at hns

/-- Exact global independence of Xi and both orientations of the factor family. -/
theorem reflected_factor_packet_isSquare_iff (S T : Finset ℕ) (e : ℕ)
    (hS : ∀ n ∈ S, 2 ≤ n) (hT : ∀ n ∈ T, 2 ≤ n) :
    IsSquare (xiElement ^ e * (∏ n ∈ S, factorElement n) *
      ∏ n ∈ T, reflectedElement n) ↔ Even e ∧ S = ∅ ∧ T = ∅ := by
  constructor
  · intro hs
    have ht : T = ∅ := by
      by_contra ht
      exact reflected_factor_packet_not_isSquare S T e
        (Finset.nonempty_iff_ne_empty.mpr ht) hS hT hs
    subst T
    have hbase := (signed_factor_packet_isSquare_iff S ∅ e hS (by simp)).mp
      (by simpa only [Finset.prod_empty, mul_one] using hs)
    exact ⟨hbase.1, hbase.2.1, rfl⟩
  · rintro ⟨he, rfl, rfl⟩
    simpa only [Finset.prod_empty, mul_one] using he.isSquare_pow xiElement

/-- Every reflected packet survives in the actual infinite original marked tower. -/
theorem reflected_packet_not_isSquare_markedExtension (T : Finset ℕ) (e : ℕ)
    (hne : T.Nonempty) (hT : ∀ n ∈ T, 2 ≤ n) :
    ¬ IsSquare (algebraMap K Marked (xiElement ^ e * ∏ n ∈ T, reflectedElement n)) := by
  classical
  apply not_isSquare_markedExtension_of_twists
  intro S
  have hS : ∀ n ∈ S.image (fun i => i + 2), 2 ≤ n := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    omega
  have hns := reflected_factor_packet_not_isSquare
    (S.image (fun i => i + 2)) T (e + S.card) hne hS hT
  have hp : (∏ n ∈ S.image (fun i => i + 2), factorElement n) =
      ∏ i ∈ S, factorElement (i + 2) := by
    rw [Finset.prod_image]
    intro i _ j _ hij
    exact Nat.add_right_cancel hij
  rw [hp, pow_add] at hns
  have he : (xiElement ^ e * ∏ n ∈ T, reflectedElement n) * ∏ i ∈ S, radicand i =
      xiElement ^ e * xiElement ^ S.card * (∏ i ∈ S, factorElement (i + 2)) *
        ∏ n ∈ T, reflectedElement n := by
    rw [prod_radicand]
    ring
  rw [he]
  exact hns

theorem xi_mul_reflectedElement_not_isSquare_markedExtension {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSquare (algebraMap K Marked (xiElement * reflectedElement n)) := by
  simpa only [pow_one, Finset.prod_singleton] using
    reflected_packet_not_isSquare_markedExtension {n} 1 (by simp) (by simpa using hn)

/-- Even an endomorphism cannot lift the functional equation to the one-sided marked field. -/
theorem no_functional_reflection_lift_to_marked :
    ¬ ∃ φ : Marked →+* Marked, ∀ a : K,
      φ (algebraMap K Marked a) = algebraMap K Marked (planeReflectEquiv 1 a) := by
  rintro ⟨φ, hφ⟩
  have hu : φ (markedRoot 0) * φ (markedRoot 0) =
      algebraMap K Marked (xiElement * reflectedElement 2) := by
    rw [← map_mul, markedRoot_sq, hφ, radicand, map_mul, planeReflectEquiv_xiElement]
    rfl
  exact (xi_mul_reflectedElement_not_isSquare_markedExtension (n := 2) (by decide))
    ⟨φ (markedRoot 0), hu.symm⟩

end RHTower.XiGlobalKummer
