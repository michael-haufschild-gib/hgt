import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Budget
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.FirstCircuitSaturationBoundary

/-! # Physical travel time controlled by two weak bonds -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open Subregister DiagonalSynthesis PrescribedTimes
noncomputable section

private def edgeCoords {n : ℕ} (a : Fin (n+1)) (ab : Fin 3 × Fin 3) : PrefixIndex n :=
  (pathCoeffEquiv n).symm (Sum.inr (a,ab))

private def edgeSet {n : ℕ} (a : Fin (n+1)) := Finset.univ.image (edgeCoords a)

/-- The independent coordinates of the two erased interactions. -/
def cutSet {n : ℕ} (a b : Fin (n+1)) := edgeSet a ∪ edgeSet b

theorem cutSet_card {n : ℕ} {a b : Fin (n+1)} (hab : a < b) : (cutSet a b).card = 18 := by
  classical
  have hcard (g : Fin (n+1)) : (edgeSet g).card = 9 := by
    have hi : Function.Injective (edgeCoords g) := fun i j he =>
      (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv n).symm.injective he))).2
    rw [edgeSet,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  have hdis : Disjoint (edgeSet a) (edgeSet b) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y,_,he⟩ := Finset.mem_image.mp hj
    exact hab.ne' (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv n).symm.injective he))).1
  rw [cutSet,Finset.card_union_of_disjoint hdis,hcard,hcard]

theorem onsite_not_in_cutSet {n : ℕ} (a b : Fin (n+1)) (i : Fin (n+2) × Fin 3) :
    (pathCoeffEquiv n).symm (Sum.inl i) ∉ cutSet a b := by
  have h (g : Fin (n+1)) : (pathCoeffEquiv n).symm (Sum.inl i) ∉ edgeSet g := by
    intro hi
    obtain ⟨ab,_,he⟩ := Finset.mem_image.mp hi
    cases (pathCoeffEquiv n).symm.injective he
  exact fun hh => (Finset.mem_union.mp hh).elim (h a) (h b)

private theorem small_edge {n : ℕ} (u : PathShell n) (a : Fin (n+1)) {δ : ℝ}
    (h : ∀ ab, |u (Sum.inr (a,ab))| ≤ δ) : ‖edgePart u a‖ ≤ 9*δ := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ab : Fin 3 × Fin 3, δ := Finset.sum_le_sum fun ab _ => by
      rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
      exact h ab
    _ = _ := by simp [nsmul_eq_mul]

/-- While t times the total strength of the two cut bonds is small, the
exact circuits for the three blocks approximate every signed increment. -/
theorem weak_increment {n : ℕ} (u : PathShell n) {a b : Fin (n+1)} (hab : a < b)
    (hL : 2 ≤ (leftBlock a).card) (hM : 2 ≤ (middleBlock a b).card) (hR : 2 ≤ (rightBlock b).card)
    {T : ℝ} (hT : 0 < T) (hweak : ∀ i ∈ cutSet a b, |u (pathCoeffEquiv n i)| ≤ 1/(1800*T))
    (t : ℝ) (ht : |t| ≤ T) :
    HasProjectiveCircuitApproximation (n+2) (1/100:ℝ)
      (packetCost (leftBlock a).card + packetCost (middleBlock a b).card + packetCost (rightBlock b).card)
      (unitaryEvolution (pathHamiltonian u) t) := by
  let K := packet u (leftBlock a) + packet u (middleBlock a b) + packet u (rightBlock b)
  have hK : IsSelfAdjoint K := ((packet_selfAdjoint u _).add (packet_selfAdjoint u _)).add (packet_selfAdjoint u _)
  have he (g : Fin (n+1)) (hg : edgeSet g ⊆ cutSet a b) : ‖edgePart u g‖ ≤ 9*(1/(1800*T)) := by
    apply small_edge
    intro ab
    have h := hweak (edgeCoords g ab) (hg (Finset.mem_image.mpr ⟨ab,Finset.mem_univ _,rfl⟩))
    simpa only [edgeCoords,Equiv.apply_symm_apply] using h
  have hnorm : ‖pathHamiltonian u-K‖ ≤ 18*(1/(1800*T)) := by
    rw [show pathHamiltonian u-K = _ from sub_three_packets u hab]
    linarith only [norm_add_le (edgePart u a) (edgePart u b),he a Finset.subset_union_left,he b Finset.subset_union_right]
  obtain ⟨z,hz,C,hC,hU⟩ := three_block_synthesis u a b hab hL hM hR t
  refine ⟨z,hz,C,hC,?_⟩
  change unitaryEvolution K t = _ at hU
  rw [←hU]
  calc
    _ ≤ |t| * ‖pathHamiltonian u-K‖ := norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u) hK t
    _ ≤ T*(18*(1/(1800*T))) := mul_le_mul ht hnorm (norm_nonneg _) hT.le
    _ = _ := by field_simp; ring

/-- For the actual first crossing, the cut-bond clock bounds both the onset
and the first return wait. Maximal projectivity only enters to guarantee that
the crossing exists, including inside arbitrarily small weak-bond boxes. -/
theorem weak_first_passage {n d : ℕ} (u : PathShell n) (e : (Fin (n+2) → Bool) ≃ Fin (d+1))
    (hmax : MaximallyProjectiveEnergy (fun i => (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues (e.symm i)))
    (hent : atMostQuarterCircuitEntropyBound (n+2) (nearHilbertContinuousCircuitBudget (n+2)) < ((2^d:ℕ):ℝ))
    {a b : Fin (n+1)} (hab : a < b)
    (hL : 2 ≤ (leftBlock a).card) (hM : 2 ≤ (middleBlock a b).card) (hR : 2 ≤ (rightBlock b).card)
    (hcost : 2*(packetCost (leftBlock a).card + packetCost (middleBlock a b).card + packetCost (rightBlock b).card)
      ≤ nearHilbertContinuousCircuitBudget (n+2)) {T : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ cutSet a b, |u (pathCoeffEquiv n i)| ≤ 1/(1800*T)) :
    let x := fun i => u (pathCoeffEquiv n i)
    let P := nearHilbertContinuousCircuitBudget (n+2)
    T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x := by
  intro x P
  let H : selfAdjoint (Register (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
  obtain ⟨σ,hσ,hd,hpre,hnone,_⟩ := first_circuit_threshold_of_increment e H hmax hent T hT.le hcost
    (weak_increment u hab hL hM hR hT hw)
  have hdist (j : ℕ) (t : ℝ) : pathGateDistance n j x t = orbitCircuitDistance H j t := by
    rw [pathGateDistance,numberedGenerator_shell u]; rfl
  have ho := crossingOrigin_eq_of_first (hT.trans hσ).le ((hdist P σ).trans hd)
    (fun t ht => (hdist P t).trans_lt (hpre t ht))
  refine ⟨ho.symm ▸ hσ,fun s hs => ?_⟩
  by_contra! h
  obtain ⟨t,ht,hvisit⟩ := (crossingWait_le_iff n P s x T).mp h
  rw [ho] at ht
  have hsep := hnone t ⟨(sub_le_self σ hT.le).trans ht.1,ht.2⟩
  obtain ⟨z,hz,C,hC,hh⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr
    ((hdist s t).symm.trans_le hvisit)
  exact (hsep z hz C (hC.trans hs)).not_ge hh

#print axioms cutSet_card
#print axioms weak_first_passage
end
end GaloisForLFunctions.HTGeometry.WeakBonds
