import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.RelativeCircuit
import GaloisForLFunctions.HTGeometry.UniformFixedErrorSpectralTorusCircuitHardnessLaw
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw

/-! # Restricted circuit fits force weighted spectral overlap -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private wave from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
noncomputable section
private abbrev Config (N : ℕ) := Fin N → Bool

private theorem weighted_overlap {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1) (y z d : I → ℂ)
    (hd : ∀ i, ‖d i‖=1) (hz : ∀ i, z i*d i=1)
    (c : ℂ) (hc : ‖c‖=1) (κ : ℝ) (he : ∑ i, w i*‖c*y i-z i‖ ≤ κ) :
    1-κ ≤ ‖∑ i, (w i:ℂ)*y i*d i‖ := by
  let S := ∑ i, (w i:ℂ)*y i*d i
  have hsum' : (∑ i, (w i:ℂ))=1 := by exact_mod_cast hsum
  have hlin : c*S-1=∑ i, (w i:ℂ)*((c*y i-z i)*d i) := by
    rw [←hsum',show c*S=∑ i, c*((w i:ℂ)*y i*d i) from mul_sum ..,←sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [sub_mul,hz]
    ring
  have herr : ‖c*S-1‖ ≤ κ := by
    rw [hlin]
    apply (norm_sum_le ..).trans
    apply le_trans _ he
    apply sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw i),hd,mul_one]
  have hh := norm_sub_le_norm_sub_add_norm_sub (1:ℂ) (c*S) 0
  rw [sub_zero,sub_zero,norm_one,norm_sub_rev (1:ℂ),norm_mul,hc,one_mul] at hh
  change 1-κ ≤ ‖S‖
  linarith only [hh,herr]

/-- Mean diagonal error for a single circuit with one global phase in a
specified energy frame. The weights represent a distribution of inputs. -/
def weightedFit {N : ℕ} (U : unitaryGroup (Config N) ℂ) (R : Finset (Config N))
    (w : R → ℝ) (s : ℕ) (ε : ℝ) (z : Config N → ℂ) : Prop :=
  ∃ c : ℂ, ‖c‖=1 ∧ ∃ C : TwoQubitCircuit N, C.gateCount ≤ s ∧
    ∑ i : R, w i*‖c*(U⁻¹*C.eval*U).val i.val i.val-z i.val‖ ≤ ε

/-- A physical fit gives a weighted diagonal fit at a loss equal to the
weighted phase error. The maximum weight discounts the unweighted error sum. -/
theorem physical_weighted_fit {n s : ℕ} (x : FieldPair n) (a b t ε δ W : ℝ)
    (R : Finset (Config (n+2))) (w : R → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i=1) (hcap : ∀ i, w i ≤ W)
    (hread : W*readingError R a b x t ≤ δ)
    (hfit : rotated a b x ∈ BlockDilations.affordableDraw n s ε t) :
    let U := (generator (base x)).2.isHermitian.eigenvectorUnitary
    weightedFit U R w s (ε+δ) (fun j => wave t (diagonalEnergy U (generator (rotated a b x)).val j)) := by
  intro U
  obtain ⟨c,hc,C,hs,he⟩ := hfit
  refine ⟨c,hc,C,hs,?_⟩
  let B := generator (rotated a b x)
  let V := unitaryEvolution B.val t
  let X := U.valᴴ*V*U.val
  have hmat : ‖c • (U⁻¹*C.eval*U).val-X‖ ≤ ε := by
    change ‖c • (U.valᴴ*C.eval.val*U.val)-U.valᴴ*V*U.val‖ ≤ _
    rw [←Matrix.smul_mul,←Matrix.mul_smul,←Matrix.sub_mul,←Matrix.mul_sub,
      CStarRing.norm_mul_mem_unitary _ U.2,←Matrix.star_eq_conjTranspose,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem U.2),norm_sub_rev]
    exact he
  have hj (i : R) : ‖c*(U⁻¹*C.eval*U).val i.val i.val-wave t (diagonalEnergy U B.val i.val)‖ ≤
      ε+phaseError U B t i.val :=
    (norm_sub_le_norm_sub_add_norm_sub _ (X i.val i.val) _).trans
      (add_le_add ((norm_entry_le_l2_opNorm _ i.val i.val).trans hmat) le_rfl)
  apply (sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hj i) (hw i))).trans
  simp only [mul_add,sum_add_distrib,←sum_mul,hsum,one_mul]
  apply add_le_add le_rfl
  apply (sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hcap i) (norm_nonneg _))).trans
  rw [←mul_sum]
  change W*(∑ i : R, phaseError U B t i.val) ≤ δ
  rw [Finset.sum_coe_sort R (phaseError U B t)]
  exact hread

/-- One fixed net circuit supplies the twist in a weighted overlap test. -/
theorem circuit_trace_witness {N s : ℕ} (U : unitaryGroup (Config N) ℂ) (R : Finset (Config N))
    (w : R → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1) (z d : Config N → ℂ)
    (hd : ∀ i, ‖d i‖=1) (hz : ∀ i, z i*d i=1) {ε : ℝ} (hfit : weightedFit U R w s ε z) :
    ∃ W ∈ atMostQuarterCircuitNet N s,
      1-(ε+1/4) ≤ ‖∑ i : R, (w i:ℂ)*(U⁻¹*W*U).val i.val i.val*d i.val‖ := by
  obtain ⟨c,hc,C,hs,he⟩ := hfit
  obtain ⟨W,hW,hn⟩ := atMostQuarterCircuitNet_cover C hs
  refine ⟨W,hW,weighted_overlap w hw hsum _ (fun i => z i.val) _ (fun i => hd i.val)
    (fun i => hz i.val) c hc (ε+1/4) ?_⟩
  have hm : ‖(U⁻¹*W*U).val-(U⁻¹*C.eval*U).val‖ ≤ 1/4 := by
    change ‖U.valᴴ*W.val*U.val-U.valᴴ*C.eval.val*U.val‖ ≤ _
    rw [←Matrix.sub_mul,←Matrix.mul_sub,CStarRing.norm_mul_mem_unitary _ U.2,
      ←Matrix.star_eq_conjTranspose,CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem U.2),norm_sub_rev]
    simpa only [dist_eq_norm] using hn
  have hj (i : R) : ‖c*(U⁻¹*W*U).val i.val i.val-z i.val‖ ≤
      1/4+‖c*(U⁻¹*C.eval*U).val i.val i.val-z i.val‖ := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ (c*(U⁻¹*C.eval*U).val i.val i.val) _).trans
    rw [←mul_sub,norm_mul,hc,one_mul]
    exact add_le_add ((norm_entry_le_l2_opNorm _ i.val i.val).trans hm) le_rfl
  apply (sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hj i) (hw i))).trans
  rw [Finset.sum_congr rfl (fun i _ => mul_add (w i) _ _),sum_add_distrib,←sum_mul,hsum,one_mul,add_comm]
  exact add_le_add he le_rfl

#print axioms physical_weighted_fit
#print axioms circuit_trace_witness
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
