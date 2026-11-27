import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Disorder.Rows.Incidence
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.Sampling.GuardedTriples
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.IncidentSupport

/-! # The guarded rows contain every coefficient in the corrected reporter -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open private source_row_bounds box_controls from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.DisjointBoxes
noncomputable section
variable {n k : ℕ}

/-- A middle triple of a twelve-row block has its enlarged support
strictly inside that block, including both adjacent sites. -/
theorem guarded_site_bounds {e f : Fin (n+1)} (he : e.val=4*(3*k+1)+1) (hf : f.val=4*(3*k+1)+2)
    {v : Fin (n+2)} (hv : v∈incidentSites (tripleSites e f)) : 12*k+4≤v.val ∧ v.val≤12*k+8 := by
  rcases mem_union.mp hv with h|h
  · simp only [tripleSites,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl <;> simp only [Fin.val_castSucc,Fin.val_succ] <;> omega
  · obtain ⟨l,hl,hv'⟩ := mem_biUnion.mp h
    have hinc : pathIncident v l := by
      by_contra hn
      exact (mem_labelSupport.mp hv') (pathWord_none_of_not_incidentSite v l hn)
    have hh := source_row_at_site hinc
    obtain ⟨h₁,h₂⟩ := source_row_bounds he hf hl
    omega

private theorem guarded_coordinate_bound {ω : PathPauliDisorder} {δ : ℝ} (hδ : δ≤1)
    (h : ∀ a : Fin 3, goodBox (1/sqrt 2) δ ω (3*k+a.val))
    (v : ℕ × PathPauliDirections) (hv : 12*k≤v.1 ∧ v.1<12*k+12) : |ω v|≤2 := by
  let x := v.1-12*k
  let a : Fin 3 := ⟨x/4,by dsimp only [x]; omega⟩
  let i : TripleBoxIndex := (⟨x%4,Nat.mod_lt _ (by decide)⟩,v.2)
  have hk : blockCoordinate (3*k+a.val,i)=v := Prod.ext (by dsimp only [blockCoordinate,a,i,x]; omega) rfl
  have hb := h a i
  rw [hk] at hb
  have hq : 1/sqrt 2≤1 := (div_le_one (sqrt_pos.mpr (by norm_num))).mpr (one_le_sqrt.mpr (by norm_num))
  have hfield : |boxField (1/sqrt 2) i|≤1 := by
    unfold boxField
    split
    · rwa [abs_of_nonneg (by positivity : (0:ℝ)≤1/sqrt 2)]
    · norm_num
  have ha := abs_le.mp hfield
  exact abs_le.mpr ⟨by linarith only [hb.1,ha.1,hδ],by linarith only [hb.2,ha.2,hδ]⟩

/-- A fixed Gaussian box gives the required quadratic remainder bound
at every short time, with all constants independent of the prefix. -/
theorem guarded_perturbation_bound {e f : Fin (n+1)} (he : e.val=4*(3*k+1)+1) (hf : f.val=4*(3*k+1)+2)
    (ω : PathPauliDisorder) (hg : ∀ a : Fin 3, goodBox (1/sqrt 2) (1/10^9) ω (3*k+a.val)) :
    let u := pathPauliDisorderShell ω n
    let d := ‖pathHamiltonian (packetPerturbation e f u)‖
    let S := incidentSites (tripleSites e f)
    let E := ∑ l∈S.biUnion pathIncidentLabels, |u l|
    4*d*(2*E+d)≤1/256 := by
  classical
  intro u d S E
  have hsite (v) (hv : v∈S) := guarded_site_bounds he hf hv
  have hsmall : d≤1/2000000 := by
    have hbox := box_controls he hf (hg (1:Fin 3)) (show |1/sqrt 2-1/sqrt 2|≤1/10^9 by norm_num)
    have hh := triple_local_error u (1/sqrt 2) (2*(1/10^9)) (by norm_num) hbox
    rw [div_mul_cancel₀ _ (sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne',Complex.ofReal_one,one_smul] at hh
    dsimp only [d]
    rw [packetPerturbation_eq]
    exact hh.trans (by norm_num)
  have hcard : S.card≤12 := by
    have hsub : S.image Fin.val⊆Finset.Ico (12*k) (12*k+12) := by
      intro i hi
      obtain ⟨v,hmem,rfl⟩ := mem_image.mp hi
      have hh := hsite v hmem
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    have hh := Finset.card_le_card hsub
    simpa only [card_image_of_injective _ Fin.val_injective,Nat.card_Ico,Nat.add_sub_cancel_left] using hh
  have hmass : E≤504 := by
    have hc := (pathIncident_union_card S).trans (Nat.mul_le_mul_left 21 hcard)
    have hbound (l : PathLabel n) (hl : l∈S.biUnion pathIncidentLabels) : |u l|≤2 := by
      obtain ⟨v,hv,hi⟩ := mem_biUnion.mp hl
      have hrow := source_row_at_site (mem_filter.mp hi).2
      have hloc := hsite v hv
      rw [show u l=ω (pathPauliSourceCoordinate l) from pathPauliDisorderShell_apply_source ..]
      exact guarded_coordinate_bound (by norm_num : (1:ℝ)/10^9≤1) hg _ ⟨by omega,by omega⟩
    have h := sum_le_sum hbound
    simp only [sum_const,nsmul_eq_mul] at h
    have hc' : ((S.biUnion pathIncidentLabels).card:ℝ)≤252 := by exact_mod_cast hc
    linarith only [h,hc']
  have hd : 0≤d := norm_nonneg _
  have hE : 0≤E := sum_nonneg fun _ _ => abs_nonneg _
  have hb : 2*E+d≤1010 := by linarith only [hmass,hsmall]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0:ℝ)≤4)) hb
    (by linarith only [hE,hd]) (by norm_num)).trans (by norm_num)

#print axioms guarded_perturbation_bound
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
