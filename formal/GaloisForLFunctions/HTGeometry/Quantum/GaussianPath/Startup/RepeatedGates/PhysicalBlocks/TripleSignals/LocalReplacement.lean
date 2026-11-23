import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.RequiredPairs
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncidentPauliTerms
import GaloisForLFunctions.HTGeometry.RationalCommonTimeWitness

/-! # Isolating a three-site quarter turn inside a disordered chain -/
open Matrix Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section
variable {n : ℕ}

def tripleField (e f : Fin (n+1)) (q : ℝ) (l : PathLabel n) : ℝ :=
  (if l=.inr (e,2,0) then q else 0) + (if l=.inr (f,2,2) then q else 0)

private theorem single_field (j : PathLabel n) (q : ℝ) :
    ∑ l : PathLabel n, (((if l=j then q else 0 : ℝ):ℂ) • finitePauliMatrix (pathWord l)) =
      (q:ℂ) • finitePauliMatrix (pathWord j) := by
  classical
  calc _ = ∑ l : PathLabel n, (if l=j then (q:ℂ) • finitePauliMatrix (pathWord j) else 0) := by
              apply sum_congr rfl
              intro l _
              by_cases h : l=j <;> simp [h]
       _ = _ := by simp

private theorem triple_field_sum (e f : Fin (n+1)) (q : ℝ) :
    ∑ l : PathLabel n, ((tripleField e f q l:ℂ) • finitePauliMatrix (pathWord l)) =
      ((q*sqrt 2:ℝ):ℂ) • tripleGenerator e f := by
  simp only [tripleField,Complex.ofReal_add,add_smul,sum_add_distrib,single_field,
    tripleGenerator,mix,smul_smul,←smul_add,←Complex.ofReal_mul]
  rw [show (q*sqrt 2)*(1/sqrt 2)=q by field_simp [(sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne']]

/-- Only the at most 63 labels incident to the triple need to be controlled.
The exterior keeps its actual Hamiltonian. -/
theorem triple_local_error {e f : Fin (n+1)} (u : PathShell n) (q δ : ℝ) (hδ : 0≤δ)
    (hw : ∀ l ∈ (tripleSites e f).biUnion pathIncidentLabels, |u l-tripleField e f q l|≤δ) :
    ‖pathHamiltonian u-(pathHamiltonianOnSites (tripleSites e f)ᶜ u +
      ((q*sqrt 2:ℝ):ℂ) • tripleGenerator e f)‖ ≤ 63*δ := by
  classical
  let S := tripleSites e f
  let W := S.biUnion pathIncidentLabels
  let x (l : PathLabel n) := u l-((if PathWordSupportedIn Sᶜ l then u l else 0)+tripleField e f q l)
  have herr : ‖pathHamiltonian u-(pathHamiltonianOnSites Sᶜ u+((q*sqrt 2:ℝ):ℂ) • tripleGenerator e f)‖ ≤
      ∑ l : PathLabel n, |x l| := by
    rw [←triple_field_sum,pathHamiltonian_eq_sum,pathHamiltonianOnSites,←sum_add_distrib,←sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro l _
    rw [←add_smul,←sub_smul,norm_smul,norm_finitePauliMatrix,mul_one,←Complex.ofReal_add,
      ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have hcard : S.card ≤ 3 := by
    dsimp [S,tripleSites]
    exact (card_insert_le ..).trans (by have h := card_insert_le e.succ {f.succ}; simpa using Nat.succ_le_succ h)
  have hwcard : (W.card:ℝ) ≤ 63 := by
    have h := (pathIncident_union_card S).trans (Nat.mul_le_mul_left 21 hcard)
    exact_mod_cast h
  have contains (v : Fin (n+2)) (hv : v∈S) (l : PathLabel n) (hl : pathIncident v l) : l∈W :=
    mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨mem_univ _,hl⟩⟩
  have hleft : (.inr (e,2,0) : PathLabel n) ∈ W :=
    contains e.castSucc (by simp [S,tripleSites]) _ (Or.inl rfl)
  have hright : (.inr (f,2,2) : PathLabel n) ∈ W :=
    contains f.succ (by simp [S,tripleSites]) _ (Or.inr rfl)
  have hout (l) (hl : l∉W) : |x l|=0 := by
    have h₁ := ne_of_mem_of_not_mem hleft hl
    have h₂ := ne_of_mem_of_not_mem hright hl
    simp [x,tripleField,(path_supported_compl_of_not_incident S l hl),h₁.symm,h₂.symm]
  have hin (l) (hl : l∈W) : |x l|≤δ := by
    obtain ⟨v,hv,hi⟩ := mem_biUnion.mp hl
    have he := pathWord_ne_none_of_incident (mem_filter.mp hi).2
    have h : ¬PathWordSupportedIn Sᶜ l := fun hs => he (hs v (by simpa using hv))
    simpa only [x,if_neg h,zero_add] using hw l hl
  rw [←sum_subset (subset_univ W) (fun l _ h => hout l h)] at herr
  exact herr.trans ((sum_le_sum hin).trans (by simpa only [sum_const,nsmul_eq_mul] using
    mul_le_mul_of_nonneg_right hwcard hδ))

private theorem triple_supported {e f : Fin (n+1)} (hm : e.succ=f.castSucc) :
    IsSiteSupported (tripleSites e f) (tripleGenerator e f) := by
  apply IsSiteSupported.complex_smul
  apply IsSiteSupported.add
  · apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro v hv
    simp only [tripleSites,mem_insert,mem_singleton,not_or] at hv
    simp [couplingWord,hv.1,hv.2.1]
  · apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro v hv
    simp only [tripleSites,mem_insert,mem_singleton,not_or] at hv
    simp [couplingWord,←hm,hv.2.1,hv.2.2]

/-- A 1/4-accurate physical circuit must transmit all six directed
signals if the incident coefficient errors cost at most 1/8. -/
theorem triple_exchange_of_fit {e f : Fin (n+1)} (hm : e.succ=f.castSucc)
    (u : PathShell n) (q δ t : ℝ) (hδ : 0≤δ) (ht : (q*sqrt 2)*t=π/2)
    (hsmall : |t|*(63*δ)≤1/8)
    (hw : ∀ l ∈ (tripleSites e f).biUnion pathIncidentLabels, |u l-tripleField e f q l|≤δ)
    (C : TwoQubitCircuit (n+2)) (z : ℂ) (hz : ‖z‖=1)
    (he : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ ≤ 1/4) :
    ∀ i∈tripleSites e f, ∀ j∈tripleSites e f, i∈Temporal.inputs (Temporal.circuitWord C) j := by
  let J := pathHamiltonianOnSites (tripleSites e f)ᶜ u
  let K := ((q*sqrt 2:ℝ):ℂ) • tripleGenerator e f
  have hJ := isSelfAdjoint_pathHamiltonianOnSites (tripleSites e f)ᶜ u
  have hK : IsSelfAdjoint K := by
    change star (((q*sqrt 2:ℝ):ℂ) • tripleGenerator e f)=_
    rw [star_smul,(tripleGenerator_selfAdjoint e f).star_eq,Complex.star_def,Complex.conj_ofReal]
  let E : unitaryGroup (Fin (n+2)→Bool) ℂ := ⟨unitaryEvolution J t, unitaryEvolution_mem_unitary hJ t⟩
  have hs := pathHamiltonianOnSites_isSiteSupported (tripleSites e f)ᶜ u
  apply triple_required_pairs hm E (isSiteSupported_unitaryEvolution hs t) C z hz
  have hfactor : unitaryEvolution (J+K) t = E.val*unitaryEvolution (tripleGenerator e f) (π/2) := by
    rw [unitaryEvolution_add_of_isSiteSupported_disjoint disjoint_compl_left hs
      (IsSiteSupported.complex_smul _ (triple_supported hm)),unitaryEvolution_smul_generator,ht]
  have hd := norm_unitaryEvolution_sub_le (J+K) (pathHamiltonian u) (hJ.add hK) (isSelfAdjoint_pathHamiltonian u) t
  rw [norm_sub_rev (J+K),hfactor] at hd
  have hb := hd.trans ((mul_le_mul_of_nonneg_left (triple_local_error u q δ hδ hw) (abs_nonneg t)).trans hsmall)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution (pathHamiltonian u) t) _).trans
    ((add_le_add hb he).trans_eq (by norm_num))

#print axioms triple_exchange_of_fit
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
