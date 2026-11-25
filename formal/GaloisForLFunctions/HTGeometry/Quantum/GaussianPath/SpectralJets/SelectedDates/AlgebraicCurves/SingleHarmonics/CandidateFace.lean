import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.GapClock
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.BoxLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.PairFrequency
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryFaces

/-! # The probability of an inward scalar entry at one specified pair winding -/

open MeasureTheory Set Filter Topology Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
open EmptyVisitFlux PrescribedTimes.PhaseLaws
noncomputable section

/-- The difference between a phase and the left endpoint at an exact
inward pair contact, expressed in units of the closing gap. -/
private theorem relative_at_pair {I : Type*} [Fintype I] (E : I→ℝ) (i j l : I)
    (h : E j<E i) (r : ℝ) (n : ℕ) :
    let t := pairDate (fun k => -E k) j i r n
    let w := fun k => -E k/(2*π)
    flow w t l-flow w t j =
      (((1-r+(n:ℝ))*(-((E l-E j)/(E i-E j))):ℝ):UnitAddCircle) := by
  intro t w
  unfold flow
  rw [←AddCircle.coe_sub]
  congr 1
  dsimp only [t,w,pairDate]
  rw [neg_sub_neg]
  field_simp [two_pi_pos.ne',(sub_pos.mpr h).ne']
  ring

/-- The selected relative phase is exactly the closing turn at this winding. -/
theorem pinned_at_pair {I : Type*} [Fintype I] (E : I→ℝ) (i j : I) (hE : E j<E i) (r : ℝ) (n : ℕ) :
    let t := pairDate (fun k => -E k) j i r n
    let w := fun k => -E k/(2*π)
    flow w t i-flow w t j=(r:UnitAddCircle) := by
  intro t w
  rw [relative_at_pair E i j i hE r n,div_self (sub_pos.mpr hE).ne']
  have hn : (((n+1:ℕ):ℝ):UnitAddCircle)=0 := by
    rw [show ((n+1:ℕ):ℝ)=(n+1) • (1:ℝ) by rw [nsmul_eq_mul,mul_one],
      AddCircle.coe_nsmul,AddCircle.coe_period,nsmul_zero]
  rw [show (1-r+(n:ℝ))*(-(1:ℝ))=r-((n+1:ℕ):ℝ) by push_cast; ring,AddCircle.coe_sub,hn,sub_zero]

theorem box_iff_face (k : ℕ) {i j : Level k} (hij : j < i) (r : ℝ) (n : ℕ)
    (x : Coupling k) (hs : Function.Injective (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x)) :
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
    let t := pairDate (fun l => -E l) j i r n
    let w := fun l => -E l/(2*π)
    pairFace (forwardUnitArc r) w r t j i ↔
      finiteClockPhasePoint (gapFrequency k i j x) (2*π*(1-r+(n:ℝ)))∈closedBox (Outside i j) r := by
  intro E t w
  have hE : E j<E i := lt_of_le_of_ne (monotone_sortedTuple _ hij.le) (hs.ne hij.ne)
  have hpin := pinned_at_pair E i j hE r n
  have he (l : Outside i j) : flow w t l.val-flow w t j =
      finiteClockPhasePoint (gapFrequency k i j x) (2*π*(1-r+(n:ℝ))) l := by
    rw [relative_at_pair E i j l.val hE r n]
    change ((_:ℝ):UnitAddCircle)=((2*π*(1-r+(n:ℝ))*(-((E l.val-E j)/(E i-E j)))/(2*π):ℝ):UnitAddCircle)
    congr 1
    field_simp [two_pi_pos.ne']
  constructor
  · intro h l _
    change _ ∈ forwardUnitArc r
    rw [←he l]
    exact h.2.2 l.val l.property.2 l.property.1
  · intro h
    exact ⟨div_lt_div_of_pos_right (neg_lt_neg hE) two_pi_pos,hpin,
      fun l hlj hli => (he ⟨l,hli,hlj⟩).symm ▸ h ⟨l,hli,hlj⟩ (mem_univ _)⟩

private theorem outside_card {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (hij : i≠j) :
    Fintype.card (Outside i j)=Fintype.card I-2 := by
  let J := {l : I // l≠i}
  let b : J := ⟨j,hij.symm⟩
  let K := {l : J // l≠b}
  let e : Outside i j ≃ K := {
    toFun := fun l => ⟨⟨l.val,l.property.1⟩,fun h => l.property.2 (congrArg Subtype.val h)⟩
    invFun := fun l => ⟨l.val.val,l.val.property,fun h => l.property (Subtype.ext h)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hJ : Fintype.card J=Fintype.card I-1 := by simp [J,Fintype.card_subtype_compl]
  have hK : Fintype.card K=Fintype.card J-1 := by simp [K,Fintype.card_subtype_compl]
  rw [Fintype.card_congr e,hK,hJ,Nat.sub_sub]

/-- Measurability of a phase observation in units of the selected gap. -/
theorem measurable_gap_point (k : ℕ) (i j : Level k) (T : ℝ) :
    Measurable (fun x => finiteClockPhasePoint (gapFrequency k i j x) T) :=
  measurable_pi_lambda _ fun l => (AddCircle.continuous_mk' (1:ℝ)).measurable.comp
    ((((measurable_pi_apply l).comp (gapFrequency_measurable k i j)).const_mul T).div_const (2*π))

/-- At one increasingly late winding of any specified ordered pair, a
genuine entry through that pair has probability tending to x^(D−2) over
the original Gaussian coefficients. The sample consists of one winding. -/
theorem single_winding_entry (k : ℕ) {i j : Level k} (hij : j < i) (r : Ioo (0:ℝ) (1/2))
    (G : ProbabilityMeasure (Coupling k)) (hG : (G : Measure (Coupling k)) ≪ volume) :
    let μ := (G : Measure (Coupling k))
    Tendsto (fun n : ℕ => μ {x | let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
      let t := pairDate (fun l => -E l) j i r n
      let w := fun l => -E l/(2*π)
      visitEntry w r t ∧ pairFace (forwardUnitArc r) w r t j i}) atTop
      (𝓝 (ENNReal.ofReal (r:ℝ)^(2^(k+3)-2))) := by
  intro μ
  let X := closedBox (Outside i j) r
  have hX : MeasurableSet X := (isClosed_set_pi fun _ _ => isClosed_forwardUnitArc (r:ℝ)).measurableSet
  obtain ⟨_,_,hvol,hbd⟩ := box_volumes (I:=Outside i j) ⟨(r:ℝ),r.2.1.le,r.2.2.le⟩
  have hb : (finiteTorusHaarProbabilityMeasure (Outside i j) : Measure _) (frontier X)=0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  let T (n : ℕ) := 2*π*(1-(r:ℝ)+(n:ℝ))
  have ht : Tendsto T atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop two_pi_pos
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (b+(r:ℝ))] with n hn
    linarith only [hn]
  have h := (gapSnapshot_haar k i j hij.ne.symm G hG).comp ht
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hb
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume,show volume X=_ from hvol] at hm
  have hs : ∀ᵐ x ∂μ, Function.Injective (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x) := by
    apply hG.ae_le
    have hh := (ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)).mono fun _ hx =>
      injective_sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) hx.injective
    exact hh
  rw [outside_card i j hij.ne.symm,Fintype.card_fin] at hm
  apply hm.congr
  intro n
  change (gapSnapshot k i j G (T n) : Measure _) X=_
  rw [gapSnapshot,frequencySnapshot,ProbabilityMeasure.toMeasure_map,Measure.map_apply (measurable_gap_point k i j (T n)) hX]
  apply measure_congr
  filter_upwards [hs] with x hx
  have he := box_iff_face k hij r n x hx
  apply propext
  refine ⟨fun h => ?_,fun h => he.mp h.2⟩
  have hf := he.mpr h
  exact ⟨(entry_iff_closed_face _ r.2.1.le r.2.2).mpr ⟨j,i,hf⟩,hf⟩

/-- Under the original Gaussian law the probability of a true inward
entry at this one candidate tends to the Haar mass of its free face. -/
theorem gaussian_single_winding_entry (k : ℕ) {i j : Level k} (hij : j < i) (r : Ioo (0:ℝ) (1/2)) :
    let μ := centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1
    Tendsto (fun n : ℕ => μ {x | let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
      let t := pairDate (fun l => -E l) j i r n
      let w := fun l => -E l/(2*π)
      visitEntry w r t ∧ pairFace (forwardUnitArc r) w r t j i}) atTop
      (𝓝 (ENNReal.ofReal (r:ℝ)^(2^(k+3)-2))) :=
  single_winding_entry k hij r ⟨centredProductGaussian _ 1,inferInstance⟩
    (productGaussian_absolutelyContinuous _ one_ne_zero _)

#print axioms gaussian_single_winding_entry
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
