import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondSections
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # Small-signal probability for a bond of the physical Gaussian chain -/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {n : ℕ}

private abbrev M (l : PathLabel n) := finitePauliMatrix (pathWord l)

/-- Pair the transported endpoint reporter with its calibrated two-site input. -/
def bondSignal (e : Fin (n+1)) (u : PathShell n) (t : ℝ) : ℝ :=
  let Y := finitePauliMatrix (bondReporter e)
  signal (pathHamiltonian u) Y (Complex.I • (M (bondLabel e)*Y)) t

private theorem prefix_measure (n : ℕ) :
    MeasurePreserving (fun ω => fun l : PathLabel n => pathPauliDisorderShell ω n l)
      pathPauliDisorderLaw (Measure.pi fun _ => gaussianReal 0 1) := by
  let e := pathCoeffEquiv n
  have h := (measurePreserving_piCongrLeft (fun _ : PathLabel n => gaussianReal 0 1) e).comp
    (gaussian_pauli_prefix_coordinates_law n)
  convert h using 1
  funext ω l
  change pathPauliDisorderShell ω n l=pathPauliDisorderShell ω n (e (e.symm l))
  rw [Equiv.apply_symm_apply]

private theorem shell_split (e : Fin (n+1)) (u : PathShell n) :
    pathHamiltonian u=affineHamiltonian (pathHamiltonian (exteriorShell u e))
      (fun i => M (localNumbering e i).val) (fun i => u (localNumbering e i).val) := by
  classical
  let p := fun l => l∈localLabels e
  let f := fun l : PathLabel n => (u l:ℂ) • M l
  have hE : pathHamiltonian (exteriorShell u e)=∑ l : {l // ¬p l}, f l := by
    rw [pathHamiltonian_eq_sum,←Fintype.sum_subtype_add_sum_subtype p]
    have hz (l : {l // p l}) : exteriorShell u e l=0 := if_pos l.property
    have he (l : {l // ¬p l}) : exteriorShell u e l=u l := if_neg l.property
    simp only [hz,he,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,zero_add]
    rfl
  rw [affineHamiltonian,hE,(localNumbering e).sum_comp (fun l => f l.val),add_comm]
  exact (pathHamiltonian_eq_sum u).trans (Fintype.sum_subtype_add_sum_subtype p f).symm

private theorem signal_measurable (e : Fin (n+1)) (t : ℝ) :
    Measurable (fun x : PathLabel n → ℝ => bondSignal e (WithLp.toLp 2 x) t) := by
  let Y := finitePauliMatrix (bondReporter e)
  apply Continuous.measurable
  apply (continuous_signal Y (Complex.I • (M (bondLabel e)*Y)) t).comp
  have he (x : PathLabel n → ℝ) : pathHamiltonian (WithLp.toLp 2 x)=∑ l, (x l:ℂ) • M l :=
    pathHamiltonian_eq_sum _
  simp_rw [he]
  exact continuous_finsetSum _ fun i _ => (Complex.continuous_ofReal.comp (continuous_apply i)).smul continuous_const

/-- At every prescribed date in a compact positive interval, each path
bond has a detectable correlation outside any fixed failure probability.
The threshold is independent of prefix length and position. -/
theorem gaussian_bond_signal_probability {a T η : ℝ} (ha : 0<a) (hη : 0<η) :
    ∃ r : ℝ, 0<r ∧ ∀ (n : ℕ) (e : Fin (n+1)) (t : ℝ), t∈Icc a T →
      pathPauliDisorderLaw {ω | |bondSignal e (pathPauliDisorderShell ω n) t|≤r} ≤ ENNReal.ofReal η := by
  classical
  obtain ⟨r,hr,hs⟩ := gaussian_bond_sections (T:=T) ha hη
  refine ⟨r,hr,?_⟩
  intro n e t ht
  let p := fun l => l∈localLabels e
  let S := {x : PathLabel n → ℝ | |bondSignal e (WithLp.toLp 2 x) t|≤r}
  have hS : MeasurableSet S := measurableSet_le (signal_measurable e t).abs measurable_const
  let E := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : PathLabel n => ℝ) p).symm
  let G := MeasurableEquiv.piCongrLeft (fun _ : Subtype p => ℝ) (localNumbering e)
  have hE := (measurePreserving_piEquivPiSubtypeProd (fun _ : PathLabel n => gaussianReal 0 1) p).symm
  have hG := measurePreserving_piCongrLeft (fun _ : Subtype p => gaussianReal 0 1) (localNumbering e)
  have h0 := (prefix_measure n).measure_preimage hS.nullMeasurableSet
  change pathPauliDisorderLaw ((fun ω => fun l => pathPauliDisorderShell ω n l) ⁻¹' S)≤_
  rw [h0,←hE.measure_preimage hS.nullMeasurableSet,Measure.prod_apply_symm (E.measurable hS)]
  calc _ ≤ ∫⁻ _y : {l // ¬p l} → ℝ, ENNReal.ofReal η ∂(Measure.pi fun _ => gaussianReal 0 1) := by
         apply lintegral_mono
         intro y
         let A := (fun x => E (x,y)) ⁻¹' S
         have hA : MeasurableSet A := (E.measurable.comp (measurable_id.prodMk measurable_const)) hS
         change (Measure.pi fun _ : Subtype p => gaussianReal 0 1) A≤_
         rw [←hG.measure_preimage hA.nullMeasurableSet]
         let u : PathShell n := WithLp.toLp 2 (E (0,y))
         apply (measure_mono (t := {x | |signal (affineHamiltonian (pathHamiltonian (exteriorShell u e))
           (fun i => M (localNumbering e i).val) x) (finitePauliMatrix (bondReporter e))
           (Complex.I • (M (bondLabel e)*finitePauliMatrix (bondReporter e))) t|≤r}) ?_).trans (hs n e u t ht)
         intro x hx
         let v : PathShell n := WithLp.toLp 2 (E (G x,y))
         change |bondSignal e v t|≤r at hx
         have hv : exteriorShell v e=exteriorShell u e := by
           ext l
           by_cases hl : p l
           · change (if l∈localLabels e then 0 else _)=(if l∈localLabels e then 0 else _)
             rw [if_pos hl,if_pos hl]
           · change (if l∈localLabels e then 0 else (if h : p l then _ else y ⟨l,h⟩))=
                 (if l∈localLabels e then 0 else (if h : p l then _ else y ⟨l,h⟩))
             simp only [if_neg hl,dif_neg hl]
         have hx' (i : Fin (localLabels e).card) : v (localNumbering e i).val=x i := by
           change (if h : p _ then G x ⟨(localNumbering e i).val,h⟩ else _)=x i
           rw [dif_pos (localNumbering e i).property]
           exact MeasurableEquiv.piCongrLeft_apply_apply ..
         simpa only [bondSignal,shell_split e v,hv,hx'] using hx
       _ = _ := by simp

#print axioms gaussian_bond_signal_probability
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
