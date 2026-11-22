import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.PhysicalPacket
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # Physical circuit probabilities at a single date with one uncertain coupling -/
open MeasureTheory Filter Topology Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
noncomputable section
private abbrev Basis (n : ℕ) := Fin n→Bool
private abbrev Reg (n : ℕ) := Matrix (Basis n) (Basis n) ℂ

/-- Frozen-basis phases which the physical circuit budget captures. -/
def packetCapture {n : ℕ} (H : Reg n) (E : Basis n→ℝ) (r : Basis n) (s : ℕ) (η : ℝ) :
    Set (UnitAddTorus {i // i≠r}) := {x | HasProjectiveCircuitApproximation n η s (physicalPacket H E r x)}

theorem closed_packetCapture {n : ℕ} (H : Reg n) (E : Basis n→ℝ) (r : Basis n) (s : ℕ) (η : ℝ) :
    IsClosed (packetCapture H E r s η) := by
  have hset : packetCapture H E r s η={x | Metric.infDist (physicalPacket H E r x) (phaseCircuitMatrixImageAtMost n s) ≤ η} :=
    Set.ext fun x => hasProjectiveCircuitApproximation_iff_infDist _ _ _
  rw [hset]
  exact isClosed_le ((Metric.continuous_infDist_pt _).comp (continuous_physicalPacket ..)) continuous_const

private theorem move_phase {n s : ℕ} {ε : ℝ} {X : Reg n} {a : ℂ} (ha : ‖a‖=1)
    (h : HasProjectiveCircuitApproximation n ε s X) : HasProjectiveCircuitApproximation n ε s (a • X) := by
  obtain ⟨c,hc,C,hC,he⟩ := h
  refine ⟨a*c,by rw [norm_mul,ha,hc,one_mul],C,hC,?_⟩
  rwa [←smul_smul,←smul_sub,norm_smul,ha,one_mul]

private theorem transfer_capture {n s : ℕ} {ε η : ℝ} {U V : Reg n}
    (h : HasProjectiveCircuitApproximation n ε s U) (hd : ‖U-V‖ < η-ε) :
    HasProjectiveCircuitApproximation n η s V := by
  obtain ⟨c,hc,C,hC,he⟩ := h
  refine ⟨c,hc,C,hC,?_⟩
  rw [norm_sub_rev] at hd
  exact (norm_sub_le_norm_sub_add_norm_sub V U _).trans (by linarith only [he,hd])

private theorem near_simple {I : Type} [Fintype I] (E : ℝ→I→ℝ) (he : ∀ i, Continuous fun z => E z i)
    {b : ℝ} (hb : Function.Injective (E b)) : ∀ᶠ z in 𝓝 b, Function.Injective (E z) := by
  have hp (i j : I) : ∀ᶠ z in 𝓝 b, E z i=E z j → i=j := by
    by_cases hij : i=j
    · exact Eventually.of_forall fun _ _ => hij
    · have h := ((he i).sub (he j)).continuousAt.tendsto.eventually (isOpen_compl_singleton.mem_nhds
          (show E b i-E b j∈({0}:Set ℝ)ᶜ from sub_ne_zero.mpr (hb.ne hij)))
      exact h.mono fun z hz hEq => (hz (sub_eq_zero.mpr hEq)).elim
  exact (eventually_all.mpr fun i => eventually_all.mpr (hp i)).mono fun _ h _ _ => h _ _

private theorem field_measure {I : Type} [Fintype I] (f : ℝ→I→ℝ) (hf : ∀ i, Continuous (fun z => f z i))
    (b w T : ℝ) {A : Set (UnitAddTorus I)} (hA : MeasurableSet A) :
    (fieldWindowLaw f hf b w T : Measure _) A=(unitIntervalProbabilityMeasure : Measure ℝ)
      {s | finiteClockPhasePoint (f (b+w*s)) T∈A} := by
  have h := congrArg ENNReal.ofReal (fieldWindowLaw_real f hf b w T hA)
  simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

/-- As w→0 and Tw→∞, the field fraction affordable at a single prescribed
date has upper limit at most the frozen Haar circuit probability at any
strictly relaxed error. The comparison holds simultaneously for all budgets. -/
theorem gaussian_fixed_date_circuit_capture :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ b ∉ B,
      let E := orderedBoundaryEnergy ω k
      let K := boundaryHamiltonian ω k
      ∀ (r : Basis (k+3)) (s : ℕ) (ε η : ℝ), ε < η → ∀ w T : ℕ→ℝ,
      Tendsto w atTop (𝓝 0) → (∀ᶠ n in atTop, 0 < w n) → Tendsto (fun n => T n*w n) atTop atTop →
      atTop.limsup (fun n => (unitIntervalProbabilityMeasure : Measure ℝ)
        {u | HasProjectiveCircuitApproximation (k+3) ε s (unitaryEvolution (K (b+w n*u)) (T n))}) ≤
        volume (packetCapture (K b) (E b) r s η) := by
  filter_upwards [gaussian_boundary_fixed_date_haar,gaussian_boundary_projective_slopes] with ω hh hs
  intro k
  obtain ⟨B,hB,h⟩ := hh k
  obtain ⟨C,hC,hc⟩ := hs k
  refine ⟨B∪C,hB.union hC,?_⟩
  intro b hb E K r s ε η hε w T hw hp ht
  obtain ⟨hf,hμ⟩ := h b (fun h => hb (Or.inl h)) r
  have hmax := (hc b (fun h => hb (Or.inr h))).1
  have hE (j : Basis (k+3)) : Continuous fun z => E z j := continuous_orderedBoundaryEnergy ω k j
  have hK : Continuous K := continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hnear := (packet_freezing hK (continuous_pi hE) hmax.injective r (sub_pos.mpr hε)).and
    (near_simple E hE hmax.injective)
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let f (z : ℝ) := projectiveFrequency (fun i => -E z i) r
  let X := packetCapture (K b) (E b) r s η
  have hclosed : IsClosed X := closed_packetCapture .. 
  have hu := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (hμ w T hw hp ht) hclosed
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hu
  apply le_trans _ hu
  apply Filter.limsup_le_limsup
  filter_upwards [hp,hw.eventually_lt_const hρ] with n hn hn'
  rw [field_measure _ _ _ _ _ hclosed.measurableSet]
  apply measure_mono_ae
  have hsup : ∀ᵐ u ∂(unitIntervalProbabilityMeasure : Measure ℝ), u∈Ioc (0:ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [hsup] with u hu
  intro hfit
  let z := b+w n*u
  let x := finiteClockPhasePoint (f z) (T n)
  have hz : z∈Metric.ball b ρ := by
    rw [Metric.mem_ball,Real.dist_eq,show z-b=w n*u by dsimp [z]; ring,
      abs_of_nonneg (mul_nonneg hn.le hu.1.le)]
    exact (mul_le_of_le_one_right hn.le hu.2).trans_lt hn'
  obtain ⟨hfreeze,hi⟩ := hball hz
  let e := Fintype.equivFin (Basis (k+3))
  let p := (e.trans (Tuple.sort ((boundaryHermitian ω k z).eigenvalues ∘ e.symm))).trans e.symm
  have he := (isOrthoEigenBasis_hermitian (K z) (boundaryHermitian ω k z)).reindex p
  have hmat : unitaryEvolution (K z) (T n)=anchorPhase (E z) r (T n) • physicalPacket (K z) (E z) r x :=
    evolution_eq_physicalPacket he hi r (T n)
  let a := anchorPhase (E z) r (T n)
  have ha : ‖a‖=1 := by simp [a,anchorPhase,Complex.norm_exp]
  have ha0 : a≠0 := fun hn => by simp [hn] at ha
  change HasProjectiveCircuitApproximation (k+3) ε s (unitaryEvolution (K z) (T n)) at hfit
  rw [hmat] at hfit
  have hraw := move_phase (a:=a⁻¹) (by rw [norm_inv,ha,inv_one]) hfit
  change HasProjectiveCircuitApproximation _ _ _ (a⁻¹ • a • _) at hraw
  rw [smul_smul,inv_mul_cancel₀ ha0,one_smul] at hraw
  exact transfer_capture hraw (hfreeze x)

#print axioms gaussian_fixed_date_circuit_capture
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
