import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.CenteredProbability

/-! # A centered Gaussian circuit test at a physical date -/

open Matrix MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private fit_subspace from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.CircuitDates
noncomputable section
private abbrev Config (N : ℕ) := Fin N → Bool

/-- For any finite schedule, the cost of replacing the physical motion on
the top r inputs is paid once for the entire horizon. Each reading tests
only a fresh centered local slope at its own displacement. -/
theorem centered_physical_schedule {ι : Type*} [Fintype ι] (n r : ℕ)
    (hr : r ≤ Fintype.card (Config (n+2))) {T L ρ : ℝ}
    (hT : 0<T) (hL : |L|≤T) (hρ : 0<ρ) (s : ι → ℕ) (ε t : ι → ℝ)
    (ht : ∀ i, |t i|≤T) :
    let R := firstRanks (Config (n+2)) r hr
    pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹'
      ⋃ i, BlockDilations.affordableDraw n (s i) (ε i) (t i)) ≤
      (∑ i, Real.sqrt ((pairLaw n).real (centeredFit n (s i+s i) R
        (Real.sqrt 2*(t i*(L/T))) (2*(ε i+ρ))))) +
        8*Fintype.card (PathLabel n)*(r:ℝ)^2*L^2/(T*ρ^2) := by
  intro R
  let b := L/T
  let a := Real.sqrt (1-b^2)
  have hb : |b| ≤ 1 := by rwa [abs_div,abs_of_pos hT,div_le_one hT]
  have hb₂ : b^2 ≤ 1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hab : a^2+b^2=1 := by rw [Real.sq_sqrt (sub_nonneg.mpr hb₂)]; ring
  have hsmall : 1-a ≤ b^2 := by
    have ha := Real.sqrt_nonneg (1-b^2)
    have ha' : a ≤ 1 := (Real.sqrt_le_iff).mpr ⟨zero_le_one,by nlinarith only [sq_nonneg b]⟩
    nlinarith only [hab,mul_nonneg ha (sub_nonneg.mpr ha')]
  let E (i : ι) := BlockDilations.affordableDraw n (s i) (ε i) (t i)
  let F (i : ι) := rotated (n:=n) a b ⁻¹' E i
  let bad : Set (FieldPair n) := {x | ∃ u : ℝ, |u|≤T ∧ ρ^2/2 < readingError R a b x u}
  let B := toMeasurable (pairLaw n) bad
  let G (i : ι) := F i \ B
  have hE (i : ι) : MeasurableSet (E i) := BlockDilations.measurable_affordableDraw ..
  have hG (i : ι) : MeasurableSet (G i) :=
    ((hE i).preimage (rotated_law n hab).measurable).diff (measurableSet_toMeasurable ..)
  have hprice : (pairLaw n).real B ≤ 8*Fintype.card (PathLabel n)*(r:ℝ)^2*L^2/(T*ρ^2) := by
    change ((pairLaw n) (toMeasurable (pairLaw n) bad)).toReal ≤ _
    rw [measure_toMeasurable]
    apply (gaussian_ranked_readings n R hab hT (show 0<ρ^2/2 by positivity)).trans
    rw [firstRanks_weight,Nat.cast_pow]
    calc
      _ ≤ 4*T*b^2*(r:ℝ)^2*Fintype.card (PathLabel n)/(ρ^2/2) := by gcongr
      _ = _ := by dsimp only [b]; field_simp; ring
  have hfit (i : ι) : G i ⊆ edgeFit n (s i) R a b (t i) (ε i+ρ) := by
    rintro x ⟨⟨z,hz,C,hsize,he⟩,hout⟩
    have hlo : readingError R a b x (t i) ≤ ρ^2/2 :=
      le_of_not_gt fun h => hout (subset_toMeasurable _ _ ⟨t i,ht i,h⟩)
    exact ⟨z,hz,C,hsize,fit_subspace R a b x (t i) (ε i) ρ hρ hlo C z he⟩
  have hcap (i : ι) := centered_capture R a b (t i) (ε i+ρ) (hG i) (hfit i)
  have hU := MeasurableSet.iUnion hE
  have hlaw : pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹' ⋃ i, E i) =
      (pairLaw n).real (⋃ i, F i) := by
    unfold Measure.real
    rw [show (⋃ i, F i)=rotated a b ⁻¹' (⋃ i, E i) from (preimage_iUnion ..).symm,
      (BlockDilations.prefix_measure n).measure_preimage hU.nullMeasurableSet,
      (rotated_law n hab).measure_preimage hU.nullMeasurableSet]
  have hu : (⋃ i, F i) ⊆ (⋃ i, G i) ∪ B := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    by_cases h : x∈B
    · exact Or.inr h
    · exact Or.inl (mem_iUnion.mpr ⟨i,hi,h⟩)
  rw [hlaw]
  apply (measureReal_mono hu).trans ((measureReal_union_le ..).trans (add_le_add _ hprice))
  exact (measureReal_iUnion_fintype_le G).trans (Finset.sum_le_sum fun i _ => hcap i)

/-- At a single physical date T the centered test depends on the
independent displacement L, while the spectral comparison costs O(1/T). -/
theorem centered_physical_circuit_date (n s r : ℕ) (hr : r ≤ Fintype.card (Config (n+2)))
    {T L ρ : ℝ} (hT : 0<T) (hL : |L|≤T) (hρ : 0<ρ) (ε : ℝ) :
    let R := firstRanks (Config (n+2)) r hr
    pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹'
      BlockDilations.affordableDraw n s ε T) ≤
      Real.sqrt ((pairLaw n).real (centeredFit n (s+s) R (Real.sqrt 2*L) (2*(ε+ρ)))) +
        8*Fintype.card (PathLabel n)*(r:ℝ)^2*L^2/(T*ρ^2) := by
  have h := centered_physical_schedule (ι:=Unit) n r hr hT hL hρ
    (fun _ => s) (fun _ => ε) (fun _ => T) (fun _ => (abs_of_pos hT).le)
  have hE : (⋃ _ : Unit, BlockDilations.affordableDraw n s ε T) = BlockDilations.affordableDraw n s ε T :=
    Set.ext fun _ => ⟨fun hx => (mem_iUnion.mp hx).choose_spec, fun hx => mem_iUnion.mpr ⟨(),hx⟩⟩
  rw [hE] at h
  have htL : T*(L/T)=L := by field_simp
  simpa [htL] using h

#print axioms centered_physical_schedule
#print axioms centered_physical_circuit_date
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
