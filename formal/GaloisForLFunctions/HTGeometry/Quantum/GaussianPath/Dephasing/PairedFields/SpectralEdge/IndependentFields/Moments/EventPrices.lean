import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.LocalReadings
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.ConditionalFields

/-! # Gaussian circuit tests chosen after observing the base Hamiltonian -/

open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private wave from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
noncomputable section

/-- For each measurable physical event, every date in its test set must
admit a fit. The independent Gaussian base can choose the date, replica
order, and spectral weights jointly. All events share a single error
allowance for the comparison of their energy readings. -/
theorem physical_event_twist_tail {ι : Type*} [Fintype ι] (n r : ℕ)
    (hr : r ≤ Fintype.card (Fin (n+2) → Bool)) {T L ρ W : ℝ}
    (hT : 0<T) (hL : |L| ≤ T) (hρ : 0<ρ) (hW : 0<W)
    (s : ι → ℕ) (ε p : ι → ℝ) (E : ι → Set (Coeff n)) (dates : ι → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (ht : ∀ i, ∀ t ∈ dates i, |t| ≤ T)
    (hfit : ∀ i, ∀ t ∈ dates i, E i ⊆ BlockDilations.affordableDraw n (s i) (ε i) t)
    (hε : ∀ i, ε i+ρ<3/4) (hp : ∀ i, 0 ≤ p i) :
    let R := firstRanks (Fin (n+2) → Bool) r hr
    let b := L/T
    let a := Real.sqrt (1-b^2)
    let τ (i : ι) := 1-(ε i+ρ+1/4)
    let passes (h : Coeff n) := ∀ i, ∃ t ∈ dates i, ∃ (q : ℕ) (w : R → ℝ),
      (∀ j, w j∈Icc 0 W) ∧ ∑ j, w j=1 ∧ affineTracePrice n (s i) h R w q a b t ≤ τ i^(2*q)*p i
    pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹'
      (⋃ i, E i)) ≤
      (fieldLaw n).real {h | ¬passes h} + (∑ i, p i) +
        4*Fintype.card (PathLabel n)*(r:ℝ)^2*W*L^2/(T*ρ) := by
  classical
  intro R b a τ passes
  have hb : |b| ≤ 1 := by rwa [abs_div,abs_of_pos hT,div_le_one hT]
  have hb₂ : b^2 ≤ 1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hab : a^2+b^2=1 := by rw [Real.sq_sqrt (sub_nonneg.mpr hb₂)]; ring
  have hsmall : 1-a ≤ b^2 := by
    have ha := Real.sqrt_nonneg (1-b^2)
    have ha' : a ≤ 1 := (Real.sqrt_le_iff).mpr ⟨zero_le_one,by nlinarith only [sq_nonneg b]⟩
    nlinarith only [hab,mul_nonneg ha (sub_nonneg.mpr ha')]
  let F := rotated (n:=n) a b ⁻¹' (⋃ i, E i)
  let Z := {x : FieldPair n | ∃ t : ℝ, |t| ≤ T ∧ ρ/W < readingError R a b x t}
  let D := toMeasurable (pairLaw n) Z
  let G := F \ D
  have hU : MeasurableSet (⋃ i, E i) := MeasurableSet.iUnion hE
  have hG : MeasurableSet G := (hU.preimage (rotated_law n hab).measurable).diff (measurableSet_toMeasurable ..)
  have weighted (i : ι) (t : ℝ) (hti : t ∈ dates i) (w : R → ℝ) (hw : ∀ j, w j∈Icc 0 W) (hsum : ∑ j, w j=1)
      (h g : Coeff n) (hout : (fun l => (h l,g l))∉D)
      (hdate : rotated a b (fun l => (h l,g l)) ∈ BlockDilations.affordableDraw n (s i) (ε i) t) :
      weightedFit (generator h).2.isHermitian.eigenvectorUnitary R w (s i) (ε i+ρ)
        (fun j => wave t (a*(generator h).2.isHermitian.eigenvalues j+b*localSlope h g j)) := by
    let x : FieldPair n := fun l => (h l,g l)
    have hl : readingError R a b x t ≤ ρ/W :=
      le_of_not_gt fun he => hout (subset_toMeasurable _ _ ⟨t,ht i t hti,he⟩)
    have hf := physical_weighted_fit x a b t (ε i) ρ W R w (fun j => (hw j).1) hsum (fun j => (hw j).2)
      (by rw [mul_comm]; exact (le_div_iff₀ hW).mp hl) hdate
    have hz : (fun j => wave t (diagonalEnergy (generator h).2.isHermitian.eigenvectorUnitary
        (generator (rotated a b x)).val j)) =
        (fun j => wave t (a*(generator h).2.isHermitian.eigenvalues j+b*localSlope h g j)) :=
      funext fun j => congrArg (wave t) (affine_energies a b x j)
    rw [←hz]
    exact hf
  have hprice : (pairLaw n).real D ≤ 4*Fintype.card (PathLabel n)*(r:ℝ)^2*W*L^2/(T*ρ) := by
    change ((pairLaw n) (toMeasurable (pairLaw n) Z)).toReal ≤ _
    rw [measure_toMeasurable]
    apply (gaussian_ranked_readings n R hab hT (show 0<ρ/W by positivity)).trans
    rw [firstRanks_weight,Nat.cast_pow]
    calc
      _ ≤ 4*T*b^2*(r:ℝ)^2*Fintype.card (PathLabel n)/(ρ/W) := by gcongr
      _ = _ := by dsimp only [b]; field_simp
  have hg : (pairLaw n).real G ≤ (fieldLaw n).real {h | ¬passes h}+∑ i, p i := by
    apply sliced_field_bound G hG _ (Finset.sum_nonneg fun i _ => hp i)
    intro h hh
    have hpass : passes h := not_not.mp hh
    let A (i : ι) := {g : Coeff n | (fun l => (h l,g l))∉D ∧
      rotated a b (fun l => (h l,g l)) ∈ E i}
    have hs : {g : Coeff n | (fun l => (h l,g l))∈G} ⊆ ⋃ i, A i := by
      rintro g ⟨hf,hout⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hf
      exact mem_iUnion.mpr ⟨i,hout,hi⟩
    apply (measureReal_mono hs).trans ((measureReal_iUnion_fintype_le A).trans _)
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨t,hti,q,w,hw,hsum,hu⟩ := hpass i
    have hm := affine_circuit_twists n (s i) h R w (fun j => (hw j).1) hsum q a b t (ε i+ρ) (hε i).le
    have hτ : 0<τ i := by dsimp only [τ]; linarith only [hε i]
    apply (measureReal_mono (fun g (hg : g∈A i) => weighted i t hti w hw hsum h g hg.1 (hfit i t hti hg.2))).trans
    exact le_of_mul_le_mul_left (hm.trans hu) (pow_pos hτ (2*q))
  have hsub : F ⊆ G ∪ D := fun x hx => by
    by_cases hd : x∈D
    · exact Or.inr hd
    · exact Or.inl ⟨hx,hd⟩
  have heq : pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹' (⋃ i, E i)) =
      (pairLaw n).real F := by
    unfold Measure.real
    rw [(BlockDilations.prefix_measure n).measure_preimage hU.nullMeasurableSet,
      (rotated_law n hab).measure_preimage hU.nullMeasurableSet]
  rw [heq]
  exact (measureReal_mono hsub).trans ((measureReal_union_le ..).trans (add_le_add hg hprice))

#print axioms physical_event_twist_tail
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
