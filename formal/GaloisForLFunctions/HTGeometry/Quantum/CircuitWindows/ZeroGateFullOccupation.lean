import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.CircularArcRange
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateReturnSpacing

/-!
# The full zero-gate occupation profile

Every enclosing-arc tolerance defines a continuity set for relative Haar
measure. Changes in tolerance charge pairwise phase differences in an arc
band, which bounds the variation of the occupation profile.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

section Relative

variable {ι : Type*}

private theorem relativePhase_at_ref (ref : ι) (x : {j : ι // j ≠ ref} → UnitAddCircle) :
    relativeUnitPhasePacket ref x ref = 0 := by simp [relativeUnitPhasePacket]

private theorem relativePhase_at_ne {ref j : ι} (h : j ≠ ref)
    (x : {k : ι // k ≠ ref} → UnitAddCircle) : relativeUnitPhasePacket ref x j = x ⟨j, h⟩ := by
  simp [relativeUnitPhasePacket, h]

private def relativePhaseCoordinate (ref j : ι) : ({k : ι // k ≠ ref} → UnitAddCircle) →+ UnitAddCircle where
  toFun x := relativeUnitPhasePacket ref x j
  map_zero' := by
    rcases eq_or_ne j ref with rfl | h
    · exact relativePhase_at_ref _ _
    · rw [relativePhase_at_ne h]; rfl
  map_add' x y := by
    rcases eq_or_ne j ref with rfl | h
    · simp only [relativePhase_at_ref, add_zero]
    · simp only [relativePhase_at_ne h, Pi.add_apply]

private theorem continuous_relativePhaseCoordinate (ref j : ι) : Continuous (relativePhaseCoordinate ref j) := by
  rcases eq_or_ne j ref with he | h
  · subst j
    have hf : (relativePhaseCoordinate ref ref : _ → UnitAddCircle) = fun _ => 0 :=
      funext fun x => relativePhase_at_ref ref x
    rw [hf]
    exact continuous_const
  · have hf : (relativePhaseCoordinate ref j : _ → UnitAddCircle) = fun x => x ⟨j, h⟩ :=
      funext fun x => relativePhase_at_ne h x
    rw [hf]
    exact continuous_apply _

variable [Fintype ι] [DecidableEq ι]

/-- The phase difference of two distinct labels is uniform under relative Haar measure. -/
theorem measurePreserving_relativePhaseDifference (ref : ι) {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x : {k : ι // k ≠ ref} → UnitAddCircle =>
      relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i) volume volume := by
  let f := relativePhaseCoordinate ref j - relativePhaseCoordinate ref i
  have hc : Continuous f := (continuous_relativePhaseCoordinate ref j).sub (continuous_relativePhaseCoordinate ref i)
  have hsurj : Function.Surjective f := by
    intro y
    rcases eq_or_ne j ref with he | hj
    · subst j
      let x : {k : ι // k ≠ ref} → UnitAddCircle := Pi.single ⟨i, hij⟩ (-y)
      refine ⟨x, ?_⟩
      change relativeUnitPhasePacket ref x ref - relativeUnitPhasePacket ref x i = y
      rw [relativePhase_at_ref, relativePhase_at_ne hij, show x ⟨i, hij⟩ = -y from Pi.single_eq_same _ _,
        zero_sub, neg_neg]
    · let x : {k : ι // k ≠ ref} → UnitAddCircle := Pi.single ⟨j, hj⟩ y
      refine ⟨x, ?_⟩
      change relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i = y
      have hi0 : relativeUnitPhasePacket ref x i = 0 := by
        rcases eq_or_ne i ref with rfl | hi
        · exact relativePhase_at_ref _ _
        · rw [relativePhase_at_ne hi]
          have hne : (⟨i, hi⟩ : {k : ι // k ≠ ref}) ≠ ⟨j, hj⟩ :=
            fun he => hij (congrArg Subtype.val he)
          exact Pi.single_eq_of_ne (M := fun _ => UnitAddCircle) hne y
      rw [hi0, sub_zero, relativePhase_at_ne hj]
      exact Pi.single_eq_same _ _
  letI : Measure.IsAddHaarMeasure (volume : Measure ({k : ι // k ≠ ref} → UnitAddCircle)) := {}
  exact f.measurePreserving hc hsurj (by rw [measure_univ, UnitAddCircle.measure_univ])

/-- The relative Haar probability of enclosure at the specified arc length. -/
def relativeUnitArcMass (ref : ι) (r : ℝ) : ℝ := volume.real (relativeEnclosingUnitArc ref r)

omit [Fintype ι] [DecidableEq ι] in
/-- The relative enclosure events are nested in the allowed arc length. -/
theorem relativeEnclosingUnitArc_mono (ref : ι) : Monotone (relativeEnclosingUnitArc ref) := by
  intro r s hrs x hx
  change relativeUnitPhasePacket ref x ∈ enclosingUnitArc r at hx
  change relativeUnitPhasePacket ref x ∈ enclosingUnitArc s
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨i, fun j hj => image_mono (Icc_subset_Icc_right hrs) (hi j hj)⟩

/-- The enclosure probability increases with the allowed covering length. -/
theorem relativeUnitArcMass_mono (ref : ι) : Monotone (relativeUnitArcMass ref) := by
  intro r s hrs
  exact measureReal_mono (relativeEnclosingUnitArc_mono ref hrs) (measure_ne_top _ _)

/-- A change in enclosure is witnessed by a pair of phases crossing the
arc threshold. The number of ordered pairs gives a Lipschitz bound. -/
theorem relativeUnitArcMass_sub_le (ref : ι) (r s : Icc (0 : ℝ) 1) (hrs : (r : ℝ) ≤ s) :
    relativeUnitArcMass ref s - relativeUnitArcMass ref r ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) * ((s : ℝ) - r) := by
  classical
  let band := forwardUnitArc s \ forwardUnitArc r
  have hB : MeasurableSet band :=
    (isClosed_forwardUnitArc s).measurableSet.diff (isClosed_forwardUnitArc r).measurableSet
  have hmass : volume.real band = (s : ℝ) - r := by
    have hs : forwardUnitArc (r : ℝ) ⊆ forwardUnitArc s := image_mono (Icc_subset_Icc_right hrs)
    unfold band
    rw [measureReal_sdiff hs (isClosed_forwardUnitArc r).measurableSet (measure_ne_top _ _),
      Measure.real, Measure.real, volume_forwardUnitArc_full s, volume_forwardUnitArc_full r,
      ENNReal.toReal_ofReal s.2.1, ENNReal.toReal_ofReal r.2.1]
  let B (i : ι) (j : {j : ι // j ≠ i}) :=
    (fun x : {k : ι // k ≠ ref} → UnitAddCircle => relativeUnitPhasePacket ref x j -
      relativeUnitPhasePacket ref x i) ⁻¹' band
  have hBvol (i : ι) (j : {j : ι // j ≠ i}) : volume.real (B i j) = (s : ℝ) - r := by
    exact ((measurePreserving_relativePhaseDifference ref j.2.symm).measureReal_preimage hB.nullMeasurableSet).trans hmass
  have hsub : relativeEnclosingUnitArc ref s \ relativeEnclosingUnitArc ref r ⊆ ⋃ i, ⋃ j, B i j := by
    rintro x ⟨hx, hnot⟩
    change relativeUnitPhasePacket ref x ∈ enclosingUnitArc s at hx
    change relativeUnitPhasePacket ref x ∉ enclosingUnitArc r at hnot
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hfalse : ¬ ∀ j, j ≠ i → relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i ∈
        forwardUnitArc r := fun h => hnot (mem_iUnion.mpr ⟨i, h⟩)
    push Not at hfalse
    obtain ⟨j, hji, hj⟩ := hfalse
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨⟨j, hji⟩, hi j hji, hj⟩⟩
  have hcard (i : ι) : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl (fun j => j = i), Fintype.card_subtype_eq]
  rw [relativeUnitArcMass, relativeUnitArcMass, ← measureReal_sdiff (relativeEnclosingUnitArc_mono ref hrs)
    (isClosed_relativeEnclosingUnitArc ref r).measurableSet (measure_ne_top _ _)]
  calc
    _ ≤ volume.real (⋃ i, ⋃ j, B i j) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i, volume.real (⋃ j, B i j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, ∑ j, volume.real (B i j) := Finset.sum_le_sum fun i _ => measureReal_iUnion_fintype_le _
    _ = _ := by simp only [hBvol, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_assoc]

/-- The full Haar profile is Lipschitz on its unit-turn domain. -/
theorem lipschitzOnWith_relativeUnitArcMass (ref : ι) :
    LipschitzOnWith ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : NNReal)
      (relativeUnitArcMass ref) (Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr s hs
  have hcast : (((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : NNReal) : ℝ) =
      ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) := rfl
  rw [Real.dist_eq, Real.dist_eq, hcast, Nat.cast_mul]
  rcases le_total r s with h | h
  · rw [abs_sub_comm r s, abs_sub_comm (relativeUnitArcMass ref r) (relativeUnitArcMass ref s),
      abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr (relativeUnitArcMass_mono ref h))]
    exact relativeUnitArcMass_sub_le ref ⟨r, hr⟩ ⟨s, hs⟩ h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr (relativeUnitArcMass_mono ref h))]
    exact relativeUnitArcMass_sub_le ref ⟨s, hs⟩ ⟨r, hr⟩ h

/-- The full profile agrees with the explicit power law up to a semicircle. -/
theorem relativeUnitArcMass_eq_power (ref : ι) (r : Icc (0 : ℝ) (1 / 2)) :
    relativeUnitArcMass ref r = zeroGateArcDensity (Fintype.card ι) r := by
  rw [relativeUnitArcMass, Measure.real, volume_relativeEnclosingUnitArc ref r,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofReal r.2.1,
    zeroGateArcDensity]

/-- The profile saturates at one once the dimension-dependent ceiling is reached. -/
theorem relativeUnitArcMass_eq_one_of_ceiling (ref : ι) (r : Icc (0 : ℝ) 1)
    (hr : finitePhaseArcCeiling (Fintype.card ι) ≤ (r : ℝ)) : relativeUnitArcMass ref r = 1 := by
  letI : Nonempty ι := ⟨ref⟩
  rw [relativeUnitArcMass, relativeEnclosingUnitArc, enclosingUnitArc_eq_univ_of_ceiling r hr,
    preimage_univ, Measure.real, measure_univ, ENNReal.toReal_one]

end Relative

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem mem_relativeEnclosingUnitArc_clock_full {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : ι → ℝ) (i : ι) (t : ℝ) (r : Icc (0 : ℝ) 1) :
    finiteClockPhasePoint (projectiveFrequency (fun j => -E j) i) t ∈ relativeEnclosingUnitArc i r ↔
      spectralEnclosingArcLength (fun j => -(t * E j)) ≤ 2 * Real.pi * (r : ℝ) := by
  let θ := fun j => -(t * E j)
  let x := finiteClockPhasePoint (projectiveFrequency (fun j => -E j) i) t
  let y := fun j => ((θ j / (2 * Real.pi) : ℝ) : UnitAddCircle)
  have hval (j : ι) : relativeUnitPhasePacket i x j = y j - y i := by
    rcases eq_or_ne j i with rfl | h
    · rw [relativePhase_at_ref, sub_self]
    · rw [relativePhase_at_ne h]
      change ((t * (-E j - -E i) / (2 * Real.pi) : ℝ) : UnitAddCircle) =
        ((θ j / (2 * Real.pi) : ℝ) : UnitAddCircle) - ((θ i / (2 * Real.pi) : ℝ) : UnitAddCircle)
      rw [← AddCircle.coe_sub]
      congr 1
      dsimp only [θ]
      ring
  change relativeUnitPhasePacket i x ∈ enclosingUnitArc r ↔ _
  rw [← mem_enclosingUnitArc_iff_spectralEnclosingArcLength_full θ r]
  simp only [enclosingUnitArc, mem_iUnion, anchoredUnitArc, mem_setOf_eq, hval, sub_sub_sub_cancel_right, y]

/-- The full phase window is exactly the physical zero-gate return set. -/
theorem zeroGateReturnSet_eq_preimage_full {n : ℕ} (H : selfAdjoint (Reg n))
    (i : Fin n → Bool) (r : Icc (0 : ℝ) 1) :
    zeroGateReturnSet H r =
      finiteClockPhasePoint (projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i) ⁻¹'
        relativeEnclosingUnitArc i r := by
  ext t
  let θ := fun j => -(t * H.2.isHermitian.eigenvalues j)
  let L := orbitSpectralEnclosingArcLength H t
  have hL0 : 0 ≤ L := spectralEnclosingArcLength_nonneg θ
  have hLπ : L < 2 * Real.pi := spectralEnclosingArcLength_lt_two_pi θ
  have ha : L / 4 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith only [hL0, Real.pi_pos], by linarith only [hLπ]⟩
  have hr0 := mul_nonneg Real.pi_pos.le r.2.1
  have hr1 := mul_le_mul_of_nonneg_left r.2.2 Real.pi_pos.le
  have hb : Real.pi * (r : ℝ) / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith only [hr0, Real.pi_pos], by linarith only [hr1]⟩
  change orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance r ↔
    finiteClockPhasePoint (projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i) t ∈
      relativeEnclosingUnitArc i r
  rw [mem_relativeEnclosingUnitArc_clock_full, orbitCircuitDistance_zeroGate_eq_enclosingArc,
    zeroGateArcTolerance, mul_le_mul_iff_of_pos_left zero_lt_two]
  change Real.sin (L / 4) ≤ Real.sin (Real.pi * (r : ℝ) / 2) ↔ L ≤ _
  rw [Real.strictMonoOn_sin.le_iff_le ha hb]
  constructor <;> intro h <;> linarith only [h]

/-- The full zero-gate occupation profile for a qubit register. -/
def zeroGateFullArcMass (n : ℕ) (r : ℝ) : ℝ := relativeUnitArcMass (fun _ : Fin n => false) r

/-- Haar mass gives the exact long-time occupation from any fixed start,
throughout the full zero-gate tolerance range. -/
theorem maximallyProjective_zeroGateFullOccupation_from_start {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (r : Icc (0 : ℝ) 1) (a : ℝ) :
    Tendsto (fun T => volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a)) atTop
      (𝓝 (zeroGateFullArcMass n r)) := by
  classical
  let i : Fin n → Bool := fun _ => false
  let ω := projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i
  let B := relativeEnclosingUnitArc i r
  have hset : zeroGateReturnSet H r = finiteClockPhasePoint ω ⁻¹' B := zeroGateReturnSet_eq_preimage_full H i r
  have hB : IsClosed B := isClosed_relativeEnclosingUnitArc i r
  have hA : IsClosed (zeroGateReturnSet H r) := by
    rw [hset]
    exact hB.preimage (finiteClockPhasePoint_continuous ω)
  apply tendsto_occupation_from_start _ hA.measurableSet
  have hω : RationallyIndependentFrequency ω :=
    maximallyProjectiveEnergy_projectiveFrequency_independent _ (maximallyProjectiveEnergy_neg hmax) i
  have hbd : (finiteTorusHaarProbabilityMeasure {j : Fin n → Bool // j ≠ i} : Measure _)
      (frontier B) = 0 := by
    rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
    exact volume_frontier_relativeEnclosingUnitArc i r
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (clockPhaseWindowLaw_tendsto_haar ω hω) hbd
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hlim
  have h := (ENNReal.tendsto_toReal (measure_ne_top _ B)).comp hlim
  change Tendsto (fun T => (clockPhaseWindowLaw ω T : Measure _).real B) atTop
    (𝓝 (zeroGateFullArcMass n r)) at h
  refine h.congr fun T => ?_
  rw [clockPhaseWindowLaw, Measure.real, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (finiteClockPhasePoint_continuous ω).measurable hB.measurableSet, ← hset]
  rfl

/-- At the dimension-dependent tolerance every time is a zero-gate return. -/
theorem zeroGateReturnSet_eq_univ_of_ceiling {n : ℕ} (H : selfAdjoint (Reg n)) (r : Icc (0 : ℝ) 1)
    (hr : finitePhaseArcCeiling (2 ^ n) ≤ (r : ℝ)) : zeroGateReturnSet H r = univ := by
  let i : Fin n → Bool := fun _ => false
  have hr' : finitePhaseArcCeiling (Fintype.card (Fin n → Bool)) ≤ (r : ℝ) := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hr
  rw [zeroGateReturnSet_eq_preimage_full H i r, relativeEnclosingUnitArc,
    enclosingUnitArc_eq_univ_of_ceiling r hr', preimage_univ, preimage_univ]

/-- On almost every Gaussian draw the full occupation profile holds at all
tolerances and all starts on every open prefix of at least three sites. -/
theorem gaussian_path_zeroGateFullOccupation_from_start :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ r : Icc (0 : ℝ) 1, ∀ a : ℝ,
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      Tendsto (fun T => volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a)) atTop
        (𝓝 (zeroGateFullArcMass (k + 3) r)) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k r a
  let u := pathPauliDisorderShell ω (k + 1)
  let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  exact maximallyProjective_zeroGateFullOccupation_from_start H (hω k) r a

#print axioms measurePreserving_relativePhaseDifference
#print axioms relativeUnitArcMass_sub_le
#print axioms lipschitzOnWith_relativeUnitArcMass
#print axioms relativeUnitArcMass_eq_power
#print axioms relativeUnitArcMass_eq_one_of_ceiling
#print axioms zeroGateReturnSet_eq_preimage_full
#print axioms maximallyProjective_zeroGateFullOccupation_from_start
#print axioms zeroGateReturnSet_eq_univ_of_ceiling
#print axioms gaussian_path_zeroGateFullOccupation_from_start

end

end GaloisForLFunctions.HTGeometry
