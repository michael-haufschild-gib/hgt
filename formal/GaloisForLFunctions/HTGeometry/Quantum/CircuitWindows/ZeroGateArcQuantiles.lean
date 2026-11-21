import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateFullOccupation

/-!
# Strict enclosure probabilities and zero-gate quantiles

An equally spaced packet realizes any covering length below saturation.
Using a strict covering arc makes each band between two such lengths
contain an open set of positive relative Haar measure.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance arcQuantileCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

private theorem arcCeiling_mem (D : ℕ) : finitePhaseArcCeiling D ∈ Icc (0 : ℝ) 1 := by
  unfold finitePhaseArcCeiling
  refine ⟨sub_nonneg.mpr ?_, sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))⟩
  by_cases h : D = 0
  · simp only [h, Nat.cast_zero, inv_zero, zero_le_one]
  · have hD : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
    rw [← one_div]
    exact (div_le_one (zero_lt_one.trans_le hD)).mpr hD

section Relative

variable {ι : Type*} [Fintype ι]

/-- Every band of positive width below saturation contains a nonempty open set. -/
theorem exists_isOpen_subset_relativeEnclosingUnitArc_diff (ref : ι) (hD : 2 ≤ Fintype.card ι)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ finitePhaseArcCeiling (Fintype.card ι)) :
    ∃ U : Set ({j : ι // j ≠ ref} → UnitAddCircle), IsOpen U ∧ U.Nonempty ∧
      U ⊆ relativeEnclosingUnitArc ref s \ relativeEnclosingUnitArc ref r := by
  classical
  let m := Fintype.card ι - 2
  have hm : m + 2 = Fintype.card ι := Nat.sub_add_cancel hD
  let f := (Fintype.equivFin ι).trans (finCongr hm.symm)
  let e := f.trans (Equiv.swap (f ref) 0)
  have he0 : e ref = 0 := by simp [e]
  let q := (r + s) / 2
  have hrq : r < q := by dsimp only [q]; linarith only [hrs]
  have hqs : q < s := by dsimp only [q]; linarith only [hrs]
  have hq : 0 < q := hr.trans_lt hrq
  have hb := arcCeiling_mem (Fintype.card ι)
  let δ := q / ((m : ℝ) + 1)
  let a (i : Fin (m + 2)) := (i.val : ℝ) * δ
  let θ (i : Fin (m + 2)) := (2 * Real.pi) * a i
  let x : {j : ι // j ≠ ref} → UnitAddCircle := fun j => (a (e j) : UnitAddCircle)
  have hx (j : ι) : relativeUnitPhasePacket ref x j = (a (e j) : UnitAddCircle) := by
    rcases eq_or_ne j ref with rfl | hj
    · simp [relativeUnitPhasePacket, he0, a]
    · simp [relativeUnitPhasePacket, hj, x]
  let C : Set UnitAddCircle := (((↑) : ℝ → UnitAddCircle) '' Ioo 0 s)
  let V : Set ({j : ι // j ≠ ref} → UnitAddCircle) := ⋂ j, (fun y => y j) ⁻¹' C
  have hC : IsOpen C := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hV : IsOpen V := isOpen_iInter_of_finite fun j => hC.preimage (continuous_apply j)
  have hxV : x ∈ V := by
    refine mem_iInter.mpr fun j => ⟨a (e j), ⟨?_, ?_⟩, rfl⟩
    · have hj : (e j).val ≠ 0 := by
        intro he
        exact j.2 (e.injective ((Fin.ext he).trans he0.symm))
      exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hj) (div_pos hq (by positivity))
    · have hj : (e j).val ≤ m + 1 := by have hh := (e j).isLt; omega
      have hmul : ((m : ℝ) + 1) * δ = q := by
        rw [mul_comm]; exact div_mul_cancel₀ _ (by positivity)
      refine lt_of_le_of_lt ?_ hqs
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (div_pos hq (by positivity)).le
  have hVsub : V ⊆ relativeEnclosingUnitArc ref s := by
    intro y hy
    change relativeUnitPhasePacket ref y ∈ enclosingUnitArc s
    refine mem_iUnion.mpr ⟨ref, fun j hj => ?_⟩
    have h : y ⟨j, hj⟩ ∈ C := mem_iInter.mp hy ⟨j, hj⟩
    simpa [relativeUnitPhasePacket, hj, forwardUnitArc] using image_mono Ioo_subset_Icc_self h
  have hnot : x ∉ relativeEnclosingUnitArc ref r := by
    intro hxmem
    let r' : Icc (0 : ℝ) 1 := ⟨r, hr, (hrs.le.trans hs).trans hb.2⟩
    have hθ : (fun j => (((θ (e j) / (2 * Real.pi)) : ℝ) : UnitAddCircle)) =
        relativeUnitPhasePacket ref x := by
      funext j
      rw [hx]
      congr 1
      dsimp only [θ]
      rw [mul_comm, mul_div_cancel_right₀ _ two_pi_pos.ne']
    haveI : Nonempty ι := ⟨ref⟩
    change relativeUnitPhasePacket ref x ∈ enclosingUnitArc r at hxmem
    rw [← hθ] at hxmem
    have hL := (mem_enclosingUnitArc_iff_spectralEnclosingArcLength_full (θ ∘ e) r').mp hxmem
    obtain ⟨i, hi⟩ := (spectralEnclosingArcLength_le_iff _ _).mp hL
    have hLe := (spectralEnclosingArcLength_le_iff θ (2 * Real.pi * r)).mpr
      ⟨e i, fun j => by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi (e.symm j)⟩
    have hqbound : q ≤ finitePhaseArcCeiling (m + 2) := by rw [hm]; exact hqs.le.trans hs
    have heq : spectralEnclosingArcLength θ = 2 * Real.pi * q :=
      spectralEnclosingArcLength_equispaced m hq.le hqbound
    rw [heq] at hLe
    exact (not_le_of_gt hrq) ((mul_le_mul_iff_of_pos_left two_pi_pos).mp hLe)
  exact ⟨V \ relativeEnclosingUnitArc ref r, hV.sdiff (isClosed_relativeEnclosingUnitArc ref r),
    ⟨x, hxV, hnot⟩, fun _ hy => ⟨hVsub hy.1, hy.2⟩⟩

variable [DecidableEq ι]

/-- The full Haar profile increases strictly all the way to saturation. -/
theorem strictMonoOn_relativeUnitArcMass (ref : ι) (hD : 2 ≤ Fintype.card ι) :
    StrictMonoOn (relativeUnitArcMass ref) (Icc 0 (finitePhaseArcCeiling (Fintype.card ι))) := by
  intro r hr s hs hrs
  obtain ⟨U, hU, hne, hsub⟩ := exists_isOpen_subset_relativeEnclosingUnitArc_diff ref hD hr.1 hrs hs.2
  have hpos : 0 < volume.real U :=
    (ENNReal.toReal_pos (hU.measure_pos volume hne).ne' (measure_ne_top _ _))
  apply sub_pos.mp
  rw [relativeUnitArcMass, relativeUnitArcMass, ← measureReal_sdiff (relativeEnclosingUnitArc_mono ref hrs.le)
    (isClosed_relativeEnclosingUnitArc ref r).measurableSet (measure_ne_top _ _)]
  exact hpos.trans_le (measureReal_mono hsub (measure_ne_top _ _))

/-- Every prescribed probability has exactly one arc quantile up to saturation. -/
theorem existsUnique_relativeUnitArcMass_eq (ref : ι) (hD : 2 ≤ Fintype.card ι) (p : Icc (0 : ℝ) 1) :
    ∃! r : Icc (0 : ℝ) (finitePhaseArcCeiling (Fintype.card ι)), relativeUnitArcMass ref r = (p : ℝ) := by
  let b := finitePhaseArcCeiling (Fintype.card ι)
  have hb : b ∈ Icc (0 : ℝ) 1 := arcCeiling_mem _
  have hcont : ContinuousOn (relativeUnitArcMass ref) (Icc 0 b) :=
    (lipschitzOnWith_relativeUnitArcMass ref).continuousOn.mono (Icc_subset_Icc_right hb.2)
  have hzero : relativeUnitArcMass ref 0 = 0 := by
    have h := relativeUnitArcMass_eq_power ref ⟨0, le_rfl, by positivity⟩
    change relativeUnitArcMass ref 0 = zeroGateArcDensity (Fintype.card ι) 0 at h
    simpa only [zeroGateArcDensity, zero_pow (by omega : Fintype.card ι - 1 ≠ 0), mul_zero] using h
  have hone : relativeUnitArcMass ref b = 1 := relativeUnitArcMass_eq_one_of_ceiling ref ⟨b, hb⟩ le_rfl
  have hp : (p : ℝ) ∈ Icc (relativeUnitArcMass ref 0) (relativeUnitArcMass ref b) := by
    rw [hzero, hone]
    exact p.2
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hb.1 hcont hp
  exact ⟨⟨r, hr⟩, he, fun s hs => Subtype.ext
    ((strictMonoOn_relativeUnitArcMass ref hD).injOn s.2 hr (hs.trans he.symm))⟩

end Relative

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The empirical occupation of a tolerance band converges to the difference
of the two Haar probabilities. -/
theorem maximallyProjective_zeroGateArcBandOccupation_from_start {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (r s : Icc (0 : ℝ) 1) (hrs : (r : ℝ) ≤ s) (a : ℝ) :
    Tendsto (fun T => volume.real ((zeroGateReturnSet H s \ zeroGateReturnSet H r) ∩ Icc a T) / (T - a))
      atTop (𝓝 (zeroGateFullArcMass n s - zeroGateFullArcMass n r)) := by
  let R := zeroGateReturnSet H r
  let S := zeroGateReturnSet H s
  have hsub : R ⊆ S := by
    let ref : Fin n → Bool := fun _ => false
    rw [show R = _ from zeroGateReturnSet_eq_preimage_full H ref r,
      show S = _ from zeroGateReturnSet_eq_preimage_full H ref s]
    exact preimage_mono (relativeEnclosingUnitArc_mono ref hrs)
  have hR : MeasurableSet R :=
    (isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const).measurableSet
  have h := (maximallyProjective_zeroGateFullOccupation_from_start H hmax s a).sub
    (maximallyProjective_zeroGateFullOccupation_from_start H hmax r a)
  refine h.congr fun T => ?_
  change volume.real (S ∩ Icc a T) / (T - a) - volume.real (R ∩ Icc a T) / (T - a) =
    volume.real ((S \ R) ∩ Icc a T) / (T - a)
  have hset : (S \ R) ∩ Icc a T = (S ∩ Icc a T) \ (R ∩ Icc a T) := by
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [hset, measureReal_sdiff (inter_subset_inter_left _ hsub) (hR.inter measurableSet_Icc)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne), sub_div]

/-- Almost surely, every positive-width band below saturation accounts for
a positive fraction of the orbit on every prefix of at least three sites. -/
theorem gaussian_path_zeroGateArcBandOccupation_pos :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ r s : Icc (0 : ℝ) 1,
      (r : ℝ) < s → (s : ℝ) ≤ finitePhaseArcCeiling (2 ^ (k + 3)) → ∀ a : ℝ,
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      let p := zeroGateFullArcMass (k + 3) s - zeroGateFullArcMass (k + 3) r
      0 < p ∧ Tendsto
        (fun T => volume.real ((zeroGateReturnSet H s \ zeroGateReturnSet H r) ∩ Icc a T) / (T - a))
        atTop (𝓝 p) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k r s hrs hs a
  let u := pathPauliDisorderShell ω (k + 1)
  let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  refine ⟨?_, maximallyProjective_zeroGateArcBandOccupation_from_start H (hω k) r s hrs.le a⟩
  have hcard : Fintype.card (Fin (k + 3) → Bool) = 2 ^ (k + 3) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hD : 2 ≤ Fintype.card (Fin (k + 3) → Bool) := by
    rw [hcard]
    exact pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ k + 3)
  rw [← hcard] at hs
  exact sub_pos.mpr (strictMonoOn_relativeUnitArcMass (fun _ => false) hD
    ⟨r.2.1, hrs.le.trans hs⟩ ⟨s.2.1, hs⟩ hrs)

#print axioms exists_isOpen_subset_relativeEnclosingUnitArc_diff
#print axioms strictMonoOn_relativeUnitArcMass
#print axioms existsUnique_relativeUnitArcMass_eq
#print axioms maximallyProjective_zeroGateArcBandOccupation_from_start
#print axioms gaussian_path_zeroGateArcBandOccupation_pos

end

end GaloisForLFunctions.HTGeometry
