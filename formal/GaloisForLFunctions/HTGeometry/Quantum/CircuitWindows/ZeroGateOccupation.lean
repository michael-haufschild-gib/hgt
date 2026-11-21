import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-!
# Exact one-sided occupation of the zero-gate tube

Up to the semicircle threshold, zero gates suffice exactly when the relative
eigenphases occupy a short arc. For maximally projective spectra the time
fraction converges to the exact Haar mass of this arc event.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem coe_fract_unitAddCircle (x : ℝ) :
    ((Int.fract x : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  have hz : (((⌊x⌋ : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨⌊x⌋, by simp [zsmul_eq_mul]⟩
  rw [Int.fract, AddCircle.coe_sub, hz, sub_zero]

private theorem mem_forwardUnitArc_iff_fract (x : ℝ) (r : Icc (0 : ℝ) (1 / 2)) :
    (x : UnitAddCircle) ∈ forwardUnitArc r ↔ Int.fract x ≤ (r : ℝ) := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' : y ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨hy.1, by linarith only [hy.2, r.2.2]⟩
    have hx' : Int.fract x ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg x, by simpa only [zero_add] using Int.fract_lt_one x⟩
    have h : y = Int.fract x := (AddCircle.coe_eq_coe_iff_of_mem_Ico hy' hx').mp
      (he.trans (coe_fract_unitAddCircle x).symm)
    exact h ▸ hy.2
  · intro h
    exact ⟨Int.fract x, ⟨Int.fract_nonneg x, h⟩, coe_fract_unitAddCircle x⟩

/-- A normalized phase packet belongs to the short-arc target exactly at
the corresponding angular cutoff for its shortest enclosing arc. -/
theorem mem_enclosingUnitArc_iff_spectralEnclosingArcLength {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : ι → ℝ) (r : Icc (0 : ℝ) (1 / 2)) :
    (fun j => ((θ j / (2 * Real.pi) : ℝ) : UnitAddCircle)) ∈ enclosingUnitArc r ↔
      spectralEnclosingArcLength θ ≤ 2 * Real.pi * (r : ℝ) := by
  have hgap (i j : ι) :
      (((θ j / (2 * Real.pi) : ℝ) : UnitAddCircle) -
        ((θ i / (2 * Real.pi) : ℝ) : UnitAddCircle)) ∈ forwardUnitArc r ↔
        forwardPhaseGap (θ i) (θ j) ≤ 2 * Real.pi * (r : ℝ) := by
    rw [← AddCircle.coe_sub, ← sub_div, mem_forwardUnitArc_iff_fract, forwardPhaseGap,
      mul_comm (2 * Real.pi), mul_le_mul_iff_of_pos_right two_pi_pos]
  rw [spectralEnclosingArcLength_le_iff, enclosingUnitArc, mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun j => ?_⟩
    by_cases h : j = i
    · subst j
      rw [forwardPhaseGap, sub_self, zero_div, Int.fract_zero, zero_mul]
      exact mul_nonneg two_pi_pos.le r.2.1
    · exact (hgap i j).mp (hi j h)
  · rintro ⟨i, hi⟩
    exact ⟨i, fun j _ => (hgap i j).mpr (hi j)⟩

private theorem mem_relativeEnclosingUnitArc_clock {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : ι → ℝ) (i : ι) (t : ℝ) (r : Icc (0 : ℝ) (1 / 2)) :
    finiteClockPhasePoint (projectiveFrequency (fun j => -E j) i) t ∈ relativeEnclosingUnitArc i r ↔
      spectralEnclosingArcLength (fun j => -(t * E j)) ≤ 2 * Real.pi * (r : ℝ) := by
  let θ := fun j => -(t * E j)
  let x := finiteClockPhasePoint (projectiveFrequency (fun j => -E j) i) t
  let y := fun j => ((θ j / (2 * Real.pi) : ℝ) : UnitAddCircle)
  have hval (j : ι) : relativeUnitPhasePacket i x j = y j - y i := by
    classical
    by_cases h : j = i
    · subst j
      simp [relativeUnitPhasePacket]
    · rw [show relativeUnitPhasePacket i x j = x ⟨j, h⟩ from by simp [relativeUnitPhasePacket, h]]
      change ((t * (-E j - -E i) / (2 * Real.pi) : ℝ) : UnitAddCircle) =
        ((θ j / (2 * Real.pi) : ℝ) : UnitAddCircle) - ((θ i / (2 * Real.pi) : ℝ) : UnitAddCircle)
      rw [← AddCircle.coe_sub]
      congr 1
      dsimp only [θ]
      ring
  change relativeUnitPhasePacket i x ∈ enclosingUnitArc r ↔ _
  rw [← mem_enclosingUnitArc_iff_spectralEnclosingArcLength θ r]
  simp only [enclosingUnitArc, mem_iUnion, anchoredUnitArc, mem_setOf_eq, hval, sub_sub_sub_cancel_right, y]

/-- Zero-gate operator approximation at a semicircle-scale tolerance is
exactly the short-arc event along the evolving relative phases. -/
theorem zeroGateApproximation_iff_clock_shortArc {n : ℕ} (H : selfAdjoint (Reg n))
    (i : Fin n → Bool) (t : ℝ) (r : Icc (0 : ℝ) (1 / 2)) :
    HasProjectiveCircuitApproximation n (2 * Real.sin (Real.pi * (r : ℝ) / 2)) 0
      (unitaryEvolution (H : Reg n) t) ↔
        finiteClockPhasePoint (projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i) t ∈
          relativeEnclosingUnitArc i r := by
  let θ := fun j => -(t * H.2.isHermitian.eigenvalues j)
  let L := orbitSpectralEnclosingArcLength H t
  have hL0 : 0 ≤ L := spectralEnclosingArcLength_nonneg θ
  have hLπ : L < 2 * Real.pi := spectralEnclosingArcLength_lt_two_pi θ
  have ha : L / 4 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith only [hL0, Real.pi_pos], by linarith only [hLπ]⟩
  have hr0 := mul_nonneg Real.pi_pos.le r.2.1
  have hrπ := mul_le_mul_of_nonneg_left r.2.2 Real.pi_pos.le
  have hb : Real.pi * (r : ℝ) / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith only [hr0, Real.pi_pos], by linarith only [hrπ, Real.pi_pos]⟩
  rw [mem_relativeEnclosingUnitArc_clock, hasProjectiveCircuitApproximation_iff_infDist,
    ← orbitCircuitDistance, orbitCircuitDistance_zeroGate_eq_enclosingArc,
    mul_le_mul_iff_of_pos_left zero_lt_two]
  change Real.sin (L / 4) ≤ Real.sin (Real.pi * (r : ℝ) / 2) ↔ L ≤ _
  rw [Real.strictMonoOn_sin.le_iff_le ha hb]
  constructor <;> intro h <;> linarith only [h]

/-- The fraction of `(0,T]` on which zero gates suffice converges to
`N r^(N-1)`, where `r` is the allowed covering length in turns. -/
theorem maximallyProjective_zeroGateWindow_tendsto {n : ℕ}
    (H : selfAdjoint (Reg n)) (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (r : Icc (0 : ℝ) (1 / 2)) :
    Tendsto (fun T => (windowProbabilityMeasure T : Measure ℝ)
      {t | HasProjectiveCircuitApproximation n (2 * Real.sin (Real.pi * (r : ℝ) / 2)) 0
        (unitaryEvolution (H : Reg n) t)}) atTop
      (𝓝 ((Fintype.card (Fin n → Bool) : ℝ≥0∞) *
        ENNReal.ofReal (r : ℝ) ^ (Fintype.card (Fin n → Bool) - 1))) := by
  classical
  let i : Fin n → Bool := fun _ => false
  let ω := projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i
  have hω : RationallyIndependentFrequency ω :=
    maximallyProjectiveEnergy_projectiveFrequency_independent _ (maximallyProjectiveEnergy_neg hmax) i
  have hbd : (finiteTorusHaarProbabilityMeasure {j : Fin n → Bool // j ≠ i} : Measure _)
      (frontier (relativeEnclosingUnitArc i r)) = 0 := by
    rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
    exact volume_frontier_relativeEnclosingUnitArc i r
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (clockPhaseWindowLaw_tendsto_haar ω hω) hbd
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume, volume_relativeEnclosingUnitArc i r] at h
  refine h.congr fun T => ?_
  rw [clockPhaseWindowLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (finiteClockPhasePoint_continuous ω).measurable
      (isClosed_relativeEnclosingUnitArc i r).measurableSet]
  congr 1
  ext t
  exact (zeroGateApproximation_iff_clock_shortArc H i t r).symm

/-- Almost surely the exact zero-gate occupation law holds for every
open Gaussian Pauli prefix of at least three sites and every short-arc tolerance. -/
theorem gaussian_path_zeroGateWindow_tendsto :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ r : Icc (0 : ℝ) (1 / 2),
      let H := pathHamiltonian (pathPauliDisorderShell ω (k + 1))
      let D : ℕ := 2 ^ (k + 3)
      Tendsto (fun T => (windowProbabilityMeasure T : Measure ℝ)
        {t | HasProjectiveCircuitApproximation (k + 3)
          (2 * Real.sin (Real.pi * (r : ℝ) / 2)) 0 (unitaryEvolution H t)}) atTop
        (𝓝 ((D : ℝ≥0∞) * ENNReal.ofReal (r : ℝ) ^ (D - 1))) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k r
  let u := pathPauliDisorderShell ω (k + 1)
  let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    (maximallyProjective_zeroGateWindow_tendsto H (hω k) r)

#print axioms mem_enclosingUnitArc_iff_spectralEnclosingArcLength
#print axioms zeroGateApproximation_iff_clock_shortArc
#print axioms maximallyProjective_zeroGateWindow_tendsto
#print axioms gaussian_path_zeroGateWindow_tendsto

end

end GaloisForLFunctions.HTGeometry
