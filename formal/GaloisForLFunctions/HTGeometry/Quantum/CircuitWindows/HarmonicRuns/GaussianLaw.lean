import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.ArcPowers
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Exact frequency of persistent empty-circuit returns at multiples of a time -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

/-- Steps whose entire finite progression from the identity is affordable
with no gates at the specified projective operator error. -/
def runSet {n : ℕ} (H : selfAdjoint (Register n)) (ε : ℝ) (m : ℕ) : Set ℝ :=
  {t | ∀ k ≤ m, HasProjectiveCircuitApproximation n ε 0 (unitaryEvolution H.val ((k:ℝ)*t))}

private theorem packet_multiple {I : Type*} [Fintype I] [DecidableEq I] (i : I) (ω : {j // j ≠ i} → ℝ)
    (k : ℕ) (t : ℝ) :
    relativeUnitPhasePacket i (finiteClockPhasePoint ω ((k:ℝ)*t)) =
      k • relativeUnitPhasePacket i (finiteClockPhasePoint ω t) := by
  classical
  funext j
  by_cases h : j=i
  · subst j
    simp [relativeUnitPhasePacket]
  · simp only [Pi.smul_apply,relativeUnitPhasePacket,dif_pos h]
    change ((((k:ℝ)*t)*ω ⟨j,h⟩/(2*Real.pi):ℝ):UnitAddCircle) =
      k • ((t*ω ⟨j,h⟩/(2*Real.pi):ℝ):UnitAddCircle)
    rw [←AddCircle.coe_nsmul,nsmul_eq_mul]
    congr 1
    change ((k:ℝ)*t)*ω ⟨j,h⟩/(2*Real.pi) = k*(t*ω ⟨j,h⟩/(2*Real.pi))
    ring

/-- A full run at one operator tolerance is one return at a smaller
angular tolerance. No spectral independence is needed for the identity. -/
theorem runSet_eq {n : ℕ} (H : selfAdjoint (Register n)) {x : ℝ} (hx : 0 ≤ x) (hshort : 3*x < 1)
    (m : ℕ) (hm : 0 < m) :
    runSet H (zeroGateArcTolerance x) m = zeroGateReturnSet H (x/(m:ℝ)) := by
  let i : Fin n → Bool := fun _ => false
  let ω := projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmp : 0 < (m:ℝ) := zero_lt_one.trans_le hm1
  let r : Icc (0:ℝ) (1/2) := ⟨x,hx,by linarith only [hshort]⟩
  let s : Icc (0:ℝ) (1/2) := ⟨x/(m:ℝ),div_nonneg hx hmp.le,
    (div_le_self hx hm1).trans r.2.2⟩
  ext t
  let θ := relativeUnitPhasePacket i (finiteClockPhasePoint ω t)
  have ht (q : Icc (0:ℝ) (1/2)) (u : ℝ) : HasProjectiveCircuitApproximation n
      (zeroGateArcTolerance q) 0 (unitaryEvolution H.val u) ↔
      relativeUnitPhasePacket i (finiteClockPhasePoint ω u) ∈ enclosingUnitArc q :=
    zeroGateApproximation_iff_clock_shortArc H i u q
  change (∀ k ≤ m, HasProjectiveCircuitApproximation n (zeroGateArcTolerance r) 0
    (unitaryEvolution H.val ((k:ℝ)*t))) ↔ orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance s
  rw [orbitCircuitDistance,←hasProjectiveCircuitApproximation_iff_infDist,ht s t]
  simp_rw [ht r,packet_multiple]
  exact consecutive_powers_iff θ hx hshort m hm

private theorem conditional_limit {n : ℕ} (H : selfAdjoint (Register n))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {x : ℝ} (hx : 0 < x)
    (hshort : 3*x < 1) (m : ℕ) (hm : 0 < m) (a : ℝ) :
    Tendsto (fun T => volume.real (runSet H (zeroGateArcTolerance x) m ∩ Icc a T) /
      volume.real (zeroGateReturnSet H x ∩ Icc a T)) atTop
        (𝓝 ((1/(m:ℝ))^(2^n-1:ℕ))) := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmp := zero_lt_one.trans_le hm1
  let r : Icc (0:ℝ) (1/2) := ⟨x,hx.le,by linarith only [hshort]⟩
  let s : Icc (0:ℝ) (1/2) := ⟨x/(m:ℝ),div_nonneg hx.le hmp.le,(div_le_self hx.le hm1).trans r.2.2⟩
  have hD : 0 < (2^n:ℕ) := by positivity
  have hd : zeroGateArcDensity (2^n) x ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hD.ne') (pow_ne_zero _ hx.ne')
  have h := (maximallyProjective_zeroGateOccupation_from_start H hi s a).div
    (maximallyProjective_zeroGateOccupation_from_start H hi r a) hd
  have he : zeroGateArcDensity (2^n) s/zeroGateArcDensity (2^n) r = (1/(m:ℝ))^(2^n-1:ℕ) := by
    dsimp only [zeroGateArcDensity,s,r]
    rw [div_pow,div_pow,one_pow]
    field_simp [pow_ne_zero _ hx.ne',pow_ne_zero _ hmp.ne',Nat.cast_ne_zero.mpr hD.ne']
  rw [he] at h
  rw [runSet_eq H hx.le hshort m hm]
  apply h.congr'
  filter_upwards [eventually_gt_atTop a] with T hT
  exact div_div_div_cancel_right₀ (sub_ne_zero.mpr hT.ne') _ _

/-- Among times when the empty circuit suffices at any fixed physical
error below one, the fraction whose first m multiples all remain affordable
is exactly m to the power 1−D in the long-time limit. -/
theorem gaussian_conditional_run_law :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ ε ∈ Ioo (0:ℝ) 1, ∀ m : ℕ, 0 < m → ∀ a : ℝ,
        Tendsto (fun T => volume.real (runSet H ε m ∩ Icc a T) /
          volume.real (visitSet H 0 ε ∩ Icc a T)) atTop (𝓝 ((1/(m:ℝ))^(D-1))) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k N D H ε hε m hm a
  have h2 : (1:ℝ) < Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [h,Real.sqrt_nonneg 2]
  obtain ⟨hx,htol⟩ := physicalArc_spec hε.1 (hε.2.trans h2)
  have hthird : zeroGateArcTolerance (1/3) = 1 := by
    rw [zeroGateArcTolerance,show Real.pi*(1/3)/2 = Real.pi/6 by ring,Real.sin_pi_div_six]
    norm_num
  have hlt : physicalArc ε < 1/3 := (strictMonoOn_zeroGateArcTolerance.lt_iff_lt
    ⟨hx.1.le,hx.2.le⟩ (by norm_num : (1/3:ℝ) ∈ Icc (0:ℝ) (1/2))).mp (by rw [htol,hthird]; exact hε.2)
  have he : visitSet H 0 ε = zeroGateReturnSet H (physicalArc ε) := by
    ext t
    change HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val t) ↔
      orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance (physicalArc ε)
    rw [htol]
    exact hasProjectiveCircuitApproximation_iff_infDist _ _ _
  rw [he]
  have hc := conditional_limit H (hω k) hx.1 (by linarith only [hlt]) m hm a
  rwa [htol] at hc

#print axioms runSet_eq
#print axioms gaussian_conditional_run_law
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
