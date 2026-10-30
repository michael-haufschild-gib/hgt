import GaloisForLFunctions.CompletedArithmeticForms.WeilInverseCost
import GaloisForLFunctions.HTGeometry.HilbertClosedRange

/-!
# Arithmetic coordinates of the complete Weil Green form

The actual completed conductor quasimodes pass through the complete inverse
in norm. Every fixed Ramanujan packet therefore has the exact reciprocal
conductor-energy limit, including its pole coordinate and every mixed entry.
-/

noncomputable section

open Matrix Finset Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The complete coercivity reserve pays the inverse of a norm quasimode. -/
theorem norm_inverse_quasimode_residual_le {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.PosDef) {e λ : ℝ} (he : 0 < e) (hλ : 0 < λ)
    (hfloor : ∀ x : EuclideanSpace ℝ I,
      e * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫)
    (v : EuclideanSpace ℝ I) :
    ‖Matrix.toEuclideanLin A⁻¹ v - λ⁻¹ • v‖ ≤
      (e * λ)⁻¹ * ‖Matrix.toEuclideanLin A v - λ • v‖ := by
  let w := Matrix.toEuclideanLin A⁻¹ v - λ⁻¹ • v
  have hinv : Matrix.toEuclideanLin A (Matrix.toEuclideanLin A⁻¹ v) = v := by
    apply PiLp.ext
    change ∀ i, (A *ᵥ (A⁻¹ *ᵥ v)) i = v i
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A
      (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
    exact fun _ => rfl
  have hw : Matrix.toEuclideanLin A w =
      -(λ⁻¹ • (Matrix.toEuclideanLin A v - λ • v)) := by
    dsimp only [w]
    rw [map_sub, map_smul, hinv, smul_sub, smul_smul,
      inv_mul_cancel₀ hλ.ne', one_smul, neg_sub]
  let L := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hb : e * ‖w‖ ≤ ‖Matrix.toEuclideanLin A w‖ :=
    ContinuousLinearMap.norm_le_of_reCoercive (S := L) hfloor w
  rw [hw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hλ)] at hb
  calc
    _ ≤ (λ⁻¹ * ‖Matrix.toEuclideanLin A v - λ • v‖) / e := by
      rw [le_div_iff₀ he]
      simpa only [mul_comm] using hb
    _ = _ := by ring

/-- Every positive completed conductor energy is paid by the actual pole floor. -/
theorem tiltedWeilConductorEnergy_pos {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    0 < completedConductorEnergy tiltedUnitSpline c m :=
  (tiltedWeilGroundEnergy_pos hc).trans_le
    (completedConductorEnergy_one_le contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hc hm)

/-- The complete inverse acts asymptotically by reciprocal completed energy on each actual mode. -/
theorem tendsto_tiltedWeil_inverse_ramanujan_residual_norm {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)⁻¹
          (normalizedRamanujanHorizonVector m N) -
        (completedConductorEnergy tiltedUnitSpline c m)⁻¹ •
          normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  obtain ⟨e, he, hfloor⟩ := exists_tiltedUnitSpline_completeWeilEnergy_uniform_boundedOverlap_floor c
  have hλ := tiltedWeilConductorEnergy_pos hc hm
  have hres := tendsto_completeWeilMatrix_completedConductor_residual_norm
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm
  have hmajor := hres.const_mul ((e * completedConductorEnergy tiltedUnitSpline c m)⁻¹)
  simp only [mul_zero] at hmajor
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmajor
  filter_upwards [hfloor, eventually_tiltedUnitSpline_completeWeilMatrix_posDef hc]
    with N hN hpos
  exact norm_inverse_quasimode_residual_le hpos he hλ (hN c hc le_rfl)
    (normalizedRamanujanHorizonVector m N)

/-- Every mixed Green entry has its exact arithmetic reciprocal-energy limit. -/
theorem tendsto_tiltedWeil_inverse_ramanujan_inner {c : ℝ} (hc : 0 < c)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)⁻¹
          (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫)
      atTop (𝓝 (if m = l then (completedConductorEnergy tiltedUnitSpline c m)⁻¹ else 0)) := by
  have herr := tendsto_horizon_inner_zero_of_norm
    (fun N => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)⁻¹
        (normalizedRamanujanHorizonVector m N) -
      (completedConductorEnergy tiltedUnitSpline c m)⁻¹ • normalizedRamanujanHorizonVector m N)
    (fun N => normalizedRamanujanHorizonVector l N)
    (tendsto_tiltedWeil_inverse_ramanujan_residual_norm hc hm)
    (tendsto_normalizedRamanujanHorizonVector_norm hl)
  have hmain := (tendsto_normalizedRamanujanHorizonVector_gram hm hl).const_mul
    (completedConductorEnergy tiltedUnitSpline c m)⁻¹
  simpa only [inner_sub_left, real_inner_smul_left, sub_add_cancel, zero_add,
    mul_ite, mul_one, mul_zero] using herr.add hmain

/-- The actual complete Green form is diagonal on every fixed finite arithmetic packet. -/
theorem tendsto_tiltedWeil_inverse_packet_inner {c : ℝ} (hc : 0 < c)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b d : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)⁻¹
          (normalizedRamanujanPacketVector S b N), normalizedRamanujanPacketVector S d N⟫)
      atTop (𝓝 (∑ m ∈ S, b m * d m / completedConductorEnergy tiltedUnitSpline c m)) := by
  have h := tendsto_finsetSum S fun m hm => tendsto_finsetSum S fun l hl =>
    ((tendsto_tiltedWeil_inverse_ramanujan_inner hc (hS m hm) (hS l hl)).const_mul
      (d l)).const_mul (b m)
  have hdiag : (∑ m ∈ S, ∑ l ∈ S, b m * (d l *
      if m = l then (completedConductorEnergy tiltedUnitSpline c m)⁻¹ else 0)) =
      ∑ m ∈ S, b m * d m / completedConductorEnergy tiltedUnitSpline c m := by
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single m]
    · rw [if_pos rfl]
      ring
    · intro l _ hl
      rw [if_neg (Ne.symm hl), mul_zero, mul_zero]
    · exact fun h => False.elim (h hm)
  rw [hdiag] at h
  refine h.congr fun N => ?_
  simp only [normalizedRamanujanPacketVector, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro m _
  ring

#print axioms norm_inverse_quasimode_residual_le
#print axioms tendsto_tiltedWeil_inverse_ramanujan_residual_norm
#print axioms tendsto_tiltedWeil_inverse_ramanujan_inner
#print axioms tendsto_tiltedWeil_inverse_packet_inner

end GaloisForLFunctions.CompletedArithmeticForms
