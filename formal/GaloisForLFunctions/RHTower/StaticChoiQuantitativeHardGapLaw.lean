import GaloisForLFunctions.RHTower.StaticChoiContinuousHardGapLaw
import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing

/-!
# Quantitative same-Hamiltonian Choi hard intervals

The projective Choi orbit has an explicit speed controlled by the sum of its anchored spectral
gaps.  Combining this speed with completed circuit occupation gives a quantitative inverse-density
law for continuous hard-block length.  For trace radii `epsn < epsw`, the visit thickness is

`(epsw - epsn) / (1 + sum_i |E_0 - E_i|)`.

No minimum spectral gap enters.
-/

open scoped BigOperators
open Filter MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A positive upper speed scale for the projective Choi vector. -/
def projectiveChoiSpeed {d : ℕ} (energy : Fin (d + 1) → ℝ) : ℝ :=
  (∑ i : Fin d, |zeroProjectiveFrequency energy i|) + 1

theorem projectiveChoiSpeed_pos {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    0 < projectiveChoiSpeed energy := by
  unfold projectiveChoiSpeed
  positivity

theorem fourier_projectiveChoiPhase_eq_exp
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (t : ℝ) (i : Fin (d + 1)) :
    fourier 1 (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t) i) =
      Complex.exp (((t * Fin.cases 0 (zeroProjectiveFrequency energy) i : ℝ) : ℂ) *
        Complex.I) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [zeroAnchoredPhase]
  · change fourier 1
      (((t * zeroProjectiveFrequency energy j / (2 * Real.pi) : ℝ)) : UnitAddCircle) =
      Complex.exp (((t * zeroProjectiveFrequency energy j : ℝ) : ℂ) * Complex.I)
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]

/-- Explicit vector-speed bound for the normalized projective Choi orbit. -/
theorem norm_fullUniformPhaseChoiVector_time_sub_le
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (t u : ℝ) :
    ‖fullUniformPhaseChoiVector (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)) -
        fullUniformPhaseChoiVector (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy u))‖ ≤
      projectiveChoiSpeed energy * |t - u| := by
  let S := projectiveChoiSpeed energy
  have hS : 0 < S := projectiveChoiSpeed_pos energy
  have hphase (i : Fin (d + 1)) :
      ‖fourier 1 (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t) i) -
        fourier 1 (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy u) i)‖ ≤
          S * |t - u| := by
    rw [fourier_projectiveChoiPhase_eq_exp,
      fourier_projectiveChoiPhase_eq_exp]
    refine (norm_exp_ofReal_mul_I_sub_le
      (t * Fin.cases 0 (zeroProjectiveFrequency energy) i)
      (u * Fin.cases 0 (zeroProjectiveFrequency energy) i)).trans ?_
    have hgap : |Fin.cases 0 (zeroProjectiveFrequency energy) i| ≤ S := by
      refine Fin.cases ?_ (fun j => ?_) i
      · have hsum0 : 0 ≤ ∑ k : Fin d, |zeroProjectiveFrequency energy k| :=
          Finset.sum_nonneg fun k _ => abs_nonneg _
        simp only [Fin.cases_zero, abs_zero]
        dsimp [S, projectiveChoiSpeed]
        linarith
      · have hsum : |zeroProjectiveFrequency energy j| ≤
            ∑ k : Fin d, |zeroProjectiveFrequency energy k| :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun k : Fin d => |zeroProjectiveFrequency energy k|)
            (fun k _ => abs_nonneg _) (Finset.mem_univ j)
        dsimp [S, projectiveChoiSpeed]
        linarith
    rw [show t * Fin.cases 0 (zeroProjectiveFrequency energy) i -
        u * Fin.cases 0 (zeroProjectiveFrequency energy) i =
        (t - u) * Fin.cases 0 (zeroProjectiveFrequency energy) i by ring,
      abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hgap (abs_nonneg _)
  have hR : 0 ≤ S * |t - u| := mul_nonneg hS.le (abs_nonneg _)
  rw [← sq_le_sq₀ (norm_nonneg _) hR]
  rw [EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_prod_type]
  have hrow (i : Fin (d + 1)) :
      (∑ j : Fin (d + 1),
        ‖(fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)) -
            fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy u))).ofLp (i, j)‖ ^ 2) ≤
        (S * |t - u|) ^ 2 / (d + 1 : ℝ) := by
    rw [Finset.sum_eq_single i]
    · simp only [PiLp.sub_apply, fullUniformPhaseChoiVector_apply, if_pos]
      rw [← mul_sub, norm_mul, mul_pow]
      have hdR : (0 : ℝ) < (d + 1 : ℕ) := by positivity
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt hdR.le, div_eq_inv_mul]
      have hp := hphase i
      have hsq := (sq_le_sq₀ (norm_nonneg _) hR).2 hp
      have hDinv : 0 ≤ ((d + 1 : ℕ) : ℝ)⁻¹ := by positivity
      simpa only [Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonneg_left hsq hDinv
    · intro j _ hji
      simp [fullUniformPhaseChoiVector_apply, Ne.symm hji]
    · simp
  calc
    (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      ‖(fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)) -
            fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy u))).ofLp (i, j)‖ ^ 2)
      ≤ ∑ _i : Fin (d + 1), (S * |t - u|) ^ 2 / (d + 1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = (S * |t - u|) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast
      ring

/-- Explicit Hilbert--Schmidt speed of the projected Choi density. -/
theorem dist_projectiveChoiDensityFlow_le
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (t u : ℝ) :
    dist (projectiveChoiDensityFlow energy t) (projectiveChoiDensityFlow energy u) ≤
      Real.sqrt 2 * projectiveChoiSpeed energy * |t - u| := by
  let psi := fullUniformPhaseChoiVector (d + 1)
    (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  let phi := fullUniformPhaseChoiVector (d + 1)
    (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy u))
  have hpsi : ‖psi‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
  have hphi : ‖phi‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
  have hcontract := dist_diagonalDensityRestriction_le (d + 1)
    (pureStateDensity psi) (pureStateDensity phi)
  have hdiagPsi : diagonalDensityRestriction (d + 1) (pureStateDensity psi) =
      projectiveChoiDensityFlow energy t := by
    simpa only [psi, projectiveChoiDensityFlow] using
      diagonalDensityRestriction_pureStateDensity_fullUniformPhaseChoiVector
        (Nat.succ_pos d)
        (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  have hdiagPhi : diagonalDensityRestriction (d + 1) (pureStateDensity phi) =
      projectiveChoiDensityFlow energy u := by
    simpa only [phi, projectiveChoiDensityFlow] using
      diagonalDensityRestriction_pureStateDensity_fullUniformPhaseChoiVector
        (Nat.succ_pos d)
        (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy u))
  rw [hdiagPsi, hdiagPhi] at hcontract
  calc
    dist (projectiveChoiDensityFlow energy t) (projectiveChoiDensityFlow energy u) ≤
        dist (pureStateDensity psi) (pureStateDensity phi) := hcontract
    _ = Real.sqrt 2 * pureStateTraceDistance psi phi :=
      dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance psi phi hpsi hphi
    _ ≤ Real.sqrt 2 * ‖psi - phi‖ := by
      gcongr
      exact pureStateTraceDistance_le_norm_sub psi phi hpsi hphi
    _ ≤ Real.sqrt 2 * (projectiveChoiSpeed energy * |t - u|) := by
      gcongr
      exact norm_fullUniformPhaseChoiVector_time_sub_le energy t u
    _ = Real.sqrt 2 * projectiveChoiSpeed energy * |t - u| := by ring

/-- **Quantitative same-Hamiltonian hard-block law.**  If the complete wide-radius circuit-union
mass is below `mesh/(W+mesh)`, where `mesh` is the explicit trace-radius gap divided by the
projective Choi speed, then arbitrarily late intervals of length `W` avoid every circuit word at
the narrow trace radius. -/
theorem maximallyProjective_pureChoiCircuitTargets_explicit_late_hard_intervals
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    {epsn epsw W : ℝ} (hgap : epsn < epsw) (hepsn : 0 ≤ epsn) (hW : 0 ≤ W)
    (hpack :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) <
        ((epsw - epsn) / projectiveChoiSpeed energy) /
          (W + (epsw - epsn) / projectiveChoiSpeed energy)) :
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
      ∀ t ∈ Set.Icc u (u + W), ∀ w,
        epsn < pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (target w) := by
  let projectedTarget : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
    fun w => diagonalDensityRestriction (d + 1) (pureStateDensity (target w))
  let b : ℝ := (Fintype.card gate : ℝ) ^ (s + 1) *
      (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
        Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
          ((d + 1 : ℕ) - 1))
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hspeed : 0 < projectiveChoiSpeed energy := projectiveChoiSpeed_pos energy
  have hepsw : 0 < Real.sqrt 2 * epsw := by nlinarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let wide : Set ℝ := {t | ∃ w,
    dist (projectiveChoiDensityFlow energy t) (projectedTarget w) ≤ Real.sqrt 2 * epsw}
  have hlimA := limsup_windowProbability_projectivePhase_preimage_le_volume
    energy hmax (isClosed_zeroAnchoredPaddedCircuitTarget d s projectedTarget
      (Real.sqrt 2 * epsw))
  have hpre := projectiveChoiCircuitTarget_time_preimage energy s projectedTarget
    (Real.sqrt 2 * epsw)
  have hvolReal := measureReal_zeroAnchoredPaddedCircuitTarget_le d s projectedTarget hepsw
  have hvolFinite : (volume : Measure (Fin d → UnitAddCircle))
      (zeroAnchoredPaddedCircuitTarget d s projectedTarget (Real.sqrt 2 * epsw)) ≠ ⊤ :=
    measure_ne_top _ _
  have hlim : Filter.atTop.limsup
      (fun T => (windowProbabilityMeasure T : Measure ℝ) wide) ≤ ENNReal.ofReal b := by
    have hmeasure : (volume : Measure (Fin d → UnitAddCircle))
        (zeroAnchoredPaddedCircuitTarget d s projectedTarget (Real.sqrt 2 * epsw)) ≤
          ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_toReal hvolFinite]
      exact ENNReal.ofReal_le_ofReal hvolReal
    rw [hpre] at hlimA
    simpa only [wide] using le_trans hlimA hmeasure
  have hmeshEq :
      ((Real.sqrt 2 * epsw - Real.sqrt 2 * epsn) /
          (Real.sqrt 2 * projectiveChoiSpeed energy)) =
        (epsw - epsn) / projectiveChoiSpeed energy := by
    field_simp [ne_of_gt hsqrt, ne_of_gt hspeed]
  have htargetSet :
      {t | ∃ z ∈ Set.range projectedTarget,
        dist (projectiveChoiDensityFlow energy t) z ≤ Real.sqrt 2 * epsw} = wide := by
    ext t
    simp only [wide, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨w, rfl⟩, hz⟩
      exact ⟨w, hz⟩
    · rintro ⟨w, hw⟩
      exact ⟨projectedTarget w, ⟨w, rfl⟩, hw⟩
  have hpackDensity : b <
      ((Real.sqrt 2 * epsw - Real.sqrt 2 * epsn) /
          (Real.sqrt 2 * projectiveChoiSpeed energy)) /
        (W + (Real.sqrt 2 * epsw - Real.sqrt 2 * epsn) /
          (Real.sqrt 2 * projectiveChoiSpeed energy)) := by
    rw [hmeshEq]
    exact hpack
  intro A0 hA0
  obtain ⟨u, hu, hdisj⟩ :=
    exists_late_interval_metric_hard_of_limsup_windowProbability_le
      (projectiveChoiDensityFlow energy) (Set.range projectedTarget)
      (speed := Real.sqrt 2 * projectiveChoiSpeed energy)
      (epsn := Real.sqrt 2 * epsn) (epsw := Real.sqrt 2 * epsw)
      (W := W) (b := b)
      (mul_pos hsqrt hspeed)
      (dist_projectiveChoiDensityFlow_le energy)
      (by nlinarith) hW hb
      (by rwa [htargetSet]) hpackDensity A0 hA0
  refine ⟨u, hu, ?_⟩
  intro t ht w
  have hprojected : Real.sqrt 2 * epsn <
      dist (projectiveChoiDensityFlow energy t) (projectedTarget w) := by
    by_contra hnot
    push Not at hnot
    have hmem : t ∈ Set.Icc u (u + W) ∩
        {t | ∃ z ∈ Set.range projectedTarget,
          dist (projectiveChoiDensityFlow energy t) z ≤ Real.sqrt 2 * epsn} :=
      ⟨ht, projectedTarget w, ⟨w, rfl⟩, hnot⟩
    rw [hdisj] at hmem
    exact hmem
  let psi := fullUniformPhaseChoiVector (d + 1)
    (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  have hpsi : ‖psi‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
  have hcontract := dist_uniformPhaseDensity_projectedTarget_le_full
    (d + 1) (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
    (pureStateDensity (target w))
  have hfull : dist (projectiveChoiDensityFlow energy t) (projectedTarget w) ≤
      Real.sqrt 2 * pureStateTraceDistance psi (target w) := by
    dsimp only [projectiveChoiDensityFlow, projectedTarget]
    refine le_trans hcontract ?_
    rw [← pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d)]
    simpa only [psi] using le_of_eq
      (dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance
        psi (target w) hpsi (htarget w))
  nlinarith

end RHTower
