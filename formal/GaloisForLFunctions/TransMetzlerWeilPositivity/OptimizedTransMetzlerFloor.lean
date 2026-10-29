import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerPositivity

/-!
# The optimal floor from the certified Trans-Metzler estimates

The reference operator has mass floor `1/25` and defect coercivity
`E ≥ -2100000 M + D/1024000`. A perturbation of size `e(D+M)` therefore leaves the
optimal floor `1/25 - K e`, where `K = 1 + 1024000(2100000 + 1/25)`. The optimal
convex weight is `1024000 e`; a scalar example attains the resulting bound.

For the complete Weil matrix at overlap `1+δ`, the perturbation coefficient tends to
`2000δ`. Every floor strictly below `1/25 - 2000Kδ` consequently holds eventually.
The exact positive range certified by these three estimates is
`δ < 1/107520002048050000`. This boundary concerns the estimates, not the actual sign.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix RHTower
open scoped Real RealInnerProductSpace

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticLorentzianGeometry
  ArithmeticElectrostatics HTGeometry

/-- Conversion factor from defect error to the optimal loss of mass floor. -/
def certifiedDefectLoss : ℝ := 1 + 1024000 * (2100000 + 1 / 25)

/-- Supremum of overlap increments certified by the reference and coercivity bounds. -/
def certifiedOverlapIncrement : ℝ := 1 / (50000 * certifiedDefectLoss)

/-- Optimal asymptotic mass floor obtained from the certified perturbation inequalities. -/
def certifiedOverlapFloor (δ : ℝ) : ℝ := 1 / 25 - 2000 * δ * certifiedDefectLoss

theorem certifiedDefectLoss_pos : 0 < certifiedDefectLoss := by
  norm_num [certifiedDefectLoss]

theorem certifiedOverlapIncrement_eq :
    certifiedOverlapIncrement = 1 / 107520002048050000 := by
  norm_num [certifiedOverlapIncrement, certifiedDefectLoss]

theorem certifiedOverlapIncrement_pos : 0 < certifiedOverlapIncrement := by
  rw [certifiedOverlapIncrement_eq]
  positivity

theorem certifiedOverlapFloor_pos_iff (δ : ℝ) :
    0 < certifiedOverlapFloor δ ↔ δ < certifiedOverlapIncrement := by
  norm_num [certifiedOverlapFloor, certifiedOverlapIncrement, certifiedDefectLoss]
  constructor <;> intro h <;> linarith only [h]

/-- Convex interpolation uses exactly the defect reserve spent by the perturbation. -/
theorem floor_of_reference_coercivity {M D E F e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 1024000)
    (hfloor : M / 25 ≤ E) (hcoerc : -2100000 * M + D / 1024000 ≤ E)
    (hpert : -e * (D + M) ≤ F - E) :
    (1 / 25 - certifiedDefectLoss * e) * M ≤ F := by
  have hweight : 0 ≤ 1 - 1024000 * e := by linarith only [he1]
  have h1 := mul_le_mul_of_nonneg_left hfloor hweight
  have h2 := mul_le_mul_of_nonneg_left hcoerc
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024000) he0)
  unfold certifiedDefectLoss
  nlinarith only [h1, h2, hpert]

/-- The scalar intersection of the two reference bounds attains the certified floor. -/
theorem reference_coercivity_floor_attained (e : ℝ) (he : 0 ≤ e) :
    ∃ D E F : ℝ, 0 ≤ D ∧ (1 : ℝ) / 25 ≤ E ∧
      -2100000 + D / 1024000 ≤ E ∧ |F - E| ≤ e * (D + 1) ∧
      F = 1 / 25 - certifiedDefectLoss * e := by
  refine ⟨certifiedDefectLoss - 1, 1 / 25, 1 / 25 - certifiedDefectLoss * e,
    ?_, le_rfl, ?_, ?_, rfl⟩
  · norm_num [certifiedDefectLoss]
  · norm_num [certifiedDefectLoss]
  · rw [sub_sub_cancel_left, abs_neg,
      abs_of_nonneg (mul_nonneg certifiedDefectLoss_pos.le he)]
    exact le_of_eq (by ring)

/-- Every strict relaxation of the optimal floor holds for the actual complete matrices. -/
theorem eventually_completeWeilMatrix_certified_floor (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ certifiedOverlapIncrement) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (certifiedOverlapFloor δ - ε) * ‖x‖ ^ 2 ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix transMetzlerProfile (1 + δ) N) x, x⟫ := by
  have hδsmall : δ ≤ 1 / 512000 := hδ.trans (by
    norm_num [certifiedOverlapIncrement, certifiedDefectLoss])
  have hebase : 2000 * δ ≤ 1 / 2048000 := calc
    2000 * δ ≤ 2000 * certifiedOverlapIncrement := by gcongr
    _ ≤ 1 / 2048000 := by norm_num [certifiedOverlapIncrement, certifiedDefectLoss]
  let τ : ℝ := min (ε / certifiedDefectLoss) (1 / 2048000)
  have hτ0 : 0 < τ := lt_min (div_pos hε certifiedDefectLoss_pos) (by norm_num)
  have hτsmall : τ ≤ 1 / 2048000 := min_le_right _ _
  have hτloss : τ * certifiedDefectLoss ≤ ε :=
    (le_div_iff₀ certifiedDefectLoss_pos).mp (min_le_left _ _)
  let e : ℝ := 2000 * δ + τ
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have he1 : e ≤ 1 / 1024000 := by dsimp [e]; linarith only [hebase, hτsmall]
  have hw : ∀ᶠ N : ℕ in atTop,
      0 < (1 + δ) / (N : ℝ) ∧ (1 + δ) / (N : ℝ) ≤ 2 / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact ⟨div_pos (by linarith only [hδ0]) hN0,
      div_le_div_of_nonneg_right (by linarith only [hδsmall]) hN0.le⟩
  obtain ⟨C, _, hpert⟩ := exists_perturbation_bound_transMetzler
  have htail : Tendsto (fun N : ℕ => C / Real.log ((N : ℝ) / 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 3)))
  filter_upwards [eventually_transMetzlerMainMatrix_eigenvalues_ge
    (fun N => (1 + δ) / N) (1 + δ) (by linarith only [hδ0])
      (by linarith only [hδsmall]) hw,
    eventually_transMetzlerMainMatrix_coercive (fun N => (1 + δ) / N) (1 + δ)
      (by linarith only [hδ0]) (by linarith only [hδsmall]) hw,
    htail.eventually (gt_mem_nhds hτ0), eventually_ge_atTop 27]
    with N heig hcoerc htailN hN x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfloor : ‖x‖ ^ 2 / 25 ≤
      ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix ((1 + δ) / N) (1 + δ) N) x, x⟫ := by
    rw [div_eq_mul_inv, mul_comm, hermitianEnergy_eq_sum
      (transMetzlerMainMatrix_isHermitian ((1 + δ) / N) (1 + δ) N) x,
      ← (transMetzlerMainMatrix_isHermitian ((1 + δ) / N) (1 + δ) N).eigenvectorBasis.sum_sq_inner_left x,
      mul_sum]
    simpa only [one_div] using
      (sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (heig i) (sq_nonneg _))
  have hp := (abs_le.mp (hpert hN hδ0 (by linarith only [hδsmall])
    (by linarith only [hδ0]) (w := (1 + δ) / N) (cStar := 1 + δ)
    (by
      rw [show (1 : ℝ) / (2 * N) = (1 / 2) / N by ring]
      exact div_le_div_of_nonneg_right (by linarith only [hδ0]) hN0.le)
    le_rfl (by rw [div_mul_cancel₀ _ hN0.ne', sub_self, abs_zero]; positivity) x)).1
  have herror : -e * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) ≤
      -((2000 * δ + C / Real.log ((N : ℝ) / 3)) *
        (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2)) := by
    rw [neg_mul]
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_right (by dsimp [e]; linarith only [htailN])
      (add_nonneg (poleDefect_nonneg N _) (sq_nonneg _))
  have hcoerc' : -2100000 * ‖x‖ ^ 2 + poleDefect N (primeHorizonExtension x) / 1024000 ≤
      ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix ((1 + δ) / N) (1 + δ) N) x, x⟫ := by
    calc -2100000 * ‖x‖ ^ 2 + poleDefect N (primeHorizonExtension x) / 1024000 =
        -2100000 * ‖x‖ ^ 2 + (1 / 1024000) * poleDefect N (primeHorizonExtension x) := by ring
      _ ≤ _ := hcoerc x
  have hbound := floor_of_reference_coercivity he0 he1 hfloor hcoerc' (herror.trans hp)
  have hcoef : certifiedOverlapFloor δ - ε ≤ 1 / 25 - certifiedDefectLoss * e := by
    dsimp [certifiedOverlapFloor, e]
    nlinarith only [hτloss]
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans hbound

/-- The complete Weil matrix is positive throughout the full open certified overlap range. -/
theorem eventually_completeWeilMatrix_posDef_certified (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ < certifiedOverlapIncrement) :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix transMetzlerProfile (1 + δ) N).PosDef := by
  have hf : 0 < certifiedOverlapFloor δ := (certifiedOverlapFloor_pos_iff δ).mpr hδ
  filter_upwards [eventually_completeWeilMatrix_certified_floor δ hδ0 hδ.le
    (certifiedOverlapFloor δ / 2) (half_pos hf)] with N hfloor
  have hH := completeWeilMatrix_isHermitian transMetzlerProfile (1 + δ) N
  rw [hH.posDef_iff_eigenvalues_pos]
  intro i
  have h := hfloor (hH.eigenvectorBasis i)
  rw [hH.eigenvectorBasis.orthonormal.1 i, one_pow, mul_one,
    hermitianEnergy_eq_sum hH] at h
  have horth (j : PrimeHorizonIndex N) :
      ⟪hH.eigenvectorBasis i, hH.eigenvectorBasis j⟫ = if i = j then 1 else 0 :=
    (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) i j
  simp only [horth, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true] at h
  linarith only [h, hf]

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.reference_coercivity_floor_attained
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeilMatrix_certified_floor
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeilMatrix_posDef_certified
