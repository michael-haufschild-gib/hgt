import GaloisForLFunctions.RHTower.SelbergModularCellUnfolding
import GaloisForLFunctions.RHTower.SelbergQuotientCurvature

/-!
# Actual standard-cell curvature and a uniform quotient budget

Literal chart and modular unfolding identify original compact regulator
pairings with standard-cell full orbit fields, with the exact factor two.
The source full-domain budget gives positive integrable cell curvature and
a regulator-uniform bound. Passing the original compact-test limit yields
the same bound for signed orbit tests of absolute value at most one.
Total limiting mass equality and the spectral quarter comparison are not
asserted here.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
open SelbergCompactPeriodization SelbergModularCellUnfolding SelbergMaassMean
  SelbergMaassCurvatureCovariance SelbergMaassCurvatureTransport SelbergMaassWeakCurvature
  SelbergUpperHalfPlaneCompactTests SelbergQuotientCurvature
  SelbergMaassFullCurvatureBudget SelbergMaassTraceStokes SelbergMaassRegularizedArea
  SelbergMaassRegulatorMass
noncomputable section

/-- The original planar full domain is exactly the closed hyperbolic modular cell. -/
theorem fullDomain_iff_fd (z : ℍ) : (z.re, z.im) ∈ fullDomain ↔ z ∈ fd := by
  change (z.re ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ arcHeight z.re ≤ z.im) ↔
    (1 ≤ Complex.normSq (z : ℂ) ∧ |z.re| ≤ 1 / 2)
  rw [Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor
  · rintro ⟨hx, hy⟩
    have hs := arcHeight_sq hx
    have hp := arcHeight_pos hx
    exact ⟨by nlinarith [z.im_pos], abs_le.mpr hx⟩
  · rintro ⟨hn, hx⟩
    have hi := abs_le.mp hx
    have hs := arcHeight_sq hi
    have hp := arcHeight_pos hi
    exact ⟨hi, by nlinarith [z.im_pos]⟩

/-- Exact cell change of coordinates, including the entire closed boundary and the hyperbolic density. -/
theorem integral_height_sq_cell (F : ℝ × ℝ → ℝ) :
    (∫ z : ℍ in fd, z.im ^ (2 : ℕ) * F (z.re, z.im)) = ∫ p in fullDomain, F p := by
  let G : ℂ → ℝ := fun z => fullDomain.indicator F (z.re, z.im)
  have he : (∫ z : ℍ in fd, z.im ^ (2 : ℕ) * F (z.re, z.im)) = ∫ z : ℍ, z.im ^ (2 : ℕ) * G z := by
    rw [← integral_indicator isClosed_fd.measurableSet]
    apply integral_congr_ae
    filter_upwards with z
    simp only [G, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    by_cases hz : z ∈ fd
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((fullDomain_iff_fd z).mpr hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem
        (fun hp => hz ((fullDomain_iff_fd z).mp hp)), mul_zero]
  rw [he, integral_height_sq_chart]
  calc
    (∫ z in {z : ℂ | 0 < z.im}, G z) = ∫ z : ℂ, G z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      change fullDomain.indicator F (z.re, z.im) = 0
      exact Set.indicator_of_notMem
        (fun (hp : (z.re, z.im) ∈ fullDomain) => hz (fullDomain_height_pos hp)) F
    _ = ∫ p : ℝ × ℝ, fullDomain.indicator F p :=
      Complex.volume_preserving_equiv_real_prod.integral_comp
        Complex.measurableEquivRealProd.measurableEmbedding (fullDomain.indicator F)
    _ = _ := integral_indicator fullDomain_measurable

section Source
variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Actual fixed-regulator hyperbolic curvature is continuous throughout the half-plane. -/
theorem hyperbolicCurvature_continuous (e : Ioi (0 : ℝ)) :
    Continuous (hyperbolicCurvature N f e) := by
  apply (UpperHalfPlane.continuous_im.pow 2).mul
  rw [continuous_iff_continuousAt]
  intro z
  exact ((curvatureWeight_continuousOn N f e).continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp UpperHalfPlane.continuous_coe.continuousAt

/-- The original retained hyperbolic curvature is nonnegative at every point. -/
theorem hyperbolicCurvature_nonneg (e : Ioi (0 : ℝ)) (z : ℍ) :
    0 ≤ hyperbolicCurvature N f e z :=
  mul_nonneg (sq_nonneg _) (curvatureWeight_nonneg N f e z)

/-- Original planar regulator pairings equal half the standard-cell full-orbit curvature pairing. -/
theorem cell_pairing_eq (e : Ioi (0 : ℝ)) (g : C_c(ℍ, ℝ)) :
    (∫ z : ℍ in fd, periodize g z * hyperbolicCurvature N f e z) =
      2 * testedCurvature N f e (zeroExtend g) := by
  rw [integral_periodize_mul g _ (hyperbolicCurvature_continuous N f e)
    (hyperbolicCurvature_invariant N f e), testedCurvature_eq_hyperbolic]

/-- The actual standard-cell compact-orbit pairings converge to twice the constructed quotient functional. -/
theorem cell_pairing_limit (g : C_c(ℍ, ℝ)) :
    Tendsto (fun e : Ioi (0 : ℝ) =>
      ∫ z : ℍ in fd, periodize g z * hyperbolicCurvature N f e z) regulatorAtZero
      (𝓝 (2 * positiveFunctional N f (orbitTest g))) := by
  simpa only [cell_pairing_eq] using
    (testedCurvature_limit_positiveFunctional N f g).const_mul 2

/-- The standard-cell curvature integral equals the original full planar curvature integral. -/
theorem cell_curvature_eq_planar (e : Ioi (0 : ℝ)) :
    (∫ z : ℍ in fd, hyperbolicCurvature N f e z) =
      ∫ p in fullDomain, weightedRemainder N f e p := by
  have he (z : ℍ) : hyperbolicCurvature N f e z =
      z.im ^ (2 : ℕ) * weightedRemainder N f e (z.re, z.im) := by
    have hz : point z.re z.im = (z : ℂ) := by apply Complex.ext <;> simp [SelbergMaassMean.point]
    simp only [hyperbolicCurvature, curvatureWeight, weightedRemainder, hz]
  simp only [he, integral_height_sq_cell]
end Source

section Exceptional
variable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- Original cusp control gives the exact standard-cell curvature budget for every positive regulator. -/
theorem cell_curvature_budget (e : Ioi (0 : ℝ)) :
    (∫ z : ℍ in fd, hyperbolicCurvature N f e z) =
      (lam : ℝ) * ∫ p in fullDomain, weightedMassDensity N f e p := by
  rw [cell_curvature_eq_planar, full_curvature_budget N lam f e]

/-- Source nonvanishing gives strictly positive standard-cell curvature. -/
theorem cell_curvature_pos (e : Ioi (0 : ℝ)) :
    0 < ∫ z : ℍ in fd, hyperbolicCurvature N f e z := by
  rw [cell_curvature_eq_planar]
  exact full_weightedRemainder_pos N lam f e

/-- The exact positive source integral discharges full-cell integrability. -/
theorem cell_curvature_integrable (e : Ioi (0 : ℝ)) :
    IntegrableOn (hyperbolicCurvature N f e) fd :=
  Integrable.of_integral_ne_zero (ne_of_gt (cell_curvature_pos N lam f e))

/-- Standard-cell curvature is bounded uniformly in the original positive regulator. -/
theorem cell_curvature_le_amplitude (e : Ioi (0 : ℝ)) :
    (∫ z : ℍ in fd, hyperbolicCurvature N f e z) ≤
      (lam : ℝ) * ∫ p in fullDomain, amplitudeMassDensity N lam f p := by
  rw [cell_curvature_eq_planar]
  linarith [full_curvature_error_nonneg N lam f e]

/-- Every nonnegative full orbit field bounded by one obeys the actual finite quotient-curvature budget. -/
theorem positiveFunctional_le_amplitude (g : C_c(ℍ, ℝ))
    (h0 : ∀ z, 0 ≤ periodize g z) (h1 : ∀ z, periodize g z ≤ 1) :
    2 * positiveFunctional N f (orbitTest g) ≤
      (lam : ℝ) * ∫ p in fullDomain, amplitudeMassDensity N lam f p := by
  apply le_of_tendsto (cell_pairing_limit N f g)
  filter_upwards with e
  apply le_trans _ (cell_curvature_le_amplitude N lam f e)
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun z => mul_nonneg (h0 z) (hyperbolicCurvature_nonneg N f e z))
    (cell_curvature_integrable N lam f e)
  exact Eventually.of_forall fun z => by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (h1 z) (hyperbolicCurvature_nonneg N f e z)

/-- Signed full orbit tests bounded in absolute value obey the same finite source budget. -/
theorem abs_positiveFunctional_le_amplitude (g : C_c(ℍ, ℝ))
    (h1 : ∀ z, |periodize g z| ≤ 1) :
    2 * |positiveFunctional N f (orbitTest g)| ≤
      (lam : ℝ) * ∫ p in fullDomain, amplitudeMassDensity N lam f p := by
  have hlim : Tendsto (fun e : Ioi (0 : ℝ) =>
      |∫ z : ℍ in fd, periodize g z * hyperbolicCurvature N f e z|) regulatorAtZero
      (𝓝 (2 * |positiveFunctional N f (orbitTest g)|)) := by
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      (cell_pairing_limit N f g).abs
  apply le_of_tendsto hlim
  filter_upwards with e
  apply le_trans _ (cell_curvature_le_amplitude N lam f e)
  calc
    |∫ z : ℍ in fd, periodize g z * hyperbolicCurvature N f e z| ≤
        ∫ z : ℍ in fd, |periodize g z * hyperbolicCurvature N f e z| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z : ℍ => periodize g z * hyperbolicCurvature N f e z) (μ := volume.restrict fd)
    _ ≤ _ := integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (cell_curvature_integrable N lam f e) (Eventually.of_forall fun z => by
        change |periodize g z * hyperbolicCurvature N f e z| ≤ hyperbolicCurvature N f e z
        rw [abs_mul, abs_of_nonneg (hyperbolicCurvature_nonneg N f e z)]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (h1 z) (hyperbolicCurvature_nonneg N f e z))

/-- Every prescribed compact region has an actual normalized nonnegative weight with the uniform source budget. -/
theorem exists_budgeted_weight {K : Set ℍ} (hK : IsCompact K) :
    ∃ w : C_c(ℍ, ℝ), (∀ z, 0 ≤ w z) ∧ (∀ z, periodize w z ≤ 1) ∧
      (∀ z ∈ K, periodize w z = 1) ∧
      2 * positiveFunctional N f (orbitTest w) ≤
        (lam : ℝ) * ∫ p in fullDomain, amplitudeMassDensity N lam f p := by
  obtain ⟨w, hw, h1, hK⟩ := exists_normalized_weight hK
  exact ⟨w, hw, h1, hK, positiveFunctional_le_amplitude N lam f w
    (fun z => periodize_nonneg hw z) h1⟩

end Exceptional
end
end GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
