import GaloisForLFunctions.RHTower.SelbergMaassUniformCusp
import GaloisForLFunctions.RHTower.SelbergMaassCellCurvature

/-!
# Uniform tails of actual regularized Maass curvature

Subtracting the original full and truncated Stokes balances retains the
literal top current. The fixed integrable amplitude dominates every
regularized mass tail, and the source current decays uniformly over all
positive regulators. Hence the original retained-curvature tails do too.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergMaassUniformCurvatureTail
open SelbergMaassMean SelbergMaassRegularizedArea SelbergModularDomainSlices
  SelbergMaassFullCurvatureBudget SelbergMaassRegulatorMass SelbergMaassUniformCusp
noncomputable section

/-- The actual planar curvature region beyond a closed modular height truncation. -/
def tailDomain (Y : ℝ) : Set (ℝ × ℝ) := fullDomain \ domain Y

/-- Every actual tail region is measurable. -/
theorem tailDomain_measurable (Y : ℝ) : MeasurableSet (tailDomain Y) :=
  fullDomain_measurable.diff (isCompact_domain Y).measurableSet

/-- Every tail region remains inside the original full modular domain. -/
theorem tailDomain_subset (Y : ℝ) : tailDomain Y ⊆ fullDomain := sdiff_subset

variable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- The actual retained curvature is nonnegative on every tail. -/
theorem curvature_tail_nonneg (e : Ioi (0 : ℝ)) (Y : ℝ) :
    0 ≤ ∫ p in tailDomain Y, weightedRemainder N f e p :=
  integral_nonneg (weightedRemainder_nonneg N f e)

/-- Subtracting actual core and full balances gives an exact tail identity, including the top current. -/
theorem curvature_tail_identity (e : Ioi (0 : ℝ)) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in tailDomain Y, weightedRemainder N f e p) =
      (lam : ℝ) * (∫ p in tailDomain Y, weightedMassDensity N f e p) -
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x Y := by
  rw [tailDomain,
    setIntegral_sdiff (isCompact_domain Y).measurableSet (full_weightedRemainder_integrable N lam f e)
      (domain_subset_full Y),
    setIntegral_sdiff (isCompact_domain Y).measurableSet (full_weightedMass_integrable N lam f e)
      (domain_subset_full Y),
    full_curvature_budget N lam f e, weighted_remainder_balance N f e hY]
  ring

/-- Original integrable amplitude has vanishing mass outside the actual modular truncations. -/
theorem amplitude_tail_limit :
    Tendsto (fun Y : ℝ => ∫ p in tailDomain Y, amplitudeMassDensity N lam f p) atTop (𝓝 0) := by
  have he (Y : ℝ) : (∫ p in tailDomain Y, amplitudeMassDensity N lam f p) =
      (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
        ∫ p in domain Y, amplitudeMassDensity N lam f p :=
    setIntegral_sdiff (isCompact_domain Y).measurableSet (full_amplitudeMass_integrable N lam f)
      (domain_subset_full Y)
  simpa only [he, sub_self] using
    (tendsto_const_nhds (x := ∫ p in fullDomain, amplitudeMassDensity N lam f p)).sub
      (full_integral_tendsto (full_amplitudeMass_integrable N lam f))

/-- One original amplitude tail and the literal top current dominate every regularized curvature tail. -/
theorem curvature_tail_le_amplitude_current (e : Ioi (0 : ℝ)) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in tailDomain Y, weightedRemainder N f e p) ≤
      (lam : ℝ) * (∫ p in tailDomain Y, amplitudeMassDensity N lam f p) +
        |∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x Y| := by
  rw [curvature_tail_identity N lam f e hY]
  have hm := integral_mono ((full_weightedMass_integrable N lam f e).mono_set (tailDomain_subset Y))
    ((full_amplitudeMass_integrable N lam f).mono_set (tailDomain_subset Y))
    (weightedMassDensity_le_amplitude N lam f e)
  have hl := mul_le_mul_of_nonneg_left hm lam.2.1.le
  linarith [neg_le_abs (∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x Y)]

/-- Original curvature tails vanish uniformly over all positive regulators; no limiting mass can hide there. -/
theorem curvature_tail_uniform_decay {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ e : Ioi (0 : ℝ), ∀ y : ℝ, Y ≤ y →
      (∫ p in tailDomain y, weightedRemainder N f e p) < eps := by
  obtain ⟨A, hA, hb⟩ := top_current_uniform_decay N f (half_pos heps)
  have hlim := (amplitude_tail_limit N lam f).const_mul (lam : ℝ)
  simp only [mul_zero] at hlim
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hlim.eventually_lt_const (half_pos heps))
  refine ⟨max 1 (max A B), le_max_left _ _, fun e y hy => ?_⟩
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hyA : A ≤ y := (le_max_left A B).trans ((le_max_right _ _).trans hy)
  have hyB : B ≤ y := (le_max_right A B).trans ((le_max_right _ _).trans hy)
  have hm := hB y hyB
  have hc := hb e y hyA
  have h := curvature_tail_le_amplitude_current N lam f e hy1
  linarith

end
end GaloisForLFunctions.RHTower.SelbergMaassUniformCurvatureTail
