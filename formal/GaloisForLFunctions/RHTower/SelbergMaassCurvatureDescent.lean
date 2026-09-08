import GaloisForLFunctions.RHTower.SelbergCompactPeriodization

/-!
# Positive descent of actual curvature through compact modular orbit sums

The actual invariant curvature measure pairs full periodizations symmetrically.
Proper discontinuity discharges every overlap sum/integral interchange. Actual
normalized compact weights then prove independence of compact representatives,
positivity, and order comparison on periodized tests, retaining all seam charge.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassCurvatureDescent
open SelbergCompactPeriodization SelbergMaassCurvatureMeasure SelbergMaassCurvatureTransport
noncomputable section
variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Each literal compact modular overlap is integrable for the actual curvature measure. -/
theorem overlap_integrable (g h : C_c(ℍ, ℝ)) (A : SL2Z) :
    Integrable (fun z : ℍ => g z * h (A • z)) (curvatureMeasure N f) :=
  compact_test_integrable N f (g * pullTest A h)

/-- Finitely many mutual overlaps give summable actual absolute overlap integrals. -/
theorem overlap_integral_norm_summable (g h : C_c(ℍ, ℝ)) :
    Summable (fun A : SL2Z => ∫ z : ℍ, ‖g z * h (A • z)‖ ∂curvatureMeasure N f) := by
  obtain ⟨s, hs⟩ := overlap_finite g h
  apply summable_of_ne_finset_zero (s := s)
  intro A hA
  simp only [hs A hA, norm_zero, integral_zero]

/-- Periodized pairings equal their actual overlap integral series, with interchange justified. -/
theorem integral_periodize_eq_tsum (g h : C_c(ℍ, ℝ)) :
    (∫ z : ℍ, g z * periodize h z ∂curvatureMeasure N f) =
      ∑' A : SL2Z, ∫ z : ℍ, g z * h (A • z) ∂curvatureMeasure N f := by
  letI : Countable SL2Z := by
    letI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
    exact Subtype.countable
  rw [integral_tsum_of_summable_integral_norm (overlap_integrable N f g h)
    (overlap_integral_norm_summable N f g h)]
  apply integral_congr_ae
  filter_upwards with z
  exact tsum_mul_left.symm

/-- Full modular periodization is symmetric in actual compact curvature pairings. -/
theorem integral_periodize_swap (g h : C_c(ℍ, ℝ)) :
    (∫ z : ℍ, g z * periodize h z ∂curvatureMeasure N f) =
      ∫ z : ℍ, h z * periodize g z ∂curvatureMeasure N f := by
  rw [integral_periodize_eq_tsum, integral_periodize_eq_tsum]
  have hterm (A : SL2Z) :
      (∫ z : ℍ, g z * h (A • z) ∂curvatureMeasure N f) =
        ∫ z : ℍ, h z * g (A⁻¹ • z) ∂curvatureMeasure N f := by
    have he := integral_modular N f A (fun z : ℍ => h z * g (A⁻¹ • z))
    simpa only [inv_smul_smul, mul_comm] using he
  simp_rw [hterm]
  exact (Equiv.inv SL2Z).tsum_eq (fun A : SL2Z => ∫ z : ℍ, h z * g (A • z) ∂curvatureMeasure N f)

/-- A weight whose orbit sum is one on a test support reproduces that test's actual curvature. -/
theorem integral_eq_weighted_periodize (g w : C_c(ℍ, ℝ))
    (hw : ∀ z ∈ tsupport g, periodize w z = 1) :
    (∫ z : ℍ, g z ∂curvatureMeasure N f) =
      ∫ z : ℍ, w z * periodize g z ∂curvatureMeasure N f := by
  rw [← integral_periodize_swap]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ tsupport g
  · rw [hw z hz, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

/-- Actual compact curvature depends only on the full modular periodization of the test. -/
theorem integral_eq_of_periodize_eq (g h : C_c(ℍ, ℝ)) (hp : periodize g = periodize h) :
    (∫ z : ℍ, g z ∂curvatureMeasure N f) = ∫ z : ℍ, h z ∂curvatureMeasure N f := by
  obtain ⟨w, _, _, hw⟩ := exists_normalized_weight (g.hasCompactSupport.union h.hasCompactSupport)
  rw [integral_eq_weighted_periodize N f g w (fun z hz => hw z (Or.inl hz)),
    integral_eq_weighted_periodize N f h w (fun z hz => hw z (Or.inr hz)), hp]

/-- Pointwise nonnegativity after periodization gives nonnegative actual curvature, even for signed tests. -/
theorem integral_nonneg_of_periodize_nonneg (g : C_c(ℍ, ℝ))
    (hp : ∀ z, 0 ≤ periodize g z) : 0 ≤ ∫ z : ℍ, g z ∂curvatureMeasure N f := by
  obtain ⟨w, hn, _, hw⟩ := exists_normalized_weight g.hasCompactSupport
  rw [integral_eq_weighted_periodize N f g w hw]
  exact integral_nonneg (fun z => mul_nonneg (hn z) (hp z))

/-- Pointwise comparison of full orbit sums controls the actual compact curvature integrals. -/
theorem integral_le_of_periodize_le (g h : C_c(ℍ, ℝ)) (hp : ∀ z, periodize g z ≤ periodize h z) :
    (∫ z : ℍ, g z ∂curvatureMeasure N f) ≤ ∫ z : ℍ, h z ∂curvatureMeasure N f := by
  obtain ⟨w, hn, _, hw⟩ := exists_normalized_weight (g.hasCompactSupport.union h.hasCompactSupport)
  rw [integral_eq_weighted_periodize N f g w (fun z hz => hw z (Or.inl hz)),
    integral_eq_weighted_periodize N f h w (fun z hz => hw z (Or.inr hz))]
  exact integral_mono
    (compact_test_integrable N f (mulContinuous w (periodize g) (periodize_continuous g)))
    (compact_test_integrable N f (mulContinuous w (periodize h) (periodize_continuous h)))
    (fun z => mul_le_mul_of_nonneg_left (hp z) (hn z))

end
end GaloisForLFunctions.RHTower.SelbergMaassCurvatureDescent
