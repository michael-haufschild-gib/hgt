import GaloisForLFunctions.RHTower.XiWeilResolventSource
import GaloisForLFunctions.HilbertSchmidt

/-!
# Hilbert realization of the square-summable Xi Weil core

Square-summable evaluation on the multiplicity-exact centered Xi divisor defines a canonical
`ell^2` vector.  Under RH, the polarized Weil form is exactly the Hilbert inner product with the
arguments reversed (matching the convention that the form is linear in its first argument).  The
theta transform evaluates to zero, while every removable Hedenmalm eigenfunction quotient gives a
finite-support vector with its exact multiplicity norm.

The closed span of regular Cauchy evaluation vectors is therefore a concrete Hilbert completion of
the resolvent test core.  This does not assert closability of the full unbounded Hedenmalm operator
on the complete Guinand--Weil domain.
-/

open Complex

namespace RHTower

noncomputable section

/-- Evaluation of a square-summable test function as an actual `ell^2` vector on the Xi divisor. -/
def xiWeilEvaluationLp (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ⟨fun q => F (xiSpectralPoint q), HilbertSchmidt.memℓp_of_sq hF⟩

@[simp] theorem xiWeilEvaluationLp_apply
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) (q : XiZeroCopy) :
    xiWeilEvaluationLp F hF q = F (xiSpectralPoint q) := rfl

/-- Under RH the zero-side Weil polarization is precisely the `ell^2` inner product. -/
theorem inner_xiWeilEvaluationLp_eq_polarization_of_riemannHypothesis
    (hRH : RiemannHypothesis) (F G : ℂ → ℂ)
    (hF : XiWeilSquareSummable F) (hG : XiWeilSquareSummable G) :
    inner ℂ (xiWeilEvaluationLp G hG) (xiWeilEvaluationLp F hF) =
      xiWeilPolarization F G := by
  rw [lp.inner_eq_tsum, xiWeilPolarization]
  apply tsum_congr
  intro q
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  have hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q := by
    rw [ht]
    exact Complex.conj_ofReal t
  rw [xiWeilSharp, hreal]
  simp [RCLike.inner_apply]

/-- The completed theta transform is square-summable because every divisor evaluation vanishes. -/
theorem XiWeilSquareSummable_XiC : XiWeilSquareSummable XiC := by
  unfold XiWeilSquareSummable
  convert (summable_zero : Summable (fun _ : XiZeroCopy => (0 : ℝ))) using 1
  funext q
  rw [XiC_xiSpectralPoint_eq_zero, norm_zero]
  norm_num

/-- The theta constraint is literally the zero vector in the evaluation Hilbert space. -/
theorem xiWeilEvaluationLp_XiC_eq_zero :
    xiWeilEvaluationLp XiC XiWeilSquareSummable_XiC = 0 := by
  apply Subtype.ext
  funext q
  change XiC (xiSpectralPoint q) = (0 : ℂ)
  exact XiC_xiSpectralPoint_eq_zero q

/-- Every centered Cauchy test has square-summable values on the Xi divisor. -/
theorem XiWeilSquareSummable_cauchy (z : ℂ) :
    XiWeilSquareSummable (xiWeilCauchyTest z) := by
  let a : XiZeroCopy → ℂ := xiSpectralPoint
  let S : ℝ := 2 * ‖z‖ + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hbase : Summable (fun q : XiZeroCopy => 1 / ‖a q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable
  have hev : ∀ᶠ q in Filter.cofinite, S ≤ ‖a q‖ := by
    have htend := hbase.tendsto_cofinite_zero
    have hlt : ∀ᶠ q in Filter.cofinite, 1 / ‖a q‖ ^ 2 < 1 / S ^ 2 :=
      htend.eventually_lt_const (by positivity)
    filter_upwards [hlt] with q hq
    have haq : 0 < ‖a q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hsq : S ^ 2 < ‖a q‖ ^ 2 :=
      lt_of_one_div_lt_one_div (pow_pos haq 2) hq
    exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)
  unfold XiWeilSquareSummable
  refine (hbase.mul_left 4).of_norm_bounded_eventually ?_
  filter_upwards [hev] with q hq
  have haz : ‖z‖ ≤ ‖a q‖ / 2 := by
    dsimp [S] at hq
    linarith
  have hdiff : ‖a q‖ / 2 ≤ ‖a q - z‖ := by
    have hrev := norm_sub_norm_le (a q) z
    linarith
  have ha0 : 0 < ‖a q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hd0 : 0 < ‖a q - z‖ := lt_of_lt_of_le (half_pos ha0) hdiff
  have hsq : (‖a q‖ / 2) ^ 2 ≤ ‖a q - z‖ ^ 2 := by gcongr
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), xiWeilCauchyTest, norm_inv]
  calc
    ‖a q - z‖⁻¹ ^ 2 = 1 / ‖a q - z‖ ^ 2 := by field_simp
    _ ≤ 1 / (‖a q‖ / 2) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos (half_pos ha0)) hsq
    _ = 4 * (1 / ‖a q‖ ^ 2) := by field_simp; ring

/-- A regular centered point, so its Cauchy test has no pole on the Xi divisor. -/
abbrev XiCRegularPoint := {z : ℂ // XiC z ≠ 0}

/-- The regular Cauchy evaluation vector in the Xi `ell^2` carrier. -/
def xiWeilCauchyLp (z : XiCRegularPoint) : lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilEvaluationLp (xiWeilCauchyTest z) (XiWeilSquareSummable_cauchy z)

@[simp] theorem xiWeilCauchyLp_apply (z : XiCRegularPoint) (q : XiZeroCopy) :
    xiWeilCauchyLp z q = xiWeilCauchyTest z (xiSpectralPoint q) := rfl

/-- Algebraic span of all regular Cauchy evaluation vectors. -/
def xiWeilCauchyAlgebraicSubspace :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ (Set.range xiWeilCauchyLp)

/-- Closed Cauchy/relative-resolvent Hilbert core. -/
def xiWeilCauchyHilbertSubspace :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  (xiWeilCauchyAlgebraicSubspace).topologicalClosure

noncomputable instance xiWeilCauchyHilbertSubspace_completeSpace :
    CompleteSpace xiWeilCauchyHilbertSubspace :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem xiWeilCauchyLp_mem_hilbertSubspace (z : XiCRegularPoint) :
    xiWeilCauchyLp z ∈ xiWeilCauchyHilbertSubspace := by
  apply (xiWeilCauchyAlgebraicSubspace).le_topologicalClosure
  exact Submodule.subset_span (Set.mem_range_self z)

/-- Under RH, the norm of the Hedenmalm eigenfunction vector is the exact multiplicity-weighted
derivative norm from the Weil polarization. -/
theorem norm_xiThetaEigenFourier_evaluationLp_sq
    (hRH : RiemannHypothesis) {alpha : ℂ} (halpha : XiC alpha = 0) :
    ‖xiWeilEvaluationLp (xiThetaEigenFourier alpha)
      (xiThetaEigenFourier_squareSummable halpha)‖ ^ 2 =
      (xiSpectralMultiplicity alpha : ℝ) * ‖deriv XiC alpha‖ ^ 2 := by
  have hinner := inner_xiWeilEvaluationLp_eq_polarization_of_riemannHypothesis hRH
    (xiThetaEigenFourier alpha) (xiThetaEigenFourier alpha)
    (xiThetaEigenFourier_squareSummable halpha)
    (xiThetaEigenFourier_squareSummable halpha)
  rw [inner_self_eq_norm_sq_to_K,
    xiWeilPolarization_thetaEigen_diagonal_of_riemannHypothesis hRH halpha] at hinner
  have hre := congrArg Complex.re hinner
  simpa [pow_two] using hre

end

end RHTower
