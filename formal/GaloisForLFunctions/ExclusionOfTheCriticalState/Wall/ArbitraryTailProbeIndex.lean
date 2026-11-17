import GaloisForLFunctions.BiScaleUncertainty.Observation.CofiniteNegativeFamilies
import GaloisForLFunctions.BiScaleUncertainty.Observation.SignedDensityForms
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SeparatedSignedWindows
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PolynomialWindowVectors
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.CofiniteColumnTailTests

/-!
# Arbitrary signed dimensions of critical-state tails

Separated signed windows and cofinite polynomial density produce definite spaces of every finite dimension.
-/

open MeasureTheory Set Polynomial
open scoped BigOperators ENNReal
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations BiScaleUncertainty.Observation

namespace TailIndex
private def density (F : ℝ → ℝ) (T : ℝ) (u : ℝ) : ℝ := F u * Real.exp (10 * (u + T))

private theorem density_measurable {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (T : ℝ) :
    Measurable (density F T) := hF.meas.mul (by fun_prop)

private theorem density_integrable {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (T : ℝ) :
    Integrable (density F T) (volume.restrict (Iio (-T))) := by
  have h := integrable_tailProbePolynomial hF T 1
  have he : (fun u => (1 : ℝ[X]).eval (Real.exp (u + T)) *
      (F u * Real.exp (10 * (u + T)))) = density F T := by
    funext u
    rw [_root_.Polynomial.eval_one, one_mul]
    rfl
  rwa [he] at h

private theorem window_density_integral (F : ℝ → ℝ) (T a b : ℝ) (P : ℝ[X]) (hb : b ≤ -T) :
    (∫ u, polynomialWindow a b P u ^ 2 * density F T u ∂volume.restrict (Iio (-T))) =
      Real.exp (10 * (b + T)) * (∫ u in Ico a b,
        P.eval (Real.exp (u - b)) ^ 2 * (F u * Real.exp (10 * (u - b)))) := by
  have he : (fun u => polynomialWindow a b P u ^ 2 * density F T u) =
      (Ico a b).indicator (fun u => P.eval (Real.exp (u - b)) ^ 2 * density F T u) := by
    funext u
    by_cases hu : u ∈ Ico a b
    · simp only [polynomialWindow, Set.indicator_of_mem hu]
    · simp only [polynomialWindow, Set.indicator_of_notMem hu, zero_pow (by omega : 2 ≠ 0), zero_mul]
  rw [he, integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
    Set.inter_eq_left.mpr (show Ico a b ⊆ Iio (-T) from fun u hu => hu.2.trans_le hb),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  have hexp : Real.exp (10 * (u + T)) =
      Real.exp (10 * (b + T)) * Real.exp (10 * (u - b)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [density, hexp]
  ring

private theorem polynomial_sum_eval {n : ℕ} (P : Fin n → ℝ[X]) (c : Fin n → ℝ) (x : ℝ) :
    (∑ i, c i • P i).eval x = ∑ i, c i * (P i).eval x := by
  change (Polynomial.evalRingHom x) (∑ i, c i • P i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (c i • P i).eval x = c i * (P i).eval x
  rw [Polynomial.eval_smul]
  rfl

/-- Every finite signed index is realized by actual polynomial tail tests. -/
theorem criticalState_polynomial_tail_family {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (T ε : ℝ) (hε : ε = 1 ∨ ε = -1) (N n : ℕ) :
    ∃ P : Fin n → ℝ[X], (∀ i, X ^ N ∣ P i) ∧ ∀ c : Fin n → ℝ, c ≠ 0 →
      ε * tailProbeQuadratic F T (∑ i, c i • P i) < 0 := by
  classical
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let μ := volume.restrict (Iio (-T))
  let ν := absoluteDensityMeasure μ (density F T)
  letI : IsFiniteMeasure ν := absoluteDensityMeasure_finite (density_integrable hd T)
  let J : ℝ → ℝ := fun u => ε * densitySign (density F T) u
  have hfm := density_measurable hd T
  have hJm : Measurable J := measurable_const.mul (Measurable.ite
    (measurableSet_le measurable_const hfm) measurable_const measurable_const)
  have hJ : MemLp J ∞ ν := by
    apply memLp_top_of_bound hJm.aestronglyMeasurable |ε|
    filter_upwards [] with u
    dsimp only [J, densitySign]
    split_ifs <;> simp [Real.norm_eq_abs]
  -- Disjoint signed windows give a diagonal definite family in the positive carrier measure.
  obtain ⟨a, b, Q, hb0, hwin, hsep, hdisj⟩ :=
    criticalState_separated_signed_windows hW ht hF (-T) ε hε
  have hbt (i : ℕ) : b i ≤ -T := by
    by_cases hi : i = 0
    · simpa only [hi] using hb0.le
    · have h := (hsep 0 i (Nat.pos_of_ne_zero hi)).trans (hwin 0).1
      exact h.le.trans hb0.le
  let v : Fin n → Lp ℝ 2 ν := fun i => polynomialWindowLp ν (a i.val) (b i.val) (Q i.val)
  have hvdisj (i j : Fin n) (hij : i ≠ j) : ∀ᵐ u ∂ν, v i u * v j u = 0 :=
    polynomialWindowLp_disjoint ν _ _ (hdisj (show i.val ≠ j.val from fun h => hij (Fin.ext h)))
  have hvneg (i : Fin n) : _root_.RHTower.linftyMultiplierQuadratic J hJ (v i) < 0 := by
    rw [_root_.RHTower.linftyMultiplierQuadratic_eq_integral]
    have he : (∫ u, v i u ^ 2 * J u ∂ν) =
        ε * (Real.exp (10 * (b i.val + T)) * (∫ u in Ico (a i.val) (b i.val),
          (Q i.val).eval (Real.exp (u - b i.val)) ^ 2 *
            (F u * Real.exp (10 * (u - b i.val))))) := by
      calc
        _ = ∫ u, (ε * polynomialWindow (a i.val) (b i.val) (Q i.val) u ^ 2) *
            densitySign (density F T) u ∂ν := by
          apply integral_congr_ae
          filter_upwards [polynomialWindowLp_ae ν (a i.val) (b i.val) (Q i.val)] with u hu
          change polynomialWindowLp ν (a i.val) (b i.val) (Q i.val) u ^ 2 *
            (ε * densitySign (density F T) u) = _
          rw [hu]
          ring
        _ = ∫ u, (ε * polynomialWindow (a i.val) (b i.val) (Q i.val) u ^ 2) * density F T u ∂μ :=
          integral_densitySign μ hfm _
        _ = ε * (∫ u, polynomialWindow (a i.val) (b i.val) (Q i.val) u ^ 2 * density F T u ∂μ) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with u
          ring
        _ = _ := by rw [window_density_integral F T _ _ _ (hbt i.val)]
    rw [he, mul_left_comm]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (hwin i.val).2
  have hφ : MeasurableEmbedding (fun u : ℝ => Real.exp (u + T)) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (u + T))).measurableEmbedding
      (fun u v h => add_right_cancel (Real.exp_injective h))
  have hbound : ∀ᵐ u ∂ν, |Real.exp (u + T)| ≤ 1 := by
    apply ae_absoluteDensityMeasure
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    change u < -T at hu
    linarith only [hu]
  -- Cofinite polynomial density preserves strict definiteness of this finite family.
  obtain ⟨P, hdiv, hP⟩ := exists_negative_polynomial_tails_of_disjoint_tests hφ hbound
    (Filter.Eventually.of_forall fun u => Real.exp_ne_zero (u + T)) N J hJ n v hvdisj hvneg
  refine ⟨P, hdiv, fun c hc => ?_⟩
  have he : (∫ u, (∑ i, c i * (P i).eval (Real.exp (u + T))) ^ 2 * J u ∂ν) =
      ε * tailProbeQuadratic F T (∑ i, c i • P i) := by
    calc
      _ = ∫ u, (ε * (∑ i, c i * (P i).eval (Real.exp (u + T))) ^ 2) *
          densitySign (density F T) u ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with u
        dsimp only [J]
        ring
      _ = ∫ u, (ε * (∑ i, c i * (P i).eval (Real.exp (u + T))) ^ 2) * density F T u ∂μ :=
        integral_densitySign μ hfm _
      _ = ε * tailProbeQuadratic F T (∑ i, c i • P i) := by
        rw [tailProbeQuadratic_eq_integral hd, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with u
        rw [polynomial_sum_eval]
        dsimp only [density]
        ring
  rw [← he]
  exact hP c hc

/-- Every finite signed index is realized without restricting the polynomial coefficients. -/
theorem criticalState_polynomial_signed_family {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (T ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℕ) :
    ∃ P : Fin n → ℝ[X], ∀ c : Fin n → ℝ, c ≠ 0 →
      ε * tailProbeQuadratic F T (∑ i, c i • P i) < 0 := by
  obtain ⟨P, _, hP⟩ := criticalState_polynomial_tail_family hW ht hF T ε hε 0 n
  exact ⟨P, hP⟩

/-- Deleting any finite residue-column gaps preserves arbitrary finite signed dimensions. -/
theorem criticalState_column_polynomial_signed_family {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (T ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (k : ℕ → ℕ) (n : ℕ) :
    ∃ P : Fin n → ℝ[X],
      (∀ i, ∀ j ∈ (P i).support, j ∈ ArithmeticEffectivityTheory.ResidueColumns.carrier m k) ∧
      ∀ c : Fin n → ℝ, c ≠ 0 → ε * tailProbeQuadratic F T (∑ i, c i • P i) < 0 := by
  obtain ⟨P, hdiv, hP⟩ := criticalState_polynomial_tail_family hW ht hF T ε hε
    (ArithmeticEffectivityTheory.ResidueColumns.tailBound m k) n
  refine ⟨P, fun i => ?_, hP⟩
  obtain ⟨Q, hQ⟩ := hdiv i
  rw [hQ]
  exact shiftedPolynomial_column_support m k Q

end TailIndex

/-- RH holds, or every critical-state tail has polynomial subspaces of arbitrary finite positive and negative dimension. -/
theorem riemannHypothesis_or_arbitrary_tail_polynomial_index :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ (T ε : ℝ), ε = 1 ∨ ε = -1 → ∀ n : ℕ,
        ∃ P : Fin n → ℝ[X], ∀ c : Fin n → ℝ, c ≠ 0 →
          ε * tailProbeQuadratic F T (∑ i, c i • P i) < 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with
    hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, TailIndex.criticalState_polynomial_signed_family hW ht hF⟩

/-- RH holds, or every cofinite column restriction retains both arbitrarily large signed polynomial spaces. -/
theorem riemannHypothesis_or_arbitrary_column_tail_index :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ (T ε : ℝ), ε = 1 ∨ ε = -1 →
        ∀ (m : ℕ) (k : ℕ → ℕ) (n : ℕ), ∃ P : Fin n → ℝ[X],
          (∀ i, ∀ j ∈ (P i).support, j ∈ ArithmeticEffectivityTheory.ResidueColumns.carrier m k) ∧
          ∀ c : Fin n → ℝ, c ≠ 0 → ε * tailProbeQuadratic F T (∑ i, c i • P i) < 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with
    hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, TailIndex.criticalState_column_polynomial_signed_family hW ht hF⟩

#print axioms riemannHypothesis_or_arbitrary_column_tail_index

#print axioms riemannHypothesis_or_arbitrary_tail_polynomial_index
end GaloisForLFunctions.ExclusionOfTheCriticalState
