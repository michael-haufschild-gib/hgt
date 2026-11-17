import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TailProbeDifferences
import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffQuadrantRH
import GaloisForLFunctions.HTGeometry.ZeroCountSturm

/-!
# Polynomial filters preserve the critical state's tail indefiniteness

A finite shift filter multiplies the compactified tail density by a real
polynomial. Polynomial-square positivity detects exactly the sign of that
density. A nonzero polynomial has only finitely many zeros along the
injective exponential coordinate, so its sign is fixed on a sufficiently
deep tail. The critical state changes sign on that tail, and hence every
nonzero finite filter retains square tests of both signs.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticHarmonicAnalysis.Coleman
open BiScaleUncertainty.Observation
open _root_.Polynomial

/-- The finite polynomial shift filter of the actual tail moments. -/
def filteredTailMoment (F : ℝ → ℝ) (T : ℝ) (q : ℝ[X]) : ℕ → ℝ :=
  _root_.RHTower.momentPolynomialTransform (tailProbeMoment F T) q

theorem filteredTailMoment_eq_sum (F : ℝ → ℝ) (T : ℝ) (q : ℝ[X]) (k : ℕ) :
    filteredTailMoment F T q k = ∑ j ∈ q.support, q.coeff j * tailProbeMoment F T (k + j) := by
  unfold filteredTailMoment _root_.RHTower.momentPolynomialTransform
  rw [momentFunctional_frequency_translate, _root_.HTGeometry.momentFunctional_eq_support_sum]

/-- Filtered square tests integrate against the full polynomial multiplier of the signed density. -/
theorem filteredTailMoment_square {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (T : ℝ) (q P : ℝ[X]) :
    _root_.HTGeometry.momentFunctional (filteredTailMoment F T q) (P ^ 2) =
      ∫ u in Iio (-T), P.eval (Real.exp (u + T)) ^ 2 *
        (q.eval (Real.exp (u + T)) * (F u * Real.exp (10 * (u + T)))) := by
  rw [filteredTailMoment, _root_.RHTower.momentFunctional_momentPolynomialTransform,
    momentFunctional_tailProbeMoment hF]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [_root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_pow (p := P) (x := Real.exp (u + T)) 2]
  ring

/-- Exact positivity classification of every finite tail-moment filter. -/
theorem filteredTailMoment_square_nonnegative_iff {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (T : ℝ) (q : ℝ[X]) :
    (∀ P : ℝ[X], 0 ≤ _root_.HTGeometry.momentFunctional (filteredTailMoment F T q) (P ^ 2)) ↔
      ∀ᵐ u ∂volume.restrict (Iio (-T)), 0 ≤ q.eval (Real.exp (u + T)) * F u := by
  have hφ : MeasurableEmbedding (fun u : ℝ => Real.exp (u + T)) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (u + T))).measurableEmbedding
      (fun u v h => add_right_cancel (Real.exp_injective h))
  have hb : ∀ᵐ u ∂volume.restrict (Iio (-T)), |Real.exp (u + T)| ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    change u < -T at hu
    linarith only [hu]
  have hm : Measurable (fun u => q.eval (Real.exp (u + T)) *
      (F u * Real.exp (10 * (u + T)))) :=
    (q.continuous.measurable.comp (by fun_prop)).mul (hF.meas.mul (by fun_prop))
  simp_rw [filteredTailMoment_square hF]
  rw [density_nonnegative_iff_coordinate_squares hφ hb hm (integrable_tailProbePolynomial hF T q)]
  constructor
  · intro h
    filter_upwards [h] with u hu
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp (by simpa only [mul_assoc] using hu)
  · intro h
    filter_upwards [h] with u hu
    simpa only [mul_assoc] using mul_nonneg hu (Real.exp_pos (10 * (u + T))).le

private theorem polynomial_exp_tail_sign {q : ℝ[X]} (hq : q ≠ 0) (T : ℝ) :
    ∃ b : ℝ, (∀ u < b, 0 < q.eval (Real.exp (u + T))) ∨
      (∀ u < b, q.eval (Real.exp (u + T)) < 0) := by
  have hinj : Function.Injective (fun u : ℝ => Real.exp (u + T)) :=
    fun u v h => add_right_cancel (Real.exp_injective h)
  have hf : {u : ℝ | q.eval (Real.exp (u + T)) = 0}.Finite :=
    (Polynomial.finite_setOf_isRoot hq).preimage hinj.injOn
  obtain ⟨b, hb⟩ := hf.bddBelow
  have hn (u : ℝ) (hu : u < b) : q.eval (Real.exp (u + T)) ≠ 0 :=
    fun hz => (not_le_of_gt hu) (hb hz)
  have hc : Continuous (fun u : ℝ => q.eval (Real.exp (u + T))) :=
    q.continuous.comp (by fun_prop)
  have hs (u : ℝ) := HTGeometry.sign_constant_of_no_zero hc
    (u := min u (b - 1) - 1) (v := b) (fun z hz => hn z hz.2)
  refine ⟨b, ?_⟩
  rcases lt_or_gt_of_ne (hn (b - 1) (by linarith)) with hneg | hpos
  · right
    intro u hu
    rcases hs u with hp | hm
    · have h := hp (b - 1) ⟨by linarith only [min_le_right u (b - 1)], by linarith⟩
      exact (not_lt_of_ge hneg.le h).elim
    · exact hm u ⟨by linarith only [min_le_left u (b - 1)], hu⟩
  · left
    intro u hu
    rcases hs u with hp | hm
    · exact hp u ⟨by linarith only [min_le_left u (b - 1)], hu⟩
    · have h := hm (b - 1) ⟨by linarith only [min_le_right u (b - 1)], by linarith⟩
      exact (not_lt_of_ge hpos.le h).elim

private theorem criticalState_filtered_density_not_nonnegative {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (T : ℝ)
    {q : ℝ[X]} (hq : q ≠ 0) :
    ¬ ∀ᵐ u ∂volume.restrict (Iio (-T)), 0 ≤ q.eval (Real.exp (u + T)) * F u := by
  intro h
  obtain ⟨b, hs⟩ := polynomial_exp_tail_sign hq T
  let U := max T (-b)
  have hUT : T ≤ U := le_max_left _ _
  have hUb : -b ≤ U := le_max_right _ _
  have hsub : Iio (-U) ⊆ Iio (-T) := fun u hu => by
    change u < -U at hu
    change u < -T
    linarith only [hu, hUT]
  have hd : ∀ᵐ u ∂volume.restrict (Iio (-U)), 0 ≤ q.eval (Real.exp (u + T)) * F u :=
    ae_restrict_of_ae_restrict_of_subset hsub h
  have hsign := criticalState_changes_sign_on_every_ray hW ht hF U
  rcases hs with hp | hm
  · apply hsign.1
    filter_upwards [hd, ae_restrict_mem measurableSet_Iio] with u hu hum
    have hub : u < b := by change u < -U at hum; linarith only [hum, hUb]
    exact (mul_nonneg_iff_of_pos_left (hp u hub)).mp hu
  · apply hsign.2
    filter_upwards [hd, ae_restrict_mem measurableSet_Iio] with u hu hum
    have hub : u < b := by change u < -U at hum; linarith only [hum, hUb]
    by_contra hpos
    exact (not_lt_of_ge hu) (mul_neg_of_neg_of_pos (hm u hub) (lt_of_not_ge hpos))

/-- Every nonzero finite moment filter retains tests of both signs on every actual state tail. -/
theorem criticalState_filteredTailMoment_both_signs {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (T : ℝ)
    {q : ℝ[X]} (hq : q ≠ 0) :
    (∃ P : ℝ[X], _root_.HTGeometry.momentFunctional (filteredTailMoment F T q) (P ^ 2) < 0) ∧
      ∃ P : ℝ[X], 0 < _root_.HTGeometry.momentFunctional (filteredTailMoment F T q) (P ^ 2) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hn (r : ℝ[X]) (hr : r ≠ 0) :
      ∃ P : ℝ[X], _root_.HTGeometry.momentFunctional (filteredTailMoment F T r) (P ^ 2) < 0 := by
    have h := mt (filteredTailMoment_square_nonnegative_iff hd T r).mp
      (criticalState_filtered_density_not_nonnegative hW ht hF T hr)
    push_neg at h
    exact h
  refine ⟨hn q hq, ?_⟩
  obtain ⟨P, hP⟩ := hn (-q) (neg_ne_zero.mpr hq)
  refine ⟨P, ?_⟩
  rw [filteredTailMoment_square hd] at hP ⊢
  simp only [_root_.Polynomial.eval_neg, neg_mul, mul_neg, integral_neg] at hP
  exact neg_neg_iff_pos.mp hP

/-- Unconditionally, RH holds or every nonzero polynomial tail filter remains indefinite. -/
theorem riemannHypothesis_or_indefinite_polynomial_tail_filters :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ (T : ℝ) (q : ℝ[X]), q ≠ 0 →
        (∃ P : ℝ[X], _root_.HTGeometry.momentFunctional (filteredTailMoment F T q) (P ^ 2) < 0) ∧
          ∃ P : ℝ[X], 0 < _root_.HTGeometry.momentFunctional (filteredTailMoment F T q) (P ^ 2) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, fun T q hq =>
      criticalState_filteredTailMoment_both_signs hW ht hF T hq⟩

#print axioms filteredTailMoment_square_nonnegative_iff
#print axioms criticalState_filteredTailMoment_both_signs
#print axioms riemannHypothesis_or_indefinite_polynomial_tail_filters

end GaloisForLFunctions.ExclusionOfTheCriticalState
