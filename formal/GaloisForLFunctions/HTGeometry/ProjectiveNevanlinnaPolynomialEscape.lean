import GaloisForLFunctions.HTGeometry.ProjectiveCauchyDensityControl
import GaloisForLFunctions.HTGeometry.PolynomialJetEscape

/-!
# Positive fixed-pattern escape in a projective Nevanlinna density chart

Surjectivity of a finite-dimensional control on a normed submodule lets arbitrarily small real
lines escape every prescribed nonzero multivariate polynomial.  Applying this to the exact frozen
kernel of projective Nevanlinna `L∞` control produces strictly positive density perturbations that
preserve the frozen packet and break any fixed algebraic relation on a disjoint target packet.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A surjective finite-dimensional control from a normed submodule has arbitrarily small
perturbations escaping every nonzero multivariate polynomial. -/
theorem surjective_normed_control_escapes_mvPolynomial
    {V σ : Type*} [Fintype σ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : Submodule ℝ V) (L : S →ₗ[ℝ] (σ → ℂ)) (hL : Function.Surjective L)
    (baseJet : σ → ℂ) (P : MvPolynomial σ ℂ) (hP : P ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ v : S, ∃ ε : ℝ,
      0 < ε ∧ ‖ε • (v : V)‖ < η ∧
      MvPolynomial.eval (baseJet + ε • L v) P ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_mvPolynomial_eval_ne_zero hP
  obtain ⟨v, hv⟩ := hL (y - baseJet)
  let ρ : ℝ := η / (‖(v : V)‖ + 1)
  have hden : 0 < ‖(v : V)‖ + 1 := by positivity
  have hρ : 0 < ρ := div_pos hη hden
  obtain ⟨ε, hε, hερ, hne⟩ := exists_small_real_line_eval_ne_zero P baseJet y hy hρ
  refine ⟨v, ε, hε, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hnormle : ‖(v : V)‖ ≤ ‖(v : V)‖ + 1 := by linarith
    calc
      ε * ‖(v : V)‖ ≤ ε * (‖(v : V)‖ + 1) :=
        mul_le_mul_of_nonneg_left hnormle hε.le
      _ < ρ * (‖(v : V)‖ + 1) := mul_lt_mul_of_pos_right hερ hden
      _ = η := by
        change (η / (‖(v : V)‖ + 1)) * (‖(v : V)‖ + 1) = η
        field_simp [hden.ne']
  · have hcoord : baseJet + ε • L v =
        fun i => baseJet i + (ε : ℂ) * (y i - baseJet i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [hv]
      simp
    rw [hcoord]
    exact hne

/-- **Positive fixed-pattern escape in the literal projective `L∞` chart.** Inside the exact
kernel of a frozen genuine Nevanlinna-jet packet, an arbitrarily small perturbation preserves
strict positivity and breaks any prescribed nonzero polynomial on a disjoint target packet. -/
theorem constrainedProjectiveNevanlinnaJet_positivePolynomialEscape
    {ιf ιt : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt]
    (a q : ℂ → ℂ)
    (zf : ιf → ℂ) (zt : ιt → ℂ)
    (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hqt_inj : Function.Injective (fun i => q (zt i)))
    (hcross : ∀ i j, q (zf i) ≠ q (zt j))
    (hupperf : ∀ i, 0 < (q (zf i)).im) (huppert : ∀ i, 0 < (q (zt i)).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (haf : ∀ i, a (zf i) ≠ 0) (hat : ∀ i, a (zt i) ≠ 0)
    (hqdf : ∀ i, deriv q (zf i) ≠ 0) (hqdt : ∀ i, deriv q (zt i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (baseJet : ((Σ i, Fin (nt i)) → ℂ))
    (P : MvPolynomial (Σ i, Fin (nt i)) ℂ) (hP : P ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ v : LinearMap.ker
        (projectiveNevanlinnaJetLinftyControl a q zf nf haf hqdf mu hupperf),
      ∃ ε : ℝ,
      0 < ε ∧ ‖ε • v.1‖ < η ∧
      LinftyStrictlyPositive mu (linftyOne mu + ε • v.1) ∧
      MvPolynomial.eval
        (baseJet + ε •
          (projectiveNevanlinnaJetLinftyControl a q zt nt hat hqdt mu huppert) v) P ≠ 0 := by
  let S := LinearMap.ker
    (projectiveNevanlinnaJetLinftyControl a q zf nf haf hqdf mu hupperf)
  let L := (projectiveNevanlinnaJetLinftyControl a q zt nt hat hqdt mu huppert).domRestrict S
  have hL : Function.Surjective L :=
    constrainedProjectiveNevanlinnaJet_linftyControl_surjective
      a q zf zt hqf_inj hqt_inj hcross hupperf huppert nf nt
      haf hat hqdf hqdt mu hmu
  have hmin : 0 < min η 1 := lt_min hη zero_lt_one
  obtain ⟨v, ε, hε, hvnorm, hescape⟩ :=
    surjective_normed_control_escapes_mvPolynomial S L hL baseJet P hP hmin
  refine ⟨v, ε, hε, hvnorm.trans_le (min_le_left _ _), ?_, ?_⟩
  · apply linftyOne_add_strictlyPositive_of_norm_lt_one mu
    exact hvnorm.trans_le (min_le_right _ _)
  · exact hescape

end
end GaloisForLFunctions.HTGeometry
