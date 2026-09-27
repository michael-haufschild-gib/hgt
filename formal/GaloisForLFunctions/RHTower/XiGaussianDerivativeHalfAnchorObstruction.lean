import GaloisForLFunctions.RHTower.XiGaussianDerivativeEnvelopeLower
import GaloisForLFunctions.RHTower.XiGaussianDerivativeNodalBudget
import GaloisForLFunctions.RHTower.XiCriticalUnreservedPhaseRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A source-capture obstruction to half-time phase domination

The leading coefficient of each nonzero adjugate polynomial survives the
signed Gaussian derivative. At half-time its envelope decays polynomially,
while its nodal weight grows exponentially. A selected critical copy omitted
from the finite source reserve forces the wrong exponential rate. In
particular, the empty-reserve ceiling diverges for every positive finite
order. This is a failure of this explicit ceiling, not of the actual form.
-/

open scoped Real BigOperators
open Complex Filter
noncomputable section

namespace RHTower

theorem xiGaussianCofactorPolynomial_ne_zero {N : ℕ}
    (x : {x : Fin N → ℝ // Function.Injective x}) (i : Fin N) :
    (∑ j, Polynomial.C ((Matrix.vandermonde x.1).adjugate j i) *
      Polynomial.X ^ (j : ℕ)) ≠ 0 := by
  let V := Matrix.vandermonde x.1
  have hd : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr x.property
  have he : (∑ j, Polynomial.C (V.adjugate j i) * Polynomial.X ^ (j : ℕ)).eval (x.1 i) =
      V.det := by
    rw [← real_vandermonde_mulVec_eq_eval]
    exact (Matrix.det_eq_sum_mul_adjugate_row V i).symm
  intro hzero
  rw [hzero, Polynomial.eval_zero] at he
  exact hd he.symm

/-- One cofactor already imposes an exponential-over-polynomial lower bound on the ceiling. -/
theorem xiGaussianDerivativeNodalBudget_half_lower {N : ℕ} (F : Finset XiZeroCopy)
    (x : Fin N → ℝ) (i : Fin N) (t : {t : ℝ // 0 < t}) :
    let P : Polynomial ℝ := ∑ j, Polynomial.C ((Matrix.vandermonde x).adjugate j i) *
      Polynomial.X ^ (j : ℕ)
    (P.leadingCoeff ^ 2 * ((2 * P.natDegree + 4).factorial : ℝ) *
      4 ^ (2 * P.natDegree + 3) * xiResidualOrientationBudget F /
        (2 * (Matrix.vandermonde x).det ^ 2)) *
          (Real.exp ((x i - xiCriticalResidualPhaseGap F / 2) * (t : ℝ)) /
            (t : ℝ) ^ (2 * P.natDegree + 2)) ≤
              xiGaussianDerivativeNodalBudget F x (xiGaussianHalfHeat t) t := by
  dsimp only
  let P : Polynomial ℝ := ∑ j, Polynomial.C ((Matrix.vandermonde x).adjugate j i) *
    Polynomial.X ^ (j : ℕ)
  let C := P.leadingCoeff ^ 2 * ((2 * P.natDegree + 4).factorial : ℝ) *
    4 ^ (2 * P.natDegree + 3)
  have hsingle := Finset.single_le_sum
    (s := Finset.univ) (f := fun k => xiGaussianDerivativeRootEnvelope
      (∑ j, Polynomial.C ((Matrix.vandermonde x).adjugate j k) *
        Polynomial.X ^ (j : ℕ)) (xiGaussianHalfHeat t) t * Real.exp ((t : ℝ) * x k))
    (fun k _ => mul_nonneg (xiGaussianDerivativeRootEnvelope_nonneg _ _ _) (Real.exp_pos _).le)
    (Finset.mem_univ i)
  have hroot := mul_le_mul_of_nonneg_right
    (xiGaussianDerivativeRootEnvelope_half_leading_lower P t) (Real.exp_pos ((t : ℝ) * x i)).le
  have hsum : C / (t : ℝ) ^ (2 * P.natDegree + 2) * Real.exp ((t : ℝ) * x i) ≤
      xiGaussianDerivativeCofactorEnvelope x (xiGaussianHalfHeat t) t := hroot.trans hsingle
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum
      (Real.exp_pos (-(((t : ℝ) - (xiGaussianHalfHeat t : ℝ)) *
        xiCriticalResidualPhaseGap F))).le) (xiResidualOrientationBudget_pos F).le)
      (show 0 ≤ 2 * (Matrix.vandermonde x).det ^ 2 by positivity)
  have he : Real.exp ((x i - xiCriticalResidualPhaseGap F / 2) * (t : ℝ)) =
      Real.exp (-(((t : ℝ) - (xiGaussianHalfHeat t : ℝ)) * xiCriticalResidualPhaseGap F)) *
        Real.exp ((t : ℝ) * x i) := by
    rw [← Real.exp_add]
    congr 1
    change (x i - xiCriticalResidualPhaseGap F / 2) * (t : ℝ) =
      -(((t : ℝ) - (t : ℝ) / 2) * xiCriticalResidualPhaseGap F) + (t : ℝ) * x i
    ring
  refine le_trans (le_of_eq ?_) hscaled
  rw [he]
  dsimp only [C, P]
  ring

/-- A positive nodal rate defeats every polynomial saving in the half-time ceiling. -/
theorem xiGaussianDerivativeNodalBudget_half_tendsto_atTop {N : ℕ} (F : Finset XiZeroCopy)
    (x : {x : Fin N → ℝ // Function.Injective x})
    (i : {i : Fin N // xiCriticalResidualPhaseGap F / 2 < x.1 i}) :
    Tendsto (fun τ : ℝ => xiGaussianDerivativeNodalBudget F x.1
      (xiGaussianHalfHeat ⟨Real.exp τ, Real.exp_pos τ⟩) (Real.exp τ)) atTop atTop := by
  let P : Polynomial ℝ := ∑ j, Polynomial.C ((Matrix.vandermonde x.1).adjugate j i.1) *
    Polynomial.X ^ (j : ℕ)
  let C := P.leadingCoeff ^ 2 * ((2 * P.natDegree + 4).factorial : ℝ) *
    4 ^ (2 * P.natDegree + 3) * xiResidualOrientationBudget F /
      (2 * (Matrix.vandermonde x.1).det ^ 2)
  have hP : P ≠ 0 := xiGaussianCofactorPolynomial_ne_zero x i.1
  have hc : 0 < C := by
    have hl := sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP)
    have hf : (0 : ℝ) < ((2 * P.natDegree + 4).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hd := sq_pos_of_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr x.property)
    have hu := xiResidualOrientationBudget_pos F
    dsimp only [C]
    positivity
  have hr : 0 < x.1 i.1 - xiCriticalResidualPhaseGap F / 2 := sub_pos.mpr i.property
  have hlimit : Tendsto (fun t : ℝ =>
      Real.exp ((x.1 i.1 - xiCriticalResidualPhaseGap F / 2) * t) /
        t ^ (2 * P.natDegree + 2)) atTop atTop := by
    simpa only [Real.rpow_natCast] using
      tendsto_exp_mul_div_rpow_atTop (2 * P.natDegree + 2 : ℕ)
        (x.1 i.1 - xiCriticalResidualPhaseGap F / 2) hr
  have h := (hlimit.comp Real.tendsto_exp_atTop).const_mul_atTop hc
  exact tendsto_atTop_mono
    (fun τ => xiGaussianDerivativeNodalBudget_half_lower F x.1 i.1
      ⟨Real.exp τ, Real.exp_pos τ⟩) h

/-- Every positive finite order has an actual node family whose empty-reserve half-time
ceiling diverges. All nodes are supplied without a zero-location premise. -/
theorem exists_xiGaussianDerivative_half_empty_divergence (n : ℕ) :
    ∃ (γ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      Tendsto (fun τ : ℝ => xiGaussianDerivativeNodalBudget ∅ (fun i => γ i ^ 2)
        (xiGaussianHalfHeat ⟨Real.exp τ, Real.exp_pos τ⟩) (Real.exp τ)) atTop atTop := by
  obtain ⟨γ, q, hinj, hq, _⟩ := exists_xiCriticalGaussian_paired_sampling_reserve (n + 1)
  refine ⟨γ, q, hinj, hq, ?_⟩
  have hcrit : (xiSpectralPoint (q 0)).im = 0 := by rw [(hq 0).2]; rfl
  have hgap := xiCriticalResidualPhaseGap_empty_lt_twice_sq ⟨q 0, hcrit⟩
  rw [(hq 0).2, Complex.ofReal_re] at hgap
  exact xiGaussianDerivativeNodalBudget_half_tendsto_atTop ∅
    ⟨fun i => γ i ^ 2, hinj⟩ ⟨0, by linarith only [hgap]⟩

/-- A half-time domination certificate cannot omit any selected actual critical copy. -/
theorem not_exists_xiGaussianDerivative_half_unreserved_domination (N : ℕ) :
    ¬ ∃ (γ : Fin N → ℝ) (q : Fin N → XiZeroCopy) (F : Finset XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∃ i, q i ∉ F) ∧
      ∀ t : {t : ℝ // 0 < t},
        xiGaussianDerivativeNodalBudget F (fun i => γ i ^ 2) (xiGaussianHalfHeat t) t ≤ 1 := by
  rintro ⟨γ, q, F, hinj, hq, ⟨i, hi⟩, hbound⟩
  have hcrit : (xiSpectralPoint (q i)).im = 0 := by rw [hq i]; rfl
  have hgap := xiCriticalResidualPhaseGap_lt_twice_unreserved_sq F ⟨q i, hi, hcrit⟩
  rw [hq i, Complex.ofReal_re] at hgap
  have hlim := xiGaussianDerivativeNodalBudget_half_tendsto_atTop F
    ⟨fun i => γ i ^ 2, hinj⟩ ⟨i, by linarith only [hgap]⟩
  obtain ⟨τ, hτ⟩ := (hlim.eventually_gt_atTop 1).exists
  exact (not_le_of_gt hτ) (hbound ⟨Real.exp τ, Real.exp_pos τ⟩)

/-- No choice of actual distinct critical nodes makes the empty-reserve half-time
ceiling at most one throughout the positive heat axis. -/
theorem not_exists_xiGaussianDerivative_half_empty_domination (n : ℕ) :
    ¬ ∃ (γ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ t : {t : ℝ // 0 < t},
        xiGaussianDerivativeNodalBudget ∅ (fun i => γ i ^ 2) (xiGaussianHalfHeat t) t ≤ 1 := by
  rintro ⟨γ, q, hinj, hq, hbound⟩
  exact not_exists_xiGaussianDerivative_half_unreserved_domination (n + 1)
    ⟨γ, q, ∅, hinj, hq, ⟨0, Finset.notMem_empty _⟩, hbound⟩

end RHTower
