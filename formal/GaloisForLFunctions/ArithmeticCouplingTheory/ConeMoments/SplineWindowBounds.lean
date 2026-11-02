import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineUniformBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineDiscreteJacobian

/-!
# Uniform spline correction costs on frequency windows

A common envelope controls every scalar in finite spline interpolation.
The envelope separates window cardinality, frequency radius, and reciprocal
frequency separation while remaining uniform on a positive vertical strip.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma splineNumeratorEnvelope_nonneg (D : ℝ) : 0 ≤ splineNumeratorEnvelope D := by
  unfold splineNumeratorEnvelope
  positivity

lemma splinePairBoundaryBound_le_strip {d δ D s : ℝ} (hd : 0 < d) (hdδ : d ≤ δ)
    (hδD : δ ≤ D) (hs : 0 < s) :
    splinePairBoundaryBound δ s ≤ splineNumeratorEnvelope D*(inverseSplineBound d/8) := by
  change splineNumeratorBound δ*splineDualBound δ s ≤ _
  have hd0 : 0 ≤ splineDualBound δ s := (norm_nonneg _).trans
    (norm_splineDual_le (s := s) (hd.trans_le hdδ) (by linarith only [hs]) 0)
  exact mul_le_mul (splineNumeratorBound_le_envelope (hd.trans_le hdδ).le hδD)
    (splineDualBound_le_strip hd hdδ hs) hd0 (splineNumeratorEnvelope_nonneg D)

lemma splineSlopeBound_le_strip {d δ D L t : ℝ} (hd : 0 < d) (hdδ : d ≤ δ)
    (hδD : δ ≤ D) (hL : 0 ≤ L) (ht : |t| ≤ L) :
    splineSlopeBound δ t ≤ (L+8)*splineNumeratorEnvelope D := by
  exact (splineSlopeBound_le ht δ).trans (mul_le_mul_of_nonneg_left
    (splineNumeratorBound_le_envelope (hd.trans_le hdδ).le hδD) (by positivity))

lemma splineSecondBound_le_strip {d δ D L t : ℝ} (hd : 0 < d) (hdδ : d ≤ δ)
    (hδD : δ ≤ D) (ht : |t| ≤ L) :
    splineSecondBound δ t ≤ (L+8)^2*splineNumeratorEnvelope D := by
  exact (splineSecondBound_le ht δ).trans (mul_le_mul_of_nonneg_left
    (splineNumeratorBound_le_envelope (hd.trans_le hdδ).le hδD) (sq_nonneg _))

/-- A common quadratic frequency bound for every grid Jacobian entry. -/
lemma splinePairLipschitzBound_le_strip {d δ D L t s : ℝ}
    (hd : 0 < d) (hdδ : d ≤ δ) (hδD : δ ≤ D) (hL : 0 ≤ L) (ht : |t| ≤ L) (hs : 0 < s) :
    splinePairLipschitzBound δ t s ≤
      ((L+8)^2*splineNumeratorEnvelope D)*(inverseSplineBound d/8)+
        ((L+8)*splineNumeratorEnvelope D)*inverseSplineBound d := by
  have hδ := hd.trans_le hdδ
  have hd0 : 0 ≤ splineDualBound δ s := (norm_nonneg _).trans
    (norm_splineDual_le (s := s) hδ (by linarith only [hs]) 0)
  have hi0 := (inverseSplineBound_pos hδ).le
  exact add_le_add
    (mul_le_mul (splineSecondBound_le_strip hd hdδ hδD ht) (splineDualBound_le_strip hd hdδ hs)
      hd0 (mul_nonneg (sq_nonneg _) (splineNumeratorEnvelope_nonneg D)))
    (mul_le_mul (splineSlopeBound_le_strip hd hdδ hδD hL ht) (inverseSplineBound_antitone hd hdδ)
      hi0 (mul_nonneg (by positivity) (splineNumeratorEnvelope_nonneg D)))

/-- Integral Jacobian errors need only ordinary frequency separation and a
positive lower bound for the frequencies. -/
lemma splineJacobianEntryBound_le_strip {d δ D τ σ t s : ℝ}
    (hd : 0 < d) (hdδ : d ≤ δ) (hδD : δ ≤ D) (hτ : 0 < τ) (hσ : 0 < σ)
    (ht : τ ≤ t) (hs : τ ≤ s) (hsep : t=s ∨ σ ≤ |t-s|) :
    splineJacobianEntryBound δ t s ≤
      4*splineNumeratorEnvelope D*(inverseSplineBound d/8)+2/σ+
        ((1+splineRatio d)^8*(1/(1-splineRatio d)^8))/τ := by
  have hts : 0 < t+s := add_pos (hτ.trans_le ht) (hτ.trans_le hs)
  have hdiag : 2/|t-s| ≤ 2/σ := by
    rcases hsep with he | hsep
    · rw [he, sub_self, abs_zero, div_zero]
      positivity
    · exact div_le_div_of_nonneg_left (by norm_num) hσ hsep
  have hsum : 2/(t+s) ≤ 1/τ := by
    apply (div_le_div_iff₀ hts hτ).2
    nlinarith only [ht,hs]
  have hR := splineBlaschke_coefficient_bound_antitone hd hdδ
  have hc : 2*((1+splineRatio δ)^8/(t+s)*(1/(1-splineRatio δ)^8)) ≤
      ((1+splineRatio d)^8*(1/(1-splineRatio d)^8))/τ := by
    calc
      _ = ((1+splineRatio δ)^8*(1/(1-splineRatio δ)^8))*(2/(t+s)) := by ring
      _ ≤ ((1+splineRatio d)^8*(1/(1-splineRatio d)^8))*(1/τ) :=
        mul_le_mul hR hsum (by positivity) (by positivity)
      _ = _ := by ring
  have hb := mul_le_mul_of_nonneg_left
    (splinePairBoundaryBound_le_strip hd hdδ hδD (hτ.trans_le hs)) (by norm_num : (0 : ℝ) ≤ 4)
  unfold splineJacobianEntryBound
  exact add_le_add (add_le_add (hb.trans_eq (by ring)) hdiag) hc

#print axioms splinePairLipschitzBound_le_strip
#print axioms splineJacobianEntryBound_le_strip
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

private lemma finite_sum_le_card_mul {f : ι → ℝ} {C : ℝ} (hf : ∀ i, f i ≤ C) :
    ∑ i, f i ≤ (Fintype.card ι : ℝ)*C := by
  calc
    _ ≤ ∑ _i : ι, C := sum_le_sum fun i _ => hf i
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]

private lemma finite_double_sum_le_card_sq_mul {f : ι → ι → ℝ} {C : ℝ}
    (hf : ∀ i j, f i j ≤ C) : ∑ i, ∑ j, f i j ≤ (Fintype.card ι : ℝ)^2*C := by
  have h := finite_sum_le_card_mul (fun i => finite_sum_le_card_mul (hf i))
  exact h.trans_eq (by ring)

/-- Every scalar entering the correction theorem is controlled by the cardinality,
frequency radius, separation, and fixed positive strip. -/
theorem finite_spline_scalar_bounds {d δ D τ σ L : ℝ}
    (hd : 0 < d) (hdδ : d ≤ δ) (hδD : δ ≤ D) (hτ : 0 < τ) (hσ : 0 < σ) (hL : 0 ≤ L)
    {t : ι → ℝ} (ht : ∀ i, τ ≤ t i) (hsize : ∀ i, |t i| ≤ L)
    (hsep : ∀ i j, i ≠ j → σ ≤ |t i-t j|) :
    (∑ i, |t i|) ≤ (Fintype.card ι : ℝ)*L ∧
    splineHeightCorrectionBound δ t ≤ 2*(Fintype.card ι : ℝ)*(inverseSplineBound d/8) ∧
    (∑ i, splineSecondBound δ (t i)) ≤
      (Fintype.card ι : ℝ)*((L+8)^2*splineNumeratorEnvelope D) ∧
    (∑ i, splineSlopeBound δ (t i)) ≤
      (Fintype.card ι : ℝ)*((L+8)*splineNumeratorEnvelope D) ∧
    (∑ i, ∑ j, splinePairLipschitzBound δ (t i) (t j)) ≤
      (Fintype.card ι : ℝ)^2*
        (((L+8)^2*splineNumeratorEnvelope D)*(inverseSplineBound d/8)+
          ((L+8)*splineNumeratorEnvelope D)*inverseSplineBound d) ∧
    (∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j)) ≤
      (Fintype.card ι : ℝ)^2*
        (4*splineNumeratorEnvelope D*(inverseSplineBound d/8)+2/σ+
          ((1+splineRatio d)^8*(1/(1-splineRatio d)^8))/τ) := by
  classical
  refine ⟨finite_sum_le_card_mul hsize, ?_, ?_, ?_, ?_, ?_⟩
  · have h := finite_sum_le_card_mul fun i => splineDualBound_le_strip hd hdδ (hτ.trans_le (ht i))
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  · exact finite_sum_le_card_mul fun i => splineSecondBound_le_strip hd hdδ hδD (hsize i)
  · exact finite_sum_le_card_mul fun i => splineSlopeBound_le_strip hd hdδ hδD hL (hsize i)
  · exact finite_double_sum_le_card_sq_mul fun i j =>
      splinePairLipschitzBound_le_strip hd hdδ hδD hL (hsize i) (hτ.trans_le (ht j))
  · apply finite_double_sum_le_card_sq_mul
    intro i j
    apply splineJacobianEntryBound_le_strip hd hdδ hδD hτ hσ (ht i) (ht j)
    by_cases hij : i=j
    · exact Or.inl (congrArg t hij)
    · exact Or.inr (hsep i j hij)

#print axioms finite_spline_scalar_bounds
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

def splineStripCostConstant (d D τ η : ℝ) : ℝ :=
  3+D+1/η+splineNumeratorEnvelope D+inverseSplineBound d+
    4*splineNumeratorEnvelope D*inverseSplineBound d+
    ((1+splineRatio d)^8*(1/(1-splineRatio d)^8))/τ

def splineWindowCostEnvelope (d D τ η m L σ : ℝ) : ℝ :=
  splineStripCostConstant d D τ η*(m+1)^2*((L+9)^2+1/σ)

/-- One explicit strip-uniform envelope controls every scalar used to realize
finite prescribed spline moments. -/
theorem finite_spline_data_le_window_envelope {d δ D τ σ η L : ℝ}
    (hd : 0 < d) (hdδ : d ≤ δ) (hδD : δ ≤ D) (hτ : 0 < τ) (hσ : 0 < σ)
    (hη : 0 < η) (hL : 0 ≤ L) {t : ι → ℝ}
    (ht : ∀ i, τ ≤ t i) (hsize : ∀ i, |t i| ≤ L)
    (hsep : ∀ i j, i ≠ j → σ ≤ |t i-t j|) :
    let X := splineWindowCostEnvelope d D τ η (Fintype.card ι) L σ
    1 ≤ X ∧ δ ≤ X ∧ 1/η ≤ X ∧ (∑ i, |t i|) ≤ X ∧
      (∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j)) ≤ X ∧
      (∑ i, ∑ j, splinePairLipschitzBound δ (t i) (t j)) ≤ X ∧
      splineHeightCorrectionBound δ t ≤ X ∧
      (∑ i, splineSecondBound δ (t i)) ≤ X ∧
      (∑ i, splineSlopeBound δ (t i)) ≤ X ∧ splineNumeratorBound δ ≤ X := by
  let m : ℝ := Fintype.card ι
  let U := splineNumeratorEnvelope D
  let C := inverseSplineBound d
  let R := ((1+splineRatio d)^8*(1/(1-splineRatio d)^8))/τ
  let V := splineStripCostConstant d D τ η
  let a := (m+1)^2
  let S := (L+9)^2+1/σ
  let X := V*a*S
  change 1 ≤ X ∧ δ ≤ X ∧ 1/η ≤ X ∧ (∑ i, |t i|) ≤ X ∧
      (∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j)) ≤ X ∧
      (∑ i, ∑ j, splinePairLipschitzBound δ (t i) (t j)) ≤ X ∧
      splineHeightCorrectionBound δ t ≤ X ∧
      (∑ i, splineSecondBound δ (t i)) ≤ X ∧
      (∑ i, splineSlopeBound δ (t i)) ≤ X ∧ splineNumeratorBound δ ≤ X
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hU : 0 ≤ U := splineNumeratorEnvelope_nonneg D
  have hC : 0 ≤ C := (inverseSplineBound_pos hd).le
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hD : 0 ≤ D := (hd.trans_le (hdδ.trans hδD)).le
  have hηi : 0 ≤ 1/η := by positivity
  have hUC := mul_nonneg hU hC
  have hdom : 1 ≤ V ∧ D ≤ V ∧ 1/η ≤ V ∧ U ≤ V ∧ C ≤ V ∧
      U*C/2+R+2 ≤ V ∧ U*C/8+U*C ≤ V := by
    change 1 ≤ 3+D+1/η+U+C+4*U*C+R ∧ D ≤ 3+D+1/η+U+C+4*U*C+R ∧
      1/η ≤ 3+D+1/η+U+C+4*U*C+R ∧ U ≤ 3+D+1/η+U+C+4*U*C+R ∧
      C ≤ 3+D+1/η+U+C+4*U*C+R ∧ U*C/2+R+2 ≤ 3+D+1/η+U+C+4*U*C+R ∧
      U*C/8+U*C ≤ 3+D+1/η+U+C+4*U*C+R
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith only [hD,hηi,hU,hC,hR,hUC]
  have hV0 : 0 ≤ V := le_trans zero_le_one hdom.1
  have ha : 1 ≤ a := by dsimp only [a]; nlinarith only [hm0,sq_nonneg m]
  have hma : m ≤ a := by dsimp only [a]; nlinarith only [hm0,sq_nonneg m]
  have hm2a : m^2 ≤ a := by dsimp only [a]; nlinarith only [hm0]
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hσi : 0 ≤ 1/σ := by positivity
  have hS : 1 ≤ S := by dsimp only [S]; nlinarith only [hL,sq_nonneg L,hσi]
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have hTS : L+8 ≤ S := by dsimp only [S]; nlinarith only [hL,sq_nonneg L,hσi]
  have hT2S : (L+8)^2 ≤ S := by dsimp only [S]; nlinarith only [hL,hσi]
  have hLS : L ≤ S := by linarith only [hTS]
  have hiS : 1/σ ≤ S := by dsimp only [S]; nlinarith only [sq_nonneg (L+9)]
  have haS : 1 ≤ a*S := by
    simpa only [one_mul] using mul_le_mul ha hS (by norm_num : (0 : ℝ) ≤ 1) ha0
  have hVX : V ≤ X := by
    calc V = V*1 := by ring
         _ ≤ V*(a*S) := mul_le_mul_of_nonneg_left haS hV0
         _ = X := by dsimp only [X]; ring
  have hscaled {f k : ℝ} (hf : f ≤ a*S) (hk : k ≤ V) (hk0 : 0 ≤ k) : f*k ≤ X := by
    exact (mul_le_mul hf hk hk0 (mul_nonneg ha0 hS0)).trans_eq (by dsimp only [X]; ring)
  have hmatrix {E : ℝ} (hE : E ≤ V*S) (hE0 : 0 ≤ E) : m^2*E ≤ X := by
    exact (mul_le_mul hm2a hE hE0 ha0).trans_eq (by dsimp only [X]; ring)
  obtain ⟨hbL,hbP,hbQ,hbG,hbJ,hbA⟩ := finite_spline_scalar_bounds hd hdδ hδD hτ hσ hL ht hsize hsep
  refine ⟨hdom.1.trans hVX,hδD.trans (hdom.2.1.trans hVX),hdom.2.2.1.trans hVX,?_,?_,?_,?_,?_,?_,?_⟩
  · have h := mul_le_mul hma hLS hL ha0
    have h' := hscaled h hdom.1 (by norm_num : (0 : ℝ) ≤ 1)
    exact hbL.trans (by simpa only [mul_one] using h')
  · have hE : 4*U*(C/8)+2/σ+R ≤ V*S := by
      have h1 := mul_le_mul_of_nonneg_left hS (show 0 ≤ U*C/2+R by positivity)
      have h2 := mul_le_mul_of_nonneg_left hiS (by norm_num : (0 : ℝ) ≤ 2)
      have h3 := mul_le_mul_of_nonneg_right hdom.2.2.2.2.2.1 hS0
      simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
      nlinarith only [h1,h2,h3]
    exact hbA.trans (hmatrix hE (by positivity))
  · have hJ : ((L+8)^2*U)*(C/8)+((L+8)*U)*C ≤ V*S := by
      have h1 := mul_le_mul_of_nonneg_right hT2S (show 0 ≤ U*C/8 by positivity)
      have h2 := mul_le_mul_of_nonneg_right hTS hUC
      have h3 := mul_le_mul_of_nonneg_right hdom.2.2.2.2.2.2 hS0
      nlinarith only [h1,h2,h3]
    exact hbJ.trans (hmatrix hJ (by positivity))
  · have hmS : m ≤ a*S := hma.trans (by nlinarith only [mul_le_mul_of_nonneg_left hS ha0])
    have hk : C/4 ≤ V := by linarith only [hC,hdom.2.2.2.2.1]
    exact hbP.trans (by
      have h := hscaled hmS hk (show 0 ≤ C/4 by positivity)
      nlinarith only [h])
  · have hf := mul_le_mul hma hT2S (sq_nonneg (L+8)) ha0
    exact hbQ.trans (by
      have h := hscaled hf hdom.2.2.2.1 hU
      nlinarith only [h])
  · have hf := mul_le_mul hma hTS (show 0 ≤ L+8 by positivity) ha0
    exact hbG.trans (by
      have h := hscaled hf hdom.2.2.2.1 hU
      nlinarith only [h])
  · exact (splineNumeratorBound_le_envelope (hd.trans_le hdδ).le hδD).trans (hdom.2.2.2.1.trans hVX)

#print axioms finite_spline_data_le_window_envelope
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
