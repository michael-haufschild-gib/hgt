import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineInterpolation

/-!
# Polynomial costs for sparse spline interpolation

A common finite-data envelope bounds the inverse correction radius cubically,
node count and span by its sixteenth power, and starting height by its
twentieth power. These bounds preserve the three-node unit-interval count.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

lemma sparseSplineRadius_pos {δ : ℝ} (hδ : 0 < δ) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) : 0 < sparseSplineRadius δ t := by
  have hP := splineHeightCorrectionBound_nonneg hδ ht
  have hI : 0 ≤ inverseSplineBound δ :=
    (norm_nonneg _).trans (norm_inverseSplineNumerator_le hδ 0)
  have hQ : 0 ≤ ∑ i, splineSecondBound δ (t i) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  unfold sparseSplineRadius
  positivity

lemma sparseSplineSamplingTolerance_pos {δ : ℝ} (hδ : 0 < δ) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) : 0 < sparseSplineSamplingTolerance δ t := by
  have hρ := sparseSplineRadius_pos hδ ht
  unfold sparseSplineSamplingTolerance
  positivity

/-- The inverse sparse correction radius has cubic scalar-envelope growth. -/
lemma inverse_sparseSplineRadius_le {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i)
    (hmX : (Fintype.card ι:ℝ) ≤ X) (hPX : splineHeightCorrectionBound δ t ≤ X)
    (hQX : (∑ i, splineSecondBound δ (t i)) ≤ X) (hIX : inverseSplineBound δ ≤ X) :
    1/sparseSplineRadius δ t ≤ 40*X^3 := by
  let m := (Fintype.card ι:ℝ)
  let P := splineHeightCorrectionBound δ t
  let Q := ∑ i, splineSecondBound δ (t i)
  let I := inverseSplineBound δ
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hP : 0 ≤ P := splineHeightCorrectionBound_nonneg hδ ht
  have hI : 0 ≤ I := (norm_nonneg _).trans (norm_inverseSplineNumerator_le hδ 0)
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hMI : 2*m*I ≤ 2*X^2 := by
    have hh := mul_le_mul hmX hIX hI hX0
    nlinarith only [hh]
  have hQP : Q*P^2 ≤ X^3 :=
    (mul_le_mul hQX (pow_le_pow_left₀ hP hPX 2) (sq_nonneg P) hX0).trans_eq (by ring)
  have h1 : 1 ≤ X^3 := one_le_pow₀ hX
  have h13 : X ≤ X^3 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 3)
  have h23 : X^2 ≤ X^3 := pow_le_pow_right₀ hX (by omega : 2 ≤ 3)
  have he : 1/sparseSplineRadius δ t=8*(1+P+2*m*I+Q*P^2) := by
    simp only [sparseSplineRadius,one_div,inv_inv,P,Q,m,I]
  rw [he]
  nlinarith only [hPX,hMI,hQP,h1,h13,h23]

lemma inverse_sparseSplineSamplingTolerance_le {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i)
    (hmX : (Fintype.card ι:ℝ) ≤ X) (hPX : splineHeightCorrectionBound δ t ≤ X)
    (hQX : (∑ i, splineSecondBound δ (t i)) ≤ X) (hIX : inverseSplineBound δ ≤ X) :
    1/sparseSplineSamplingTolerance δ t ≤ 1280*X^4 := by
  have hρ := sparseSplineRadius_pos hδ ht
  have hr := inverse_sparseSplineRadius_le hδ hX ht hmX hPX hQX hIX
  have hm : (Fintype.card ι:ℝ)+1 ≤ 2*X := by linarith only [hmX,hX]
  have he : 1/sparseSplineSamplingTolerance δ t=
      (16*((Fintype.card ι:ℝ)+1))*(1/sparseSplineRadius δ t) := by
    simp only [sparseSplineSamplingTolerance,div_eq_mul_inv,one_mul,mul_inv_rev,inv_inv]
  rw [he]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) hr
    (by positivity) (by positivity)).trans_eq (by ring)

lemma splineSamplingBound_le_envelope {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hPX : splineHeightCorrectionBound δ t ≤ X)
    (hGX : (∑ i, splineSlopeBound δ (t i)) ≤ X) (hBX : splineNumeratorBound δ ≤ X) :
    splineSamplingBound δ t ≤ 3*X^2 := by
  have hD : 0 ≤ ∑ i, splineDualBound δ (t i) := sum_nonneg fun i _ =>
    (norm_nonneg _).trans (norm_splineDual_le (s := t i) hδ (by linarith only [ht i]) 0)
  have hDX : (∑ i, splineDualBound δ (t i)) ≤ X := by
    change 2*(∑ i, splineDualBound δ (t i)) ≤ X at hPX
    linarith only [hPX,hD]
  have hprod := mul_le_mul hGX hDX hD (zero_le_one.trans hX)
  have h1 : 1 ≤ X^2 := one_le_pow₀ hX
  have h12 : X ≤ X^2 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 2)
  unfold splineSamplingBound
  nlinarith only [hprod,hBX,h1,h12]

lemma splineSampling_constant_le_envelope {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hmX : (Fintype.card ι:ℝ) ≤ X)
    (hPX : splineHeightCorrectionBound δ t ≤ X)
    (hGX : (∑ i, splineSlopeBound δ (t i)) ≤ X) (hBX : splineNumeratorBound δ ≤ X) :
    ((Fintype.card (SplineSamplingIndex ι):ℝ)+1)*splineSamplingBound δ t ≤ 12*X^4 := by
  have he : (Fintype.card (SplineSamplingIndex ι):ℝ)=
      (Fintype.card ι:ℝ)+2*(Fintype.card ι:ℝ)^2 := by
    simp only [SplineSamplingIndex,Fintype.card_sum,Fintype.card_prod,Nat.cast_add,Nat.cast_mul]
    ring
  have hm0 : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hm2 := pow_le_pow_left₀ hm0 hmX 2
  have h12 : X ≤ X^2 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 2)
  have h1 : 1 ≤ X^2 := one_le_pow₀ hX
  have hq : (Fintype.card (SplineSamplingIndex ι):ℝ)+1 ≤ 4*X^2 := by
    rw [he]
    nlinarith only [hmX,hm2,h12,h1]
  exact (mul_le_mul hq (splineSamplingBound_le_envelope hδ hX ht hPX hGX hBX)
    (splineSamplingBound_pos hδ ht).le (by positivity)).trans_eq (by ring)


/-- Fixed coefficient for the sixteenth-power node-count bound. -/
def sparseSplineNodeCost : ℝ := 2+15360^2+16+1280

/-- Fixed coefficient for the twentieth-power height bound. -/
def sparseSplineHeightCost : ℝ :=
  1+64*(sparseSplineNodeCost+4)+2560*(sparseSplineNodeCost+3)

lemma sparseSplineNodeCost_pos : 0 < sparseSplineNodeCost := by
  norm_num [sparseSplineNodeCost]

lemma sparseSplineHeightCost_pos : 0 < sparseSplineHeightCost := by
  norm_num [sparseSplineHeightCost,sparseSplineNodeCost]

lemma sparseSplineNodeCountBound_le {δ η X : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hX : 1 ≤ X) {t : ι → ℝ} (ht : ∀ i, 0 < t i)
    (hmX : (Fintype.card ι:ℝ) ≤ X) (hPX : splineHeightCorrectionBound δ t ≤ X)
    (hQX : (∑ i, splineSecondBound δ (t i)) ≤ X) (hIX : inverseSplineBound δ ≤ X)
    (hGX : (∑ i, splineSlopeBound δ (t i)) ≤ X) (hBX : splineNumeratorBound δ ≤ X)
    (hJX : (∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j)) ≤ X)
    (hηX : 1/η ≤ X) :
    sparseSplineNodeCountBound δ η t ≤ sparseSplineNodeCost*X^16 := by
  have hρ := sparseSplineRadius_pos hδ ht
  have hε := sparseSplineSamplingTolerance_pos hδ ht
  have hB := (splineSamplingBound_pos hδ ht).le
  have hX0 := zero_le_one.trans hX
  have hC := splineSampling_constant_le_envelope hδ hX ht hmX hPX hGX hBX
  have hiε := inverse_sparseSplineSamplingTolerance_le hδ hX ht hmX hPX hQX hIX
  have hiρ := inverse_sparseSplineRadius_le hδ hX ht hmX hPX hQX hIX
  have hratio : (((Fintype.card (SplineSamplingIndex ι):ℝ)+1)*splineSamplingBound δ t)/
      sparseSplineSamplingTolerance δ t ≤ 15360*X^8 := by
    calc
      _ = (((Fintype.card (SplineSamplingIndex ι):ℝ)+1)*splineSamplingBound δ t)*
          (1/sparseSplineSamplingTolerance δ t) := by ring
      _ ≤ (12*X^4)*(1280*X^4) := mul_le_mul hC hiε (by positivity) (by positivity)
      _ = _ := by ring
  have hratio0 : 0 ≤ (((Fintype.card (SplineSamplingIndex ι):ℝ)+1)*splineSamplingBound δ t)/
      sparseSplineSamplingTolerance δ t := by positivity
  have hsquare := pow_le_pow_left₀ hratio0 hratio 2
  have hM : 2*splineNumeratorBound δ/η ≤ 2*X^2 := by
    calc
      _ = 2*(splineNumeratorBound δ*(1/η)) := by ring
      _ ≤ 2*(X*X) := mul_le_mul_of_nonneg_left
        (mul_le_mul hBX hηX (by positivity) hX0) (by norm_num)
      _ = _ := by ring
  have hMρ : (2*splineNumeratorBound δ/η)/sparseSplineRadius δ t ≤ 80*X^5 := by
    calc
      _ = (2*splineNumeratorBound δ/η)*(1/sparseSplineRadius δ t) := by ring
      _ ≤ (2*X^2)*(40*X^3) := mul_le_mul hM hiρ (by positivity) (by positivity)
      _ = _ := by ring
  have h1 : 1 ≤ X^16 := one_le_pow₀ hX
  have h116 : X ≤ X^16 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 16)
  have h516 : X^5 ≤ X^16 := pow_le_pow_right₀ hX (by omega : 5 ≤ 16)
  have he : (15360*X^8)^2=15360^2*X^16 := by ring
  rw [he] at hsquare
  unfold sparseSplineNodeCountBound sparseSplineNodeCost
  rw [show 16*(2*splineNumeratorBound δ/η)/sparseSplineRadius δ t=
    16*((2*splineNumeratorBound δ/η)/sparseSplineRadius δ t) by ring]
  nlinarith only [hsquare,hJX,hMρ,h1,h116,h516]

lemma sparseSplineHeightThreshold_le {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i)
    (hmX : (Fintype.card ι:ℝ) ≤ X) (hPX : splineHeightCorrectionBound δ t ≤ X)
    (hQX : (∑ i, splineSecondBound δ (t i)) ≤ X) (hIX : inverseSplineBound δ ≤ X)
    (hGX : (∑ i, splineSlopeBound δ (t i)) ≤ X) (hBX : splineNumeratorBound δ ≤ X)
    (hδX : δ ≤ X) {n : ℕ} (hnX : (n:ℝ) ≤ sparseSplineNodeCost*X^16) :
    sparseSplineHeightThreshold δ t n ≤ sparseSplineHeightCost*X^20 := by
  have hX0 := zero_le_one.trans hX
  have hρ := sparseSplineRadius_pos hδ ht
  have hP := splineHeightCorrectionBound_nonneg hδ ht
  have hG : 0 ≤ ∑ i, splineSlopeBound δ (t i) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hB := splineNumeratorBound_nonneg δ
  have hK := sparseSplineNodeCost_pos.le
  have hiρ := inverse_sparseSplineRadius_le hδ hX ht hmX hPX hQX hIX
  have h1 : 1 ≤ X^16 := one_le_pow₀ hX
  have h116 : X ≤ X^16 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 16)
  have h117 : X ≤ X^17 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 17)
  have hL : (n:ℝ)+2+δ ≤ (sparseSplineNodeCost+3)*X^16 := by
    nlinarith only [hnX,hδX,h1,h116]
  have hLG := mul_le_mul hL hGX hG (by positivity : 0 ≤ (sparseSplineNodeCost+3)*X^16)
  have hLGB : ((n:ℝ)+2+δ)*(∑ i, splineSlopeBound δ (t i))+splineNumeratorBound δ ≤
      (sparseSplineNodeCost+4)*X^17 := by
    nlinarith only [hLG,hBX,h117]
  have hfirst := mul_le_mul hLGB hPX hP (by positivity : 0 ≤ (sparseSplineNodeCost+4)*X^17)
  have hLB := mul_le_mul hL hBX hB (by positivity : 0 ≤ (sparseSplineNodeCost+3)*X^16)
  have hlast := mul_le_mul hLB hiρ (by positivity : 0 ≤ 1/sparseSplineRadius δ t)
    (by positivity : 0 ≤ ((sparseSplineNodeCost+3)*X^16)*X)
  have h120 : 1 ≤ X^20 := one_le_pow₀ hX
  have h1820 : X^18 ≤ X^20 := pow_le_pow_right₀ hX (by omega : 18 ≤ 20)
  have hfirst' :
      (((n:ℝ)+2+δ)*(∑ i, splineSlopeBound δ (t i))+splineNumeratorBound δ)*
        splineHeightCorrectionBound δ t ≤ (sparseSplineNodeCost+4)*X^20 := by
    calc
      _ ≤ ((sparseSplineNodeCost+4)*X^17)*X := hfirst
      _ = (sparseSplineNodeCost+4)*X^18 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1820 (by positivity)
  have hlast' : ((n:ℝ)+2+δ)*splineNumeratorBound δ/sparseSplineRadius δ t ≤
      40*(sparseSplineNodeCost+3)*X^20 := by
    calc
      _ = (((n:ℝ)+2+δ)*splineNumeratorBound δ)*(1/sparseSplineRadius δ t) := by ring
      _ ≤ (((sparseSplineNodeCost+3)*X^16)*X)*(40*X^3) := hlast
      _ = _ := by ring
  unfold sparseSplineHeightThreshold sparseSplineHeightCost
  rw [show 64*((n:ℝ)+2+δ)*splineNumeratorBound δ/sparseSplineRadius δ t=
    64*(((n:ℝ)+2+δ)*splineNumeratorBound δ/sparseSplineRadius δ t) by ring]
  nlinarith only [hfirst',hlast',h120]


def sparseSplineCorrectionCost : ℝ := sparseSplineNodeCost+sparseSplineHeightCost+163

lemma sparseSplineCorrectionCost_pos : 0 < sparseSplineCorrectionCost := by
  norm_num [sparseSplineCorrectionCost,sparseSplineHeightCost,sparseSplineNodeCost]

/-- Sparse exact interpolation has polynomial node, span, height, and
inverse-target costs in a common finite-data envelope. -/
theorem exists_sparse_spline_correction_polynomial_bound {δ η X : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hX : 1 ≤ X) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hgap : ∀ i j, η ≤ |t i+splineShift j|)
    (hmX : (Fintype.card ι:ℝ) ≤ X) (hPX : splineHeightCorrectionBound δ t ≤ X)
    (hQX : (∑ i, splineSecondBound δ (t i)) ≤ X) (hIX : inverseSplineBound δ ≤ X)
    (hGX : (∑ i, splineSlopeBound δ (t i)) ≤ X) (hBX : splineNumeratorBound δ ≤ X)
    (hJX : (∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j)) ≤ X)
    (hηX : 1/η ≤ X) (hδX : δ ≤ X) :
    ∃ n : ℕ, ∃ span H₀ κ : ℝ, 0 < n ∧ 0 < span ∧ 0 < H₀ ∧ 0 < κ ∧
      (n:ℝ) ≤ sparseSplineCorrectionCost*X^16 ∧
      span ≤ sparseSplineCorrectionCost*X^16 ∧
      H₀ ≤ sparseSplineCorrectionCost*X^20 ∧
      1/κ ≤ sparseSplineCorrectionCost*X^3 ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ r : ι → ℂ, (∀ i, ‖r i‖ ≤ κ*n/H^8) →
      ∃ γ : Fin n → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc H (H+span)) ∧
        (∀ T : ℝ, ((univ : Finset (Fin n)).filter (fun j => γ j ∈ Set.Icc T (T+1))).card ≤ 3) ∧
        ∀ i, (∑ j, (Complex.sinh ((δ:ℂ)+(γ j:ℂ)*Complex.I)/
          ((δ:ℂ)+(γ j:ℂ)*Complex.I))^8*phase (t i) (γ j))=r i := by
  obtain ⟨n,H₀,κ,hn,hH₀,hκ,hκeq,hnB,hH₀eq,hrealize⟩ :=
    exists_sparse_prescribed_spline_correction_data hδ hη ht hinj hgap
  have hnX := hnB.trans (sparseSplineNodeCountBound_le hδ hη hX ht hmX hPX hQX hIX hGX hBX hJX hηX)
  have hρ := sparseSplineRadius_pos hδ ht
  have hiρ := inverse_sparseSplineRadius_le hδ hX ht hmX hPX hQX hIX
  have hK1 : sparseSplineNodeCost+2 ≤ sparseSplineCorrectionCost := by
    norm_num [sparseSplineCorrectionCost,sparseSplineHeightCost,sparseSplineNodeCost]
  have hK2 : sparseSplineHeightCost ≤ sparseSplineCorrectionCost := by
    norm_num [sparseSplineCorrectionCost,sparseSplineNodeCost,sparseSplineHeightCost]
  have hK3 : (160:ℝ) ≤ sparseSplineCorrectionCost := by
    norm_num [sparseSplineCorrectionCost,sparseSplineNodeCost,sparseSplineHeightCost]
  have hnK : (n:ℝ) ≤ sparseSplineCorrectionCost*X^16 := hnX.trans
    (mul_le_mul_of_nonneg_right (by linarith only [hK1]) (by positivity))
  have hsK : (n:ℝ)+2 ≤ sparseSplineCorrectionCost*X^16 := by
    have h1 : 1 ≤ X^16 := one_le_pow₀ hX
    have hh := mul_le_mul_of_nonneg_right hK1 (by positivity : 0 ≤ X^16)
    nlinarith only [hnX,h1,hh]
  have hHK : H₀ ≤ sparseSplineCorrectionCost*X^20 := by
    rw [hH₀eq]
    exact (sparseSplineHeightThreshold_le hδ hX ht hmX hPX hQX hIX hGX hBX hδX hnX).trans
      (mul_le_mul_of_nonneg_right hK2 (by positivity))
  have hκK : 1/κ ≤ sparseSplineCorrectionCost*X^3 := by
    calc
      _ = 4*(1/sparseSplineRadius δ t) := by rw [hκeq]; ring
      _ ≤ 4*(40*X^3) := mul_le_mul_of_nonneg_left hiρ (by norm_num)
      _ = 160*X^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK3 (by positivity)
  refine ⟨n,(n:ℝ)+2,H₀,κ,hn,by positivity,hH₀,hκ,hnK,hsK,hHK,hκK,?_⟩
  intro H hH r hr
  obtain ⟨γ,hinj,hmem,hcount,heq⟩ := hrealize H hH r hr
  exact ⟨γ,hinj,by simpa only [add_assoc] using hmem,hcount,heq⟩

#print axioms inverse_sparseSplineRadius_le
#print axioms inverse_sparseSplineSamplingTolerance_le
#print axioms splineSampling_constant_le_envelope
#print axioms sparseSplineNodeCountBound_le
#print axioms sparseSplineHeightThreshold_le
#print axioms exists_sparse_spline_correction_polynomial_bound
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
