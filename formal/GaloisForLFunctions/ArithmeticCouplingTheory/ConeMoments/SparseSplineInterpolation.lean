import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineFiniteCorrection
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineParameters
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineFiniteCorrection

/-!
# Sparse exact spline interpolation

Finite two-prime cone moments admit prescribed small targets with unit spline
coefficients and at most three nodes in each unit height interval. Stratified
quadrature controls the real Jacobian; a small increasing node correction
preserves the local count. Explicit parameters expose polynomial costs.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

def sparseSplineRadius (δ : ℝ) (t : ι → ℝ) : ℝ :=
  1/(8*(1+splineHeightCorrectionBound δ t+
    2*(Fintype.card ι:ℝ)*inverseSplineBound δ+
    (∑ i, splineSecondBound δ (t i))*(splineHeightCorrectionBound δ t)^2))

def sparseSplineSamplingTolerance (δ : ℝ) (t : ι → ℝ) : ℝ :=
  sparseSplineRadius δ t/(16*((Fintype.card ι:ℝ)+1))

def sparseSplineNodeCountBound (δ η : ℝ) (t : ι → ℝ) : ℝ :=
  2+((((Fintype.card (SplineSamplingIndex ι):ℝ)+1)*splineSamplingBound δ t)/
    sparseSplineSamplingTolerance δ t)^2+
    16*(∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j))+
    16*(2*splineNumeratorBound δ/η)/sparseSplineRadius δ t

def sparseSplineHeightThreshold (δ : ℝ) (t : ι → ℝ) (n : ℕ) : ℝ :=
  1+64*((((n:ℝ)+2)+δ)*(∑ i, splineSlopeBound δ (t i))+splineNumeratorBound δ)*
    splineHeightCorrectionBound δ t+
    64*(((n:ℝ)+2)+δ)*splineNumeratorBound δ/sparseSplineRadius δ t

/-- Exact finite spline interpolation with a uniform three-node count on
unit intervals and explicit finite-data costs. -/
theorem exists_sparse_prescribed_spline_correction_data {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hgap : ∀ i j, η ≤ |t i+splineShift j|) :
    ∃ n : ℕ, ∃ H₀ κ : ℝ, 0 < n ∧ 0 < H₀ ∧ 0 < κ ∧
      κ=sparseSplineRadius δ t/4 ∧ (n:ℝ) ≤ sparseSplineNodeCountBound δ η t ∧
      H₀=sparseSplineHeightThreshold δ t n ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ r : ι → ℂ, (∀ i, ‖r i‖ ≤ κ*n/H^8) →
      ∃ γ : Fin n → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc H (H+(n:ℝ)+2)) ∧
        (∀ T : ℝ, ((univ : Finset (Fin n)).filter (fun j => γ j ∈ Set.Icc T (T+1))).card ≤ 3) ∧
        ∀ i, (∑ j, (Complex.sinh ((δ:ℂ)+(γ j:ℂ)*Complex.I)/
          ((δ:ℂ)+(γ j:ℂ)*Complex.I))^8*phase (t i) (γ j))=r i := by
  classical
  let m := (Fintype.card ι:ℝ)
  let P := splineHeightCorrectionBound δ t
  let Q := ∑ i, splineSecondBound δ (t i)
  let I := inverseSplineBound δ
  let J := ∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j)
  let B := splineNumeratorBound δ
  let G := ∑ i, splineSlopeBound δ (t i)
  let M₀ := 2*B/η
  let C := ((Fintype.card (SplineSamplingIndex ι):ℝ)+1)*splineSamplingBound δ t
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hP : 0 ≤ P := splineHeightCorrectionBound_nonneg hδ ht
  have hQi (i : ι) : 0 ≤ splineSecondBound δ (t i) := sum_nonneg fun _ _ => abs_nonneg _
  have hGi (i : ι) : 0 ≤ splineSlopeBound δ (t i) := sum_nonneg fun _ _ => abs_nonneg _
  have hQ : 0 ≤ Q := sum_nonneg fun i _ => hQi i
  have hG : 0 ≤ G := sum_nonneg fun i _ => hGi i
  have hI : 0 ≤ I := (norm_nonneg _).trans (norm_inverseSplineNumerator_le hδ 0)
  have hJrow (i : ι) : 0 ≤ ∑ j, splineJacobianEntryBound δ (t i) (t j) :=
    sum_nonneg fun j _ => splineJacobianEntryBound_nonneg hδ (ht j) (ht i)
  have hJ : 0 ≤ J := sum_nonneg fun i _ => hJrow i
  have hB : 0 ≤ B := splineNumeratorBound_nonneg δ
  have hM : 0 ≤ M₀ := by dsimp only [M₀]; positivity
  obtain ⟨ρ,ε,H₀,n,hρ,hε,hH₀,hn,hρeq,hεeq,hdisp,hspace,hquad,hcost,hrow,hbase0,
    hnUpper,hH₀eq,hheight⟩ := exists_sparse_spline_parameters (C := C) hδ hm hP hQ hI hJ hM hB hG
  have hρdef : ρ=sparseSplineRadius δ t := hρeq
  have hεdef : ε=sparseSplineSamplingTolerance δ t := by
    rw [hεeq,hρdef]
    rfl
  have hnBound : (n:ℝ) ≤ sparseSplineNodeCountBound δ η t := by
    simpa only [hρdef,hεdef,C,J,M₀,B,sparseSplineNodeCountBound] using hnUpper
  have hThreshold : H₀=sparseSplineHeightThreshold δ t n := by
    simpa only [hρdef,G,B,P,sparseSplineHeightThreshold] using hH₀eq
  refine ⟨n,H₀,ρ/4,hn,hH₀,by positivity,by rw [hρdef],hnBound,hThreshold,?_⟩
  intro H hHH r hr
  have hH := hH₀.trans_le hHH
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hCspan : 0 < (n:ℝ)+2 := by positivity
  obtain ⟨hEH,hBH⟩ := hheight H hHH
  obtain ⟨x,hx,hsample⟩ := exists_stratified_complex_averages
    (splineSamplingFamily δ t) (continuous_splineSamplingFamily hδ ht)
    (splineSamplingBound_pos hδ ht).le hε.le (norm_splineSamplingFamily_le hδ ht)
    (H+1) hn hcost
  have hjac (y : ι → ℂ) (i : ι) :
      ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
        (splineHeightCorrection δ t y u:ℂ))-y i‖ ≤ (1/4:ℝ)*‖y‖ := by
    have hi := norm_sparse_spline_jacobian_defect_le hδ ht hinj hn x hsample y i
    have hJi : ∑ j, splineJacobianEntryBound δ (t i) (t j) ≤ J :=
      single_le_sum (fun i _ => hJrow i) (mem_univ i)
    have hh := add_le_add (div_le_div_of_nonneg_right hJi hnR.le) (le_refl (2*m*ε))
    exact hi.trans (mul_le_mul_of_nonneg_right (hh.trans hrow) (norm_nonneg _))
  have herr (i : ι) : splineSecondBound δ (t i)*P^2*ρ+
      splineNormalizationErrorBound H δ (t i) ((n:ℝ)+2)*P ≤ 1/4 := by
    have hQi' : splineSecondBound δ (t i) ≤ Q := single_le_sum (fun i _ => hQi i) (mem_univ i)
    have hGi' : splineSlopeBound δ (t i) ≤ G := single_le_sum (fun i _ => hGi i) (mem_univ i)
    have h1 := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hQi' (sq_nonneg P)) hρ.le).trans hquad
    have h2 : splineNormalizationErrorBound H δ (t i) ((n:ℝ)+2)*P ≤
        8*((((n:ℝ)+2)+δ)*G+B)*P/H := by
      unfold splineNormalizationErrorBound
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hH.le
      apply mul_le_mul_of_nonneg_right _ hP
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (mul_le_mul_of_nonneg_left hGi' (add_pos hCspan hδ).le) le_rfl
    have h3 := h2.trans hEH
    linarith only [h1,h3]
  have hbase : ‖exactSplineNodeMap H δ t x 0‖ ≤ ρ/4 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ρ/4)).mpr
    intro i
    have hi := norm_exactSplineNodeMap_zero_le hH hδ hη hgap hn hx hsample i
    have hb := add_le_add hbase0 hBH
    exact hi.trans (hb.trans_eq (by ring))
  let v : ι → ℂ := fun i => (H:ℂ)^8/(n:ℂ)*r i
  have hv : ‖v‖ ≤ ρ/4 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ρ/4)).mpr
    intro i
    change ‖(H:ℂ)^8/(n:ℂ)*r i‖ ≤ _
    rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH,
      Complex.norm_natCast]
    refine (mul_le_mul_of_nonneg_left (hr i) (by positivity : 0 ≤ H^8/(n:ℝ))).trans_eq ?_
    field_simp [hH.ne',hnR.ne']
  obtain ⟨γ,hγinj,hγmem,hγcount,hγeq⟩ := exists_sparse_exact_spline_correction
    hH hδ hρ.le ht hn hx hdisp hspace hjac herr hbase hv
  refine ⟨γ,hγinj,hγmem,hγcount,?_⟩
  intro i
  have hHC : (H:ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact mul_left_cancel₀ (div_ne_zero (pow_ne_zero 8 hHC) hnC) (hγeq i)

#print axioms exists_sparse_prescribed_spline_correction_data

/-- Positive two-prime cone moments admit exact small targets using unit spline
coefficients and at most three nodes in every unit height interval. -/
theorem exists_two_prime_sparse_spline_finite_correction {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {δ : ℝ} (hδ : 0 < δ)
    (t : ι → PositiveCone (Real.log p) (Real.log q)) (hinj : Function.Injective t) :
    ∃ n : ℕ, ∃ H₀ κ : ℝ, 0 < n ∧ 0 < H₀ ∧ 0 < κ ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ r : ι → ℂ, (∀ i, ‖r i‖ ≤ κ*n/H^8) →
      ∃ γ : Fin n → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc H (H+(n:ℝ)+2)) ∧
        (∀ T : ℝ, ((univ : Finset (Fin n)).filter (fun j => γ j ∈ Set.Icc T (T+1))).card ≤ 3) ∧
        ∀ i, (∑ j, (Complex.sinh ((δ:ℂ)+(γ j:ℂ)*Complex.I)/
          ((δ:ℂ)+(γ j:ℂ)*Complex.I))^8*phase (t i).val (γ j))=r i := by
  obtain ⟨η,hη,hgap⟩ := exists_cone_spline_shift_gap hp hq hpq
  have ht (i : ι) : 0 < (t i).val := (t i).property.1
  have hti : Function.Injective (fun i => (t i).val) :=
    fun _ _ he => hinj (Subtype.ext he)
  have hshift (i : ι) (j : Fin 9) : η ≤ |(t i).val+splineShift j| := by
    have he : (((8:ℤ)-2*(j.val:ℤ):ℤ):ℝ)=splineShift j := by
      simp only [splineShift,Int.cast_sub,Int.cast_ofNat,Int.cast_mul,Int.cast_natCast]
    have hr : |(((8:ℤ)-2*(j.val:ℤ):ℤ):ℝ)| ≤ 8 := by
      rw [he]
      exact abs_splineShift_le j
    simpa only [he] using hgap (t i) (8-2*(j.val:ℤ)) hr
  obtain ⟨n,H₀,κ,hn,hH₀,hκ,_,_,_,hrealize⟩ :=
    exists_sparse_prescribed_spline_correction_data hδ hη ht hti hshift
  exact ⟨n,H₀,κ,hn,hH₀,hκ,hrealize⟩

#print axioms exists_two_prime_sparse_spline_finite_correction
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
