import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.StratifiedQuadrature
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineHeightCorrection

/-!
# Simultaneous sparse sampling of spline moments

A quadratic cell-count bound controls normalized quadrature errors for a
finite complex family. The spline numerators and both derivative/dual
pairings form a uniformly bounded continuous family. A shifted-frequency
gap bounds the numerator's interval integral independently of translation.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- A quadratic cell-count condition makes all normalized quadrature errors small. -/
lemma exists_stratified_complex_averages {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) (hbound : ∀ i x, ‖f i x‖ ≤ B)
    (a : ℝ) {n : ℕ} (hn : 0 < n)
    (hcost : (((Fintype.card ι:ℝ)+1)*B)^2 ≤ (n:ℝ)*ε^2) :
    ∃ x : Fin n → ℝ, (∀ j, x j ∈ Set.Ioo (a+j.val) (a+j.val+1)) ∧
      ∀ i, ‖(∑ j, f i (x j))/(n:ℂ)-(∫ y in a..(a+n), f i y)/(n:ℂ)‖ ≤ ε := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨x,hx,he⟩ := exists_stratified_complex_quadrature f hf hB hbound a n
  refine ⟨x,hx,?_⟩
  intro i
  let d := (∑ j, f i (x j))-∫ y in a..(a+n), f i y
  have hsq : ‖d‖^2 ≤ (n:ℝ)^2*ε^2 := by
    exact (he i).trans ((mul_le_mul_of_nonneg_left hcost hnR.le).trans_eq (by ring))
  have hp : 0 ≤ (n:ℝ)*ε := mul_nonneg hnR.le hε
  have hd : ‖d‖ ≤ (n:ℝ)*ε := by nlinarith only [hsq,hp,norm_nonneg d]
  rw [← sub_div,norm_div,Complex.norm_natCast]
  exact (div_le_iff₀ hnR).2 (by simpa only [mul_comm] using hd)

/-- Numerators and both real-Jacobian pairings must be sampled simultaneously. -/
abbrev SplineSamplingIndex (ι : Type*) := ι ⊕ ((ι × ι) ⊕ (ι × ι))

variable {ι : Type*} [Fintype ι]

def splineSamplingFamily (δ : ℝ) (t : ι → ℝ) : SplineSamplingIndex ι → ℝ → ℂ
  | .inl i => shiftedSplineNumerator δ (t i)
  | .inr (.inl (i,j)) => fun x => shiftedSplineSlope δ (t i) x*splineDual δ (t j) x
  | .inr (.inr (i,j)) => fun x =>
      shiftedSplineSlope δ (t i) x*(starRingEnd ℂ) (splineDual δ (t j) x)

def splineSamplingBound (δ : ℝ) (t : ι → ℝ) : ℝ :=
  1+splineNumeratorBound δ+(∑ i, splineSlopeBound δ (t i))*(∑ i, splineDualBound δ (t i))

#print axioms exists_stratified_complex_averages

omit [Fintype ι] in
lemma continuous_splineSamplingFamily {δ : ℝ} (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (k : SplineSamplingIndex ι) :
    Continuous (splineSamplingFamily δ t k) := by
  rcases k with i | k
  · exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_shiftedSplineNumerator δ (t i) x).continuousAt
  rcases k with ⟨i,j⟩ | ⟨i,j⟩
  · exact (continuous_shiftedSplineSlope δ (t i)).mul (continuous_splineDual hδ (ht j))
  · exact (continuous_shiftedSplineSlope δ (t i)).mul (continuous_conj_splineDual hδ (ht j))

lemma splineSamplingBound_pos {δ : ℝ} (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) : 0 < splineSamplingBound δ t := by
  have hnum := splineNumeratorBound_nonneg δ
  have hs : 0 ≤ ∑ i, splineSlopeBound δ (t i) := sum_nonneg fun i _ =>
    (norm_nonneg _).trans (norm_shiftedSplineSlope_le δ (t i) 0)
  have hd : 0 ≤ ∑ i, splineDualBound δ (t i) := sum_nonneg fun i _ =>
    (norm_nonneg _).trans (norm_splineDual_le (s := t i) hδ (by linarith only [ht i]) 0)
  unfold splineSamplingBound
  positivity

lemma norm_splineSamplingFamily_le {δ : ℝ} (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (k : SplineSamplingIndex ι) (x : ℝ) :
    ‖splineSamplingFamily δ t k x‖ ≤ splineSamplingBound δ t := by
  have hnum := splineNumeratorBound_nonneg δ
  have hs (i) : 0 ≤ splineSlopeBound δ (t i) :=
    (norm_nonneg _).trans (norm_shiftedSplineSlope_le δ (t i) 0)
  have hd (i) : 0 ≤ splineDualBound δ (t i) :=
    (norm_nonneg _).trans (norm_splineDual_le (s := t i) hδ (by linarith only [ht i]) 0)
  have hS := sum_nonneg (fun i (_ : i ∈ (univ : Finset ι)) => hs i)
  have hD := sum_nonneg (fun i (_ : i ∈ (univ : Finset ι)) => hd i)
  have hpair (i j : ι) :
      ‖shiftedSplineSlope δ (t i) x‖*‖splineDual δ (t j) x‖ ≤ splineSamplingBound δ t := by
    have hsi : ‖shiftedSplineSlope δ (t i) x‖ ≤ ∑ i, splineSlopeBound δ (t i) :=
      (norm_shiftedSplineSlope_le δ (t i) x).trans (single_le_sum (fun k _ => hs k) (mem_univ i))
    have hdj : ‖splineDual δ (t j) x‖ ≤ ∑ i, splineDualBound δ (t i) :=
      (norm_splineDual_le (s := t j) hδ (by linarith only [ht j]) x).trans
        (single_le_sum (fun k _ => hd k) (mem_univ j))
    have hh := mul_le_mul hsi hdj (norm_nonneg _) hS
    unfold splineSamplingBound
    linarith only [hh,hnum]
  rcases k with i | k
  · have hh := norm_shiftedSplineNumerator_le δ (t i) x
    have hp := mul_nonneg hS hD
    change ‖shiftedSplineNumerator δ (t i) x‖ ≤ _
    unfold splineSamplingBound
    linarith only [hh,hp]
  rcases k with ⟨i,j⟩ | ⟨i,j⟩
  · simpa only [splineSamplingFamily,norm_mul] using hpair i j
  · simpa only [splineSamplingFamily,norm_mul,Complex.norm_conj] using hpair i j

#print axioms norm_splineSamplingFamily_le

/-- The baseline numerator has a bounded interval integral when all shifted
frequencies stay away from zero. -/
lemma norm_integral_shiftedSplineNumerator_le {η t : ℝ} (hη : 0 < η)
    (hgap : ∀ j : Fin 9, η ≤ |t+splineShift j|) (δ a b : ℝ) :
    ‖∫ x in a..b, shiftedSplineNumerator δ t x‖ ≤ 2*splineNumeratorBound δ/η := by
  have he : (∫ x in a..b, shiftedSplineNumerator δ t x)=
      ∑ j : Fin 9, (splineCoefficient δ j:ℂ)*(∫ x in a..b, phase (t+splineShift j) x) := by
    unfold shiftedSplineNumerator
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro j _
      exact intervalIntegral.integral_const_mul _ _
    · intro j _
      exact (continuous_const.mul (continuous_phase _)).intervalIntegrable a b
  rw [he]
  calc
    _ ≤ ∑ j : Fin 9, |splineCoefficient δ j| *(2/η) := by
      refine (norm_sum_le _ _).trans ?_
      apply sum_le_sum
      intro j _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hpos := hη.trans_le (hgap j)
      have hne : t+splineShift j ≠ 0 := abs_pos.mp hpos
      exact (norm_integral_phase_le hne a b).trans
        (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤2) hη (hgap j))
    _ = _ := by rw [← sum_mul]; unfold splineNumeratorBound; ring

#print axioms norm_integral_shiftedSplineNumerator_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
