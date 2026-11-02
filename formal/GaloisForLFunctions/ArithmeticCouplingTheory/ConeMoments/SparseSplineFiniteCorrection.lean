import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineNodes
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineNodeAverages
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineJacobian

/-!
# Exact spline correction on sparse selected nodes

A quarter-size Jacobian defect and a quarter-size nonlinear remainder give
an inverse for the normalized exact moment map. Small spatial corrections
preserve distinctness and the three-node unit-interval bound. The exact
baseline is controlled by sparse quadrature and an inverse-height error.
-/

open Finset Complex Metric
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma corrected_stratified_node_mem {δ H ρ : ℝ} (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) {x : Fin n → ℝ}
    (hx : ∀ j, x j ∈ Set.Ioo (H+1+j.val) (H+1+j.val+1))
    {y : ι → ℂ} (hy : ‖y‖ ≤ ρ) (hdisp : splineHeightCorrectionBound δ t*ρ ≤ 1/4)
    (j : Fin n) :
    x j+splineHeightCorrection δ t y (x j) ∈ Set.Icc H (H+(n:ℝ)+2) := by
  have hh := ((abs_splineHeightCorrection_le hδ ht y (x j)).trans
    (mul_le_mul_of_nonneg_left hy (splineHeightCorrectionBound_nonneg hδ ht))).trans hdisp
  have hc := abs_le.mp hh
  have hj := hx j
  have hjn : (j.val:ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hj0 : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
  constructor <;> linarith only [hc.1,hc.2,hj.1,hj.2,hjn,hj0]

def exactSplineNodeMap (H δ : ℝ) (t : ι → ℝ) (x : Fin n → ℝ)
    (y : ι → ℂ) : ι → ℂ := fun i =>
  splineNodeAverage x (fun u => normalizedSplineNumerator H δ (t i)
    (u+splineHeightCorrection δ t y u))

/-- Sparse sampling errors and the exact denominator remainder suffice for
inversion; no lower spacing between adjacent nodes is needed. -/
theorem exactSplineNodeMap_approximates_identity {H δ ρ : ℝ}
    (hH : 0 < H) (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) {x : Fin n → ℝ} (hn : 0 < n)
    (hx : ∀ j, x j ∈ Set.Ioo (H+1+j.val) (H+1+j.val+1))
    (hdisp : splineHeightCorrectionBound δ t*ρ ≤ 1/4)
    (hjac : ∀ (y : ι → ℂ) i,
      ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
        (splineHeightCorrection δ t y u:ℂ))-y i‖ ≤ (1/4:ℝ)*‖y‖)
    (herr : ∀ i, splineSecondBound δ (t i)*(splineHeightCorrectionBound δ t)^2*ρ+
      splineNormalizationErrorBound H δ (t i) ((n:ℝ)+2)*splineHeightCorrectionBound δ t ≤ 1/4) :
    ApproximatesLinearOn (exactSplineNodeMap H δ t x)
      (ContinuousLinearMap.id ℝ (ι → ℂ)) (closedBall 0 ρ) (1/2) := by
  intro y hy z hz
  have hy' : ‖y‖ ≤ ρ := by simpa only [mem_closedBall,dist_zero_right] using hy
  have hz' : ‖z‖ ≤ ρ := by simpa only [mem_closedBall,dist_zero_right] using hz
  change ‖exactSplineNodeMap H δ t x y-exactSplineNodeMap H δ t x z-(y-z)‖ ≤
    (1/2:ℝ)*‖y-z‖
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)*‖y-z‖)).mpr
  intro i
  have he : ‖splineNodeAverage x (fun u =>
      normalizedSplineNumerator H δ (t i) (u+splineHeightCorrection δ t y u)-
      normalizedSplineNumerator H δ (t i) (u+splineHeightCorrection δ t z u)-
      shiftedSplineSlope δ (t i) u*
        ((splineHeightCorrection δ t y u-splineHeightCorrection δ t z u:ℝ):ℂ))‖ ≤
      (1/4:ℝ)*‖y-z‖ := by
    apply norm_splineNodeAverage_le hn
    intro j
    apply (norm_exact_corrected_spline_increment_le hH hδ ht hρ hz' hy' i (x j)
      (by simpa only [add_assoc] using corrected_stratified_node_mem hδ ht hx hz' hdisp j)
      (by simpa only [add_assoc] using corrected_stratified_node_mem hδ ht hx hy' hdisp j)).trans
    exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
  have hj := hjac (y-z) i
  have hid : exactSplineNodeMap H δ t x y i-exactSplineNodeMap H δ t x z i-(y-z) i=
      splineNodeAverage x (fun u =>
        normalizedSplineNumerator H δ (t i) (u+splineHeightCorrection δ t y u)-
        normalizedSplineNumerator H δ (t i) (u+splineHeightCorrection δ t z u)-
        shiftedSplineSlope δ (t i) u*
          ((splineHeightCorrection δ t y u-splineHeightCorrection δ t z u:ℝ):ℂ))+
      (splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
        (splineHeightCorrection δ t (y-z) u:ℂ))-(y-z) i) := by
    simp_rw [splineHeightCorrection_sub]
    rw [splineNodeAverage_sub,splineNodeAverage_sub]
    unfold exactSplineNodeMap
    ring
  change ‖exactSplineNodeMap H δ t x y i-exactSplineNodeMap H δ t x z i-(y-z) i‖ ≤ _
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add he hj).trans_eq (by ring))

#print axioms exactSplineNodeMap_approximates_identity

lemma exactSplineNodeMap_eq (H δ : ℝ) (t : ι → ℝ) (x : Fin n → ℝ)
    (y : ι → ℂ) (i : ι) :
    exactSplineNodeMap H δ t x y i=(H:ℂ)^8/(n:ℂ)*
      ∑ j, (Complex.sinh ((δ:ℂ)+((x j+splineHeightCorrection δ t y (x j):ℝ):ℂ)*Complex.I)/
        ((δ:ℂ)+((x j+splineHeightCorrection δ t y (x j):ℝ):ℂ)*Complex.I))^8*
        phase (t i) (x j+splineHeightCorrection δ t y (x j)) := by
  simp only [exactSplineNodeMap,splineNodeAverage,normalizedSplineNumerator_eq,mul_assoc,← mul_sum]
  ring

/-- Exact finite moments can be realized without losing the three-node local
count once the sparse Jacobian and denominator errors are controlled. -/
theorem exists_sparse_exact_spline_correction {H δ ρ : ℝ}
    (hH : 0 < H) (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) {x : Fin n → ℝ} (hn : 0 < n)
    (hx : ∀ j, x j ∈ Set.Ioo (H+1+j.val) (H+1+j.val+1))
    (hdisp : splineHeightCorrectionBound δ t*ρ ≤ 1/4)
    (hspace : (2*(Fintype.card ι:ℝ)*inverseSplineBound δ)*ρ ≤ 1/2)
    (hjac : ∀ (y : ι → ℂ) i,
      ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
        (splineHeightCorrection δ t y u:ℂ))-y i‖ ≤ (1/4:ℝ)*‖y‖)
    (herr : ∀ i, splineSecondBound δ (t i)*(splineHeightCorrectionBound δ t)^2*ρ+
      splineNormalizationErrorBound H δ (t i) ((n:ℝ)+2)*splineHeightCorrectionBound δ t ≤ 1/4)
    (hbase : ‖exactSplineNodeMap H δ t x 0‖ ≤ ρ/4)
    {v : ι → ℂ} (hv : ‖v‖ ≤ ρ/4) :
    ∃ γ : Fin n → ℝ, Function.Injective γ ∧
      (∀ j, γ j ∈ Set.Icc H (H+(n:ℝ)+2)) ∧
      (∀ T : ℝ, ((univ : Finset (Fin n)).filter (fun j => γ j ∈ Set.Icc T (T+1))).card ≤ 3) ∧
      ∀ i, (H:ℂ)^8/(n:ℂ)*
        (∑ j, (Complex.sinh ((δ:ℂ)+(γ j:ℂ)*Complex.I)/
          ((δ:ℂ)+(γ j:ℂ)*Complex.I))^8*phase (t i) (γ j))=v i := by
  classical
  obtain ⟨y,hy,hyv⟩ := exists_small_solution_of_half_defect hρ
    (exactSplineNodeMap_approximates_identity hH hδ hρ ht hn hx hdisp hjac herr) hbase hv
  let γ := fun j => x j+splineHeightCorrection δ t y (x j)
  have hi : 0 ≤ inverseSplineBound δ :=
    (norm_nonneg _).trans (norm_inverseSplineNumerator_le hδ 0)
  have hsp : (2*(Fintype.card ι:ℝ)*inverseSplineBound δ)*‖y‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hy (by positivity)).trans hspace
  have hmono : StrictMono γ :=
    (strictMono_corrected_spline_height hδ ht y hsp).comp (strictMono_stratified_nodes hx)
  refine ⟨γ,hmono.injective,?_,?_,?_⟩
  · exact fun j => corrected_stratified_node_mem hδ ht hx hy hdisp j
  · intro T
    apply card_stratified_perturbation_unit_le hx
    intro j
    exact ((abs_splineHeightCorrection_le hδ ht y (x j)).trans
      (mul_le_mul_of_nonneg_left hy (splineHeightCorrectionBound_nonneg hδ ht))).trans hdisp
  · intro i
    rw [← exactSplineNodeMap_eq]
    exact congrFun hyv i

#print axioms exists_sparse_exact_spline_correction

/-- The exact baseline combines the sparse numerator mean with an inverse-height
normalization error. -/
lemma norm_exactSplineNodeMap_zero_le {H δ η ε : ℝ} (hH : 0 < H)
    (hδ : 0 < δ) (hη : 0 < η) {t : ι → ℝ}
    (hgap : ∀ i j, η ≤ |t i+splineShift j|) {x : Fin n → ℝ} (hn : 0 < n)
    (hx : ∀ j, x j ∈ Set.Ioo (H+1+j.val) (H+1+j.val+1))
    (hsample : ∀ k : SplineSamplingIndex ι,
      ‖splineNodeAverage x (splineSamplingFamily δ t k)-
        (∫ u in (H+1)..(H+1+n), splineSamplingFamily δ t k u)/(n:ℂ)‖ ≤ ε)
    (i : ι) :
    ‖exactSplineNodeMap H δ t x 0 i‖ ≤
      ε+(2*splineNumeratorBound δ/η)/(n:ℝ)+
        8*(((n:ℝ)+2)+δ)*splineNumeratorBound δ/H := by
  have hm := norm_integral_shiftedSplineNumerator_le hη (hgap i) δ (H+1) (H+1+n)
  have hm' : ‖(∫ u in (H+1)..(H+1+n), shiftedSplineNumerator δ (t i) u)-(n:ℂ)*(0:ℂ)‖ ≤
      2*splineNumeratorBound δ/η := by simpa only [mul_zero,sub_zero] using hm
  have hb : ‖splineNodeAverage x (shiftedSplineNumerator δ (t i))‖ ≤
      (2*splineNumeratorBound δ/η)/(n:ℝ)+ε := by
    simpa only [sub_zero] using norm_splineNodeAverage_sub_center_le hn x hm' (hsample (.inl i))
  have hC : 0 ≤ (n:ℝ)+2 := by positivity
  have he : ‖splineNodeAverage x (fun u =>
      (splineHeightFactor H δ u-1)*shiftedSplineNumerator δ (t i) u)‖ ≤
      8*(((n:ℝ)+2)+δ)*splineNumeratorBound δ/H := by
    apply norm_splineNodeAverage_le hn
    intro j
    have hj := hx j
    have hjn : (j.val:ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
    have hj0 : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
    have hx0 : H ≤ x j := by linarith only [hj.1,hj0]
    have hx1 : x j ≤ H+((n:ℝ)+2) := by linarith only [hj.2,hjn]
    rw [norm_mul]
    exact (mul_le_mul (norm_splineHeightFactor_sub_one_le hH hδ.le hx0 hx1)
      (norm_shiftedSplineNumerator_le δ (t i) _) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hz : ∀ u, splineHeightCorrection δ t (0:ι → ℂ) u=0 := by
    intro u
    simp [splineHeightCorrection]
  have hid (u : ℝ) : normalizedSplineNumerator H δ (t i) u=
      shiftedSplineNumerator δ (t i) u+
        (splineHeightFactor H δ u-1)*shiftedSplineNumerator δ (t i) u := by
    unfold normalizedSplineNumerator
    ring
  simp only [exactSplineNodeMap,hz,add_zero,hid,splineNodeAverage_add]
  refine (norm_add_le _ _).trans ?_
  have hh := add_le_add hb he
  linarith only [hh]

#print axioms norm_exactSplineNodeMap_zero_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
