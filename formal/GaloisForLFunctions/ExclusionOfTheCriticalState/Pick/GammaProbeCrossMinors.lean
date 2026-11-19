import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.CauchyJumpMinors
import GaloisForLFunctions.HilbertMetric.QuantumInformation.GammaCauchyAffinity
import Mathlib.Analysis.Analytic.Binomial

/-!
# Strict total positivity of fractional Cauchy probes

Every positive real Schur power of the Cauchy coherence has strictly
positive minors on independently ordered log-rate grids. This gives
strict total positivity of the Hellinger affinity between Gamma laws of
any common positive shape. In positive contrast coordinates the first
binomial coefficients give a quantitative Vandermonde lower bound.
-/

noncomputable section
open Finset Matrix
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.GammaProbes
open HilbertMetric HilbertMetric.CauchyDephasing HilbertMetric.CauchyDephasing.GammaAffinity
open LogCauchy

private def coefficient (a : Shape) (n : ℕ) : Set.Ioi (0:ℝ) :=
  ⟨Ring.multichoose a.val n,by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a.val n
    rw [Polynomial.ascPochhammer_smeval_eq_eval,nsmul_eq_mul] at h
    exact pos_of_mul_pos_right (h.symm ▸ ascPochhammer_pos n a.val a.property) (by positivity)⟩

private theorem binomial_sum (a : Shape) (z : ℝ) (hz : |z|<1) :
    HasSum (fun n : ℕ => (coefficient a n).val*z^n) (1/(1-z)^a.val) := by
  have hball : z ∈ Metric.eball (0:ℝ) 1 := by
    rw [Metric.mem_eball,edist_dist,dist_zero_right,Real.norm_eq_abs,ENNReal.ofReal_lt_one]
    exact hz
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,zero_add,coefficient,Ring.multichoose_eq]
    using (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a.val).hasSum hball

private def volumeFactor {n : ℕ} (z : ContrastGrid n) :=
  ∏ i, ∏ j ∈ Ioi i, ((z j).val-(z i).val)

private theorem vandermonde_eq {n : ℕ} (z : ContrastGrid n) :
    (genVandermonde Fin.val (fun i => (z i).val)).det=volumeFactor z := by
  have h : genVandermonde Fin.val (fun i => (z i).val)=(vandermonde (fun i => (z i).val)).transpose := by
    ext i j
    rfl
  rw [h,det_transpose,det_vandermonde,volumeFactor]

private def disk (a : Shape) {n : ℕ} (z w : ContrastGrid n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => 1/(1-(z i).val*(w j).val)^a.val

private theorem product_lt_one (z w : Set.Ioo (0:ℝ) 1) : z.val*w.val<1 := by
  calc
    _ < z.val*1 := mul_lt_mul_of_pos_left w.property.2 z.property.1
    _ = z.val := mul_one _
    _ < 1 := z.property.2

/-- A single block of n binomial coefficients bounds each fractional minor. -/
theorem binomial_minor_lower (a : Shape) {n : ℕ} (z w : ContrastGrid n) :
    volumeFactor z*((∏ i : Fin n, Ring.multichoose a.val i.val)*volumeFactor w) ≤ (disk a z w).det := by
  let e := OrderEmbedding.ofStrictMono (fun m : ℕ => m) strictMono_id
  have H := seriesMinor_grid_lower e (coefficient a) (positiveGrid z) (positiveGrid w) (disk a z w)
    (fun i j => by
      have hp := mul_pos (z i).property.1 (w j).property.1
      exact binomial_sum a _ (by rw [abs_of_pos hp]; exact product_lt_one _ _))
  simpa only [e,OrderEmbedding.coe_ofStrictMono,positiveGrid,coefficient,vandermonde_eq] using H

private theorem disk_positive (a : Shape) {n : ℕ} (z w : ContrastGrid n) : 0<(disk a z w).det := by
  have hv (g : ContrastGrid n) : 0<volumeFactor g :=
    prod_pos fun i _ => prod_pos fun j h => sub_pos.mpr (g.strictMono (mem_Ioi.mp h))
  exact (mul_pos (hv z) (mul_pos (prod_pos fun i _ => (coefficient a i.val).property) (hv w))).trans_le
    (binomial_minor_lower a z w)

private def grid {n : ℕ} (r : Fin n ↪o ℝ) (o : ℝ) (ho : ∀ i, o<r i) : ContrastGrid n :=
  OrderEmbedding.ofStrictMono (fun i => ⟨contrast (r i) o,by
    have h := ordered_contrast o (ho i)
    exact ⟨by simpa [contrast] using h,(abs_lt.mp (contrast_inside _ _)).2⟩⟩)
    ((ordered_contrast o).comp r.strictMono)

/-- Cross minors are strictly positive for all positive real powers and
all independent ordered log-rate grids, including noninteger powers. -/
theorem fractional_cross_det_pos (a : Shape) {n : ℕ} (r s : Fin n ↪o ℝ) :
    0<(Matrix.of fun i j => (coherence (r i) (s j))^a.val).det := by
  cases n with
  | zero => simp
  | succ n =>
    let o := min (r 0) (s 0)-1
    have hr (i) : o<r i := lt_of_lt_of_le (by dsimp [o]; linarith only [min_le_left (r 0) (s 0)])
      (r.monotone (Fin.zero_le i))
    have hs (i) : o<s i := lt_of_lt_of_le (by dsimp [o]; linarith only [min_le_right (r 0) (s 0)])
      (s.monotone (Fin.zero_le i))
    let z := grid r o hr
    let w := grid s o hs
    let row := fun i => (coherence (r i) o)^a.val
    let col := fun j => (coherence (s j) o)^a.val
    have M : (Matrix.of fun i j => (coherence (r i) (s j))^a.val)=
        Matrix.of fun i j => row i*(Matrix.of fun u v => col v*disk a z w u v) i j := by
      ext i j
      let d := 1-(z i).val*(w j).val
      have hd : 0<d := sub_pos.mpr (product_lt_one (z i) (w j))
      have schur := coherence_schur_contrast (r i) (s j) o
      rw [coherence_symm o (s j)] at schur
      have he : coherence (r i) (s j)=coherence (r i) o*coherence (s j) o/d := by
        apply (eq_div_iff hd.ne').mpr
        change _*(1-contrast (r i) o*contrast (s j) o)=_
        linear_combination schur
      change (coherence (r i) (s j))^a.val=row i*(col j*(1/d^a.val))
      rw [he,Real.div_rpow (mul_nonneg (coherence_pos _ _).le (coherence_pos _ _).le) hd.le,
        Real.mul_rpow (coherence_pos _ _).le (coherence_pos _ _).le]
      unfold row col
      ring
    rw [M,det_mul_column,det_mul_row]
    exact mul_pos (prod_pos fun i _ => Real.rpow_pos_of_pos (coherence_pos _ _) _) (mul_pos
      (prod_pos fun j _ => Real.rpow_pos_of_pos (coherence_pos _ _) _) (disk_positive a z w))

/-- The Hellinger affinity matrix of two independently ordered Gamma
families of common shape is strictly totally positive. -/
theorem gamma_affinity_cross_det_pos (a : Shape) {n : ℕ} (r s : Fin n ↪o ℝ) :
    0<(Matrix.of fun i j => ∫ x : ℝ, Real.sqrt (density a (r i) x)*Real.sqrt (density a (s j) x)).det := by
  simp only [hellinger_mass]
  exact fractional_cross_det_pos a r s

/-- Every entry of the inverse affinity matrix has its strict checkerboard
sign. The formula applies to two different ordered lists of rates. -/
theorem fractional_inverse_checkerboard (a : Shape) {n : ℕ} (r s : Fin (n+1) ↪o ℝ)
    (i j : Fin (n+1)) :
    0<(-1:ℝ)^(j.val+i.val)*(Matrix.of fun u v => (coherence (r u) (s v))^a.val)⁻¹ i j := by
  let M := Matrix.of fun u v => (coherence (r u) (s v))^a.val
  have hp := fractional_cross_det_pos a r s
  have hm : 0<(M.submatrix j.succAbove i.succAbove).det :=
    fractional_cross_det_pos a ((Fin.succAboveOrderEmb j).trans r) ((Fin.succAboveOrderEmb i).trans s)
  change 0<(-1:ℝ)^(j.val+i.val)*M⁻¹ i j
  rw [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,adjugate_fin_succ_eq_det_submatrix,Ring.inverse_eq_inv]
  have square : (-1:ℝ)^(j.val+i.val)*(-1)^(j.val+i.val)=1 := by rw [← mul_pow]; simp
  calc
    0 < M.det⁻¹*(M.submatrix j.succAbove i.succAbove).det := mul_pos (inv_pos.mpr hp) hm
    _ = _ := by
      conv_lhs => rw [← one_mul (M.det⁻¹*_),← square]
      ring

#print axioms binomial_minor_lower
#print axioms fractional_cross_det_pos
#print axioms gamma_affinity_cross_det_pos
#print axioms fractional_inverse_checkerboard
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.GammaProbes
