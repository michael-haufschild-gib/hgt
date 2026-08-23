import GaloisForLFunctions.RHTower.CompletedPrimeGammaMomentFarRightAsymptotic
import GaloisForLFunctions.HTGeometry.MomentInnerProduct
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Completed prime--Gamma Hankel far-right anchor

The scalar completed-source asymptotic is promoted to every fixed Hankel determinant.  The signed
limit sequence

`(-1)^k / (2(2k+1)) = (1/2) ∫₀¹ (-t²)^k dt`

is a strictly positive moment form: a nonzero polynomial cannot vanish on the infinite image of
`t ↦ -t²`.  Entrywise convergence therefore gives eventual positive definiteness of the normalized
completed-source Hankel blocks.  An exact positive diagonal congruence transfers positivity to the
original blocks, while its determinant gives the paper's exponent `2n²-n` and exact determinant
limit.
-/

open Filter Matrix MeasureTheory Polynomial Set Topology
open scoped BigOperators Interval

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Signed Hilbert moment exposed by the completed Gamma channel at far right. -/
def completedPrimeGammaFarRightMoment (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k / (2 * (2 * k + 1))

/-- The signed Hilbert moment matrix which is the far-right limit of every fixed normalized
completed-source Hankel block. -/
def completedPrimeGammaFarRightHankelMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  _root_.HTGeometry.momentHankelMatrix completedPrimeGammaFarRightMoment n

/-- Negated squaring is injective on the positive unit interval. -/
theorem injOn_neg_sq_Ioo_zero_one :
    Set.InjOn (fun x : ℝ => -(x ^ 2)) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have hfactor : (x - y) * (x + y) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hdiff | hsum
  · linarith
  · exact False.elim ((add_pos hx.1 hy.1).ne' hsum)

/-- The image of the positive unit interval under negated squaring is infinite. -/
theorem infinite_neg_sq_image_Ioo_zero_one :
    ((fun x : ℝ => -(x ^ 2)) '' Set.Ioo 0 1).Infinite := by
  exact (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image injOn_neg_sq_Ioo_zero_one

/-- A nonzero real polynomial is nonzero after the `-x²` substitution somewhere in `(0,1)`. -/
theorem exists_Ioo_eval_neg_sq_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∃ x ∈ Set.Ioo (0 : ℝ) 1, p.eval (-(x ^ 2)) ≠ 0 := by
  by_contra h
  push Not at h
  have hroot :
      (fun x : ℝ => -(x ^ 2)) '' Set.Ioo 0 1 ⊆ {x : ℝ | p.IsRoot x} := by
    rintro y ⟨x, hx, rfl⟩
    exact h x hx
  exact hp (Polynomial.eq_zero_of_infinite_isRoot p
    (Set.Infinite.mono hroot infinite_neg_sq_image_Ioo_zero_one))

/-- A nonzero polynomial square has strictly positive integral after the `-x²` substitution. -/
theorem integral_Ioo_eval_neg_sq_sq_pos {p : Polynomial ℝ} (hp : p ≠ 0) :
    0 < ∫ x in (0 : ℝ)..1, (p.eval (-(x ^ 2))) ^ 2 := by
  let f : ℝ → ℝ := fun x => (p.eval (-(x ^ 2))) ^ 2
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfint : IntervalIntegrable f volume (0 : ℝ) 1 :=
    hfcont.intervalIntegrable _ _
  have hfnn : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hfnn) hfint]
  refine ⟨by norm_num, ?_⟩
  let W : Set ℝ := Set.Ioo (0 : ℝ) 1 ∩ {x : ℝ | p.eval (-(x ^ 2)) ≠ 0}
  have hWopen : IsOpen W := by
    exact isOpen_Ioo.inter (isOpen_ne.preimage (p.continuous.comp
      (continuous_neg.comp (continuous_id.pow 2))))
  have hWne : W.Nonempty := by
    obtain ⟨x, hx, hpx⟩ := exists_Ioo_eval_neg_sq_ne_zero hp
    exact ⟨x, hx, hpx⟩
  have hWsub : W ⊆ Function.support f ∩ Set.Ioc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨Function.mem_support.mpr (pow_ne_zero 2 hx.2), ⟨hx.1.1, hx.1.2.le⟩⟩
  exact (hWopen.measure_pos volume hWne).trans_le (measure_mono hWsub)

/-- The signed Hilbert sequence is exactly half the uniform moment functional after negated
squaring. -/
theorem momentFunctional_completedPrimeGammaFarRightMoment_eq_integral
    (p : Polynomial ℝ) :
    _root_.HTGeometry.momentFunctional completedPrimeGammaFarRightMoment p =
      (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1, p.eval (-(x ^ 2))) := by
  rw [_root_.HTGeometry.momentFunctional_eq_support_sum]
  have heval (x : ℝ) :
      p.eval (-(x ^ 2)) =
        ∑ k ∈ p.support, p.coeff k * ((-1 : ℝ) ^ k * x ^ (2 * k)) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    calc
      (-(x ^ 2)) ^ k = ((-1 : ℝ) * x ^ 2) ^ k := by ring
      _ = (-1 : ℝ) ^ k * (x ^ 2) ^ k := by rw [mul_pow]
      _ = (-1 : ℝ) ^ k * x ^ (2 * k) := by rw [← pow_mul]
  rw [intervalIntegral.integral_congr (fun x _ => heval x)]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow]
    simp [completedPrimeGammaFarRightMoment]
    field_simp
  · intro k _
    exact ((continuous_const.mul (continuous_id.pow (2 * k))).const_mul _).intervalIntegrable _ _

/-- The signed Hilbert sequence defines a strict moment form on every nonzero real polynomial. -/
theorem completedPrimeGammaFarRightMoment_positiveMomentForm :
    _root_.HTGeometry.PositiveMomentForm completedPrimeGammaFarRightMoment := by
  refine ⟨fun p hp => ?_⟩
  rw [_root_.HTGeometry.momentInner_self,
    momentFunctional_completedPrimeGammaFarRightMoment_eq_integral]
  simp only [Polynomial.eval_pow]
  exact mul_pos (by norm_num) (integral_Ioo_eval_neg_sq_sq_pos hp)

/-- Every signed Hilbert limit block is strictly positive definite. -/
theorem completedPrimeGammaFarRightHankelMatrix_posDef (n : ℕ) :
    (completedPrimeGammaFarRightHankelMatrix n).PosDef :=
  _root_.HTGeometry.positiveMomentForm_iff_momentHankelMatrix_posDef.mp
    completedPrimeGammaFarRightMoment_positiveMomentForm n

/-- Every signed Hilbert limit determinant is strictly positive. -/
theorem completedPrimeGammaFarRightHankelMatrix_det_pos (n : ℕ) :
    0 < (completedPrimeGammaFarRightHankelMatrix n).det :=
  (completedPrimeGammaFarRightHankelMatrix_posDef n).det_pos

/-- Real completed-source Hankel block on the positive-real axis. -/
def completedOddLogDerivRealHankelMatrix (x : ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (completedOddLogDerivMoment (x : ℂ) ((i : ℕ) + (j : ℕ))).re

/-- Entrywise normalization retaining the completed Gamma channel. -/
def completedOddLogDerivFarRightNormalizedMoment (x : ℝ) (k : ℕ) : ℝ :=
  x ^ (2 * k + 1) * (completedOddLogDerivMoment (x : ℂ) k).re

/-- Entrywise normalization retaining the completed Gamma channel. -/
def completedOddLogDerivFarRightNormalizedHankelMatrix (x : ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  _root_.HTGeometry.momentHankelMatrix
    (completedOddLogDerivFarRightNormalizedMoment x) n

/-- Real mass dilation underlying the determinant normalization. -/
def completedOddLogDerivFarRightDilation (x : ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => x ^ (2 * (i : ℕ)))

theorem completedOddLogDerivFarRightNormalizedHankelMatrix_isHermitian (x : ℝ) (n : ℕ) :
    (completedOddLogDerivFarRightNormalizedHankelMatrix x n).IsHermitian :=
  _root_.HTGeometry.momentHankelMatrix_isHermitian _ _

/-- Each normalized matrix entry converges to its signed Hilbert moment. -/
theorem tendsto_completedOddLogDerivFarRightNormalizedHankelMatrix_apply
    {n : ℕ} (i j : Fin n) :
    Tendsto
      (fun x : ℝ => completedOddLogDerivFarRightNormalizedHankelMatrix x n i j)
      atTop
      (nhds (completedPrimeGammaFarRightHankelMatrix n i j)) := by
  simpa [completedOddLogDerivFarRightNormalizedHankelMatrix,
    completedOddLogDerivFarRightNormalizedMoment,
    completedPrimeGammaFarRightHankelMatrix, _root_.HTGeometry.momentHankelMatrix,
    completedPrimeGammaFarRightMoment] using
    (completedOddLogDerivMomentFarRightAsymptotic ((i : ℕ) + (j : ℕ)))

/-- Every fixed normalized completed-source Hankel block is eventually positive definite. -/
theorem completedOddLogDerivFarRightNormalizedHankelMatrix_posDef_eventually (n : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (completedOddLogDerivFarRightNormalizedHankelMatrix x n).PosDef := by
  exact posDef_eventually_of_tendsto
    (completedPrimeGammaFarRightHankelMatrix_posDef n)
    (Filter.Eventually.of_forall fun x =>
      completedOddLogDerivFarRightNormalizedHankelMatrix_isHermitian x n)
    tendsto_completedOddLogDerivFarRightNormalizedHankelMatrix_apply

/-- Exact positive diagonal congruence between normalized and original real Hankel blocks. -/
theorem completedOddLogDerivFarRightNormalizedHankelMatrix_eq_congruence
    (x : ℝ) (n : ℕ) :
    completedOddLogDerivFarRightNormalizedHankelMatrix x n =
      x • (completedOddLogDerivFarRightDilation x n *
        completedOddLogDerivRealHankelMatrix x n *
          completedOddLogDerivFarRightDilation x n) := by
  ext i j
  simp [completedOddLogDerivFarRightNormalizedHankelMatrix,
    completedOddLogDerivFarRightNormalizedMoment, _root_.HTGeometry.momentHankelMatrix,
    completedOddLogDerivFarRightDilation, completedOddLogDerivRealHankelMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal, pow_add]
  ring

/-- The mass dilation is invertible away from zero. -/
theorem completedOddLogDerivFarRightDilation_isUnit {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    IsUnit (completedOddLogDerivFarRightDilation x n) := by
  rw [completedOddLogDerivFarRightDilation, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hx)

/-- Every original completed-source real Hankel block is positive definite sufficiently far
right. -/
theorem completedOddLogDerivRealHankelMatrix_posDef_eventually (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, (completedOddLogDerivRealHankelMatrix x n).PosDef := by
  filter_upwards [completedOddLogDerivFarRightNormalizedHankelMatrix_posDef_eventually n,
    eventually_gt_atTop (0 : ℝ)] with x hB hx
  let D := completedOddLogDerivFarRightDilation x n
  let H := completedOddLogDerivRealHankelMatrix x n
  have hfactor : completedOddLogDerivFarRightNormalizedHankelMatrix x n =
      x • (D * H * D) := completedOddLogDerivFarRightNormalizedHankelMatrix_eq_congruence x n
  rw [hfactor] at hB
  have hconjScaled := hB.smul (inv_pos.mpr hx)
  have hconj : (D * H * D).PosDef := by
    simpa [smul_smul, inv_mul_cancel₀ hx.ne'] using hconjScaled
  have hstar : star D = D := by
    rw [star_eq_conjTranspose]
    simp [D, completedOddLogDerivFarRightDilation]
  have hconj' : (star D * H * D).PosDef := by
    simpa only [hstar] using hconj
  have hunit : IsUnit D := completedOddLogDerivFarRightDilation_isUnit hx.ne' n
  exact hunit.posDef_star_left_conjugate_iff.mp hconj'

/-- Eventual strict positivity of every fixed original real completed-source determinant. -/
theorem completedOddLogDerivRealHankelMatrix_det_pos_eventually (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 < (completedOddLogDerivRealHankelMatrix x n).det := by
  filter_upwards [completedOddLogDerivRealHankelMatrix_posDef_eventually n] with x hx
  exact hx.det_pos

/-- Sum of the even dilation exponents on a `Fin n` block. -/
private theorem sum_fin_two_val (n : ℕ) :
    ∑ i : Fin n, 2 * (i : ℕ) = n * (n - 1) := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      cases n with
      | zero => simp
      | succ m => simp; ring

/-- Determinant of the mass dilation. -/
theorem det_completedOddLogDerivFarRightDilation (x : ℝ) (n : ℕ) :
    (completedOddLogDerivFarRightDilation x n).det = x ^ (n * (n - 1)) := by
  rw [completedOddLogDerivFarRightDilation, Matrix.det_diagonal]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [sum_fin_two_val]

/-- Exact determinant scaling; the exponent is the paper's `2n²-n`. -/
theorem det_completedOddLogDerivFarRightNormalizedHankelMatrix
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (completedOddLogDerivFarRightNormalizedHankelMatrix x n).det =
      x ^ (2 * n ^ 2 - n) * (completedOddLogDerivRealHankelMatrix x n).det := by
  rw [completedOddLogDerivFarRightNormalizedHankelMatrix_eq_congruence,
    Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
    det_completedOddLogDerivFarRightDilation]
  simp only [Fintype.card_fin]
  have hexp : n + n * (n - 1) + n * (n - 1) = 2 * n ^ 2 - n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hsq : m + 1 ≤ (m + 1) ^ 2 := by
      simpa only [pow_two] using Nat.le_mul_of_pos_right (m + 1) (Nat.succ_pos m)
    have hle : m + 1 ≤ 2 * (m + 1) ^ 2 := by omega
    symm
    apply (Nat.sub_eq_iff_eq_add hle).2
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    ring
  calc
    x ^ n * (x ^ (n * (n - 1)) * (completedOddLogDerivRealHankelMatrix x n).det *
        x ^ (n * (n - 1))) =
        x ^ (n + n * (n - 1) + n * (n - 1)) *
          (completedOddLogDerivRealHankelMatrix x n).det := by
            rw [pow_add, pow_add]
            ring
    _ = x ^ (2 * n ^ 2 - n) *
        (completedOddLogDerivRealHankelMatrix x n).det := by rw [hexp]

/-- Entrywise convergence upgraded through continuity of the finite determinant. -/
theorem tendsto_det_completedOddLogDerivFarRightNormalizedHankelMatrix (n : ℕ) :
    Tendsto
      (fun x : ℝ => (completedOddLogDerivFarRightNormalizedHankelMatrix x n).det)
      atTop
      (nhds (completedPrimeGammaFarRightHankelMatrix n).det) := by
  have hmatrix : Tendsto
      (fun x : ℝ => completedOddLogDerivFarRightNormalizedHankelMatrix x n)
      atTop (nhds (completedPrimeGammaFarRightHankelMatrix n)) := by
    change Tendsto
      (fun x : ℝ => fun i j => completedOddLogDerivFarRightNormalizedHankelMatrix x n i j)
      atTop (nhds (fun i j => completedPrimeGammaFarRightHankelMatrix n i j))
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro j
    exact tendsto_completedOddLogDerivFarRightNormalizedHankelMatrix_apply i j
  change Tendsto
    ((fun M : Matrix (Fin n) (Fin n) ℝ => M.det) ∘
      fun x : ℝ => completedOddLogDerivFarRightNormalizedHankelMatrix x n)
    atTop (nhds (completedPrimeGammaFarRightHankelMatrix n).det)
  exact continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix

/-- **Exact completed prime--Gamma Hankel far-right determinant anchor.** -/
theorem completedOddLogDerivRealHankelDetFarRightAsymptotic
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun x : ℝ => x ^ (2 * n ^ 2 - n) *
        (completedOddLogDerivRealHankelMatrix x n).det)
      atTop
      (nhds (completedPrimeGammaFarRightHankelMatrix n).det) := by
  apply (tendsto_det_completedOddLogDerivFarRightNormalizedHankelMatrix n).congr'
  filter_upwards with x
  exact det_completedOddLogDerivFarRightNormalizedHankelMatrix hn x

/-- The complex completed-source determinant is the scalar extension of its real-axis matrix. -/
theorem completedOddLogDerivHankelDet_ofReal_re (n : ℕ) (x : ℝ) :
    (completedOddLogDerivHankelDet n (x : ℂ)).re =
      (completedOddLogDerivRealHankelMatrix x n).det := by
  have hmatrix : completedOddLogDerivHankelMatrix n (x : ℂ) =
      (algebraMap ℝ ℂ).mapMatrix (completedOddLogDerivRealHankelMatrix x n) := by
    ext i j
    apply Complex.ext
    · simp [completedOddLogDerivHankelMatrix, completedOddLogDerivRealHankelMatrix]
    · simp [completedOddLogDerivHankelMatrix, completedOddLogDerivRealHankelMatrix,
        completedOddLogDerivMoment_ofReal_im]
  rw [completedOddLogDerivHankelDet, hmatrix, ← RingHom.map_det]
  simp

/-- Exact paper form of the determinant limit for the complex completed-source determinant. -/
theorem completedOddLogDerivHankelDetFarRightAsymptotic
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun x : ℝ => x ^ (2 * n ^ 2 - n) *
        (completedOddLogDerivHankelDet n (x : ℂ)).re)
      atTop
      (nhds (completedPrimeGammaFarRightHankelMatrix n).det) := by
  simpa only [completedOddLogDerivHankelDet_ofReal_re] using
    completedOddLogDerivRealHankelDetFarRightAsymptotic hn

/-- **Eventual completed prime--Gamma Hankel positivity.** Every fixed leading determinant is
strictly positive sufficiently far to the right. -/
theorem completedOddLogDerivHankelDet_ofReal_re_pos_eventually (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 < (completedOddLogDerivHankelDet n (x : ℂ)).re := by
  filter_upwards [completedOddLogDerivRealHankelMatrix_det_pos_eventually n] with x hx
  simpa only [completedOddLogDerivHankelDet_ofReal_re] using hx

end

end RHTower
