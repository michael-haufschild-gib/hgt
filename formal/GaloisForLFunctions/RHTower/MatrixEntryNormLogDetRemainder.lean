import GaloisForLFunctions.HilbertMetric.DeterminantCurvatureJet
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# The determinant-level Taylor remainder: `log det(1 + N) = tr N − ½ tr N² + O(‖N‖³)`

For a real square matrix `N` with `ℓ¹` entry norm `‖N‖₁ = Σ_{i,j} |N i j| < 1` we prove the
explicit third-order remainder bound

  `|log det(1 + N) − tr N + ½ tr(N N)| ≤ d (d + 1) ‖N‖₁³ / (1 − ‖N‖₁)²`,  `d = card ι`,

by two mean-value estimates along the path `t ↦ log det(1 + tN)` on `[0, 1]`: its derivative is
`tr((1+tN)⁻¹ N)`, its second derivative is `−tr((1+tN)⁻¹ N (1+tN)⁻¹ N)`, and the second derivative
is Lipschitz at `0` with the Neumann bound `‖(1+tN)⁻¹‖₁ ≤ d/(1 − t‖N‖₁)`.

The decomposition form `N = M₁ + M₂ + E` (first-order, second-order and third-order pieces of a
perturbed Gram matrix) turns this into the statement that `log det(1 + N)` equals the second-order
jet `tr M₁ + tr M₂ − ½ tr M₁²` up to an explicit third-order remainder.  Everything is elementary
finite-sum analysis; no operator-norm or Banach-algebra machinery is used.
-/

namespace RHTower.MatrixLogDet

open Matrix Finset Set GaloisForLFunctions.HilbertMetric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `ℓ¹` entry norm `Σ_{i,j} |A i j|`. -/
noncomputable def entryNorm (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, |A i j|

theorem entryNorm_nonneg (A : Matrix ι ι ℝ) : 0 ≤ entryNorm A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem row_sum_le_entryNorm (A : Matrix ι ι ℝ) (i : ι) : ∑ j, |A i j| ≤ entryNorm A :=
  Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem abs_apply_le_entryNorm (A : Matrix ι ι ℝ) (i j : ι) : |A i j| ≤ entryNorm A :=
  (Finset.single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)).trans (row_sum_le_entryNorm A i)

theorem abs_trace_le_entryNorm (A : Matrix ι ι ℝ) : |Matrix.trace A| ≤ entryNorm A := by
  unfold Matrix.trace entryNorm
  calc |∑ i, A.diag i| ≤ ∑ i, |A.diag i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j| := Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem entryNorm_mul_le (A B : Matrix ι ι ℝ) : entryNorm (A * B) ≤ entryNorm A * entryNorm B := by
  unfold entryNorm
  calc ∑ i, ∑ k, |(A * B) i k| ≤ ∑ i, ∑ k, ∑ j, |A i j| * |B j k| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        rw [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ = ∑ i, ∑ j, |A i j| * ∑ k, |B j k| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |A i j| * (∑ j', ∑ k, |B j' k|) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (row_sum_le_entryNorm B j) (abs_nonneg _)
    _ = (∑ i, ∑ j, |A i j|) * (∑ j', ∑ k, |B j' k|) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]

theorem entryNorm_add_le (A B : Matrix ι ι ℝ) : entryNorm (A + B) ≤ entryNorm A + entryNorm B := by
  unfold entryNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => abs_add_le _ _

theorem entryNorm_neg (A : Matrix ι ι ℝ) : entryNorm (-A) = entryNorm A := by
  unfold entryNorm
  simp [abs_neg]

theorem entryNorm_sub_le (A B : Matrix ι ι ℝ) : entryNorm (A - B) ≤ entryNorm A + entryNorm B := by
  rw [sub_eq_add_neg]
  exact (entryNorm_add_le _ _).trans (by rw [entryNorm_neg])

theorem entryNorm_smul (c : ℝ) (A : Matrix ι ι ℝ) : entryNorm (c • A) = |c| * entryNorm A := by
  unfold entryNorm
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem entryNorm_one : entryNorm (1 : Matrix ι ι ℝ) = Fintype.card ι := by
  unfold entryNorm
  simp [Matrix.one_apply, apply_ite abs]

theorem entryNorm_sum_le {κ : Type*} (s : Finset κ) (A : κ → Matrix ι ι ℝ) :
    entryNorm (∑ a ∈ s, A a) ≤ ∑ a ∈ s, entryNorm (A a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [entryNorm]
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc]
    exact (entryNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem entryNorm_le_of_abs_apply_le {A : Matrix ι ι ℝ} {ρ : ℝ} (h : ∀ i j, |A i j| ≤ ρ) :
    entryNorm A ≤ (Fintype.card ι : ℝ) ^ 2 * ρ := by
  unfold entryNorm
  calc ∑ i, ∑ j, |A i j| ≤ ∑ i : ι, ∑ j : ι, ρ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = (Fintype.card ι : ℝ) ^ 2 * ρ := by simp [Finset.sum_const, Finset.card_univ]; ring

/-! ## Invertibility and the Neumann bound -/

theorem det_one_add_ne_zero {N : Matrix ι ι ℝ} (h : entryNorm N < 1) : (1 + N).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hne : ∃ i, v i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hv (funext hall)
  obtain ⟨i₀, hi₀⟩ := hne
  have hnonempty : (Finset.univ : Finset ι).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) hnonempty
  have hmpos : 0 < |v m| := lt_of_lt_of_le (abs_pos.mpr hi₀) (hm i₀ (Finset.mem_univ _))
  have hrow : v m + ∑ j, N m j * v j = 0 := by
    have hv' : v + N *ᵥ v = 0 := by
      have := hmul
      rwa [Matrix.add_mulVec, Matrix.one_mulVec] at this
    have := congrFun hv' m
    simpa [Matrix.mulVec, dotProduct] using this
  have hbound : |v m| ≤ entryNorm N * |v m| := by
    calc |v m| = |∑ j, N m j * v j| := by
          rw [show v m = -∑ j, N m j * v j by linarith, abs_neg]
      _ ≤ ∑ j, |N m j| * |v j| := (Finset.abs_sum_le_sum_abs _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun j _ => abs_mul _ _))
      _ ≤ ∑ j, |N m j| * |v m| := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hm j (Finset.mem_univ _)) (abs_nonneg _)
      _ = (∑ j, |N m j|) * |v m| := by rw [Finset.sum_mul]
      _ ≤ entryNorm N * |v m| :=
          mul_le_mul_of_nonneg_right (row_sum_le_entryNorm N m) (abs_nonneg _)
  have : entryNorm N * |v m| < 1 * |v m| := mul_lt_mul_of_pos_right h hmpos
  linarith

theorem entryNorm_inv_one_add_le {N : Matrix ι ι ℝ} (h : entryNorm N < 1) :
    entryNorm (1 + N)⁻¹ ≤ (Fintype.card ι : ℝ) / (1 - entryNorm N) := by
  have hdet := det_one_add_ne_zero h
  have hunit : IsUnit (1 + N).det := isUnit_iff_ne_zero.mpr hdet
  have hR : (1 + N) * (1 + N)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have h1 : (1 + N)⁻¹ + N * (1 + N)⁻¹ = 1 := by
    have := hR
    rwa [Matrix.add_mul, Matrix.one_mul] at this
  have h2 : (1 + N)⁻¹ = 1 - N * (1 + N)⁻¹ := eq_sub_of_add_eq h1
  have h3 : entryNorm (1 + N)⁻¹ ≤ Fintype.card ι + entryNorm N * entryNorm (1 + N)⁻¹ := by
    calc entryNorm (1 + N)⁻¹ = entryNorm (1 - N * (1 + N)⁻¹) := congrArg entryNorm h2
      _ ≤ entryNorm 1 + entryNorm (N * (1 + N)⁻¹) := entryNorm_sub_le _ _
      _ ≤ _ := by
          rw [entryNorm_one]
          exact add_le_add le_rfl (entryNorm_mul_le _ _)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [entryNorm_nonneg (1 + N)⁻¹]

theorem entryNorm_inv_one_add_sub_one_le {N : Matrix ι ι ℝ} (h : entryNorm N < 1) :
    entryNorm ((1 + N)⁻¹ - 1) ≤ entryNorm N * entryNorm (1 + N)⁻¹ := by
  have hdet := det_one_add_ne_zero h
  have hunit : IsUnit (1 + N).det := isUnit_iff_ne_zero.mpr hdet
  have hR : (1 + N) * (1 + N)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have h1 : (1 + N)⁻¹ + N * (1 + N)⁻¹ = 1 := by
    have := hR
    rwa [Matrix.add_mul, Matrix.one_mul] at this
  have h2 : (1 + N)⁻¹ - 1 = -(N * (1 + N)⁻¹) := by
    calc (1 + N)⁻¹ - 1 = (1 + N)⁻¹ - ((1 + N)⁻¹ + N * (1 + N)⁻¹) := by rw [h1]
      _ = -(N * (1 + N)⁻¹) := by abel
  rw [h2, entryNorm_neg]
  exact entryNorm_mul_le _ _

/-! ## The path `t ↦ log det(1 + tN)` -/

/-- `f(t) = log det(1 + tN)`. -/
noncomputable def logDetPath (N : Matrix ι ι ℝ) (t : ℝ) : ℝ := Real.log (1 + t • N).det

/-- `f'(t) = tr((1 + tN)⁻¹ N)`. -/
noncomputable def logDetSlope (N : Matrix ι ι ℝ) (t : ℝ) : ℝ := Matrix.trace ((1 + t • N)⁻¹ * N)

/-- `f''(t) = −tr((1 + tN)⁻¹ N (1 + tN)⁻¹ N)`. -/
noncomputable def logDetCurv (N : Matrix ι ι ℝ) (t : ℝ) : ℝ :=
  -Matrix.trace ((1 + t • N)⁻¹ * N * (1 + t • N)⁻¹ * N)

theorem hasDerivAt_path_entry (N : Matrix ι ι ℝ) (t : ℝ) (i j : ι) :
    HasDerivAt (fun s : ℝ => (1 + s • N) i j) (N i j) t := by
  have hfun : (fun s : ℝ => (1 + s • N) i j) =
      fun s => (1 : Matrix ι ι ℝ) i j + s * N i j := by
    funext s
    simp [Matrix.add_apply, Matrix.smul_apply]
  rw [hfun]
  exact ((hasDerivAt_id' t).mul_const (N i j)).const_add _ |>.congr_deriv (one_mul _)

theorem entryNorm_smul_lt_one {N : Matrix ι ι ℝ} (h : entryNorm N < 1) {t : ℝ} (ht : |t| ≤ 1) :
    entryNorm (t • N) < 1 := by
  rw [entryNorm_smul]
  calc |t| * entryNorm N ≤ 1 * entryNorm N :=
        mul_le_mul_of_nonneg_right ht (entryNorm_nonneg N)
    _ < 1 := by rw [one_mul]; exact h

theorem hasDerivAt_logDetPath (N : Matrix ι ι ℝ) {t : ℝ} (hdet : (1 + t • N).det ≠ 0) :
    HasDerivAt (logDetPath N) (logDetSlope N t) t := by
  have h := hasDerivAt_matrixDet (fun s => 1 + s • N) N t (fun i j => hasDerivAt_path_entry N t i j)
  rw [detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet] at h
  have h2 := h.log hdet
  refine h2.congr_deriv ?_
  unfold logDetSlope
  field_simp

theorem hasDerivAt_logDetSlope (N : Matrix ι ι ℝ) {t : ℝ} (hdet : (1 + t • N).det ≠ 0) :
    HasDerivAt (logDetSlope N) (logDetCurv N t) t := by
  have hinv := hasDerivAt_matrix_inv (fun s => 1 + s • N) N t
    (fun i j => hasDerivAt_path_entry N t i j) hdet
  have hfun : logDetSlope N = fun s => ∑ i, ∑ k, (1 + s • N)⁻¹ i k * N k i := by
    funext s
    unfold logDetSlope
    rfl
  rw [hfun]
  have hsum : HasDerivAt (fun s => ∑ i, ∑ k, (1 + s • N)⁻¹ i k * N k i)
      (∑ i, ∑ k, -((1 + t • N)⁻¹ * N * (1 + t • N)⁻¹) i k * N k i) t := by
    refine HasDerivAt.fun_sum (𝕜 := ℝ) fun i _ => HasDerivAt.fun_sum (𝕜 := ℝ) fun k _ => ?_
    exact (hinv i k).mul_const (N k i)
  refine hsum.congr_deriv ?_
  unfold logDetCurv
  show _ = -(∑ i, ∑ k, ((1 + t • N)⁻¹ * N * (1 + t • N)⁻¹) i k * N k i)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem logDetPath_zero (N : Matrix ι ι ℝ) : logDetPath N 0 = 0 := by
  unfold logDetPath
  simp

theorem logDetSlope_zero (N : Matrix ι ι ℝ) : logDetSlope N 0 = Matrix.trace N := by
  unfold logDetSlope
  simp

theorem logDetCurv_zero (N : Matrix ι ι ℝ) : logDetCurv N 0 = -Matrix.trace (N * N) := by
  unfold logDetCurv
  simp

/-- The explicit third-order constant `d (d+1) η³ / (1 − η)²`. -/
noncomputable def remainderConst (d η : ℝ) : ℝ := d * (d + 1) * η ^ 3 / (1 - η) ^ 2

/-- **Lipschitz bound on the second derivative at `0`.** -/
theorem abs_logDetCurv_sub_zero_le {N : Matrix ι ι ℝ} (h : entryNorm N < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |logDetCurv N t - logDetCurv N 0| ≤
      t * remainderConst (Fintype.card ι) (entryNorm N) := by
  set η := entryNorm N with hη
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hη0 : 0 ≤ η := entryNorm_nonneg N
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have htN : entryNorm (t • N) < 1 := entryNorm_smul_lt_one h (by rw [abs_of_nonneg ht0]; exact ht1)
  have htN' : entryNorm (t • N) = t * η := by rw [entryNorm_smul, abs_of_nonneg ht0]
  set R := (1 + t • N)⁻¹ with hR
  have hRle : entryNorm R ≤ d / (1 - t * η) := by
    have := entryNorm_inv_one_add_le htN
    rwa [htN'] at this
  have hR1 : entryNorm (R - 1) ≤ t * η * entryNorm R := by
    have := entryNorm_inv_one_add_sub_one_le htN
    rwa [htN'] at this
  have h1tη : 1 - η ≤ 1 - t * η := by nlinarith
  have h1η : 0 < 1 - η := by linarith
  have hRle' : entryNorm R ≤ d / (1 - η) := hRle.trans (div_le_div_of_nonneg_left hd0 h1η h1tη)
  have hR1' : entryNorm (R - 1) ≤ t * η * (d / (1 - η)) :=
    hR1.trans (mul_le_mul_of_nonneg_left hRle' (by positivity))
  -- the algebraic identity R N R N − N N = (R − 1) N R N + N (R − 1) N
  have hid : R * N * R * N - N * N = (R - 1) * N * R * N + N * (R - 1) * N := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have hcurv : logDetCurv N t - logDetCurv N 0 = -Matrix.trace (R * N * R * N - N * N) := by
    rw [logDetCurv_zero]
    unfold logDetCurv
    rw [Matrix.trace_sub]
    ring
  rw [hcurv, abs_neg]
  refine (abs_trace_le_entryNorm _).trans ?_
  rw [hid]
  have hA : entryNorm ((R - 1) * N * R * N) ≤ entryNorm (R - 1) * η * entryNorm R * η := by
    calc entryNorm ((R - 1) * N * R * N) ≤ entryNorm ((R - 1) * N * R) * entryNorm N :=
          entryNorm_mul_le _ _
      _ ≤ entryNorm ((R - 1) * N) * entryNorm R * entryNorm N :=
          mul_le_mul_of_nonneg_right (entryNorm_mul_le _ _) (entryNorm_nonneg N)
      _ ≤ entryNorm (R - 1) * entryNorm N * entryNorm R * entryNorm N :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (entryNorm_mul_le _ _) (entryNorm_nonneg R))
            (entryNorm_nonneg N)
  have hB : entryNorm (N * (R - 1) * N) ≤ η * entryNorm (R - 1) * η := by
    calc entryNorm (N * (R - 1) * N) ≤ entryNorm (N * (R - 1)) * entryNorm N := entryNorm_mul_le _ _
      _ ≤ entryNorm N * entryNorm (R - 1) * entryNorm N :=
          mul_le_mul_of_nonneg_right (entryNorm_mul_le _ _) (entryNorm_nonneg N)
  have hsum := (entryNorm_add_le ((R - 1) * N * R * N) (N * (R - 1) * N)).trans (add_le_add hA hB)
  refine hsum.trans ?_
  have hR1nn : 0 ≤ entryNorm (R - 1) := entryNorm_nonneg _
  have hRnn : 0 ≤ entryNorm R := entryNorm_nonneg _
  -- entryNorm (R−1) η² (entryNorm R + 1) ≤ t η³ (d/(1−η)) (d/(1−η) + 1) ≤ t d (d+1) η³/(1−η)²
  have hstep : entryNorm (R - 1) * η * entryNorm R * η + η * entryNorm (R - 1) * η ≤
      (t * η * (d / (1 - η))) * η ^ 2 * (d / (1 - η) + 1) := by
    have e1 : entryNorm (R - 1) * η * entryNorm R * η + η * entryNorm (R - 1) * η =
        entryNorm (R - 1) * η ^ 2 * (entryNorm R + 1) := by ring
    rw [e1]
    have hpos : 0 ≤ η ^ 2 * (entryNorm R + 1) := by positivity
    calc entryNorm (R - 1) * η ^ 2 * (entryNorm R + 1) ≤
          (t * η * (d / (1 - η))) * η ^ 2 * (entryNorm R + 1) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hR1' hpos
      _ ≤ (t * η * (d / (1 - η))) * η ^ 2 * (d / (1 - η) + 1) := by
          gcongr
  refine hstep.trans ?_
  unfold remainderConst
  have hd1 : d / (1 - η) + 1 ≤ (d + 1) / (1 - η) := by
    rw [div_add_one h1η.ne', div_le_div_iff_of_pos_right h1η]
    linarith
  calc (t * η * (d / (1 - η))) * η ^ 2 * (d / (1 - η) + 1) ≤
        (t * η * (d / (1 - η))) * η ^ 2 * ((d + 1) / (1 - η)) := by gcongr
    _ = t * (d * (d + 1) * η ^ 3 / (1 - η) ^ 2) := by
        field_simp

theorem remainderConst_nonneg {d η : ℝ} (hd : 0 ≤ d) (hη : 0 ≤ η) : 0 ≤ remainderConst d η := by
  unfold remainderConst
  positivity

/-! ## Mean-value estimates along the path -/

theorem det_path_ne_zero {N : Matrix ι ι ℝ} (h : entryNorm N < 1) {t : ℝ} (ht : |t| ≤ 1) :
    (1 + t • N).det ≠ 0 :=
  det_one_add_ne_zero (entryNorm_smul_lt_one h ht)

theorem continuous_det_path (N : Matrix ι ι ℝ) : Continuous (fun t : ℝ => (1 + t • N).det) := by
  apply Continuous.matrix_det
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- **The determinant is positive**: the path never vanishes and starts at `1`. -/
theorem det_one_add_pos {N : Matrix ι ι ℝ} (h : entryNorm N < 1) : 0 < (1 + N).det := by
  by_contra hneg
  push_neg at hneg
  have hcont : ContinuousOn (fun t : ℝ => (1 + t • N).det) (Icc 0 1) :=
    (continuous_det_path N).continuousOn
  have hmem : (0 : ℝ) ∈ Icc ((fun t : ℝ => (1 + t • N).det) 1) ((fun t : ℝ => (1 + t • N).det) 0) := by
    simp only [one_smul, zero_smul, add_zero, Matrix.det_one]
    exact ⟨hneg, zero_le_one⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  exact det_path_ne_zero h (by rw [abs_of_nonneg hs.1]; exact hs.2) hs0

theorem abs_logDetSlope_sub_le {N : Matrix ι ι ℝ} (h : entryNorm N < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |logDetSlope N t - logDetSlope N 0 - t * logDetCurv N 0| ≤
      t * remainderConst (Fintype.card ι) (entryNorm N) := by
  set M := remainderConst (Fintype.card ι) (entryNorm N) with hM
  have hM0 : 0 ≤ M := remainderConst_nonneg (by positivity) (entryNorm_nonneg N)
  set g : ℝ → ℝ := fun s => logDetSlope N s - logDetSlope N 0 - s * logDetCurv N 0 with hg
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt g (logDetCurv N s - logDetCurv N 0) (Icc 0 1) s := by
    intro s hs
    have h1 := hasDerivAt_logDetSlope N
      (det_path_ne_zero h (by rw [abs_of_nonneg hs.1]; exact hs.2))
    have h2 : HasDerivAt (fun s : ℝ => s * logDetCurv N 0) (logDetCurv N 0) s :=
      ((hasDerivAt_id' s).mul_const _).congr_deriv (one_mul _)
    exact ((h1.sub_const _).sub h2).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖logDetCurv N s - logDetCurv N 0‖ ≤ M := by
    intro s hs
    rw [Real.norm_eq_abs]
    refine (abs_logDetCurv_sub_zero_le h hs.1 hs.2.le).trans ?_
    nlinarith [hs.1, hs.2]
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t ⟨ht0, ht1⟩
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, Real.norm_eq_abs, sub_zero, mul_comm] at key
  exact key

/-- **Second-order Taylor formula with remainder along the path.** -/
theorem abs_logDetPath_sub_taylor_le {N : Matrix ι ι ℝ} (h : entryNorm N < 1) :
    |logDetPath N 1 - logDetSlope N 0 - (1 / 2) * logDetCurv N 0| ≤
      remainderConst (Fintype.card ι) (entryNorm N) := by
  set M := remainderConst (Fintype.card ι) (entryNorm N) with hM
  have hM0 : 0 ≤ M := remainderConst_nonneg (by positivity) (entryNorm_nonneg N)
  set F : ℝ → ℝ := fun s => logDetPath N s - logDetPath N 0 - s * logDetSlope N 0 -
    (s ^ 2 / 2) * logDetCurv N 0 with hF
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt F (logDetSlope N s - logDetSlope N 0 - s * logDetCurv N 0) (Icc 0 1) s := by
    intro s hs
    have h1 := hasDerivAt_logDetPath N
      (det_path_ne_zero h (by rw [abs_of_nonneg hs.1]; exact hs.2))
    have h2 : HasDerivAt (fun s : ℝ => s * logDetSlope N 0) (logDetSlope N 0) s :=
      ((hasDerivAt_id' s).mul_const _).congr_deriv (one_mul _)
    have h3 : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) * logDetCurv N 0) (s * logDetCurv N 0) s := by
      have := ((hasDerivAt_pow 2 s).div_const 2).mul_const (logDetCurv N 0)
      refine this.congr_deriv ?_
      simp
    exact (((h1.sub_const _).sub h2).sub h3).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖logDetSlope N s - logDetSlope N 0 - s * logDetCurv N 0‖ ≤ M := by
    intro s hs
    rw [Real.norm_eq_abs]
    refine (abs_logDetSlope_sub_le h hs.1 hs.2.le).trans ?_
    nlinarith [hs.1, hs.2]
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨zero_le_one, le_rfl⟩
  have hF0 : F 0 = 0 := by simp [hF]
  have hF1 : F 1 = logDetPath N 1 - logDetSlope N 0 - (1 / 2) * logDetCurv N 0 := by
    simp only [hF, logDetPath_zero, one_pow, one_mul, sub_zero]
  rw [hF0, sub_zero, Real.norm_eq_abs, sub_zero, mul_one, hF1] at key
  exact key

/-- **The determinant-level Taylor remainder.**
`|log det(1 + N) − tr N + ½ tr(N N)| ≤ d (d+1) ‖N‖₁³ / (1 − ‖N‖₁)²` for `‖N‖₁ < 1`. -/
theorem abs_log_det_one_add_sub_jet_le {N : Matrix ι ι ℝ} (h : entryNorm N < 1) :
    |Real.log (1 + N).det - Matrix.trace N + (1 / 2) * Matrix.trace (N * N)| ≤
      remainderConst (Fintype.card ι) (entryNorm N) := by
  have key := abs_logDetPath_sub_taylor_le h
  rw [logDetSlope_zero, logDetCurv_zero] at key
  unfold logDetPath at key
  rw [one_smul] at key
  convert key using 2
  ring

/-- **Decomposition form.** With `N = M₁ + M₂ + E`, `log det(1 + N)` equals the second-order jet
`tr M₁ + tr M₂ − ½ tr M₁²` up to the third-order remainder, the trace of `E`, and the mixed
second-order terms `M₁(M₂+E)`, `(M₂+E)²`. -/
theorem abs_log_det_sub_secondOrderJet_le (M₁ M₂ E : Matrix ι ι ℝ)
    (h : entryNorm (M₁ + M₂ + E) < 1) :
    |Real.log (1 + (M₁ + M₂ + E)).det -
        (Matrix.trace M₁ + Matrix.trace M₂ - (1 / 2) * Matrix.trace (M₁ * M₁))| ≤
      remainderConst (Fintype.card ι) (entryNorm (M₁ + M₂ + E)) + entryNorm E +
        (1 / 2) * (2 * entryNorm M₁ * entryNorm (M₂ + E) + entryNorm (M₂ + E) ^ 2) := by
  set N := M₁ + M₂ + E with hN
  set K := M₂ + E with hK
  have hNK : N = M₁ + K := by rw [hN, hK, add_assoc]
  have hmain := abs_log_det_one_add_sub_jet_le h
  have htr : Matrix.trace N = Matrix.trace M₁ + Matrix.trace M₂ + Matrix.trace E := by
    rw [hN, Matrix.trace_add, Matrix.trace_add]
  have hsq : N * N - M₁ * M₁ = M₁ * K + K * M₁ + K * K := by
    rw [hNK]
    simp only [Matrix.add_mul, Matrix.mul_add]
    abel
  have hE : |Matrix.trace E| ≤ entryNorm E := abs_trace_le_entryNorm E
  have hK2 : |Matrix.trace (N * N) - Matrix.trace (M₁ * M₁)| ≤
      2 * entryNorm M₁ * entryNorm K + entryNorm K ^ 2 := by
    rw [← Matrix.trace_sub, hsq]
    refine (abs_trace_le_entryNorm _).trans ?_
    refine (entryNorm_add_le _ _).trans ?_
    refine (add_le_add (entryNorm_add_le _ _) (entryNorm_mul_le _ _)).trans ?_
    have h1 := entryNorm_mul_le M₁ K
    have h2 := entryNorm_mul_le K M₁
    nlinarith [entryNorm_nonneg K, entryNorm_nonneg M₁]
  have hdecomp : Real.log (1 + N).det -
      (Matrix.trace M₁ + Matrix.trace M₂ - (1 / 2) * Matrix.trace (M₁ * M₁)) =
      (Real.log (1 + N).det - Matrix.trace N + (1 / 2) * Matrix.trace (N * N)) + Matrix.trace E -
        (1 / 2) * (Matrix.trace (N * N) - Matrix.trace (M₁ * M₁)) := by
    rw [htr]
    ring
  rw [hdecomp]
  have habs : |(Real.log (1 + N).det - Matrix.trace N + (1 / 2) * Matrix.trace (N * N)) +
      Matrix.trace E - (1 / 2) * (Matrix.trace (N * N) - Matrix.trace (M₁ * M₁))| ≤
      |Real.log (1 + N).det - Matrix.trace N + (1 / 2) * Matrix.trace (N * N)| + |Matrix.trace E| +
        (1 / 2) * |Matrix.trace (N * N) - Matrix.trace (M₁ * M₁)| := by
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact add_le_add (abs_add_le _ _) le_rfl
  refine habs.trans ?_
  linarith [hmain, hE, hK2]

end RHTower.MatrixLogDet
