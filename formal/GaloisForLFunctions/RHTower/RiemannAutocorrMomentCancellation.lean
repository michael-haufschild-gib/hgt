import GaloisForLFunctions.RHTower.RiemannKernelMomentCancellation

/-!
# All-order moment cancellation for the actual autocorrelation

Cancel the finite Taylor polynomial before integrating. All integral identities
use the existing integrability of actual kernel translates.
-/

open scoped BigOperators
open MeasureTheory

namespace RHTower

theorem exists_riemannAutocorr_moment_transfer_constant :
    ∃ T : ℝ, 0 < T ∧ ∀ (r : ℕ) (D : ℝ), 0 < D →
      (∀ (ι : Type) [Fintype ι] (c h : ι → ℝ) (H : ℝ),
        0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
        (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ x : ℝ,
        |∑ i, c i * riemannKernelReal (x + h i)| ≤
          D * Real.exp (-3 * |x|) * (∑ i, |c i|) * H ^ (r + 1)) →
      ∀ (ι : Type) [Fintype ι] (c h : ι → ℝ) (H : ℝ),
      0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
      (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ y : ℝ,
      |∑ i, c i * riemannAutocorr (y - h i)| ≤
        (T * D) * Real.exp (-2 * |y|) * (∑ i, |c i|) * H ^ (r + 1) := by
  obtain ⟨C, hC, hkernel⟩ := exists_riemannKernelDeriv_cubic_exp_envelope 0
  have hreal (t : ℝ) : |riemannKernelReal t| ≤ C * Real.exp (-3 * |t|) := by
    simpa only [riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal, Complex.norm_real,
      Real.norm_eq_abs, neg_mul] using hkernel t
  let I : ℝ := ∫ t : ℝ, Real.exp (-|t|)
  have hI : 0 ≤ I := integral_nonneg fun t => (Real.exp_pos _).le
  refine ⟨C * (I + 1), by positivity, ?_⟩
  intro r D hD hcancel ι _ c h H hH0 hH1 hh hm y
  let L : ℝ := ∑ i, |c i|
  have hL : 0 ≤ L := Finset.sum_nonneg fun i hi => abs_nonneg _
  let A : ℝ := C * D * Real.exp (-2 * |y|) * L * H ^ (r + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let f : ι → ℝ → ℝ := fun i t =>
    c i * (riemannKernelReal t * riemannKernelReal (t - (y - h i)))
  have hfi (i : ι) : Integrable (f i) :=
    (integrable_riemannKernelReal_mul (y - h i)).const_mul (c i)
  have heq (t : ℝ) : (∑ i, f i t) =
      riemannKernelReal t * ∑ i, c i * riemannKernelReal ((t - y) + h i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f]
    rw [show t - (y - h i) = (t - y) + h i by ring]
    ring
  have hsum : (∑ i, c i * riemannAutocorr (y - h i)) =
      ∫ t : ℝ, ∑ i, f i t := by
    rw [integral_finsetSum _ (fun i hi => hfi i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact (integral_const_mul (c i)
      (fun t => riemannKernelReal t * riemannKernelReal (t - (y - h i)))).symm
  have hpoint (t : ℝ) : |∑ i, f i t| ≤ A * Real.exp (-|t|) := by
    rw [heq, abs_mul]
    have hc := hcancel ι c h H hH0 hH1 hh hm (t - y)
    have ht : |y| ≤ |t| + |t - y| := by
      calc
        |y| = |t + (y - t)| := by congr 1; ring
        _ ≤ |t| + |y - t| := abs_add_le _ _
        _ = |t| + |t - y| := by rw [abs_sub_comm y t]
    have hexp : Real.exp (-3 * |t|) * Real.exp (-3 * |t - y|) ≤
        Real.exp (-2 * |y|) * Real.exp (-|t|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg (t - y)]
    calc
      |riemannKernelReal t| * |∑ i, c i * riemannKernelReal (t - y + h i)| ≤
          (C * Real.exp (-3 * |t|)) *
            (D * Real.exp (-3 * |t - y|) * L * H ^ (r + 1)) :=
        mul_le_mul (hreal t) hc (abs_nonneg _) (by positivity)
      _ = (C * D * L * H ^ (r + 1)) *
          (Real.exp (-3 * |t|) * Real.exp (-3 * |t - y|)) := by ring
      _ ≤ (C * D * L * H ^ (r + 1)) *
          (Real.exp (-2 * |y|) * Real.exp (-|t|)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = A * Real.exp (-|t|) := by dsimp [A]; ring
  calc
    |∑ i, c i * riemannAutocorr (y - h i)| = |∫ t : ℝ, ∑ i, f i t| := by rw [hsum]
    _ ≤ ∫ t : ℝ, |∑ i, f i t| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun t => ∑ i, f i t)
    _ ≤ ∫ t : ℝ, A * Real.exp (-|t|) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _)
        (integrable_exp_neg_abs.const_mul A) (Filter.Eventually.of_forall hpoint)
    _ = A * I := integral_const_mul A _
    _ ≤ A * (I + 1) := by nlinarith
    _ = (C * (I + 1)) * D * Real.exp (-2 * |y|) * (∑ i, |c i|) * H ^ (r + 1) := by
      dsimp [A, L]
      ring

theorem exists_riemannAutocorr_moment_cancellation_envelope (r : ℕ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (ι : Type) [Fintype ι] (c h : ι → ℝ) (H : ℝ),
      0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
      (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ y : ℝ,
      |∑ i, c i * riemannAutocorr (y - h i)| ≤
        E * Real.exp (-2 * |y|) * (∑ i, |c i|) * H ^ (r + 1) := by
  obtain ⟨D, hD, hcancel⟩ := exists_riemannKernelReal_moment_cancellation_envelope r
  obtain ⟨T, hT, htransfer⟩ := exists_riemannAutocorr_moment_transfer_constant
  exact ⟨T * D, mul_pos hT hD, htransfer r D hD hcancel⟩

end RHTower
