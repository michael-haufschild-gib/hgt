import GaloisForLFunctions.HTGeometry.ClockSeriesDerivative
import GaloisForLFunctions.HTGeometry.ClockTubeSolution

/-!
# The step operator on a tube commutes with a convergent series

Summing the recursion needs the transverse Laplacian to pass through the sum. Along a fixed
coordinate slice the second partial derivative *is* a second derivative in one variable, so the
one-variable theorem on term-by-term differentiation applies slice by slice; the finitely many
coordinates are then exchanged with the sum by the finite-sum rule, and the potential term is a
multiplication by a fixed value.

The summability of the second partial derivatives is Cauchy's estimate applied to the summable bound
on the functions themselves.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- **The second partial derivative along a coordinate commutes with a series that is slice
holomorphic and uniformly bounded.** -/
theorem cpartial_cpartial_tsum {ρ₂ ρ₁ ρ' : ℝ} (h21 : ρ₂ < ρ₁) (h1ρ : ρ₁ < ρ')
    {f : ℕ → (Fin k → ℂ) → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, SliceHolo (f m) ρ') (hM : ∀ m, ∀ w ∈ tube k ρ', ‖f m w‖ ≤ M m) (hMs : Summable M)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) (i : Fin k) :
    cpartial i (cpartial i fun w => ∑' m, f m w) z = ∑' m, cpartial i (cpartial i (f m)) z := by
  have h2ρ : ρ₂ < ρ' := lt_trans h21 h1ρ
  have hzρ' : z ∈ tube k ρ' := tube_mono h2ρ.le hz
  have hslice : ∀ m, DifferentiableOn ℂ (fun ζ : ℂ => f m (Function.update z i ζ)) (imStrip ρ') :=
    fun m => hf m z hzρ' i
  have hMslice : ∀ m, ∀ w ∈ imStrip ρ', ‖f m (Function.update z i w)‖ ≤ M m :=
    fun m w hw => hM m _ (update_mem_tube hzρ' i hw)
  have hbase := deriv_deriv_tsum_of_holomorphic h21 h1ρ hslice hMslice hMs
    (mem_imStrip.mpr (hz i))
  rw [cpartial_cpartial_eq, hbase]
  exact tsum_congr fun m => (cpartial_cpartial_eq i (f m) z).symm

/-- **The step operator on a tube commutes with a series of slice holomorphic functions.** -/
theorem tubeStep_tsum {ρ₂ ρ₁ ρ' : ℝ} (h21 : ρ₂ < ρ₁) (h1ρ : ρ₁ < ρ')
    {V : (Fin k → ℂ) → ℂ} {f : ℕ → (Fin k → ℂ) → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, SliceHolo (f m) ρ') (hM : ∀ m, ∀ w ∈ tube k ρ', ‖f m w‖ ≤ M m) (hMs : Summable M)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) :
    tubeStep V (fun w => ∑' m, f m w) z = ∑' m, tubeStep V (f m) z := by
  classical
  have h2ρ : ρ₂ < ρ' := lt_trans h21 h1ρ
  have hzρ' : z ∈ tube k ρ' := tube_mono h2ρ.le hz
  have hgap : (0 : ℝ) < ρ' - ρ₂ := by linarith
  -- summability of the second partial derivatives, by Cauchy's estimate
  have hsumd : ∀ i : Fin k, Summable fun m => cpartial i (cpartial i (f m)) z := by
    intro i
    refine Summable.of_norm_bounded
      (g := fun m => 16 * M m / (ρ' - ρ₂) ^ 2) ?_ fun m => ?_
    · simpa [mul_div_assoc] using (hMs.mul_left 16).div_const ((ρ' - ρ₂) ^ 2)
    · exact norm_cpartial_cpartial_le_of_sliceHolo h2ρ (hf m) (hM m) (fun j => (hz j).le) i
  have hsumS : Summable fun m => ∑ i, cpartial i (cpartial i (f m)) z :=
    summable_sum fun i _ => hsumd i
  have hsumf : Summable fun m => f m z :=
    Summable.of_norm_bounded hMs fun m => hM m z hzρ'
  have hsum2 : Summable fun m => V z * f m z := hsumf.mul_left _
  have hlhs : tubeStep V (fun w => ∑' m, f m w) z
      = ((∑ i, cpartial i (cpartial i fun w => ∑' m, f m w) z) + V z * ∑' m, f m z) / 4 := rfl
  have hpart : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      cpartial i (cpartial i fun w => ∑' m, f m w) z = ∑' m, cpartial i (cpartial i (f m)) z :=
    fun i _ => cpartial_cpartial_tsum h21 h1ρ hf hM hMs hz i
  rw [hlhs, Finset.sum_congr rfl hpart, ← Summable.tsum_finsetSum fun i _ => hsumd i, ← tsum_mul_left,
    ← hsumS.tsum_add hsum2, ← tsum_div_const]
  exact tsum_congr fun m => rfl

end GaloisForLFunctions.HTGeometry
