import GaloisForLFunctions.BiScaleUncertainty.SignedPhysicalGramEnergy

/-!
# Capacity of the full measured signed Gram deficit

The exact Gram square root is the norm of an actual translation packet. Triangle
inequalities control every cross entry at once: adding nonnegative node weights
increases the anchored deficit by between zero and twice the added source mass.
No grid-zero condition, sign condition on correlations, or origin-weight condition
is required. Padding preserves the exact packet, not merely a Gram majorant.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.AnchoredGram
noncomputable section
variable {ι : Type*}

def packet (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (W : ℂ) • translationFeature f 0 + ∑ i ∈ M, (a i : ℂ) • translationFeature f (t i)

theorem packet_norm_sq (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W : ℝ) :
    ‖packet f M a t W‖ ^ 2 = gram f M a t W := by
  simpa [packet, gram, nodes, weights, shifts, Finset.sum_disjSum] using
    translationFeature_packet_energy f (nodes M) (weights W a) (shifts t)

theorem kernel_eq_packet (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W : ℝ) :
    kernel f M a t W = autocorr f 0 * (W + ∑ i ∈ M, a i) -
      Real.sqrt (autocorr f 0) * ‖packet f M a t W‖ := by
  unfold kernel
  rw [Real.sqrt_mul (autocorr_zero_nonneg f), ← packet_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

theorem packet_add (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ) :
    packet f M (fun i => a i + b i) t W = packet f M a t W + packet f M b t 0 := by
  simp only [packet, Complex.ofReal_add, add_smul, Finset.sum_add_distrib,
    Complex.ofReal_zero, zero_smul, zero_add]
  abel

theorem packet_zero_anchor_norm_le (f : C_c(ℝ, ℝ)) (M : Finset ι) (b t : ι → ℝ)
    (hb : ∀ i ∈ M, 0 ≤ b i) :
    ‖packet f M b t 0‖ ≤ Real.sqrt (autocorr f 0) * ∑ i ∈ M, b i := by
  have hn (i : ι) : ‖translationFeature f (t i)‖ = Real.sqrt (autocorr f 0) := by
    rw [← translationFeature_norm_sq f (t i), Real.sqrt_sq (norm_nonneg _)]
  simp only [packet, Complex.ofReal_zero, zero_smul, zero_add]
  calc
    _ ≤ ∑ i ∈ M, ‖(b i : ℂ) • translationFeature f (t i)‖ := norm_sum_le _ _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi), hn]
      ring

/-- Nonnegative coordinate capacity for the full signed Gram matrix. -/
theorem kernel_add_bounds (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ)
    (hb : ∀ i ∈ M, 0 ≤ b i) :
    0 ≤ kernel f M (fun i => a i + b i) t W - kernel f M a t W ∧
      kernel f M (fun i => a i + b i) t W - kernel f M a t W ≤
        2 * autocorr f 0 * ∑ i ∈ M, b i := by
  have hq := packet_zero_anchor_norm_le f M b t hb
  have hp := norm_add_le (packet f M a t W) (packet f M b t 0)
  have hr := norm_sub_le (packet f M a t W + packet f M b t 0) (packet f M b t 0)
  simp only [add_sub_cancel_right] at hr
  have hs := Real.sqrt_nonneg (autocorr f 0)
  have hsq := Real.sq_sqrt (autocorr_zero_nonneg f)
  have hq' := mul_le_mul_of_nonneg_left hq hs
  rw [← mul_assoc, ← pow_two, hsq] at hq'
  have hp' := mul_le_mul_of_nonneg_left hp hs
  have hr' := mul_le_mul_of_nonneg_left hr hs
  simp only [kernel_eq_packet, packet_add, Finset.sum_add_distrib]
  constructor <;> nlinarith only [hq', hp', hr']

/-- Coordinate monotonicity needs no sign assumption on the incumbent weights. -/
theorem kernel_mono (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ)
    (hab : ∀ i ∈ M, a i ≤ b i) : kernel f M a t W ≤ kernel f M b t W := by
  have h := (kernel_add_bounds f M a (fun i => b i - a i) t W
    (fun i hi => sub_nonneg.mpr (hab i hi))).1
  have he : (fun i => a i + (b i - a i)) = b := by funext i; ring
  rw [he] at h
  exact sub_nonneg.mp h

/-- Unordered perturbations are controlled by any nonnegative coordinate cover. -/
theorem kernel_error_bound (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b e t : ι → ℝ) (W : ℝ)
    (he : ∀ i ∈ M, 0 ≤ e i) (hab : ∀ i ∈ M, b i ≤ a i + e i) :
    kernel f M b t W - kernel f M a t W ≤ 2 * autocorr f 0 * ∑ i ∈ M, e i := by
  have hm := kernel_mono f M b (fun i => a i + e i) t W hab
  have hc := (kernel_add_bounds f M a e t W he).2
  linarith only [hm, hc]

/-- Zero extension preserves all anchor, diagonal, and signed cross entries. -/
theorem kernel_subset (f : C_c(ℝ, ℝ)) {M L : Finset ι} (hML : M ⊆ L)
    (a b t : ι → ℝ) (W : ℝ) (hab : ∀ i ∈ M, a i = b i)
    (hb : ∀ i ∈ L, i ∉ M → b i = 0) : kernel f L b t W = kernel f M a t W := by
  classical
  have hm : (∑ i ∈ L, b i) = ∑ i ∈ M, a i := by
    calc
      _ = ∑ i ∈ M, b i := (Finset.sum_subset hML hb).symm
      _ = _ := Finset.sum_congr rfl (fun i hi => (hab i hi).symm)
  have hp : packet f L b t W = packet f M a t W := by
    unfold packet
    congr 1
    calc
      _ = ∑ i ∈ M, (b i : ℂ) • translationFeature f (t i) := by
        symm
        apply Finset.sum_subset hML
        intro i hi hni
        rw [hb i hi hni, Complex.ofReal_zero, zero_smul]
      _ = _ := Finset.sum_congr rfl (fun i hi => by rw [hab i hi])
  simp only [kernel_eq_packet, hm, hp]

end
end GaloisForLFunctions.BiScaleUncertainty.AnchoredGram
