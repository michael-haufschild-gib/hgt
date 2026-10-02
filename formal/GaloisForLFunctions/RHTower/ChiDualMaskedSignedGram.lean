import GaloisForLFunctions.RHTower.BagPhysicalWindowGram
import GaloisForLFunctions.RHTower.ChiDualMaskedCompactEnvelope
import GaloisForLFunctions.RHTower.SteinhausComplexConvolution

/-!
# Actual masked physical energy with its full signed Gram

The static normalized Gaussian amplitudes retain every multiplicative collision
under arbitrary finite positive-frequency resonators. The actual chi-row bound
transports their entire signed physical Gram to the literal masked carrier.
No support-length restriction or absolute coefficient aggregation is inserted.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace RHTower
open GaloisForLFunctions.RHTower

private theorem resonator_mul_eq_conv (A S : Finset ℕ) (d v : ℕ → ℂ)
    (hA : ∀ a ∈ A, 0 < a) (hS : ∀ n ∈ S, 0 < n) (t : ℝ) :
    zetaChiDualResonator A d t * zetaChiDualResonator S v t =
      zetaChiDualResonator (prodSupport A S) (dpolyComplexConv d v A S) t := by
  classical
  unfold zetaChiDualResonator
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hmap : ∀ q ∈ A ×ˢ S, q.1 * q.2 ∈ prodSupport A S := fun q hq =>
    Finset.mem_image.mpr ⟨q, hq, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun q => (d q.1 * bourgainOscillation (t * Real.log q.1)) *
      (v q.2 * bourgainOscillation (t * Real.log q.2)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [dpolyComplexConv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqAS, hprod⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqa, hqn⟩ := Finset.mem_product.mp hqAS
  have hlog : Real.log ((q.1 * q.2 : ℕ) : ℝ) = Real.log q.1 + Real.log q.2 := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (hA q.1 hqa).ne')
      (by exact_mod_cast (hS q.2 hqn).ne')]
  have hp : bourgainOscillation (t * Real.log q.1) * bourgainOscillation (t * Real.log q.2) =
      bourgainOscillation (t * Real.log k) := by
    unfold bourgainOscillation
    rw [← Complex.exp_add, ← hprod, hlog]
    congr 1
    push_cast
    ring
  calc
    _ = (d q.1 * v q.2) * (bourgainOscillation (t * Real.log q.1) *
        bourgainOscillation (t * Real.log q.2)) := by ring
    _ = _ := by rw [hp]

private theorem continuous_resonator (A : Finset ℕ) (d : ℕ → ℂ) :
    Continuous (zetaChiDualResonator A d) := by
  unfold zetaChiDualResonator
  apply continuous_finsetSum
  intro a _
  unfold bourgainOscillation
  fun_prop

/-- Exact signed Gram of the actual normalized masked block under any finite
resonator. Positive resonator frequencies may be arbitrarily large. -/
theorem integral_chiDualNormalizedMasked_resonator_gram {N : ℝ} (hN : 0 < N)
    (s : ℂ) (A S : Finset ℕ) (d : ℕ → ℂ)
    (hA : ∀ a ∈ A, 0 < a) (hS : ∀ n ∈ S, 0 < n) :
    let V := prodSupport A S
    let b := dpolyComplexConv d (fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) A S
    (∫ t in N..2 * N, bagPhysicalHeightWindow (t / N) *
      ‖zetaChiDualResonator A d t * chiDualNormalizedMaskedPolynomial N S t s‖ ^ 2) =
        N * bagPhysicalHeightMass * ∑ j ∈ V, ‖b j‖ ^ 2 +
          (∑ j ∈ V, ∑ k ∈ V.erase j, b j * conj (b k) *
            bagPhysicalLinearKernel N (Real.log j - Real.log k)).re := by
  classical
  dsimp only
  have hV (j : ℕ) (hj : j ∈ prodSupport A S) : 0 < j := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact Nat.mul_pos (hA q.1 (Finset.mem_product.mp hq).1) (hS q.2 (Finset.mem_product.mp hq).2)
  have hh := integral_bagPhysicalWindow_resonator_sq_sub_diagonal hN (prodSupport A S)
    (dpolyComplexConv d (fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) A S) hV
  have hr := congrArg Complex.re hh
  rw [show (fun t => (bagPhysicalHeightWindow (t / N) : ℂ) *
      ((‖zetaChiDualResonator (prodSupport A S)
        (dpolyComplexConv d (fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) A S) t‖ ^ 2 : ℝ) : ℂ)) =
      (fun t => ((bagPhysicalHeightWindow (t / N) *
        ‖zetaChiDualResonator (prodSupport A S)
          (dpolyComplexConv d (fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) A S) t‖ ^ 2 : ℝ) : ℂ)) by
        funext t; rw [Complex.ofReal_mul], intervalIntegral.integral_ofReal] at hr
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  have he : (fun t => bagPhysicalHeightWindow (t / N) *
      ‖zetaChiDualResonator A d t * chiDualNormalizedMaskedPolynomial N S t s‖ ^ 2) =
      (fun t => bagPhysicalHeightWindow (t / N) *
        ‖zetaChiDualResonator (prodSupport A S)
          (dpolyComplexConv d (fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) A S) t‖ ^ 2) := by
    funext t
    rw [chiDualNormalizedMaskedPolynomial, resonator_mul_eq_conv A S _ _ hA hS]
  rw [he]
  linarith only [hr]

/-- The literal chi-weighted physical square is controlled by the complete
signed source Gram, uniformly on the disc and without a support-length restriction.
No cross term is discarded or replaced by an absolute coefficient sum. -/
theorem exists_chiDualMaskedResonator_signed_gram_bound
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ A S : Finset ℕ, (∀ a ∈ A, 0 < a) → (∀ n ∈ S, 0 < n) → ∀ d : ℕ → ℂ,
      let V := prodSupport A S
      let b := dpolyComplexConv d (fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) A S
      (∫ t in (N : ℝ)..2 * N, bagPhysicalHeightWindow (t / N) *
        ‖zetaChiDualResonator A d t *
          (∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t)‖ ^ 2) ≤
        C * (bagPhysicalHeightMass * ∑ j ∈ V, ‖b j‖ ^ 2 +
          (∑ j ∈ V, ∑ k ∈ V.erase j, b j * conj (b k) *
            bagPhysicalLinearKernel N (Real.log j - Real.log k)).re / N) := by
  obtain ⟨C, hC, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  refine ⟨C ^ 2, by positivity, ?_⟩
  filter_upwards [hrow, eventually_ge_atTop (1 : ℕ)] with N hrow hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  intro s hs A S hA hS d
  dsimp only
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs1 : s.re < 1 := by linarith [(abs_le.mp hre).2]
  let P : ℝ → ℂ := fun t => zetaChiDualResonator A d t * chiDualNormalizedMaskedPolynomial N S t s
  have hP : Continuous P := (continuous_resonator A d).mul (continuous_resonator S _)
  have hW : Continuous (fun t : ℝ => bagPhysicalHeightWindow (t / N)) :=
    bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const (N : ℝ))
  have hleft : Continuous (fun t : ℝ => bagPhysicalHeightWindow (t / N) *
      ‖zetaChiDualResonator A d t *
        (∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t)‖ ^ 2) :=
    hW.mul (((continuous_resonator A d).mul (continuous_chiDualMaskedBlock hs1 N S)).norm.pow 2)
  have hright : Continuous (fun t : ℝ => (C ^ 2 / N) *
      (bagPhysicalHeightWindow (t / N) * ‖P t‖ ^ 2)) :=
    continuous_const.mul (hW.mul (hP.norm.pow 2))
  have hpoint (t : ℝ) (ht : t ∈ Icc (N : ℝ) (2 * N)) :
      bagPhysicalHeightWindow (t / N) *
        ‖zetaChiDualResonator A d t *
          (∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t)‖ ^ 2 ≤
        (C ^ 2 / N) * (bagPhysicalHeightWindow (t / N) * ‖P t‖ ^ 2) := by
    have hf : ‖zetaChi (s + (t : ℂ) * I) * ((N : ℝ) : ℂ) ^ (s - 1)‖ ^ 2 ≤ C ^ 2 / N := by
      apply (le_div_iff₀ hN0).mpr
      rw [norm_chiDualScaledFactor_sq hN0]
      exact pow_le_pow_left₀ (norm_nonneg _) (hrow t ht s hs).1 2
    rw [chiDualMaskedBlock_eq_normalized hN0 S hS s t,
      show zetaChiDualResonator A d t *
          ((zetaChi (s + (t : ℂ) * I) * ((N : ℝ) : ℂ) ^ (s - 1)) * chiDualNormalizedMaskedPolynomial N S t s) =
        (zetaChi (s + (t : ℂ) * I) * ((N : ℝ) : ℂ) ^ (s - 1)) * P t by dsimp only [P]; ring,
      norm_mul, mul_pow]
    calc
      _ = ‖zetaChi (s + (t : ℂ) * I) * ((N : ℝ) : ℂ) ^ (s - 1)‖ ^ 2 *
          (bagPhysicalHeightWindow (t / N) * ‖P t‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hf (mul_nonneg bagPhysicalHeightWindow.nonneg (sq_nonneg _))
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := (N : ℝ)) (b := 2 * (N : ℝ))
    (by linarith only [hN0]) (hleft.intervalIntegrable _ _) (hright.intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul] at hi
  have he := integral_chiDualNormalizedMasked_resonator_gram hN0 s A S d hA hS
  dsimp only at he
  change _ ≤ (C ^ 2 / N) * (∫ t in (N : ℝ)..2 * N, bagPhysicalHeightWindow (t / N) *
    ‖zetaChiDualResonator A d t * chiDualNormalizedMaskedPolynomial N S t s‖ ^ 2) at hi
  rw [he] at hi
  convert hi using 1
  field_simp [hN0.ne']

end RHTower
