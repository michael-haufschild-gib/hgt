import GaloisForLFunctions.HTGeometry.SmoothWeight
import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# A compactly supported smooth block window with scaled derivative bounds

`blockWindow p q η` is smooth, equal to `1` on `[p, q]`, to `0` outside `[p - η, q + η]`, takes
values in `[0, 1]`, and its `j`-th derivative is bounded by `blockWindowConst j / η ^ j` with a
constant depending only on `j`.

Its Fourier transform therefore decays like `(q - p + 2η) · blockWindowConst K / (η |ξ|)^K` for
every `K`: the height oscillation `exp(-iξt)` integrated against the window costs one factor
`1/(η|ξ|)` per integration by parts, and nothing else, because the window has compact support.
This is the window used for the smoothed dyadic mean values: the block `[p, q]` is covered exactly,
the transition zones have total length `2η`, and every derivative that a height integration by
parts produces is paid for by the scale `η`.
-/

open Real MeasureTheory FourierTransform

namespace GaloisForLFunctions.HTGeometry

/-- The uniform derivative constant of the one-sided smooth weight. -/
noncomputable def smoothWeightDerivConst (j : ℕ) : ℝ :=
  (exists_bound_iteratedDeriv_smoothWeight_uniform j).choose

theorem smoothWeightDerivConst_nonneg (j : ℕ) : 0 ≤ smoothWeightDerivConst j :=
  (exists_bound_iteratedDeriv_smoothWeight_uniform j).choose_spec.1

theorem abs_iteratedDeriv_smoothWeight_le (j : ℕ) (N : ℝ) {H : ℝ} (hH : 0 < H) (x : ℝ) :
    |iteratedDeriv j (smoothWeight N H) x| ≤ smoothWeightDerivConst j / H ^ j :=
  (exists_bound_iteratedDeriv_smoothWeight_uniform j).choose_spec.2 N H hH x

/-- The block window: `1` on `[p, q]`, `0` outside `[p - η, q + η]`. -/
noncomputable def blockWindow (p q η : ℝ) : ℝ → ℝ :=
  fun t => (1 - smoothWeight (p - η) η t) * smoothWeight q η t

theorem blockWindow_eq_one {p q η : ℝ} (hη : 0 < η) {t : ℝ} (hp : p ≤ t) (hq : t ≤ q) :
    blockWindow p q η t = 1 := by
  unfold blockWindow
  rw [smoothWeight_eq_zero hη (by linarith), smoothWeight_eq_one hη hq]
  ring

theorem blockWindow_eq_zero_of_le {p q η : ℝ} (hη : 0 < η) {t : ℝ} (ht : t ≤ p - η) :
    blockWindow p q η t = 0 := by
  unfold blockWindow
  rw [smoothWeight_eq_one hη ht]
  ring

theorem blockWindow_eq_zero_of_ge {p q η : ℝ} (hη : 0 < η) {t : ℝ} (ht : q + η ≤ t) :
    blockWindow p q η t = 0 := by
  unfold blockWindow
  rw [smoothWeight_eq_zero hη ht]
  ring

theorem blockWindow_nonneg (p q η t : ℝ) : 0 ≤ blockWindow p q η t :=
  mul_nonneg (by linarith [smoothWeight_le_one (p - η) η t]) (smoothWeight_nonneg q η t)

theorem blockWindow_le_one (p q η t : ℝ) : blockWindow p q η t ≤ 1 := by
  unfold blockWindow
  have h1 := smoothWeight_nonneg (p - η) η t
  have h2 := smoothWeight_le_one q η t
  have h3 := smoothWeight_nonneg q η t
  nlinarith

theorem contDiff_blockWindow (p q η : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (blockWindow p q η) := by
  unfold blockWindow
  exact (contDiff_const.sub (smoothWeight_contDiff (p - η) η)).mul (smoothWeight_contDiff q η)

theorem support_blockWindow_subset {p q η : ℝ} (hη : 0 < η) :
    Function.support (blockWindow p q η) ⊆ Set.Icc (p - η) (q + η) := by
  intro t ht
  by_contra h
  rw [Set.mem_Icc, not_and_or] at h
  apply ht
  rcases h with h | h
  · exact blockWindow_eq_zero_of_le hη (le_of_lt (not_le.mp h))
  · exact blockWindow_eq_zero_of_ge hη (le_of_lt (not_le.mp h))

theorem hasCompactSupport_blockWindow {p q η : ℝ} (hη : 0 < η) :
    HasCompactSupport (blockWindow p q η) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_blockWindow_subset hη)

/-- The scaled derivative constant of the block window: the Leibniz sum of the two step constants. -/
noncomputable def blockWindowConst (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * (1 + smoothWeightDerivConst i) * smoothWeightDerivConst (j - i)

theorem blockWindowConst_nonneg (j : ℕ) : 0 ≤ blockWindowConst j :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (by positivity) (by linarith [smoothWeightDerivConst_nonneg i]))
      (smoothWeightDerivConst_nonneg _)

/-- The rising step `1 - smoothWeight N H` has the scaled derivative bounds of the weight, plus one
for the constant term at order zero. -/
theorem abs_iteratedDeriv_one_sub_smoothWeight_le (i : ℕ) (N : ℝ) {H : ℝ} (hH : 0 < H) (x : ℝ) :
    |iteratedDeriv i (fun t => 1 - smoothWeight N H t) x|
      ≤ (1 + smoothWeightDerivConst i) / H ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [iteratedDeriv_zero, pow_zero, div_one]
    have h1 := smoothWeight_nonneg N H x
    have h2 := smoothWeight_le_one N H x
    have h3 := smoothWeightDerivConst_nonneg 0
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [iteratedDeriv_const_sub hi, iteratedDeriv_neg, abs_neg]
    calc |iteratedDeriv i (smoothWeight N H) x| ≤ smoothWeightDerivConst i / H ^ i :=
          abs_iteratedDeriv_smoothWeight_le i N hH x
      _ ≤ (1 + smoothWeightDerivConst i) / H ^ i := by gcongr; linarith

/-- **Scaled derivative bounds of the block window.** -/
theorem abs_iteratedDeriv_blockWindow_le (j : ℕ) (p q : ℝ) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    |iteratedDeriv j (blockWindow p q η) t| ≤ blockWindowConst j / η ^ j := by
  unfold blockWindow
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => 1 - smoothWeight (p - η) η t) :=
    contDiff_const.sub (smoothWeight_contDiff (p - η) η)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (smoothWeight q η) := smoothWeight_contDiff q η
  have hL := norm_iteratedFDeriv_mul_le hf hg t (n := j) (by exact_mod_cast le_top)
  have hL' : |iteratedDeriv j (fun y => (1 - smoothWeight (p - η) η y) * smoothWeight q η y) t|
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
          * |iteratedDeriv i (fun t => 1 - smoothWeight (p - η) η t) t|
          * |iteratedDeriv (j - i) (smoothWeight q η) t| := by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hL
  refine le_trans hL' ?_
  rw [blockWindowConst, Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ j := by
    have := Finset.mem_range.mp hi
    omega
  have h1 := abs_iteratedDeriv_one_sub_smoothWeight_le i (p - η) hη t
  have h2 := abs_iteratedDeriv_smoothWeight_le (j - i) q hη t
  have hpow : η ^ i * η ^ (j - i) = η ^ j := by rw [← pow_add, Nat.add_sub_cancel' hi']
  calc (j.choose i : ℝ) * |iteratedDeriv i (fun t => 1 - smoothWeight (p - η) η t) t|
        * |iteratedDeriv (j - i) (smoothWeight q η) t|
      ≤ (j.choose i : ℝ) * ((1 + smoothWeightDerivConst i) / η ^ i)
          * (smoothWeightDerivConst (j - i) / η ^ (j - i)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (abs_nonneg _)
          (mul_nonneg (by positivity)
            (div_nonneg (by linarith [smoothWeightDerivConst_nonneg i]) (by positivity)))
    _ = (j.choose i : ℝ) * (1 + smoothWeightDerivConst i) * smoothWeightDerivConst (j - i)
          / η ^ j := by
        rw [← hpow]
        field_simp

/-- The complexified window. -/
noncomputable def blockWindowC (p q η : ℝ) : ℝ → ℂ :=
  fun t => ((blockWindow p q η t : ℝ) : ℂ)

theorem contDiff_blockWindowC (p q η : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (blockWindowC p q η) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_blockWindow p q η)

theorem iteratedDeriv_blockWindowC (p q η : ℝ) (n : ℕ) :
    iteratedDeriv n (blockWindowC p q η)
      = fun t => ((iteratedDeriv n (blockWindow p q η) t : ℝ) : ℂ) :=
  iteratedDeriv_ofReal_comp (contDiff_blockWindow p q η) n

theorem norm_iteratedDeriv_blockWindowC_le (n : ℕ) (p q : ℝ) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    ‖iteratedDeriv n (blockWindowC p q η) t‖ ≤ blockWindowConst n / η ^ n := by
  rw [iteratedDeriv_blockWindowC, Complex.norm_real, Real.norm_eq_abs]
  exact abs_iteratedDeriv_blockWindow_le n p q hη t

theorem tsupport_blockWindowC_subset {p q η : ℝ} (hη : 0 < η) :
    tsupport (blockWindowC p q η) ⊆ Set.Icc (p - η) (q + η) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  apply support_blockWindow_subset hη
  simpa [blockWindowC, Function.mem_support] using ht

theorem iteratedDeriv_blockWindowC_eq_zero (n : ℕ) {p q η : ℝ} (hη : 0 < η) {t : ℝ}
    (ht : t ∉ Set.Icc (p - η) (q + η)) : iteratedDeriv n (blockWindowC p q η) t = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hnot : t ∉ Function.support (iteratedFDeriv ℝ n (blockWindowC p q η)) := fun h =>
    ht (tsupport_blockWindowC_subset hη (support_iteratedFDeriv_subset n h))
  simp [Function.notMem_support.mp hnot]

theorem hasCompactSupport_iteratedDeriv_blockWindowC (n : ℕ) {p q η : ℝ} (hη : 0 < η) :
    HasCompactSupport (iteratedDeriv n (blockWindowC p q η)) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (Function.support_subset_iff'.mpr fun _ ht => iteratedDeriv_blockWindowC_eq_zero n hη ht)

theorem continuous_iteratedDeriv_blockWindowC (n : ℕ) (p q η : ℝ) :
    Continuous (iteratedDeriv n (blockWindowC p q η)) :=
  (contDiff_blockWindowC p q η).continuous_iteratedDeriv n (by exact_mod_cast le_top)

theorem integrable_iteratedDeriv_blockWindowC (n : ℕ) {p q η : ℝ} (hη : 0 < η) :
    Integrable (iteratedDeriv n (blockWindowC p q η)) :=
  (continuous_iteratedDeriv_blockWindowC n p q η).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv_blockWindowC n hη)

theorem integrable_blockWindowC {p q η : ℝ} (hη : 0 < η) : Integrable (blockWindowC p q η) := by
  simpa using integrable_iteratedDeriv_blockWindowC 0 (p := p) (q := q) hη

/-- The `L¹` norm of the `K`-th derivative of the window. -/
theorem integral_norm_iteratedDeriv_blockWindowC_le (K : ℕ) {p q η : ℝ} (hη : 0 < η)
    (hpq : p ≤ q) :
    ∫ t, ‖iteratedDeriv K (blockWindowC p q η) t‖
      ≤ (q - p + 2 * η) * (blockWindowConst K / η ^ K) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (p - η) (q + η))
    (fun t ht => by rw [iteratedDeriv_blockWindowC_eq_zero K hη ht, norm_zero])]
  calc ∫ t in Set.Icc (p - η) (q + η), ‖iteratedDeriv K (blockWindowC p q η) t‖
      ≤ ∫ _ in Set.Icc (p - η) (q + η), blockWindowConst K / η ^ K :=
        setIntegral_mono_on (integrable_iteratedDeriv_blockWindowC K hη).norm.integrableOn
          (integrableOn_const (by simp)) measurableSet_Icc
          (fun t _ => norm_iteratedDeriv_blockWindowC_le K p q hη t)
    _ = (q - p + 2 * η) * (blockWindowConst K / η ^ K) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

theorem norm_fourier_le_integral_norm (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ t, ‖f t‖ := by
  rw [Real.fourier_real_eq]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  congr 1
  funext t
  rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

/-- **Fourier decay of the block window.** Every order `K` of decay is available at the price
`(q - p + 2η) · blockWindowConst K / (η · 2π|ξ|)^K`. -/
theorem norm_fourier_blockWindowC_le (K : ℕ) {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q) {ξ : ℝ}
    (hξ : ξ ≠ 0) :
    ‖𝓕 (blockWindowC p q η) ξ‖
      ≤ (q - p + 2 * η) * (blockWindowConst K / η ^ K) / (2 * π * |ξ|) ^ K := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (blockWindowC p q η) := contDiff_blockWindowC p q η
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ ⊤ → Integrable (iteratedDeriv n (blockWindowC p q η)) :=
    fun n _ => integrable_iteratedDeriv_blockWindowC n hη
  have h := Real.fourier_iteratedDeriv (N := ⊤) hcd hint (n := K) le_top
  have hK : 𝓕 (iteratedDeriv K (blockWindowC p q η)) ξ
      = (2 * π * Complex.I * ξ) ^ K • 𝓕 (blockWindowC p q η) ξ := by rw [h]
  have hnorm : ‖(2 * π * Complex.I * (ξ : ℂ)) ^ K‖ = (2 * π * |ξ|) ^ K := by
    rw [norm_pow, Complex.norm_mul, Complex.norm_mul, Complex.norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  have hpos : 0 < (2 * π * |ξ|) ^ K := by
    have := abs_pos.mpr hξ
    positivity
  rw [le_div_iff₀ hpos, ← hnorm, mul_comm, ← norm_smul, ← hK]
  exact le_trans (norm_fourier_le_integral_norm _ _)
    (integral_norm_iteratedDeriv_blockWindowC_le K hη hpq)

/-- The window against the height oscillation `exp(-iξt)` is its Fourier transform at `ξ/2π`. -/
theorem integral_blockWindowC_mul_cexp_eq (p q η ξ : ℝ) :
    ∫ t, blockWindowC p q η t * Complex.exp (-(ξ * t) * Complex.I)
      = 𝓕 (blockWindowC p q η) (ξ / (2 * π)) := by
  rw [Real.fourier_real_eq]
  congr 1
  funext t
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/-- **Height-oscillation decay of the block window**, in the `exp(-iξt)` normalisation. -/
theorem norm_integral_blockWindowC_mul_cexp_le (K : ℕ) {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖∫ t, blockWindowC p q η t * Complex.exp (-(ξ * t) * Complex.I)‖
      ≤ (q - p + 2 * η) * (blockWindowConst K / η ^ K) / |ξ| ^ K := by
  rw [integral_blockWindowC_mul_cexp_eq]
  have hξ' : ξ / (2 * π) ≠ 0 := div_ne_zero hξ (by positivity)
  refine le_trans (norm_fourier_blockWindowC_le K hη hpq hξ') (le_of_eq ?_)
  congr 2
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  field_simp

end GaloisForLFunctions.HTGeometry
