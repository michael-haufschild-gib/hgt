import GaloisForLFunctions.RHTower.PaperWoldFullSpectrum
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-! # Literal finite-square means, including moving interaction masks

Normalized finite flat probes have norm one and converge weakly to zero.
The full strict-half kernel has a common product majorant, so its normalized
finite-square means vanish even when the bounded mask changes at every cutoff.
These increment means are distinct from the integrated RH source covariance.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal InnerProductSpace

def paperWoldFlatAmplitude (N : ℕ) : ℝ := ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))

theorem paperWoldFlatAmplitude_nonneg (N : ℕ) : 0 ≤ paperWoldFlatAmplitude N :=
  Real.rpow_nonneg (by positivity) _

theorem paperWoldFlatAmplitude_sq (N : ℕ) :
    paperWoldFlatAmplitude N ^ 2 = ((N : ℝ) + 1)⁻¹ := by
  unfold paperWoldFlatAmplitude
  rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg_one]

theorem paperWoldFlatAmplitude_tendsto : Tendsto paperWoldFlatAmplitude atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h

def paperWoldFlat (N : ℕ) : PaperWoldHistory :=
  ∑ n ∈ Finset.range (N + 1), lp.single 2 n (paperWoldFlatAmplitude N : ℂ)

@[simp] theorem paperWoldFlat_apply (N n : ℕ) :
    paperWoldFlat N n = if n < N + 1 then (paperWoldFlatAmplitude N : ℂ) else 0 := by
  simp only [paperWoldFlat, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, Finset.mem_range]

theorem paperWoldFlat_norm (N : ℕ) : ‖paperWoldFlat N‖ = 1 := by
  have h := lp.norm_sum_single (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (fun _ : ℕ => (paperWoldFlatAmplitude N : ℂ)) (Finset.range (N + 1))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperWoldFlatAmplitude_nonneg N), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, paperWoldFlatAmplitude_sq] at h
  rw [mul_inv_cancel₀ (by positivity : (N : ℝ) + 1 ≠ 0)] at h
  change ‖paperWoldFlat N‖ ^ 2 = 1 at h
  nlinarith [norm_nonneg (paperWoldFlat N)]

theorem paperWoldFlat_coordinate_tendsto (n : ℕ) :
    Tendsto (fun N => paperWoldFlat N n) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp paperWoldFlatAmplitude_tendsto
  apply h.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  simp only [Function.comp_def, paperWoldFlat_apply, if_pos (by omega : n < N + 1)]

theorem paperWoldFlat_weak_tendsto (x : PaperWoldHistory) :
    Tendsto (fun N => inner ℂ x (paperWoldFlat N)) atTop (𝓝 0) :=
  tendsto_inner_lp_of_coord paperWoldFlat zero_le_one
    (fun N => (paperWoldFlat_norm N).le) paperWoldFlat_coordinate_tendsto x

theorem paperWoldFlat_compact_tendsto (K : compactOperatorStarAlgebra PaperWoldHistory) :
    Tendsto (fun N => K.1 (paperWoldFlat N)) atTop (𝓝 0) :=
  tendsto_norm_compact_of_weaklyNull K.1 K.2 paperWoldFlat
    (fun N => (paperWoldFlat_norm N).le) paperWoldFlat_weak_tendsto

theorem paperWoldFlat_compact_form_tendsto (K : compactOperatorStarAlgebra PaperWoldHistory) :
    Tendsto (fun N => inner ℂ (paperWoldFlat N) (K.1 (paperWoldFlat N))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _)
    (fun N => (norm_inner_le_norm _ _).trans_eq (by rw [paperWoldFlat_norm, one_mul]))
  exact tendsto_zero_iff_norm_tendsto_zero.mp (paperWoldFlat_compact_tendsto K)

theorem paperWoldFlat_inner (N : ℕ) (x : PaperWoldHistory) :
    inner ℂ (paperWoldFlat N) x =
      (paperWoldFlatAmplitude N : ℂ) * ∑ n ∈ Finset.range (N + 1), x n := by
  rw [paperWoldFlat, sum_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [lp.inner_single_left]
  change x n * (starRingEnd ℂ) (paperWoldFlatAmplitude N : ℂ) = _
  rw [Complex.conj_ofReal, mul_comm]

theorem paperWoldFlat_eq_smul_sum (N : ℕ) :
    paperWoldFlat N = (paperWoldFlatAmplitude N : ℂ) •
      ∑ n ∈ Finset.range (N + 1), lp.single 2 n (1 : ℂ) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← lp.single_smul]
  simp only [smul_eq_mul, mul_one]

theorem paperWoldFlat_quadratic (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) (N : ℕ) :
    inner ℂ (paperWoldFlat N) (T (paperWoldFlat N)) =
      Complex.ofReal (((N : ℝ) + 1)⁻¹) * ∑ n ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range (N + 1), T (lp.single 2 j (1 : ℂ)) n := by
  have h : inner ℂ (∑ n ∈ Finset.range (N + 1), lp.single 2 n (1 : ℂ))
      (T (∑ j ∈ Finset.range (N + 1), lp.single 2 j (1 : ℂ))) =
      ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), T (lp.single 2 j (1 : ℂ)) n := by
    simp only [map_sum, sum_inner, inner_sum, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    exact Finset.sum_comm
  simp only [paperWoldFlat_eq_smul_sum, map_smul, inner_smul_left, inner_smul_right]
  rw [h]
  rw [Complex.conj_ofReal]
  rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, paperWoldFlatAmplitude_sq]

def paperWoldMaskedMean (p : PaperWoldStrictHalf) (m : PaperWoldMask) (N : ℕ) : ℂ :=
  Complex.ofReal (((N : ℝ) + 1)⁻¹) * ∑ n ∈ Finset.range (N + 1),
    ∑ j ∈ Finset.range (N + 1), paperWoldMaskedKernel p m (n,j)

theorem paperWoldMaskedMean_eq_form (p : PaperWoldStrictHalf) (m : PaperWoldMask) (N : ℕ) :
    paperWoldMaskedMean p m N =
      inner ℂ (paperWoldFlat N) (paperWoldMaskedOperator p m (paperWoldFlat N)) := by
  rw [paperWoldFlat_quadratic]
  simp only [paperWoldMaskedMean, paperWoldMaskedOperator_single]

def paperWoldEnvelopeVector (p : PaperWoldStrictHalf) : PaperWoldHistory :=
  ⟨fun n => (paperWoldFullEnvelope p n : ℂ), HilbertSchmidt.memℓp_of_sq (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using paperWoldFullEnvelope_sq_summable p)⟩

@[simp] theorem paperWoldEnvelopeVector_apply (p : PaperWoldStrictHalf) (n : ℕ) :
    paperWoldEnvelopeVector p n = (paperWoldFullEnvelope p n : ℂ) := rfl

def paperWoldFlatEnvelopePair (p : PaperWoldStrictHalf) (N : ℕ) : ℝ :=
  paperWoldFlatAmplitude N * ∑ n ∈ Finset.range (N + 1), paperWoldFullEnvelope p n

theorem paperWoldFlatEnvelopePair_eq_re (p : PaperWoldStrictHalf) (N : ℕ) :
    paperWoldFlatEnvelopePair p N = (inner ℂ (paperWoldEnvelopeVector p) (paperWoldFlat N)).re := by
  have hs : (inner ℂ (paperWoldEnvelopeVector p) (paperWoldFlat N)).re =
      (inner ℂ (paperWoldFlat N) (paperWoldEnvelopeVector p)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hs, paperWoldFlat_inner]
  simp [paperWoldFlatEnvelopePair, ← Complex.ofReal_sum, ← Complex.ofReal_mul]

theorem paperWoldFlatEnvelopePair_tendsto (p : PaperWoldStrictHalf) :
    Tendsto (paperWoldFlatEnvelopePair p) atTop (𝓝 0) := by
  have h := (Complex.continuous_re.tendsto 0).comp (paperWoldFlat_weak_tendsto (paperWoldEnvelopeVector p))
  simpa only [Function.comp_def, ← paperWoldFlatEnvelopePair_eq_re, Complex.zero_re] using h

theorem paperWoldMaskedMean_norm_le (p : PaperWoldStrictHalf) (m : PaperWoldMask) (N : ℕ) :
    ‖paperWoldMaskedMean p m N‖ ≤ paperWoldFlatEnvelopePair p N ^ 2 := by
  have hsum : ‖∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      paperWoldMaskedKernel p m (n,j)‖ ≤ (∑ n ∈ Finset.range (N + 1), paperWoldFullEnvelope p n) ^ 2 := by
    calc
      _ ≤ ∑ n ∈ Finset.range (N + 1), ‖∑ j ∈ Finset.range (N + 1), paperWoldMaskedKernel p m (n,j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ‖paperWoldMaskedKernel p m (n,j)‖ :=
        Finset.sum_le_sum (fun n hn => norm_sum_le _ _)
      _ ≤ ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          paperWoldFullEnvelope p n * paperWoldFullEnvelope p j := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro j hj
        exact (paperWoldMaskedKernel_norm_le p m (n,j)).trans (paperWoldFullKernel_bound p (n,j))
      _ = _ := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, pow_two]
  rw [paperWoldFlatEnvelopePair, mul_pow, paperWoldFlatAmplitude_sq]
  simp only [paperWoldMaskedMean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((N : ℝ) + 1)⁻¹)]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- One vanishing bound covers every cutoff-dependent choice of bounded mask. -/
theorem paperWoldMaskedMean_moving_tendsto (p : PaperWoldStrictHalf) (m : ℕ → PaperWoldMask) :
    Tendsto (fun N => paperWoldMaskedMean p (m N) N) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => paperWoldMaskedMean_norm_le p (m N) N)
    (by simpa using (paperWoldFlatEnvelopePair_tendsto p).pow 2)

theorem paperWoldFullMean_tendsto (p : PaperWoldStrictHalf) :
    Tendsto (fun N : ℕ => Complex.ofReal (((N : ℝ) + 1)⁻¹) * ∑ n ∈ Finset.range (N + 1),
      ∑ j ∈ Finset.range (N + 1), paperWoldFullKernel p (n,j)) atTop (𝓝 0) := by
  simpa only [paperWoldMaskedMean, paperWoldMaskedKernel_full] using
    paperWoldMaskedMean_moving_tendsto p (fun _ => paperWoldFullMask)

theorem paperWoldWindowMean_moving_tendsto (p : PaperWoldStrictHalf) (w : ℕ → ℕ → ℕ) :
    Tendsto (fun N => paperWoldMaskedMean p (paperWoldWindowMask (w N)) N) atTop (𝓝 0) :=
  paperWoldMaskedMean_moving_tendsto p (fun N => paperWoldWindowMask (w N))

theorem paperWoldNearMatrixMean_tendsto (p : PaperWoldNearParameters) :
    Tendsto (fun N : ℕ => Complex.ofReal (((N : ℝ) + 1)⁻¹) * ∑ n ∈ Finset.range (N + 1),
      ∑ j ∈ Finset.range (N + 1), paperWoldNearOperator p (lp.single 2 j (1 : ℂ)) n)
      atTop (𝓝 0) := by
  simp_rw [← paperWoldFlat_quadratic]
  exact paperWoldFlat_compact_form_tendsto ⟨_, paperWoldNearOperator_compact p⟩

theorem paperWoldCriticalNearFlat_tendsto :
    Tendsto (fun N => paperWoldNearOperator paperWoldCriticalNearParameters (paperWoldFlat N))
      atTop (𝓝 0) :=
  paperWoldFlat_compact_tendsto ⟨_, paperWoldNearOperator_compact _⟩

end
end RHTower
