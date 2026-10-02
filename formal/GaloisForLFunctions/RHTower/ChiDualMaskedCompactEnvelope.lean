import GaloisForLFunctions.RHTower.ChiDualMaskedMeanSquare
import GaloisForLFunctions.RHTower.CompactDiscMeanSqEnvelope
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Simultaneous compact control of actual masked dual blocks

The normalized finite polynomial is entire in the compact variable and jointly
measurable in height. Its planar mean-square envelope controls all disc points
at each same physical height. Sharp mean value bounds and actual chi row
normalization give integral cost O(card F). The complete free-prime mask then
pays the proved harmonic cofactor budget, with every product cutoff retained.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace RHTower


/-- The literal masked polynomial after removing the common chi/height factor. -/
def chiDualNormalizedMaskedPolynomial (N : ℝ) (S : Finset ℕ) (t : ℝ) (s : ℂ) : ℂ :=
  zetaChiDualResonator S (fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) t

private theorem chiDualUnitSpatialAmplitude_entire {N : ℝ} (hN : 0 < N)
    {n : ℕ} (hn : 0 < n) : Differentiable ℂ (fun s => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) := by
  have hx : (0 : ℝ) < (n : ℝ) / N := div_pos (by exact_mod_cast hn) hN
  have hne : (((n : ℝ) / N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hd : Differentiable ℂ (fun s : ℂ => ((((n : ℝ) / N : ℝ) : ℂ)) ^ (s - 1)) :=
    (differentiable_id.sub_const 1).const_cpow (Or.inl hne)
  exact hd.const_mul _

/-- Removing the actual chi factor leaves an entire compact-variable polynomial. -/
theorem differentiable_chiDualNormalizedMaskedPolynomial {N : ℝ} (hN : 0 < N)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (t : ℝ) :
    Differentiable ℂ (chiDualNormalizedMaskedPolynomial N S t) := by
  unfold chiDualNormalizedMaskedPolynomial zetaChiDualResonator
  apply Differentiable.fun_sum
  intro n hn
  exact (chiDualUnitSpatialAmplitude_entire hN (hS n hn)).mul_const _

/-- The same actual normalized polynomial is jointly measurable in height and
compact variable, so its planar mean-square envelope is a genuine measurable function. -/
theorem measurable_chiDualNormalizedMaskedPolynomial {N : ℝ} (hN : 0 < N)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    Measurable (fun q : ℝ × ℂ => chiDualNormalizedMaskedPolynomial N S q.1 q.2) := by
  apply Continuous.measurable
  unfold chiDualNormalizedMaskedPolynomial zetaChiDualResonator
  apply continuous_finsetSum
  intro n hn
  exact (((chiDualUnitSpatialAmplitude_entire hN (hS n hn)).continuous.comp continuous_snd).mul
    (by unfold bourgainOscillation; fun_prop))

/-- Exact factorization of the literal masked carrier, without omitting any term. -/
theorem chiDualMaskedBlock_eq_normalized {N : ℝ} (hN : 0 < N)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (s : ℂ) (t : ℝ) :
    (∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) =
      (zetaChi (s + (t : ℂ) * I) * (N : ℂ) ^ (s - 1)) * chiDualNormalizedMaskedPolynomial N S t s := by
  unfold chiDualNormalizedMaskedPolynomial zetaChiDualResonator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he := chiDualSpatialSlowAmplitude_eq s (x := (n : ℝ)) hN (by exact_mod_cast hS n hn)
  simp only [chiDualSpatialSlowAmplitude, Complex.ofReal_natCast] at he
  unfold zetaChiDualInteriorAtom
  calc
    _ = zetaChi (s + (t : ℂ) * I) *
        (smoothAFECutoff ((n : ℝ) / N) * (n : ℂ) ^ (s - 1)) *
          bourgainOscillation (t * Real.log n) := by ring
    _ = _ := by rw [← he]; ring

/-- Exact source normalization of the physical chi factor, retaining the full height scale. -/
theorem norm_chiDualScaledFactor_sq {N : ℝ} (hN : 0 < N) (s : ℂ) (t : ℝ) :
    ‖zetaChi (s + (t : ℂ) * I) * (N : ℂ) ^ (s - 1)‖ ^ 2 * N =
      ‖reflectedCompactGaussianRow s N t‖ ^ 2 := by
  have hi : ‖zetaChi (s + (t : ℂ) * I) * (N : ℂ) ^ (s - 1)‖ * Real.sqrt N =
      ‖reflectedCompactGaussianRow s N t‖ := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, norm_reflectedCompactGaussianRow s hN t]
    simp only [Complex.sub_re, Complex.one_re]
    have hp : N ^ (s.re - 1) * Real.sqrt N = N ^ (s.re - 1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
      congr 1
      ring
    calc
      _ = ‖zetaChi (s + (t : ℂ) * I)‖ * (N ^ (s.re - 1) * Real.sqrt N) := by ring
      _ = _ := by rw [hp]
  have hsq := congrArg (fun x : ℝ => x ^ 2) hi
  rwa [mul_pow, Real.sq_sqrt hN.le] at hsq

/-- One measurable physical envelope controls all compact-disc points at the
same height. Its full physical integral is bounded by actual mask cardinality. -/
theorem exists_chiDual_masked_common_envelope
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ, (∀ n ∈ S, (N : ℝ) / 5 ≤ n ∧ (n : ℝ) ≤ 6 * N / 25) →
      ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
        (∀ t ∈ Icc (N : ℝ) (2 * N), ∀ s ∈ Metric.closedBall c r,
          ENNReal.ofReal (‖∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t‖ ^ 2) ≤ G t) ∧
        (∫⁻ t in Icc (N : ℝ) (2 * N), G t) ≤ ENNReal.ofReal (C * S.card) := by
  obtain ⟨C₀, hC₀, hunit⟩ := exists_chiDualUnitSpatialJets_bound c (r + 1)
  obtain ⟨C₁, hC₁, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  refine ⟨53 * C₀ ^ 2 * C₁ ^ 2 * (r + 1) ^ 2, by positivity, ?_⟩
  filter_upwards [hrow, eventually_ge_atTop (1 : ℕ)] with N hrow hN1
  have hN : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 < r + 1 := by linarith only [hr]
  intro S hS
  have hn (n : ℕ) (hn : n ∈ S) : 0 < n ∧ n ≤ N := by
    have hb := hS n hn
    have hp : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hN0 (by norm_num)) hb.1
    have hu : (n : ℝ) ≤ N := by linarith only [hb.2, hN0]
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hu⟩
  have hpos (n : ℕ) (hnS : n ∈ S) : 0 < n := (hn n hnS).1
  have hratio (n : ℕ) (hn : n ∈ S) : (n : ℝ) / N ∈ Icc (1 / 6 : ℝ) (1 / 3) := by
    have hb := hS n hn
    constructor
    · apply (le_div_iff₀ hN0).mpr
      linarith only [hb.1, hN0]
    · apply (div_le_iff₀ hN0).mpr
      linarith only [hb.2, hN0]
  let P := chiDualNormalizedMaskedPolynomial (N : ℝ) S
  have hPd : ∀ t, Differentiable ℂ (P t) := differentiable_chiDualNormalizedMaskedPolynomial hN0 S hpos
  have hPm : Measurable (fun q : ℝ × ℂ => P q.1 q.2) := measurable_chiDualNormalizedMaskedPolynomial hN0 S hpos
  let E := compactDiscMeanSqEnvelope P c r (r + 1)
  have hEm : Measurable E := measurable_compactDiscMeanSqEnvelope P hPm c r (r + 1)
  let W := Icc (N : ℝ) (2 * N)
  have hpoint (s : ℂ) (hs : s ∈ Metric.ball c (r + 1)) :
      (∫⁻ t, ENNReal.ofReal (‖P t s‖ ^ 2) ∂volume.restrict W) ≤
        ENNReal.ofReal (53 * (N : ℝ) * C₀ ^ 2 * S.card) := by
    have hPc : Continuous (fun t => P t s) := by
      unfold P chiDualNormalizedMaskedPolynomial zetaChiDualResonator
      apply continuous_finsetSum
      intro n _
      unfold bourgainOscillation
      fun_prop
    have hi : Integrable (fun t => ‖P t s‖ ^ 2) (volume.restrict W) := (hPc.norm.pow 2).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    have hb := integral_zetaChiDualResonator_sq_sharp_le hN S
      (fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)) hn (N : ℝ) N
    rw [show (N : ℝ) + N = 2 * N by ring, intervalIntegral.integral_of_le (by linarith only [hN0]),
      ← integral_Icc_eq_integral_Ioc] at hb
    have he : (∑ n ∈ S, ‖chiDualUnitSpatialAmplitude s ((n : ℝ) / N)‖ ^ 2) ≤ S.card * C₀ ^ 2 := by
      calc
        _ ≤ ∑ _n ∈ S, C₀ ^ 2 := Finset.sum_le_sum (fun n hnS =>
          pow_le_pow_left₀ (norm_nonneg _) (hunit s (Metric.ball_subset_closedBall hs) _ (hratio n hnS)).1 2)
        _ = _ := by simp
    apply hb.trans
    calc
      _ ≤ ((N : ℝ) + 52 * N) * (S.card * C₀ ^ 2) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  have hmean := lintegral_compactDiscMeanSqEnvelope_le (volume.restrict W) P hPm c r (r + 1)
    (53 * (N : ℝ) * C₀ ^ 2 * S.card) hpoint
  let G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (C₁ ^ 2 / (N : ℝ)) * E t
  refine ⟨G, hEm.const_mul _, ?_, ?_⟩
  · intro t ht s hs
    have hfac : ‖zetaChi (s + (t : ℂ) * I) * ((N : ℝ) : ℂ) ^ (s - 1)‖ ^ 2 ≤ C₁ ^ 2 / N := by
      apply (le_div_iff₀ hN0).mpr
      rw [norm_chiDualScaledFactor_sq hN0]
      exact pow_le_pow_left₀ (norm_nonneg _) (hrow t ht s hs).1 2
    rw [chiDualMaskedBlock_eq_normalized hN0 S hpos, norm_mul, mul_pow]
    calc
      _ ≤ ENNReal.ofReal ((C₁ ^ 2 / (N : ℝ)) * ‖P t s‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hfac (sq_nonneg _))
      _ = ENNReal.ofReal (C₁ ^ 2 / (N : ℝ)) * ENNReal.ofReal (‖P t s‖ ^ 2) :=
        ENNReal.ofReal_mul (by positivity)
      _ ≤ G t := mul_le_mul_right (norm_sq_le_compactDiscMeanSqEnvelope P hPd c (by linarith) t hs) _
  · change (∫⁻ t, ENNReal.ofReal (C₁ ^ 2 / (N : ℝ)) * E t ∂volume.restrict W) ≤ _
    rw [lintegral_const_mul _ hEm]
    apply (mul_le_mul_right hmean _).trans_eq
    have hvol : volume (Metric.ball c (r + 1)) = ENNReal.ofReal ((r + 1) ^ 2 * Real.pi) := by
      rw [Complex.volume_ball, ENNReal.ofReal_mul (sq_nonneg (r + 1)), ENNReal.ofReal_pow hρ.le,
        ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hvol, show r + 1 - r = (1 : ℝ) by ring, one_pow, mul_one]
    have he : ENNReal.ofReal (C₁ ^ 2 / (N : ℝ)) *
        (ENNReal.ofReal (Real.pi⁻¹) * ENNReal.ofReal (53 * (N : ℝ) * C₀ ^ 2 * S.card) *
          ENNReal.ofReal ((r + 1) ^ 2 * Real.pi)) =
        ENNReal.ofReal ((C₁ ^ 2 / (N : ℝ)) *
          (Real.pi⁻¹ * (53 * (N : ℝ) * C₀ ^ 2 * S.card) * ((r + 1) ^ 2 * Real.pi))) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C₁ ^ 2 / (N : ℝ)),
        ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi⁻¹ * (53 * (N : ℝ) * C₀ ^ 2 * S.card)),
        ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi⁻¹)]
    rw [he]
    congr 1
    field_simp

/-- A single measurable envelope controls the complete actual free-prime mask
simultaneously over the disc, with its full harmonic cofactor budget. -/
theorem exists_chiDual_prime_mask_common_envelope
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ, (∀ n ∈ S, (N : ℝ) / 5 ≤ n ∧ (n : ℝ) ≤ 6 * N / 25) →
      ∀ H : ℕ, 1 ≤ H → H ^ 2 ≤ N →
      ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
        (∀ t ∈ Icc (N : ℝ) (2 * N), ∀ s ∈ Metric.closedBall c r,
          ENNReal.ofReal (‖∑ n ∈ primeWindowSupported S N H,
            smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t‖ ^ 2) ≤ G t) ∧
        (∫⁻ t in Icc (N : ℝ) (2 * N), G t) * ENNReal.ofReal (Real.log N) ≤
          ENNReal.ofReal (C * (1 + Real.log H) * N) := by
  obtain ⟨C, hC, henv⟩ := exists_chiDual_masked_common_envelope c hr hc0 hc1
  refine ⟨C * (2 * Real.log 4), by positivity, ?_⟩
  filter_upwards [henv, eventually_ge_atTop (1 : ℕ)] with N henv hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  intro S hS H hH hHN
  have hsub : primeWindowSupported S N H ⊆ S := Finset.filter_subset _ _
  have hn (n : ℕ) (hn : n ∈ S) : 0 < n ∧ n ≤ N := by
    have hb := hS n hn
    have hp : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hN0 (by norm_num)) hb.1
    have hu : (n : ℝ) ≤ N := by linarith only [hb.2, hN0]
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hu⟩
  obtain ⟨G, hGm, hGpoint, hGmean⟩ := henv (primeWindowSupported S N H) (fun n hn => hS n (hsub hn))
  refine ⟨G, hGm, hGpoint, ?_⟩
  have hc := card_primeWindowSupported_mul_log_le_log hH hHN hn
  calc
    _ ≤ ENNReal.ofReal (C * (primeWindowSupported S N H).card) * ENNReal.ofReal (Real.log N) := by
      gcongr
    _ = ENNReal.ofReal (C * (primeWindowSupported S N H).card * Real.log N) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (C * (2 * (N : ℝ) * Real.log 4 * (1 + Real.log H))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = C * ((primeWindowSupported S N H).card * Real.log N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc hC.le
    _ = _ := by congr 1; ring

end RHTower
