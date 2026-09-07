import GaloisForLFunctions.RHTower.WindowCarrierOscillation
import GaloisForLFunctions.RHTower.ProductAFEExact
import GaloisForLFunctions.RHTower.ZetaChiVerticalGrowth
import GaloisForLFunctions.HTGeometry.GaussianPolynomialTail

/-!
# Height oscillation of the windowed dual carrier weight

The dual side of the product approximate functional equation on the Levinson lines carries the
weight `χ(s₁)χ(s₂)·W(y)`, which is the frequency integral

`A_y(t) = (1/2π) ∫ G(t;v) k_y(v) dv`,   `G(t;v) = χ(s₁+w)χ(s₂+w)`,   `k_y(v) = y^{-(1+iv)} e^{(1+iv)²}/(1+iv)`.

Against the block window `w` and a height oscillation `e^{-iξt}`, Fubini turns the block integral
into a frequency integral of the windowed-carrier oscillations of `WindowCarrierOscillation`.  The
frequencies `|v| ≤ (p−η)/2` obey the `K`-fold integration-by-parts bound, uniformly through the
monotone jet constant, and the Gaussian kernel makes the remaining frequencies exponentially small
in `(p−η)²`.  The result is an explicit bound

`‖∫ w(t) A_y(t) e^{-iξt} dt‖ ≤ (1/2π)(e/y)(q−p+2η) · [ J_K e⁸(1+q+η+(p−η)/2)⁴ √π / |ξ|^K
                                                   + C (1+q+η)⁴ e^{16} e^{-(p−η)²/8} √(4π) ]`,

with `C` depending only on the displacement `d`.  Every power `K` of `1/|ξ|` is available.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The frequency kernel on the positive line `Re w = 1`. -/
def dualFrequencyKernel (y : ℝ) (v : ℝ) : ℂ :=
  smoothAFEMellinIntegrand y (((1 : ℝ) : ℂ) + (v : ℂ) * I)

theorem continuous_dualFrequencyKernel {y : ℝ} (hy : 0 < y) :
    Continuous (dualFrequencyKernel y) := by
  haveI : NeZero (y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hy.ne'⟩
  unfold dualFrequencyKernel smoothAFEMellinIntegrand smoothAFEGaussianKernel
  apply Continuous.mul
  · exact (continuous_const_cpow (y : ℂ)).comp (by fun_prop)
  · exact (Complex.continuous_exp.comp (by fun_prop)).div (by fun_prop) (fun v hzero => by
      have hre := congrArg Complex.re hzero
      norm_num at hre)

theorem norm_dualFrequencyKernel_le {y : ℝ} (hy : 0 < y) (v : ℝ) :
    ‖dualFrequencyKernel y v‖ ≤ (y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
  have hm := norm_smoothAFEMellinIntegrand_vertical_le hy (show (0 : ℝ) < 1 by norm_num) v
  simpa [dualFrequencyKernel, Real.rpow_neg_one] using hm

/-- The dual carrier weight `A_y(t) = (1/2π)∫ G(t;v) k_y(v) dv`. -/
def dualCarrierWeight (d y : ℝ) (t : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ, chiCarrier d v t * dualFrequencyKernel y v

/-- `A_y = χ(s₁)χ(s₂)·W(y)`: the carrier weight is the modulus weight times the exact two-ratio
dual weight of the product approximate functional equation. -/
theorem dualCarrierWeight_eq {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (y t : ℝ) :
    dualCarrierWeight d y t
      = chiPairWeight d t * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t)) y := by
  unfold dualCarrierWeight productAFEDualWeight
  rw [mul_smul_comm, ← integral_const_mul]
  congr 2
  funext v
  rw [chiCarrier_eq hd hdq v t]
  unfold chiRatioProduct dualFrequencyKernel levinsonShift
  push_cast
  ring

/-! ## Envelopes and continuity of the carrier on the whole plane -/

theorem continuous_chiCarrier_uncurry {d : ℝ} (hd : 0 < d) :
    Continuous (fun z : ℝ × ℝ => chiCarrier d z.2 z.1) := by
  have hχ : ∀ z : ℂ, z.re < 1 → ContinuousAt zetaChi z := fun z hz =>
    (zetaChi_analyticAt (Gammaℝ_ne_zero_of_re_pos
      (by rw [Complex.sub_re, Complex.one_re]; linarith))).continuousAt
  refine continuous_iff_continuousAt.mpr fun z => ?_
  unfold chiCarrier
  apply ContinuousAt.mul
  · have hA : Continuous (fun z : ℝ × ℝ => displacedLinePt d z.1 + levinsonShift z.2) := by
      unfold displacedLinePt levinsonShift
      fun_prop
    refine (hχ _ ?_).comp hA.continuousAt
    rw [displacedLinePt_add_levinsonShift_eq]
    simp
    linarith
  · have hA : Continuous (fun z : ℝ × ℝ => displacedLinePt d (-z.1) + levinsonShift z.2) := by
      unfold displacedLinePt levinsonShift
      fun_prop
    refine (hχ _ ?_).comp hA.continuousAt
    rw [displacedLinePt_add_levinsonShift_eq]
    simp
    linarith

/-- Whole-plane polynomial envelope of the carrier, with a constant depending only on `d`. -/
theorem exists_norm_chiCarrier_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v t : ℝ,
      ‖chiCarrier d v t‖ ≤ C * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_bound_norm_zetaChi_vertical (σ := -1 / 2 - d) (by linarith)
    (by linarith) (by linarith)
  refine ⟨C₀ ^ 2, by positivity, fun v t => ?_⟩
  unfold chiCarrier
  rw [displacedLinePt_add_levinsonShift_eq, displacedLinePt_add_levinsonShift_eq, norm_mul]
  calc ‖zetaChi (((-1 / 2 - d : ℝ) : ℂ) + ((t - v : ℝ) : ℂ) * I)‖
        * ‖zetaChi (((-1 / 2 - d : ℝ) : ℂ) + ((-t - v : ℝ) : ℂ) * I)‖
      ≤ (C₀ * (1 + |t - v|) ^ 2) * (C₀ * (1 + |-t - v|) ^ 2) :=
        mul_le_mul (h _) (h _) (norm_nonneg _) (by positivity)
    _ = C₀ ^ 2 * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2) := by
        rw [show -t - v = -(t + v) by ring, abs_neg]
        ring

/-- On the window support the envelope separates: `‖G(t;v)‖ ≤ C (1+q+η)⁴ (1+|v|)⁴`. -/
theorem norm_chiCarrier_le_window {d C : ℝ}
    (hC : ∀ v t : ℝ, ‖chiCarrier d v t‖ ≤ C * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2))
    (hC0 : 0 ≤ C) {p q η : ℝ} (hL : 0 ≤ p - η) (v : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (p - η) (q + η)) :
    ‖chiCarrier d v t‖ ≤ (C * (1 + (q + η)) ^ 4) * (1 + |v|) ^ 4 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hq : 0 ≤ q + η := by linarith [ht.2]
  have hv := abs_nonneg v
  have hb1 : 1 + |t - v| ≤ (1 + (q + η)) * (1 + |v|) := by
    have := abs_sub t v
    rw [abs_of_nonneg ht0] at this
    nlinarith [ht.2]
  have hb2 : 1 + |t + v| ≤ (1 + (q + η)) * (1 + |v|) := by
    have := abs_add_le t v
    rw [abs_of_nonneg ht0] at this
    nlinarith [ht.2]
  have h1 : (1 + |t - v|) ^ 2 ≤ ((1 + (q + η)) * (1 + |v|)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hb1 2
  have h2 : (1 + |t + v|) ^ 2 ≤ ((1 + (q + η)) * (1 + |v|)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hb2 2
  calc ‖chiCarrier d v t‖ ≤ C * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2) := hC v t
    _ ≤ C * (((1 + (q + η)) * (1 + |v|)) ^ 2 * ((1 + (q + η)) * (1 + |v|)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (C * (1 + (q + η)) ^ 4) * (1 + |v|) ^ 4 := by ring

/-- The jet constant is monotone in the frequency. -/
theorem windowCarrierJetConst_mono (K : ℕ) {η L v V : ℝ} (hη : 0 < η) (hL : 0 < L)
    (hV : 0 ≤ V) (hv : |v| ≤ V) :
    windowCarrierJetConst K η L v ≤ windowCarrierJetConst K η L V := by
  unfold windowCarrierJetConst
  refine Finset.sum_le_sum fun j _ => ?_
  have hbase : 33 * (1 + |v|) / L ≤ 33 * (1 + |V|) / L := by
    rw [abs_of_nonneg hV]
    apply div_le_div_of_nonneg_right _ hL.le
    linarith
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity)
    (div_nonneg (blockWindowConst_nonneg j) (by positivity)))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)

theorem norm_blockWindowC_le_one (p q η t : ℝ) : ‖blockWindowC p q η t‖ ≤ 1 := by
  unfold blockWindowC
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (blockWindow_nonneg p q η t)]
  exact blockWindow_le_one p q η t

theorem blockWindowC_eq_zero {p q η : ℝ} (hη : 0 < η) {t : ℝ}
    (ht : t ∉ Set.Icc (p - η) (q + η)) : blockWindowC p q η t = 0 := by
  have := iteratedDeriv_blockWindowC_eq_zero 0 hη ht
  simpa using this

theorem norm_cexp_neg_mul_I (ξ t : ℝ) : ‖Complex.exp (-(ξ * t) * I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **The windowed dual carrier weight against a height oscillation.** For every order `K`, with a
constant `C` depending only on the displacement `d`: for all blocks `[p, q]` with `p − η ≥ 4`,
every `y > 0` and every frequency `ξ ≠ 0`,

`‖∫ w(t) A_y(t) e^{-iξt} dt‖ ≤ (1/2π)(e/y)(q−p+2η) [J_K e⁸(1+q+η+(p−η)/2)⁴√π/|ξ|^K + C(1+q+η)⁴e^{16}e^{-(p−η)²/8}√(4π)]`. -/
theorem exists_norm_integral_blockWindow_dualCarrierWeight_le {d : ℝ} (hd : 0 < d)
    (hdq : d ≤ 1 / 4) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q η y ξ : ℝ), 4 ≤ p - η → p ≤ q → 0 < η → 0 < y → ξ ≠ 0 →
      ‖∫ t, blockWindowC p q η t * dualCarrierWeight d y t * Complex.exp (-(ξ * t) * I)‖
        ≤ (1 / (2 * Real.pi)) * ((y⁻¹ * Real.exp 1) * (q - p + 2 * η)) *
          (windowCarrierJetConst K η (p - η) ((p - η) / 2)
              * (Real.exp 8 * (1 + (q + η) + (p - η) / 2) ^ 4) * Real.sqrt Real.pi / |ξ| ^ K
            + C * (1 + (q + η)) ^ 4
              * (Real.exp 16 * Real.exp (-(((p - η) / 2) ^ 2) / 2) * Real.sqrt (4 * Real.pi))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_chiCarrier_le hd hdq
  refine ⟨C, hC0, fun p q η y ξ hL hpq hη hy hξ => ?_⟩
  -- notation
  set L : ℝ := p - η with hLdef
  set V : ℝ := L / 2 with hVdef
  set κ : ℝ := y⁻¹ * Real.exp 1 with hκdef
  set Cw : ℝ := C * (1 + (q + η)) ^ 4 with hCwdef
  set c : ℝ := 1 / (2 * Real.pi) with hcdef
  have hL0 : 0 < L := by linarith
  have hV0 : 0 ≤ V := by positivity
  have hκ0 : 0 ≤ κ := by positivity
  have hCw0 : 0 ≤ Cw := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hqη : 0 ≤ q + η := by linarith
  have hlen : 0 ≤ q - p + 2 * η := by linarith
  -- the joint integrand
  let F : ℝ × ℝ → ℂ := fun z =>
    windowCarrier d z.2 p q η z.1 * dualFrequencyKernel y z.2 * Complex.exp (-(ξ * z.1) * I)
  have hFcont : Continuous F := by
    have h1 : Continuous (fun z : ℝ × ℝ => windowCarrier d z.2 p q η z.1) := by
      unfold windowCarrier
      exact ((contDiff_blockWindowC p q η).continuous.comp continuous_fst).mul
        (continuous_chiCarrier_uncurry hd)
    have h2 : Continuous (fun z : ℝ × ℝ => dualFrequencyKernel y z.2) :=
      (continuous_dualFrequencyKernel hy).comp continuous_snd
    have h3 : Continuous (fun z : ℝ × ℝ => Complex.exp (-(ξ * z.1) * I)) := by fun_prop
    exact (h1.mul h2).mul h3
  -- pointwise envelope of the joint integrand
  have hFbound : ∀ z : ℝ × ℝ, ‖F z‖ ≤
      (Set.Icc (p - η) (q + η)).indicator (fun _ => (1 : ℝ)) z.1
        * ((Cw * κ) * ((1 + |z.2|) ^ 4 * Real.exp (-(z.2 ^ 2)))) := by
    intro z
    simp only [F, norm_mul, norm_cexp_neg_mul_I, mul_one]
    by_cases hz : z.1 ∈ Set.Icc (p - η) (q + η)
    · rw [Set.indicator_of_mem hz, one_mul]
      unfold windowCarrier
      rw [norm_mul]
      have hw := norm_blockWindowC_le_one p q η z.1
      have hG := norm_chiCarrier_le_window hC hC0 (by linarith) z.2 hz
      have hk := norm_dualFrequencyKernel_le hy z.2
      calc ‖blockWindowC p q η z.1‖ * ‖chiCarrier d z.2 z.1‖ * ‖dualFrequencyKernel y z.2‖
          ≤ 1 * (Cw * (1 + |z.2|) ^ 4) * (κ * Real.exp (-(z.2 ^ 2))) :=
            mul_le_mul (mul_le_mul hw hG (norm_nonneg _) zero_le_one) hk (norm_nonneg _)
              (by positivity)
        _ = (Cw * κ) * ((1 + |z.2|) ^ 4 * Real.exp (-(z.2 ^ 2))) := by ring
    · rw [Set.indicator_of_notMem hz, zero_mul]
      unfold windowCarrier
      rw [blockWindowC_eq_zero hη hz, zero_mul, norm_zero, zero_mul]
  have hFint : Integrable F (volume.prod volume) := by
    have hind : Integrable ((Set.Icc (p - η) (q + η)).indicator (fun _ => (1 : ℝ))) :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hpoly : Integrable (fun v : ℝ => (Cw * κ) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))) :=
      (integrable_one_add_abs_pow_mul_exp_neg_sq 4).const_mul _
    exact Integrable.mono' (hind.mul_prod hpoly) hFcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hFbound)
  -- the block integral is `c • ∫∫ F`
  have hpt : ∀ t, blockWindowC p q η t * dualCarrierWeight d y t * Complex.exp (-(ξ * t) * I)
      = c • ∫ v, F (t, v) := by
    intro t
    unfold dualCarrierWeight
    rw [mul_smul_comm, smul_mul_assoc, ← integral_const_mul, ← integral_mul_const]
    congr 2
    funext v
    simp only [F, windowCarrier]
    ring
  have hLHS : (∫ t, blockWindowC p q η t * dualCarrierWeight d y t * Complex.exp (-(ξ * t) * I))
      = c • ∫ v, ∫ t, F (t, v) := by
    rw [show (fun t => blockWindowC p q η t * dualCarrierWeight d y t
        * Complex.exp (-(ξ * t) * I)) = fun t => c • ∫ v, F (t, v) from funext hpt,
      integral_smul, integral_integral_swap hFint]
  -- the inner height integral
  have hinner : ∀ v, (∫ t, F (t, v)) = dualFrequencyKernel y v
      * ∫ t, windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I) := by
    intro v
    rw [← integral_const_mul]
    congr 1
    funext t
    simp only [F]
    ring
  -- integrability of the frequency integrand
  have hΦint : Integrable (fun v => ‖∫ t, F (t, v)‖) := hFint.integral_prod_right.norm
  -- the frequency set
  set S : Set ℝ := {v : ℝ | |v| ≤ V} with hSdef
  have hS : MeasurableSet S := (isClosed_le continuous_abs continuous_const).measurableSet
  -- main range bound
  set B₁ : ℝ := (q - p + 2 * η) * (windowCarrierJetConst K η L V
    * (Real.exp 8 * (1 + (q + η) + V) ^ 4)) with hB₁def
  have hB₁0 : 0 ≤ B₁ := mul_nonneg hlen (mul_nonneg
    (windowCarrierJetConst_nonneg K hη hL0 V) (by positivity))
  have hmain : ∀ v ∈ S, ‖∫ t, F (t, v)‖ ≤ (κ * B₁ / |ξ| ^ K) * Real.exp (-(v ^ 2)) := by
    intro v hv
    have hvV : |v| ≤ V := hv
    have h2v : 2 * |v| ≤ p - η := by linarith
    rw [hinner, norm_mul]
    have hk := norm_dualFrequencyKernel_le hy v
    have hI := norm_integral_windowCarrier_mul_cexp_le K hd hdq hη hL hpq h2v hξ
    have hJ := windowCarrierJetConst_mono K hη hL0 hV0 hvV
    have hpow : (1 + (q + η) + |v|) ^ 4 ≤ (1 + (q + η) + V) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hI' : ‖∫ t, windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I)‖ ≤ B₁ / |ξ| ^ K := by
      refine hI.trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [hB₁def]
      apply mul_le_mul_of_nonneg_left _ hlen
      exact mul_le_mul hJ (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by positivity) (windowCarrierJetConst_nonneg K hη hL0 V)
    calc ‖dualFrequencyKernel y v‖
          * ‖∫ t, windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I)‖
        ≤ (κ * Real.exp (-(v ^ 2))) * (B₁ / |ξ| ^ K) :=
          mul_le_mul hk hI' (norm_nonneg _) (by positivity)
      _ = (κ * B₁ / |ξ| ^ K) * Real.exp (-(v ^ 2)) := by ring
  -- tail range bound
  have htail : ∀ v, ‖∫ t, F (t, v)‖
      ≤ (κ * ((q - p + 2 * η) * Cw)) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
    intro v
    rw [hinner, norm_mul]
    have hk := norm_dualFrequencyKernel_le hy v
    have hI : ‖∫ t, windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I)‖
        ≤ (q - p + 2 * η) * (Cw * (1 + |v|) ^ 4) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      have hg : Integrable (fun t => windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I)) := by
        have hcont : Continuous (fun t => windowCarrier d v p q η t
            * Complex.exp (-(ξ * t) * I)) :=
          (contDiff_windowCarrier hd hdq v p q η 0).continuous.mul (by fun_prop)
        exact hcont.integrable_of_hasCompactSupport
          ((hasCompactSupport_windowCarrier hη).mul_right)
      have h := integral_norm_le_of_forall_mem_Icc (g := fun t => windowCarrier d v p q η t
          * Complex.exp (-(ξ * t) * I)) (a := p - η) (b := q + η)
          (M := Cw * (1 + |v|) ^ 4) (by linarith) hg
          (fun t ht => by
            show windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I) = 0
            unfold windowCarrier
            rw [blockWindowC_eq_zero hη ht, zero_mul, zero_mul])
          (fun t ht => by
            show ‖windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I)‖ ≤ Cw * (1 + |v|) ^ 4
            rw [norm_mul, norm_cexp_neg_mul_I, mul_one]
            unfold windowCarrier
            rw [norm_mul]
            calc ‖blockWindowC p q η t‖ * ‖chiCarrier d v t‖
                ≤ 1 * (Cw * (1 + |v|) ^ 4) :=
                  mul_le_mul (norm_blockWindowC_le_one p q η t)
                    (norm_chiCarrier_le_window hC hC0 (by linarith) v ht) (norm_nonneg _)
                    zero_le_one
              _ = Cw * (1 + |v|) ^ 4 := one_mul _)
      refine h.trans (le_of_eq ?_)
      ring
    calc ‖dualFrequencyKernel y v‖
          * ‖∫ t, windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I)‖
        ≤ (κ * Real.exp (-(v ^ 2))) * ((q - p + 2 * η) * (Cw * (1 + |v|) ^ 4)) :=
          mul_le_mul hk hI (norm_nonneg _) (by positivity)
      _ = (κ * ((q - p + 2 * η) * Cw)) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by ring
  -- assemble
  rw [hLHS, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hsplit : (∫ v, ‖∫ t, F (t, v)‖)
      = (∫ v in S, ‖∫ t, F (t, v)‖) + ∫ v in Sᶜ, ‖∫ t, F (t, v)‖ :=
    (integral_add_compl hS hΦint).symm
  have hS_bound : (∫ v in S, ‖∫ t, F (t, v)‖) ≤ (κ * B₁ / |ξ| ^ K) * Real.sqrt Real.pi := by
    have hint : Integrable (fun v : ℝ => (κ * B₁ / |ξ| ^ K) * Real.exp (-(v ^ 2))) := by
      have : Integrable (fun v : ℝ => Real.exp (-(v ^ 2))) := by
        simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
      exact this.const_mul _
    calc (∫ v in S, ‖∫ t, F (t, v)‖)
        ≤ ∫ v in S, (κ * B₁ / |ξ| ^ K) * Real.exp (-(v ^ 2)) :=
          setIntegral_mono_on hΦint.integrableOn hint.integrableOn hS hmain
      _ = (κ * B₁ / |ξ| ^ K) * ∫ v in S, Real.exp (-(v ^ 2)) := integral_const_mul _ _
      _ ≤ (κ * B₁ / |ξ| ^ K) * Real.sqrt Real.pi :=
          mul_le_mul_of_nonneg_left (setIntegral_exp_neg_sq_le S) (by positivity)
  have hSc_bound : (∫ v in Sᶜ, ‖∫ t, F (t, v)‖)
      ≤ (κ * ((q - p + 2 * η) * Cw))
          * (Real.exp (4 ^ 2) * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi)) := by
    have hint : Integrable (fun v : ℝ => (κ * ((q - p + 2 * η) * Cw))
        * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))) :=
      (integrable_one_add_abs_pow_mul_exp_neg_sq 4).const_mul _
    calc (∫ v in Sᶜ, ‖∫ t, F (t, v)‖)
        ≤ ∫ v in Sᶜ, (κ * ((q - p + 2 * η) * Cw)) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) :=
          setIntegral_mono_on hΦint.integrableOn hint.integrableOn hS.compl
            (fun v _ => htail v)
      _ = (κ * ((q - p + 2 * η) * Cw)) * ∫ v in Sᶜ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)) :=
          integral_const_mul _ _
      _ ≤ (κ * ((q - p + 2 * η) * Cw))
          * (Real.exp (4 ^ 2) * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := integral_one_add_abs_pow_mul_exp_neg_sq_compl_le 4 hV0
          simpa [hSdef] using this
  calc c * ‖∫ v, ∫ t, F (t, v)‖ ≤ c * ∫ v, ‖∫ t, F (t, v)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hc0
    _ = c * ((∫ v in S, ‖∫ t, F (t, v)‖) + ∫ v in Sᶜ, ‖∫ t, F (t, v)‖) := by rw [hsplit]
    _ ≤ c * ((κ * B₁ / |ξ| ^ K) * Real.sqrt Real.pi
          + (κ * ((q - p + 2 * η) * Cw))
            * (Real.exp (4 ^ 2) * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi))) :=
        mul_le_mul_of_nonneg_left (add_le_add hS_bound hSc_bound) hc0
    _ = c * (κ * (q - p + 2 * η)) *
          (windowCarrierJetConst K η L V * (Real.exp 8 * (1 + (q + η) + V) ^ 4)
              * Real.sqrt Real.pi / |ξ| ^ K
            + C * (1 + (q + η)) ^ 4
              * (Real.exp 16 * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi))) := by
        rw [hB₁def, hCwdef, show (4 : ℝ) ^ 2 = 16 by norm_num]
        ring

end RHTower

end
