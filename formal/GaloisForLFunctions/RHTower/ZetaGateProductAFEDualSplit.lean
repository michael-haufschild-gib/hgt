import GaloisForLFunctions.RHTower.DualOffDiagonalEnvelope

/-!
# The dual off-diagonal envelope with a free frequency split

`DualCarrierWeightOscillation.exists_norm_integral_blockWindow_dualCarrierWeight_le` splits the
frequency integral of the dual carrier weight at `|v| = (p − η)/2`.  With that split the jet
constant `windowCarrierJetConst K η (p−η) ((p−η)/2)` carries the carrier factor
`(33(1 + (p−η)/2)/(p−η))^{K−j} ≈ 16.5^{K−j}`, so the oscillation gain `J_K/|ξ|^K` never beats the
trivial bound for near-diagonal pairs and the intermediate range `Y ∈ [a, a²]` of the dual
off-diagonal sum is uncovered.

This module repeats the same three proofs with the split at an arbitrary `0 ≤ V ≤ (p − η)/2`
(main range: jets at frequency `V`; tail: `e^{−V²/2}`).  With `V ≍ √(log a)` the carrier factor
becomes `≍ (V/a)^{K−j}`, which is what the crude `ζΨ` gate assembly needs.  Everything else is
verbatim from `DualCarrierWeightOscillation` and `DualOffDiagonalEnvelope`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## A `χ` bound on the strip `−3/4 ≤ σ ≤ −1/2`, uniform in the abscissa -/

/-- `‖χ(σ+it)‖ ≤ C (1+|t|)²` for all `−3/4 ≤ σ ≤ −1/2` and all `t`, with one constant: the corpus
bound `e⁴(1+|t|)²` above ordinate `2` and compactness below it. -/
theorem exists_norm_zetaChi_le_negative_strip_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, -3 / 4 ≤ σ → σ ≤ -1 / 2 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2 := by
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Set.Icc (-3 / 4 : ℝ) (-1 / 2) ×ˢ Set.Icc (-2 : ℝ) 2)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn zetaChi K := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hG : Gammaℝ (1 - ((p.1 : ℂ) + (p.2 : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp
      linarith [hp.1.2]
    exact (zetaChi_analyticAt hG).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨Real.exp 4 + max C₀ 0, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hsq : (1 : ℝ) ≤ (1 + |t|) ^ 2 := one_le_pow₀ hbase
  have hsq0 : (0 : ℝ) ≤ (1 + |t|) ^ 2 := by positivity
  have hmax0 : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  have he4 : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos _).le
  rcases le_total 2 |t| with hbig | hsmall
  · have h := norm_zetaChi_le_negative_one_strip (by linarith) hσ2 hbig
    have hcoef : Real.exp 4 * (1 + |t|) ^ 2 ≤ (Real.exp 4 + max C₀ 0) * (1 + |t|) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hsq0
    linarith [h, hcoef]
  · have hmem : (σ : ℂ) + (t : ℂ) * I ∈ K :=
      ⟨(σ, t), ⟨⟨hσ1, hσ2⟩, abs_le.mp hsmall⟩, rfl⟩
    have h := hC₀ _ hmem
    have h' : ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max C₀ 0 := le_trans h (le_max_left _ _)
    have hcoef : max C₀ 0 * 1 ≤ (Real.exp 4 + max C₀ 0) * (1 + |t|) ^ 2 := by
      calc max C₀ 0 * 1 ≤ max C₀ 0 * (1 + |t|) ^ 2 := mul_le_mul_of_nonneg_left hsq hmax0
        _ ≤ (Real.exp 4 + max C₀ 0) * (1 + |t|) ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hsq0
    linarith [h', hcoef]

/-- The carrier bound `‖G(t;v)‖ ≤ C (1+|t−v|)² (1+|t+v|)²` with one constant for every
displacement `0 < d ≤ 1/4`. -/
theorem exists_norm_chiCarrier_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d v t : ℝ, 0 < d → d ≤ 1 / 4 →
      ‖chiCarrier d v t‖ ≤ C * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_norm_zetaChi_le_negative_strip_uniform
  refine ⟨C₀ ^ 2, by positivity, fun d v t hd hdq => ?_⟩
  unfold chiCarrier
  rw [displacedLinePt_add_levinsonShift_eq, displacedLinePt_add_levinsonShift_eq, norm_mul]
  calc ‖zetaChi (((-1 / 2 - d : ℝ) : ℂ) + ((t - v : ℝ) : ℂ) * I)‖
        * ‖zetaChi (((-1 / 2 - d : ℝ) : ℂ) + ((-t - v : ℝ) : ℂ) * I)‖
      ≤ (C₀ * (1 + |t - v|) ^ 2) * (C₀ * (1 + |-t - v|) ^ 2) :=
        mul_le_mul (h _ _ (by linarith) (by linarith)) (h _ _ (by linarith) (by linarith))
          (norm_nonneg _) (by positivity)
    _ = C₀ ^ 2 * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2) := by
        rw [show -t - v = -(t + v) by ring, abs_neg]
        ring

/-- **The dual carrier oscillation bound with a free frequency split `V`.** Identical to
`exists_norm_integral_blockWindow_dualCarrierWeight_le`, but the frequency integral is split at
`|v| = V` for any `0 ≤ V ≤ (p − η)/2`; the main range carries the jet constant at frequency `V`,
the tail carries `e^{−V²/2}`. -/
theorem norm_integral_blockWindow_dualCarrierWeight_le_split_of_bound {d : ℝ} (hd : 0 < d)
    (hdq : d ≤ 1 / 4) (K : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v t : ℝ, ‖chiCarrier d v t‖ ≤ C * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2)) :
    ∀ (p q η y ξ V : ℝ), 4 ≤ p - η → p ≤ q → 0 < η → 0 < y → ξ ≠ 0 →
      0 ≤ V → 2 * V ≤ p - η →
      ‖∫ t, blockWindowC p q η t * dualCarrierWeight d y t * Complex.exp (-(ξ * t) * I)‖
        ≤ (1 / (2 * Real.pi)) * ((y⁻¹ * Real.exp 1) * (q - p + 2 * η)) *
          (windowCarrierJetConst K η (p - η) V
              * (Real.exp 8 * (1 + (q + η) + V) ^ 4) * Real.sqrt Real.pi / |ξ| ^ K
            + C * (1 + (q + η)) ^ 4
              * (Real.exp 16 * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi))) := by
  intro p q η y ξ V hL hpq hη hy hξ hV0 hV2
  -- notation
  set L : ℝ := p - η with hLdef
  set κ : ℝ := y⁻¹ * Real.exp 1 with hκdef
  set Cw : ℝ := C * (1 + (q + η)) ^ 4 with hCwdef
  set c : ℝ := 1 / (2 * Real.pi) with hcdef
  have hL0 : 0 < L := by linarith
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


/-- The split oscillation bound with a constant depending only on `K` (not on `d`). -/
theorem exists_norm_integral_blockWindow_dualCarrierWeight_le_split_uniform (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 4 →
      ∀ (p q η y ξ V : ℝ), 4 ≤ p - η → p ≤ q → 0 < η → 0 < y → ξ ≠ 0 →
      0 ≤ V → 2 * V ≤ p - η →
      ‖∫ t, blockWindowC p q η t * dualCarrierWeight d y t * Complex.exp (-(ξ * t) * I)‖
        ≤ (1 / (2 * Real.pi)) * ((y⁻¹ * Real.exp 1) * (q - p + 2 * η)) *
          (windowCarrierJetConst K η (p - η) V
              * (Real.exp 8 * (1 + (q + η) + V) ^ 4) * Real.sqrt Real.pi / |ξ| ^ K
            + C * (1 + (q + η)) ^ 4
              * (Real.exp 16 * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_chiCarrier_le_uniform
  exact ⟨C, hC0, fun d hd hdq =>
    norm_integral_blockWindow_dualCarrierWeight_le_split_of_bound hd hdq K hC0
      (fun v t => hC d v t hd hdq)⟩

theorem exists_norm_integral_blockWindow_dualCarrierWeight_le_split {d : ℝ} (hd : 0 < d)
    (hdq : d ≤ 1 / 4) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q η y ξ V : ℝ), 4 ≤ p - η → p ≤ q → 0 < η → 0 < y → ξ ≠ 0 →
      0 ≤ V → 2 * V ≤ p - η →
      ‖∫ t, blockWindowC p q η t * dualCarrierWeight d y t * Complex.exp (-(ξ * t) * I)‖
        ≤ (1 / (2 * Real.pi)) * ((y⁻¹ * Real.exp 1) * (q - p + 2 * η)) *
          (windowCarrierJetConst K η (p - η) V
              * (Real.exp 8 * (1 + (q + η) + V) ^ 4) * Real.sqrt Real.pi / |ξ| ^ K
            + C * (1 + (q + η)) ^ 4
              * (Real.exp 16 * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_integral_blockWindow_dualCarrierWeight_le_split_uniform K
  exact ⟨C, hC0, hC d hd hdq⟩

/-- The oscillation-regime constant at a free frequency split `V`. -/
def dualOffDiagOscConstV (K : ℕ) (C x p q η V : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ((x⁻¹ * Real.exp 1) * (q - p + 2 * η)) *
    (windowCarrierJetConst K η (p - η) V
        * (Real.exp 8 * (1 + (q + η) + V) ^ 4) * Real.sqrt Real.pi * 2 ^ K
      + C * (1 + (q + η)) ^ 4
        * (Real.exp 16 * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi)))

theorem dualOffDiagOscConstV_nonneg (K : ℕ) {C x p q η V : ℝ} (hC : 0 ≤ C) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) (hV0 : 0 ≤ V) :
    0 ≤ dualOffDiagOscConstV K C x p q η V := by
  unfold dualOffDiagOscConstV
  have hlen : 0 ≤ q - p + 2 * η := by linarith
  have hJ := windowCarrierJetConst_nonneg K hη (show 0 < p - η by linarith) V
  have hqη : 0 ≤ q + η := by linarith
  have h1 : 0 ≤ 1 + (q + η) + V := by linarith
  positivity

/-- **Oscillation envelope of one dual off-diagonal term at a free split `V`.** -/
theorem dualOffDiagTerm_le_oscV {d : ℝ} (K : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (p q η y ξ V : ℝ), 4 ≤ p - η → p ≤ q → 0 < η → 0 < y → ξ ≠ 0 →
      0 ≤ V → 2 * V ≤ p - η →
      ‖∫ t, blockWindowC p q η t * dualCarrierWeight d y t * Complex.exp (-(ξ * t) * I)‖
        ≤ (1 / (2 * Real.pi)) * ((y⁻¹ * Real.exp 1) * (q - p + 2 * η)) *
          (windowCarrierJetConst K η (p - η) V
              * (Real.exp 8 * (1 + (q + η) + V) ^ 4) * Real.sqrt Real.pi / |ξ| ^ K
            + C * (1 + (q + η)) ^ 4
              * (Real.exp 16 * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi))))
    {x p q η V : ℝ} (hx : 0 < x) (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q)
    (hV0 : 0 ≤ V) (hV2 : 2 * V ≤ p - η)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (P : ℕ × ℕ) :
    dualOffDiagTerm d x p q η h k P
      ≤ dualOffDiagOscConstV K C x p q η V * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d)
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ ((K : ℝ) / 2 - 3 / 2 - d)) := by
  unfold dualOffDiagTerm
  split_ifs with hne
  · have hm : (0 : ℝ) < P.1 + 1 := by positivity
    have hn : (0 : ℝ) < P.2 + 1 := by positivity
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    set mn : ℝ := (P.1 + 1 : ℝ) * (P.2 + 1) with hmn
    set hk' : ℝ := (h : ℝ) * k with hhk
    have hmn0 : 0 < mn := by positivity
    have hhk0 : 0 < hk' := by positivity
    have hmn1 : 1 ≤ mn := by
      rw [hmn]
      have h1 : (1 : ℝ) ≤ P.1 + 1 := by
        have : (0 : ℝ) ≤ P.1 := by positivity
        linarith
      have h2 : (1 : ℝ) ≤ P.2 + 1 := by
        have : (0 : ℝ) ≤ P.2 := by positivity
        linarith
      nlinarith
    have hhk1 : 1 ≤ hk' := by
      rw [hhk]
      have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
      have h2 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    -- the frequency and its separation
    have hAn : 0 < (P.2 + 1) * h := by positivity
    have hBn : 0 < (P.1 + 1) * k := by positivity
    have hsep := inv_two_sqrt_le_abs_log_sub_log hAn hBn hne
    set ξ : ℝ := Real.log (((P.2 + 1) * h : ℕ) : ℝ) - Real.log (((P.1 + 1) * k : ℕ) : ℝ) with hξ
    have hprod : ((((P.2 + 1) * h : ℕ) : ℝ) * (((P.1 + 1) * k : ℕ) : ℝ)) = mn * hk' := by
      push_cast
      ring
    have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hsep
      have : (0 : ℝ) < 1 / (2 * Real.sqrt ((((P.2 + 1) * h : ℕ) : ℝ) * (((P.1 + 1) * k : ℕ) : ℝ))) := by
        rw [hprod]
        positivity
      linarith
    have hinv : 1 / |ξ| ^ K ≤ 2 ^ K * (mn * hk') ^ ((K : ℝ) / 2) := by
      have h1 : 1 / |ξ| ≤ 2 * Real.sqrt (mn * hk') := by
        rw [← hprod]
        have hpos : 0 < 2 * Real.sqrt ((((P.2 + 1) * h : ℕ) : ℝ) * (((P.1 + 1) * k : ℕ) : ℝ)) := by
          rw [hprod]; positivity
        rw [div_le_iff₀ (abs_pos.mpr hξ0)]
        have := hsep
        rw [div_le_iff₀ hpos] at this
        linarith
      have h2 : (1 / |ξ|) ^ K ≤ (2 * Real.sqrt (mn * hk')) ^ K :=
        pow_le_pow_left₀ (by positivity) h1 K
      rw [one_div_pow] at h2
      refine h2.trans (le_of_eq ?_)
      rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity),
        show (1 / 2 : ℝ) * K = (K : ℝ) / 2 by ring]
    -- the oscillation bound at `y = mn·x`
    have hy : 0 < mn * x := by positivity
    have hosc := hC p q η (mn * x) ξ V hL hpq hη hy hξ0 hV0 hV2
    -- notation for the two pieces
    set J : ℝ := windowCarrierJetConst K η (p - η) V
      * (Real.exp 8 * (1 + (q + η) + V) ^ 4) * Real.sqrt Real.pi with hJdef
    set G : ℝ := C * (1 + (q + η)) ^ 4
      * (Real.exp 16 * Real.exp (-(V ^ 2) / 2) * Real.sqrt (4 * Real.pi)) with hGdef
    have hJ0 : 0 ≤ J := by
      have := windowCarrierJetConst_nonneg K hη (show 0 < p - η by linarith) V
      have h1 : 0 ≤ 1 + (q + η) + V := by linarith
      positivity
    have hG0 : 0 ≤ G := by
      have : 0 ≤ 1 + (q + η) := by linarith
      positivity
    have hlen : 0 ≤ q - p + 2 * η := by linarith
    have hpow1 : 1 ≤ (mn * hk') ^ ((K : ℝ) / 2) :=
      Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hmn1 hhk1) (by positivity)
    -- combine: `J/|ξ|^K + G ≤ (J 2^K + G) (mn hk')^{K/2}`
    have hcomb : J / |ξ| ^ K + G ≤ (J * 2 ^ K + G) * (mn * hk') ^ ((K : ℝ) / 2) := by
      have h1 : J / |ξ| ^ K ≤ J * 2 ^ K * (mn * hk') ^ ((K : ℝ) / 2) := by
        rw [div_eq_mul_one_div]
        calc J * (1 / |ξ| ^ K) ≤ J * (2 ^ K * (mn * hk') ^ ((K : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hinv hJ0
          _ = J * 2 ^ K * (mn * hk') ^ ((K : ℝ) / 2) := by ring
      have h2 : G ≤ G * (mn * hk') ^ ((K : ℝ) / 2) := le_mul_of_one_le_right hG0 hpow1
      linarith
    have hosc' : ‖∫ t, blockWindowC p q η t * dualCarrierWeight d (mn * x) t
        * Complex.exp (-(ξ * t) * I)‖
        ≤ (1 / (2 * Real.pi)) * (((mn * x)⁻¹ * Real.exp 1) * (q - p + 2 * η))
          * ((J * 2 ^ K + G) * (mn * hk') ^ ((K : ℝ) / 2)) := by
      refine hosc.trans ?_
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    -- assemble the powers
    have hsplit : (mn * hk') ^ ((K : ℝ) / 2) = mn ^ ((K : ℝ) / 2) * hk' ^ ((K : ℝ) / 2) :=
      Real.mul_rpow hmn0.le hhk0.le
    have hmninv : (mn * x)⁻¹ = mn ^ (-(1 : ℝ)) * x⁻¹ := by
      rw [Real.rpow_neg_one, mul_inv]
    calc mn ^ (-(1 / 2 + d)) * hk' ^ (-(1 / 2 - d))
          * ‖∫ t, blockWindowC p q η t * dualCarrierWeight d (mn * x) t
              * Complex.exp (-(ξ * t) * I)‖
        ≤ mn ^ (-(1 / 2 + d)) * hk' ^ (-(1 / 2 - d))
          * ((1 / (2 * Real.pi)) * (((mn * x)⁻¹ * Real.exp 1) * (q - p + 2 * η))
            * ((J * 2 ^ K + G) * (mn * hk') ^ ((K : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hosc' (by positivity)
      _ = dualOffDiagOscConstV K C x p q η V * hk' ^ ((K : ℝ) / 2 - 1 / 2 + d)
            * mn ^ ((K : ℝ) / 2 - 3 / 2 - d) := by
          rw [hsplit, hmninv, dualOffDiagOscConstV, ← hJdef, ← hGdef,
            show hk' ^ ((K : ℝ) / 2 - 1 / 2 + d) = hk' ^ (-(1 / 2 - d)) * hk' ^ ((K : ℝ) / 2) by
              rw [← Real.rpow_add hhk0]; ring_nf,
            show mn ^ ((K : ℝ) / 2 - 3 / 2 - d)
                = mn ^ (-(1 / 2 + d)) * mn ^ (-(1 : ℝ)) * mn ^ ((K : ℝ) / 2) by
              rw [← Real.rpow_add hmn0, ← Real.rpow_add hmn0]; ring_nf]
          ring
  · exact mul_nonneg (mul_nonneg (dualOffDiagOscConstV_nonneg K hC0 hx hη hL hpq hV0)
      (by positivity)) (by positivity)

/-! ## Summation over the pairs `(m,n)` -/

/-- **The dual off-diagonal envelope, summed over `(m,n)`, at a free frequency split `V`.** -/
theorem exists_tsum_dualOffDiagTerm_le_split (K : ℕ) {K'' : ℕ} (hK'' : 1 ≤ K'') :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (d x p q η Y₀ V : ℝ) (h k : ℕ), 0 < d → d ≤ 1 / 4 →
      0 < x → 0 < η → 4 ≤ p - η →
      p ≤ q → 0 < Y₀ → 0 ≤ V → 2 * V ≤ p - η → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConstV K C₁ x p q η V * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ ((K : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst K'' C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-((K'' : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁u⟩ := exists_norm_integral_blockWindow_dualCarrierWeight_le_split_uniform K
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_dualCarrierWeight_le_rightShift hK''
  refine ⟨C₁, C₂, hC₁0, hC₂0,
    fun d x p q η Y₀ V h k hd hdq hx hη hL hpq hY₀ hV0 hV2 hh hk => ?_⟩
  have hC₁ := hC₁u d hd hdq
  have hOsc := dualOffDiagOscConstV_nonneg K hC₁0 hx hη hL hpq hV0
  have hSh := dualOffDiagShiftConst_nonneg K'' (d := d) hC₂0 hx hη hL hpq
  set Osc := dualOffDiagOscConstV K C₁ x p q η V with hOscdef
  set Sh := dualOffDiagShiftConst K'' C₂ d x p q η with hShdef
  have hbound : ∀ P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
      ≤ Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(5 / 2 + d)))
        + Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ))) := fun P =>
    dualOffDiagTerm_le_envelope hK'' hOsc hSh hh hk hY₀ P
      (dualOffDiagTerm_le_oscV K hC₁0 hC₁ hx hη hL hpq hV0 hV2 hh hk P)
      (dualOffDiagTerm_le_shift hd hdq K'' hC₂0 (fun Y τ hY => hC₂ d Y τ hd hdq hY) hx hη hL hpq
        hh hk P)
  have hr1 : (1 : ℝ) < 5 / 2 + d := by linarith
  have hr2 : (1 : ℝ) < 2 := by norm_num
  have hs1 : Summable (fun P : ℕ × ℕ =>
      Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(5 / 2 + d)))) :=
    (summable_prod_succ_rpow_neg hr1).mul_left _
  have hs2 : Summable (fun P : ℕ × ℕ =>
      Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)))) :=
    (summable_prod_succ_rpow_neg hr2).mul_left _
  have hterm : Summable (fun P : ℕ × ℕ => dualOffDiagTerm d x p q η h k P) :=
    Summable.of_nonneg_of_le (fun P => dualOffDiagTerm_nonneg _ _ _ _ _ _ _ P) hbound (hs1.add hs2)
  calc ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
      ≤ ∑' P : ℕ × ℕ, (Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(5 / 2 + d)))
        + Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)))) :=
        hterm.tsum_le_tsum hbound (hs1.add hs2)
    _ = Osc * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) * Y₀ ^ ((K : ℝ) / 2 + 1)
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
        + Sh * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * Y₀ ^ (-((K'' : ℝ) - 1))
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 := by
        rw [hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, tsum_prod_succ_rpow_neg hr1,
          tsum_prod_succ_rpow_neg hr2]

end RHTower

end
