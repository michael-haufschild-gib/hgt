import GaloisForLFunctions.RHTower.XiHorizontalStripDecay
import GaloisForLFunctions.RHTower.TiltedRiemannKernel
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact

/-!
# Exponential decay of `Ξ` on every horizontal strip

The complexified theta source `Φ(z)` decays double-exponentially in `|Re z|` on every closed
substrip `|Im z| ≤ δ`, `δ < π/4` (`norm_thetaCuspStripSource_le_of_rate`).  Hence it beats every
exponential:

**Lemma** (`exists_norm_thetaCuspStripSource_le_rate`).  For every `K ≥ 0` there is `C` with
`‖Φ(z)‖ ≤ C e^{−K|Re z|}` on `|Im z| ≤ δ`.

**Theorem** (`exists_norm_XiC_horizontal_le_wide`).  For every `A ≥ 0` and `0 ≤ δ < π/4` there is
`C` with `‖Ξ(t + ia)‖ ≤ C e^{−δ|t|}` for all real `t` and `|a| ≤ A`.

Proof.  `Ξ(w) = ∫ e^{−iwx} Φ(x) dx` for every `w` (`thetaCuspFourierLaplace_eq_XiC_all`).  Shift the
contour to `Im x = δ`; the tilt `e^{a Re x}` is absorbed by the source rate `K = A + 1`, and the
shift turns `Re w = t ≤ 0` into the factor `e^{tδ}`.  Evenness of `Ξ` covers `t > 0`.  This extends
the corpus bound, which was restricted to `A < 1`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- `e^{−y} ≤ m!/y^m` for `y > 0`. -/
theorem exp_neg_le_fact_div_pow {y : ℝ} (hy : 0 < y) (m : ℕ) :
    Real.exp (-y) ≤ (m.factorial : ℝ) / y ^ m := by
  have h := Real.pow_div_factorial_le_exp y hy.le m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  exact h

/-- **The theta source beats every exponential on a closed substrip.** -/
theorem exists_norm_thetaCuspStripSource_le_rate {δ K : ℝ} (hδ0 : 0 ≤ δ)
    (hδ4 : 2 * δ < Real.pi / 2) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ δ →
      ‖thetaCuspStripSource z‖ ≤ C * Real.exp (-(K * |z.re|)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_thetaCuspStripSource_le hδ0 hδ4
  have hcos : 0 < Real.cos (2 * δ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩
  set a : ℝ := Real.pi * Real.cos (2 * δ) with ha
  have ha0 : 0 < a := by positivity
  set m : ℕ := ⌈K⌉₊ + 3 with hm
  have hm2 : 9 / 2 + K ≤ 2 * (m : ℝ) := by
    have := Nat.le_ceil K
    rw [hm]; push_cast; linarith
  set x₀ : ℝ := max 0 (-Real.log a / 2) with hx₀
  have hx₀0 : 0 ≤ x₀ := le_max_left _ _
  set M := tiltedPhiTailConst * (m.factorial : ℝ) / a ^ m with hM
  have hM0 : 0 ≤ M := by
    have := tiltedPhiTailConst_nonneg; rw [hM]; positivity
  refine ⟨M + C₁ * Real.exp (K * x₀), by positivity, ?_⟩
  -- the bound for `0 ≤ Re z`
  have hright : ∀ z : ℂ, |z.im| ≤ δ → 0 ≤ z.re →
      ‖thetaCuspStripSource z‖ ≤ (M + C₁ * Real.exp (K * x₀)) * Real.exp (-(K * z.re)) := by
    intro z hz hre
    rcases le_or_gt x₀ z.re with hbig | hsmall
    · -- double-exponential regime
      have hX : 1 ≤ Real.pi * Real.cos (2 * δ) * Real.exp (2 * z.re) := by
        rw [← ha]
        have h2 : -Real.log a ≤ 2 * z.re := by
          have := le_max_right 0 (-Real.log a / 2); rw [← hx₀] at this; linarith
        have := Real.exp_le_exp.mpr h2
        rw [Real.exp_neg, Real.exp_log ha0] at this
        calc (1 : ℝ) = a * a⁻¹ := (mul_inv_cancel₀ ha0.ne').symm
          _ ≤ a * Real.exp (2 * z.re) := mul_le_mul_of_nonneg_left this ha0.le
      have hb := norm_thetaCuspStripSource_le_of_rate hδ4.le hz hre hX
      rw [← ha] at hb
      have hy : 0 < a * Real.exp (2 * z.re) := by positivity
      have he := exp_neg_le_fact_div_pow hy m
      have hpow : (a * Real.exp (2 * z.re)) ^ m = a ^ m * Real.exp (2 * m * z.re) := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
      rw [hpow] at he
      have hcomb : Real.exp (9 / 2 * z.re) * Real.exp (-(a * Real.exp (2 * z.re))) ≤
          (m.factorial : ℝ) / a ^ m * Real.exp (-(K * z.re)) := by
        calc Real.exp (9 / 2 * z.re) * Real.exp (-(a * Real.exp (2 * z.re)))
            ≤ Real.exp (9 / 2 * z.re) *
                ((m.factorial : ℝ) / (a ^ m * Real.exp (2 * m * z.re))) :=
              mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
          _ = (m.factorial : ℝ) / a ^ m * Real.exp (9 / 2 * z.re - 2 * m * z.re) := by
              rw [Real.exp_sub]; field_simp
          _ ≤ (m.factorial : ℝ) / a ^ m * Real.exp (-(K * z.re)) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
              nlinarith
      have hT := tiltedPhiTailConst_nonneg
      calc ‖thetaCuspStripSource z‖
          ≤ tiltedPhiTailConst * Real.exp (9 / 2 * z.re) *
              Real.exp (-(a * Real.exp (2 * z.re))) := hb
        _ = tiltedPhiTailConst *
              (Real.exp (9 / 2 * z.re) * Real.exp (-(a * Real.exp (2 * z.re)))) := by
            ring
        _ ≤ tiltedPhiTailConst * ((m.factorial : ℝ) / a ^ m * Real.exp (-(K * z.re))) :=
            mul_le_mul_of_nonneg_left hcomb hT
        _ = M * Real.exp (-(K * z.re)) := by rw [hM]; ring
        _ ≤ (M + C₁ * Real.exp (K * x₀)) * Real.exp (-(K * z.re)) := by
            have := Real.exp_pos (-(K * z.re))
            have : 0 ≤ C₁ * Real.exp (K * x₀) := by positivity
            nlinarith
    · -- bounded regime
      have hb := h₁ z hz
      rw [abs_of_nonneg hre] at hb
      have he : Real.exp (-z.re) ≤ Real.exp (K * x₀) * Real.exp (-(K * z.re)) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        nlinarith
      calc ‖thetaCuspStripSource z‖ ≤ C₁ * Real.exp (-z.re) := hb
        _ ≤ C₁ * (Real.exp (K * x₀) * Real.exp (-(K * z.re))) :=
            mul_le_mul_of_nonneg_left he hC₁
        _ ≤ (M + C₁ * Real.exp (K * x₀)) * Real.exp (-(K * z.re)) := by
            have := Real.exp_pos (-(K * z.re))
            nlinarith
  intro z hz
  rcases le_or_gt 0 z.re with hre | hre
  · rw [abs_of_nonneg hre]; exact hright z hz hre
  · have hzmem : z ∈ thetaCuspStrip := by
      rw [thetaCuspStrip, Set.mem_setOf_eq]; linarith
    rw [← thetaCuspStripSource_neg hzmem, abs_of_neg hre]
    have := hright (-z) (by rwa [Complex.neg_im, abs_neg]) (by rw [Complex.neg_re]; linarith)
    rwa [Complex.neg_re] at this

/-- **Exponential decay of `Ξ` on every horizontal strip.** -/
theorem exists_norm_XiC_horizontal_le_wide {A δ : ℝ} (hA : 0 ≤ A) (hδ0 : 0 ≤ δ)
    (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t a : ℝ, |a| ≤ A →
      ‖XiC ((t : ℂ) + (a : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(δ * |t|)) := by
  obtain ⟨CK, hCK, hK⟩ := exists_norm_thetaCuspStripSource_le_rate hδ0 hδ4
    (by linarith : (0 : ℝ) ≤ A + 1)
  set B : ℝ := ∫ x : ℝ, Real.exp (-(1 * |x|)) with hB
  have hBnn : 0 ≤ B := integral_nonneg fun x => (Real.exp_pos _).le
  have hδlt : δ < Real.pi / 4 := by linarith
  refine ⟨CK * B, by positivity, ?_⟩
  have hcore : ∀ t a : ℝ, t ≤ 0 → |a| ≤ A →
      ‖XiC ((t : ℂ) + (a : ℂ) * Complex.I)‖ ≤ CK * B * Real.exp (-(δ * |t|)) := by
    intro t a ht ha
    set w : ℂ := (t : ℂ) + (a : ℂ) * Complex.I with hw
    have hwre : w.re = t := by rw [hw]; simp
    have hwim : w.im = a := by rw [hw]; simp
    have hgen : ∀ (M : ℝ) (z : ℂ), t * z.im ≤ M → |z.im| ≤ δ →
        ‖thetaStripKernel w z‖ ≤ (CK * Real.exp M) * Real.exp (-(1 * |z.re|)) := by
      intro M z hM hz
      rw [norm_thetaStripKernel, hwre, hwim]
      have hKz := hK z hz
      have hexp1 : Real.exp (t * z.im + a * z.re) ≤ Real.exp M * Real.exp (A * |z.re|) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h2 : a * z.re ≤ A * |z.re| := by
          calc a * z.re ≤ |a * z.re| := le_abs_self _
            _ = |a| * |z.re| := abs_mul _ _
            _ ≤ A * |z.re| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        linarith
      calc Real.exp (t * z.im + a * z.re) * ‖thetaCuspStripSource z‖
          ≤ (Real.exp M * Real.exp (A * |z.re|)) * (CK * Real.exp (-((A + 1) * |z.re|))) :=
            mul_le_mul hexp1 hKz (norm_nonneg _) (by positivity)
        _ = (CK * Real.exp M) * (Real.exp (A * |z.re|) * Real.exp (-((A + 1) * |z.re|))) := by
            ring
        _ = (CK * Real.exp M) * Real.exp (-(1 * |z.re|)) := by
            rw [← Real.exp_add]; congr 2; ring
    have hbound : ∀ z : ℂ, |z.im| ≤ δ →
        ‖thetaStripKernel w z‖ ≤ (CK * Real.exp (|t| * δ)) * Real.exp (-(1 * |z.re|)) := by
      intro z hz
      refine hgen (|t| * δ) z ?_ hz
      calc t * z.im ≤ |t * z.im| := le_abs_self _
        _ = |t| * |z.im| := abs_mul _ _
        _ ≤ |t| * δ := mul_le_mul_of_nonneg_left hz (abs_nonneg t)
    have hdiff : ∀ z : ℂ, |z.im| ≤ δ → DifferentiableAt ℂ (thetaStripKernel w) z := by
      intro z hz
      refine differentiableAt_thetaStripKernel w ?_
      rw [thetaCuspStrip, Set.mem_setOf_eq]
      linarith [hz, hδlt]
    have hshift := integral_horizontal_shift_of_decay (F := thetaStripKernel w) (c := δ)
      (C := CK * Real.exp (|t| * δ)) (r := 1) hδ0 one_pos hdiff hbound
    have hFL : (∫ x : ℝ, thetaStripKernel w ((x : ℝ) : ℂ)) = XiC w := by
      rw [integral_thetaStripKernel_real]
      exact HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all w
    rw [← hFL, ← hshift]
    have hmaj : Integrable (fun x : ℝ =>
        (CK * Real.exp (t * δ)) * Real.exp (-(1 * |x|))) :=
      (integrable_exp_neg_mul_abs' one_pos).const_mul _
    have hbd : ∀ x : ℝ, ‖thetaStripKernel w ((x : ℂ) + (δ : ℂ) * Complex.I)‖ ≤
        (CK * Real.exp (t * δ)) * Real.exp (-(1 * |x|)) := by
      intro x
      have him : |((x : ℂ) + (δ : ℂ) * Complex.I).im| ≤ δ := by
        simpa using le_of_eq (abs_of_nonneg hδ0)
      have hval : ((x : ℂ) + (δ : ℂ) * Complex.I).im = δ := by simp
      have hre : ((x : ℂ) + (δ : ℂ) * Complex.I).re = x := by simp
      have := hgen (t * δ) _ (by rw [hval]) him
      rwa [hre] at this
    calc ‖∫ x : ℝ, thetaStripKernel w ((x : ℂ) + (δ : ℂ) * Complex.I)‖
        ≤ ∫ x : ℝ, ‖thetaStripKernel w ((x : ℂ) + (δ : ℂ) * Complex.I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, (CK * Real.exp (t * δ)) * Real.exp (-(1 * |x|)) := by
          refine integral_mono ?_ hmaj hbd
          refine Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall fun x => ?_)
          · have hcont : Continuous
                (fun x : ℝ => thetaStripKernel w ((x : ℂ) + (δ : ℂ) * Complex.I)) := by
              refine continuous_iff_continuousAt.mpr fun x => ?_
              have hmem : |((x : ℂ) + (δ : ℂ) * Complex.I).im| ≤ δ := by
                simpa using le_of_eq (abs_of_nonneg hδ0)
              have hcomp := ((hdiff _ hmem).continuousAt).comp (x := x)
                (f := fun y : ℝ => ((y : ℂ) + (δ : ℂ) * Complex.I)) (by fun_prop)
              simpa [Function.comp_def] using hcomp
            exact hcont.norm.aestronglyMeasurable
          · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            exact hbd x
      _ = (CK * Real.exp (t * δ)) * B := by
          rw [MeasureTheory.integral_const_mul, ← hB]
      _ = CK * B * Real.exp (-(δ * |t|)) := by
          rw [abs_of_nonpos ht]
          ring_nf
  intro t a ha
  rcases le_or_gt t 0 with ht | ht
  · exact hcore t a ht ha
  · have heven : XiC ((t : ℂ) + (a : ℂ) * Complex.I) =
        XiC (((-t : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * Complex.I) := by
      rw [show (((-t : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * Complex.I) =
        -((t : ℂ) + (a : ℂ) * Complex.I) by push_cast; ring, XiC_even]
    rw [heven]
    have hna : |(-a)| ≤ A := by rwa [abs_neg]
    have := hcore (-t) (-a) (by linarith) hna
    rwa [abs_neg] at this

end RHTower
