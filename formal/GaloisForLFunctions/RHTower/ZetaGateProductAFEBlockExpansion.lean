import GaloisForLFunctions.RHTower.ZetaGateProductAFEDualSplit
import GaloisForLFunctions.RHTower.HardyZ
import GaloisForLFunctions.RHTower.EntireDirichletPolynomialTrace

/-!
# The block twisted moment of `ζΨ` through the product approximate functional equation

For `s₁ = σ₀ + it`, `s₂ = σ₀ − it` (`σ₀ = ½ − d`), the window `w = blockWindow p q η` and a real
mollifier `Ψ = edPoly b (Icc 1 N)`,

  `∫ w(t) ‖ζ(s₁)Ψ(s₁)‖² dt = Σ_{h,k} b_h b_k [Σ'_P directTerm + Σ'_P dualTerm − residueTerm]`,

where `directTerm` and `dualTerm` are the window integrals of the direct and dual double series of
`riemannZeta_mul_eq_productAFE` twisted by `(k/h)^{it}`, and `residueTerm` collects the two
Gaussian-decaying residues.  Off their diagonals the norms of `directTerm`/`dualTerm` are exactly
`directOffDiagTerm`/`dualOffDiagTerm` of the envelope modules.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## Powers on the displaced line: modulus times phase -/

theorem ofReal_cpow_neg_displacedLinePt {r : ℝ} (hr : 0 < r) (d τ : ℝ) :
    (r : ℂ) ^ (-displacedLinePt d τ)
      = ((r ^ (-(1 / 2 - d)) : ℝ) : ℂ) * Complex.exp (((-τ * Real.log r : ℝ) : ℂ) * I) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero hr0, ← Complex.ofReal_log hr.le]
  have h1 : ((Real.log r : ℝ) : ℂ) * (-displacedLinePt d τ)
      = ((Real.log r * (-(1 / 2 - d)) : ℝ) : ℂ) + ((-τ * Real.log r : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  rw [h1, Complex.exp_add, Real.rpow_def_of_pos hr, Complex.ofReal_exp]

theorem ofReal_cpow_displacedLinePt_sub_one {r : ℝ} (hr : 0 < r) (d τ : ℝ) :
    (r : ℂ) ^ (displacedLinePt d τ - 1)
      = ((r ^ ((1 / 2 - d) - 1) : ℝ) : ℂ) * Complex.exp (((τ * Real.log r : ℝ) : ℂ) * I) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero hr0, ← Complex.ofReal_log hr.le]
  have h1 : ((Real.log r : ℝ) : ℂ) * (displacedLinePt d τ - 1)
      = ((Real.log r * ((1 / 2 - d) - 1) : ℝ) : ℂ) + ((τ * Real.log r : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  rw [h1, Complex.exp_add, Real.rpow_def_of_pos hr, Complex.ofReal_exp]

theorem displacedLinePt_neg_eq_conj' (d t : ℝ) :
    displacedLinePt d (-t) = (starRingEnd ℂ) (displacedLinePt d t) := by
  unfold displacedLinePt
  apply Complex.ext <;> simp

theorem displacedLinePt_ne_one {d : ℝ} (hd : 0 < d) (t : ℝ) : displacedLinePt d t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp [displacedLinePt] at this
  linarith

theorem displacedLinePt_re_pos {d : ℝ} (hd4 : d ≤ 1 / 4) (t : ℝ) : 0 < (displacedLinePt d t).re := by
  simp [displacedLinePt]; linarith

theorem displacedLinePt_re_lt_one {d : ℝ} (hd : 0 < d) (t : ℝ) : (displacedLinePt d t).re < 1 := by
  simp [displacedLinePt]; linarith

theorem displacedLinePt_ne_neg {d t : ℝ} (ht : t ≠ 0) :
    displacedLinePt d t ≠ displacedLinePt d (-t) := by
  intro h
  have := congrArg Complex.im h
  simp [displacedLinePt] at this
  exact ht (by linarith)

/-! ## Continuity of the dual carrier weight in the height -/

theorem continuous_dualCarrierWeight {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {y : ℝ} (hy : 0 < y) :
    Continuous (dualCarrierWeight d y) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_chiCarrier_le hd hdq
  have hint : Continuous (fun t : ℝ => ∫ v : ℝ, chiCarrier d v t * dualFrequencyKernel y v) := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have hU : Continuous (Function.uncurry (fun t v : ℝ => chiCarrier d v t)) :=
      continuous_chiCarrier_uncurry hd
    have hcont_v : ∀ t : ℝ, Continuous (fun v : ℝ => chiCarrier d v t * dualFrequencyKernel y v) := by
      intro t
      have h1 : Continuous (fun v : ℝ => chiCarrier d v t) := hU.uncurry_left t
      exact h1.mul (continuous_dualFrequencyKernel hy)
    have hcont_t : ∀ v : ℝ, Continuous (fun t : ℝ => chiCarrier d v t) := fun v =>
      (contDiff_chiCarrier hd hdq v 0).continuous
    refine continuousAt_of_dominated
      (F := fun t v => chiCarrier d v t * dualFrequencyKernel y v)
      (bound := fun v : ℝ =>
        (C * (2 + |t₀|) ^ 4) * ((1 + |v|) ^ 4 * (y⁻¹ * Real.exp 1 * Real.exp (-(v ^ 2))))) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun t => (hcont_v t).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
      refine Filter.Eventually.of_forall fun v => ?_
      rw [norm_mul]
      have h1 := hC v t
      have hk := norm_dualFrequencyKernel_le hy v
      have htt : |t - t₀| < 1 := by simpa [Real.dist_eq] using ht
      have hbound : (1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2 ≤ (2 + |t₀|) ^ 4 * (1 + |v|) ^ 4 := by
        have ha : 1 + |t - v| ≤ (2 + |t₀|) * (1 + |v|) := by
          have : |t - v| ≤ |t - t₀| + |t₀| + |v| := by
            calc |t - v| = |(t - t₀) + t₀ - v| := by ring_nf
              _ ≤ |(t - t₀) + t₀| + |v| := abs_sub _ _
              _ ≤ |t - t₀| + |t₀| + |v| := by linarith [abs_add_le (t - t₀) t₀]
          nlinarith [abs_nonneg t₀, abs_nonneg v]
        have hb : 1 + |t + v| ≤ (2 + |t₀|) * (1 + |v|) := by
          have : |t + v| ≤ |t - t₀| + |t₀| + |v| := by
            calc |t + v| = |(t - t₀) + t₀ + v| := by ring_nf
              _ ≤ |(t - t₀) + t₀| + |v| := abs_add_le _ _
              _ ≤ |t - t₀| + |t₀| + |v| := by linarith [abs_add_le (t - t₀) t₀]
          nlinarith [abs_nonneg t₀, abs_nonneg v]
        have h0a : 0 ≤ 1 + |t - v| := by positivity
        have h0b : 0 ≤ 1 + |t + v| := by positivity
        calc (1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2
            ≤ ((2 + |t₀|) * (1 + |v|)) ^ 2 * ((2 + |t₀|) * (1 + |v|)) ^ 2 := by
              gcongr
          _ = (2 + |t₀|) ^ 4 * (1 + |v|) ^ 4 := by ring
      calc ‖chiCarrier d v t‖ * ‖dualFrequencyKernel y v‖
          ≤ (C * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2)) * (y⁻¹ * Real.exp 1 * Real.exp (-(v ^ 2))) :=
            mul_le_mul h1 hk (norm_nonneg _) (by positivity)
        _ ≤ (C * ((2 + |t₀|) ^ 4 * (1 + |v|) ^ 4)) * (y⁻¹ * Real.exp 1 * Real.exp (-(v ^ 2))) := by
            gcongr
        _ = (C * (2 + |t₀|) ^ 4) * ((1 + |v|) ^ 4 * (y⁻¹ * Real.exp 1 * Real.exp (-(v ^ 2)))) := by
            ring
    · have h0 := integrable_one_add_abs_pow_mul_exp_neg_sq 4
      have h1 := h0.const_mul (y⁻¹ * Real.exp 1)
      have h2 := h1.const_mul (C * (2 + |t₀|) ^ 4)
      refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
      simp only
      ring
    · exact Filter.Eventually.of_forall fun v =>
        ((hcont_t v).mul continuous_const).continuousAt
  unfold dualCarrierWeight
  exact hint.const_smul (1 / (2 * Real.pi) : ℝ)


/-! ## The three terms of the block twisted moment -/

/-- Direct term of the block twisted moment for the mollifier pair `(h,k)` and the series pair
`P = (m,n)` (here `m = P.1 + 1`, `n = P.2 + 1`). -/
def directTerm (d x p q η : ℝ) (h k : ℕ) (P : ℕ × ℕ) : ℂ :=
  ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
    * ((((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
    * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1)) / x)
    * ∫ t, blockWindowC p q η t * Complex.exp
        (-((Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ)) * t) * I)

/-- Dual term of the block twisted moment. -/
def dualTerm (d x p q η : ℝ) (h k : ℕ) (P : ℕ × ℕ) : ℂ :=
  ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
    * ((((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
    * ∫ t, blockWindowC p q η t * dualCarrierWeight d ((P.1 + 1 : ℝ) * (P.2 + 1) * x) t
        * Complex.exp (-(((Real.log (((P.2 + 1) * h : ℕ) : ℝ)
            - Real.log (((P.1 + 1) * k : ℕ) : ℝ) : ℝ) : ℂ) * t) * I)

/-- The two product-AFE residues, twisted and integrated against the window. -/
def residueTerm (d x p q η : ℝ) (h k : ℕ) : ℂ :=
  ∫ t, blockWindowC p q η t
    * ((h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t)))
    * (productAFEShiftedResidue (displacedLinePt d t) (displacedLinePt d (-t)) x
      + productAFEShiftedResidue (displacedLinePt d (-t)) (displacedLinePt d t) x)

/-! ## Pointwise identities for the integrands -/

/-- The direct integrand: coefficient times cutoff times window phase. -/
theorem direct_integrand_eq {d x : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (P : ℕ × ℕ) (p q η t : ℝ) :
    blockWindowC p q η t * ((h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t)))
      * ((P.1 + 1 : ℂ) ^ (-displacedLinePt d t) * (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
        * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x))
    = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1)) / x)
        * (blockWindowC p q η t * Complex.exp
          (-((Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ)) * t) * I)) := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  have e1 : (h : ℂ) ^ (-displacedLinePt d t)
      = (((h : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ) * Complex.exp (((-t * Real.log h : ℝ) : ℂ) * I) :=
    ofReal_cpow_neg_displacedLinePt hhr d t
  have e2 : (k : ℂ) ^ (-displacedLinePt d (-t))
      = (((k : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ) * Complex.exp (((-(-t) * Real.log k : ℝ) : ℂ) * I) :=
    ofReal_cpow_neg_displacedLinePt hkr d (-t)
  have e3 : (P.1 + 1 : ℂ) ^ (-displacedLinePt d t)
      = (((P.1 + 1 : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * Complex.exp (((-t * Real.log (P.1 + 1 : ℝ) : ℝ) : ℂ) * I) := by
    have := ofReal_cpow_neg_displacedLinePt hm d t
    push_cast at this ⊢
    exact this
  have e4 : (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
      = (((P.2 + 1 : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * Complex.exp (((-(-t) * Real.log (P.2 + 1 : ℝ) : ℝ) : ℂ) * I) := by
    have := ofReal_cpow_neg_displacedLinePt hn d (-t)
    push_cast at this ⊢
    exact this
  rw [e1, e2, e3, e4]
  have hc1 : (((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) = (h : ℝ) ^ (-(1 / 2 - d)) * (k : ℝ) ^ (-(1 / 2 - d)) :=
    Real.mul_rpow hhr.le hkr.le
  have hc2 : (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d)) : ℝ)
      = (P.1 + 1 : ℝ) ^ (-(1 / 2 - d)) * (P.2 + 1 : ℝ) ^ (-(1 / 2 - d)) :=
    Real.mul_rpow hm.le hn.le
  have hlog1 : Real.log (((P.1 + 1) * h : ℕ) : ℝ) = Real.log (P.1 + 1 : ℝ) + Real.log h := by
    push_cast
    exact Real.log_mul hm.ne' hhr.ne'
  have hlog2 : Real.log (((P.2 + 1) * k : ℕ) : ℝ) = Real.log (P.2 + 1 : ℝ) + Real.log k := by
    push_cast
    exact Real.log_mul hn.ne' hkr.ne'
  have hexp : Complex.exp (((-t * Real.log h : ℝ) : ℂ) * I)
      * Complex.exp (((-(-t) * Real.log k : ℝ) : ℂ) * I)
      * (Complex.exp (((-t * Real.log (P.1 + 1 : ℝ) : ℝ) : ℂ) * I)
        * Complex.exp (((-(-t) * Real.log (P.2 + 1 : ℝ) : ℝ) : ℂ) * I))
      = Complex.exp
          (-((Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ)) * t) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hlog1, hlog2]
    congr 1
    push_cast
    ring
  rw [hc1, hc2, ← hexp]
  push_cast
  ring

/-- The dual integrand: coefficient times window times carrier weight times phase. -/
theorem dual_integrand_eq {d x : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (P : ℕ × ℕ) (p q η t : ℝ) :
    blockWindowC p q η t * ((h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t)))
      * ((zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))
          * (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1) * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1))
        * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t))
            ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x))
    = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
        * (blockWindowC p q η t * dualCarrierWeight d ((P.1 + 1 : ℝ) * (P.2 + 1) * x) t
            * Complex.exp (-(((Real.log (((P.2 + 1) * h : ℕ) : ℝ)
                - Real.log (((P.1 + 1) * k : ℕ) : ℝ) : ℝ) : ℂ) * t) * I)) := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  rw [dualCarrierWeight_eq hd hdq, chiPairWeight]
  have e1 : (h : ℂ) ^ (-displacedLinePt d t)
      = (((h : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ) * Complex.exp (((-t * Real.log h : ℝ) : ℂ) * I) :=
    ofReal_cpow_neg_displacedLinePt hhr d t
  have e2 : (k : ℂ) ^ (-displacedLinePt d (-t))
      = (((k : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ) * Complex.exp (((-(-t) * Real.log k : ℝ) : ℂ) * I) :=
    ofReal_cpow_neg_displacedLinePt hkr d (-t)
  have e3 : (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1)
      = (((P.1 + 1 : ℝ) ^ ((1 / 2 - d) - 1) : ℝ) : ℂ)
        * Complex.exp (((t * Real.log (P.1 + 1 : ℝ) : ℝ) : ℂ) * I) := by
    have := ofReal_cpow_displacedLinePt_sub_one hm d t
    push_cast at this ⊢
    exact this
  have e4 : (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1)
      = (((P.2 + 1 : ℝ) ^ ((1 / 2 - d) - 1) : ℝ) : ℂ)
        * Complex.exp ((((-t) * Real.log (P.2 + 1 : ℝ) : ℝ) : ℂ) * I) := by
    have := ofReal_cpow_displacedLinePt_sub_one hn d (-t)
    push_cast at this ⊢
    exact this
  rw [e1, e2, e3, e4]
  have hc1 : (((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) = (h : ℝ) ^ (-(1 / 2 - d)) * (k : ℝ) ^ (-(1 / 2 - d)) :=
    Real.mul_rpow hhr.le hkr.le
  have hc2 : (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d)) : ℝ)
      = (P.1 + 1 : ℝ) ^ ((1 / 2 - d) - 1) * (P.2 + 1 : ℝ) ^ ((1 / 2 - d) - 1) := by
    rw [show (-(1 / 2 + d) : ℝ) = (1 / 2 - d) - 1 by ring]
    exact Real.mul_rpow hm.le hn.le
  have hlog1 : Real.log (((P.2 + 1) * h : ℕ) : ℝ) = Real.log (P.2 + 1 : ℝ) + Real.log h := by
    push_cast
    exact Real.log_mul hn.ne' hhr.ne'
  have hlog2 : Real.log (((P.1 + 1) * k : ℕ) : ℝ) = Real.log (P.1 + 1 : ℝ) + Real.log k := by
    push_cast
    exact Real.log_mul hm.ne' hkr.ne'
  have hexp : Complex.exp (((-t * Real.log h : ℝ) : ℂ) * I)
      * Complex.exp (((-(-t) * Real.log k : ℝ) : ℂ) * I)
      * (Complex.exp (((t * Real.log (P.1 + 1 : ℝ) : ℝ) : ℂ) * I)
        * Complex.exp ((((-t) * Real.log (P.2 + 1 : ℝ) : ℝ) : ℂ) * I))
      = Complex.exp (-(((Real.log (((P.2 + 1) * h : ℕ) : ℝ)
            - Real.log (((P.1 + 1) * k : ℕ) : ℝ) : ℝ) : ℂ) * t) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hlog1, hlog2]
    congr 1
    push_cast
    ring
  rw [hc1, hc2, ← hexp]
  push_cast
  ring

/-! ## The pointwise expansion of `‖ζΨ‖²` -/

/-- **Pointwise product-AFE expansion.**  For `t > 0`, the squared modulus of `ζΨ` on the displaced
line is the mollifier double sum of the product AFE at scale `x`. -/
theorem normSq_zeta_mul_edPoly_eq {d x : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x)
    {t : ℝ} (ht : t ≠ 0) (b : ℕ → ℂ) (N : ℕ)
    (hbreal : ∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) :
    ((‖riemannZeta (displacedLinePt d t) * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, b h * b k
          * ((h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t)))
          * ((∑' P : ℕ × ℕ, (P.1 + 1 : ℂ) ^ (-displacedLinePt d t)
                * (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
                * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x))
            + (∑' P : ℕ × ℕ, (zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))
                * (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1)
                * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1))
                * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t))
                    ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x))
            - productAFEShiftedResidue (displacedLinePt d t) (displacedLinePt d (-t)) x
            - productAFEShiftedResidue (displacedLinePt d (-t)) (displacedLinePt d t) x) := by
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hconj : displacedLinePt d (-t) = (starRingEnd ℂ) (displacedLinePt d t) :=
    displacedLinePt_neg_eq_conj' d t
  have hre : 0 < (displacedLinePt d t).re := displacedLinePt_re_pos hd4 t
  have hne1 : displacedLinePt d t ≠ 1 := displacedLinePt_ne_one hd t
  -- `‖z‖² = z · conj z`
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_mul,
    ← riemannZeta_conj_of_re_pos hre hne1, ← edPoly_conj b hs hbreal, ← hconj]
  -- the product AFE
  rw [show riemannZeta (displacedLinePt d t) * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)
        * (riemannZeta (displacedLinePt d (-t)) * edPoly b (Finset.Icc 1 N) (displacedLinePt d (-t)))
      = (riemannZeta (displacedLinePt d t) * riemannZeta (displacedLinePt d (-t)))
        * (edPoly b (Finset.Icc 1 N) (displacedLinePt d t)
          * edPoly b (Finset.Icc 1 N) (displacedLinePt d (-t))) by ring]
  rw [riemannZeta_mul_eq_productAFE hx hre (displacedLinePt_re_lt_one hd t)
    (displacedLinePt_re_pos hd4 (-t)) (displacedLinePt_re_lt_one hd (-t)) (displacedLinePt_ne_neg ht)]
  unfold edPoly
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.ofReal_natCast]
  ring


/-! ## The series functions and their regularity -/

/-- The pair coefficient `h^{-s₁} k^{-s₂}`. -/
def pairCoeff (d : ℝ) (h k : ℕ) (t : ℝ) : ℂ :=
  (h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t))

/-- The direct double series of the product AFE at scale `x`. -/
def directSeries (d x t : ℝ) : ℂ :=
  ∑' P : ℕ × ℕ, (P.1 + 1 : ℂ) ^ (-displacedLinePt d t) * (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
    * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x)

/-- The dual double series of the product AFE at scale `x`. -/
def dualSeries (d x t : ℝ) : ℂ :=
  ∑' P : ℕ × ℕ, (zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))
      * (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1) * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1))
    * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t))
        ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x)

/-- The two product-AFE residues. -/
def residuePair (d x t : ℝ) : ℂ :=
  productAFEShiftedResidue (displacedLinePt d t) (displacedLinePt d (-t)) x
    + productAFEShiftedResidue (displacedLinePt d (-t)) (displacedLinePt d t) x

theorem continuous_displacedLinePt (d : ℝ) : Continuous (fun t : ℝ => displacedLinePt d t) := by
  unfold displacedLinePt
  fun_prop

theorem continuous_displacedLinePt_neg (d : ℝ) : Continuous (fun t : ℝ => displacedLinePt d (-t)) :=
  (continuous_displacedLinePt d).comp continuous_neg

theorem continuous_pairCoeff (d : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Continuous (pairCoeff d h k) := by
  unfold pairCoeff
  have h0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have k0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  exact ((continuous_displacedLinePt d).neg.const_cpow (Or.inl h0)).mul
    ((continuous_displacedLinePt_neg d).neg.const_cpow (Or.inl k0))

theorem norm_pairCoeff {d : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (t : ℝ) :
    ‖pairCoeff d h k t‖ = ((h : ℝ) * k) ^ (-(1 / 2 - d)) := by
  unfold pairCoeff
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hh, Complex.norm_natCast_cpow_of_pos hk]
  have e1 : (-displacedLinePt d t).re = -(1 / 2 - d) := by simp [displacedLinePt]
  have e2 : (-displacedLinePt d (-t)).re = -(1 / 2 - d) := by simp [displacedLinePt]
  rw [e1, e2, ← Real.mul_rpow (by positivity) (by positivity)]

/-- Continuity of one direct summand in the height. -/
theorem continuous_direct_summand (d x : ℝ) (P : ℕ × ℕ) :
    Continuous (fun t : ℝ => (P.1 + 1 : ℂ) ^ (-displacedLinePt d t)
      * (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
      * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x)) := by
  have hm : (P.1 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero P.1
  have hn : (P.2 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero P.2
  exact (((continuous_displacedLinePt d).neg.const_cpow (Or.inl hm)).mul
    ((continuous_displacedLinePt_neg d).neg.const_cpow (Or.inl hn))).mul continuous_const

/-- The dual summand in carrier form. -/
theorem dual_summand_eq {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (x t : ℝ) (P : ℕ × ℕ) :
    (zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))
        * (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1) * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1))
      * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t))
          ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x)
    = (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1) * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1)
      * dualCarrierWeight d ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x) t := by
  rw [dualCarrierWeight_eq hd hdq, chiPairWeight]
  ring

theorem continuous_dual_summand {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {x : ℝ} (hx : 0 < x)
    (P : ℕ × ℕ) :
    Continuous (fun t : ℝ => (zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))
        * (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1) * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1))
      * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t))
          ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x)) := by
  have hm : (P.1 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero P.1
  have hn : (P.2 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero P.2
  have hY : 0 < (P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x := by positivity
  have h1 : Continuous (fun t : ℝ => (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1)) :=
    ((continuous_displacedLinePt d).sub continuous_const).const_cpow (Or.inl hm)
  have h2 : Continuous (fun t : ℝ => (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1)) :=
    ((continuous_displacedLinePt_neg d).sub continuous_const).const_cpow (Or.inl hn)
  have h := (h1.mul h2).mul (continuous_dualCarrierWeight hd hdq hY)
  refine h.congr fun t => ?_
  exact (dual_summand_eq hd hdq x t P).symm

/-- The norm of a dual summand on a height window, from the right-shift bound. -/
theorem norm_dual_summand_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {x : ℝ} (hx : 0 < x)
    {C : ℝ} (hC : ∀ Y τ : ℝ, 0 < Y → ‖dualCarrierWeight d Y τ‖ ≤
        C * (1 + |τ|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) * Y ^ (-(1 / 2 - d + (1 : ℕ))))
    {T t : ℝ} (ht : |t| ≤ T) (P : ℕ × ℕ) :
    ‖(zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))
        * (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1) * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1))
      * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t))
          ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x)‖
    ≤ (C * (1 + T) ^ (3 : ℝ) * x ^ (-(3 / 2 - d))) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)) := by
  rw [dual_summand_eq hd hdq x t P, norm_mul, norm_mul]
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  have hY : 0 < (P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x := by positivity
  have e1 : ‖(P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1)‖ = (P.1 + 1 : ℝ) ^ ((1 / 2 - d) - 1) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos hm (displacedLinePt d t - 1)
    push_cast at this ⊢
    rw [this]
    congr 1
    simp [displacedLinePt]
  have e2 : ‖(P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1)‖ = (P.2 + 1 : ℝ) ^ ((1 / 2 - d) - 1) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos hn (displacedLinePt d (-t) - 1)
    push_cast at this ⊢
    rw [this]
    congr 1
    simp [displacedLinePt]
  rw [e1, e2]
  have hA := hC _ t hY
  have h1T : (1 + |t|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) ≤ (1 + T) ^ (3 : ℝ) := by
    rw [show (2 * ((1 : ℕ) + 1 / 2 : ℝ)) = (3 : ℝ) by norm_num]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hYpow : ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x) ^ (-(1 / 2 - d + (1 : ℕ)))
      = ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(3 / 2 - d)) * x ^ (-(3 / 2 - d)) := by
    rw [show (-(1 / 2 - d + ((1 : ℕ) : ℝ)) : ℝ) = -(3 / 2 - d) by push_cast; ring,
      Real.mul_rpow (by positivity) hx.le]
  have hcoef : (P.1 + 1 : ℝ) ^ ((1 / 2 - d) - 1) * (P.2 + 1 : ℝ) ^ ((1 / 2 - d) - 1)
      = ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d)) := by
    rw [show ((1 / 2 - d) - 1 : ℝ) = -(1 / 2 + d) by ring, Real.mul_rpow hm.le hn.le]
  have hexp : ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d)) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(3 / 2 - d))
      = ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  calc (P.1 + 1 : ℝ) ^ ((1 / 2 - d) - 1) * (P.2 + 1 : ℝ) ^ ((1 / 2 - d) - 1)
        * ‖dualCarrierWeight d ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x) t‖
      ≤ ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d))
        * (C * (1 + T) ^ (3 : ℝ) * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(3 / 2 - d)) * x ^ (-(3 / 2 - d)))) := by
        rw [hcoef]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine hA.trans ?_
        rw [hYpow]
        have hC0 : 0 ≤ C := by
          have := hC 1 0 one_pos
          have hn0 := norm_nonneg (dualCarrierWeight d 1 0)
          nlinarith [Real.one_rpow (2 * ((1 : ℕ) + 1 / 2 : ℝ)), Real.one_rpow (-(1 / 2 - d + (1 : ℕ)))]
        have := mul_le_mul_of_nonneg_left h1T hC0
        have h2 : 0 ≤ ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(3 / 2 - d)) * x ^ (-(3 / 2 - d)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right this h2]
    _ = (C * (1 + T) ^ (3 : ℝ) * x ^ (-(3 / 2 - d))) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)) := by
        rw [← hexp]; ring


/-! ## Integrability on the window -/

/-- A function continuous on the closed window support, multiplied by the window, is integrable. -/
theorem integrable_window_mul {p q η : ℝ} (hη : 0 < η) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Icc (p - η) (q + η))) :
    Integrable (fun t => blockWindowC p q η t * g t) := by
  have hcont : ContinuousOn (fun t => blockWindowC p q η t * g t) (Set.Icc (p - η) (q + η)) :=
    (contDiff_blockWindowC p q η).continuous.continuousOn.mul hg
  refine (hcont.integrableOn_compact isCompact_Icc).integrable_of_forall_notMem_eq_zero ?_
  intro t ht
  rw [blockWindowC_eq_zero hη ht, zero_mul]

theorem norm_direct_summand {d x : ℝ} (P : ℕ × ℕ) (t : ℝ) :
    ‖(P.1 + 1 : ℂ) ^ (-displacedLinePt d t) * (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
      * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x)‖
    = ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d))
      * ‖smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x)‖ := by
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  rw [norm_mul, norm_mul]
  have e1 : ‖(P.1 + 1 : ℂ) ^ (-displacedLinePt d t)‖ = (P.1 + 1 : ℝ) ^ (-(1 / 2 - d)) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos hm (-displacedLinePt d t)
    push_cast at this ⊢
    rw [this]
    congr 1
    simp [displacedLinePt]
  have e2 : ‖(P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))‖ = (P.2 + 1 : ℝ) ^ (-(1 / 2 - d)) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos hn (-displacedLinePt d (-t))
    push_cast at this ⊢
    rw [this]
    congr 1
    simp [displacedLinePt]
  rw [e1, e2, ← Real.mul_rpow hm.le hn.le]

/-- Uniform majorant of the direct summands. -/
theorem exists_direct_majorant {d x : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x) :
    ∃ u : ℕ × ℕ → ℝ, Summable u ∧ ∀ P t,
      ‖(P.1 + 1 : ℂ) ^ (-displacedLinePt d t) * (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
        * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x)‖ ≤ u P := by
  obtain ⟨K, hK0, hV⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) two_pos
  refine ⟨fun P => K * x ^ (2 : ℝ) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-((1 / 2 - d) + 2)), ?_, ?_⟩
  · exact (summable_prod_succ_rpow_neg (by linarith)).mul_left _
  · intro P t
    rw [norm_direct_summand]
    have hm : (0 : ℝ) < P.1 + 1 := by positivity
    have hn : (0 : ℝ) < P.2 + 1 := by positivity
    have hmn : (0 : ℝ) < (P.1 + 1 : ℝ) * (P.2 + 1) := by positivity
    have hu : (0 : ℝ) < ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x := by positivity
    have hVb := hV hu
    have hpow : (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x) ^ (-(2 : ℝ))
        = ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)) * x ^ (2 : ℝ) := by
      rw [Real.div_rpow hmn.le hx.le, Real.rpow_neg hx.le, div_eq_mul_inv, inv_inv]
    have hsplit : ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-((1 / 2 - d) + 2))
        = ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d)) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hmn]; congr 1; ring
    calc ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d)) * ‖smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x)‖
        ≤ ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d))
          * (K * (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hVb (by positivity)
      _ = K * x ^ (2 : ℝ) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-((1 / 2 - d) + 2)) := by
          rw [hpow, hsplit]; ring

/-- The direct series is continuous in the height. -/
theorem continuous_directSeries {d x : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x) :
    Continuous (directSeries d x) := by
  obtain ⟨u, hu, hbound⟩ := exists_direct_majorant hd hd4 hx
  delta directSeries
  exact continuous_tsum (fun P => continuous_direct_summand d x P) hu (fun P t => hbound P t)

/-- The dual series is continuous on every bounded height set. -/
theorem continuousOn_dualSeries {d x : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hx : 0 < x) (T : ℝ) :
    ContinuousOn (dualSeries d x) (Set.Icc (-T) T) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_dualCarrierWeight_le_rightShift (K'' := 1) le_rfl
  have hb : ∀ P : ℕ × ℕ, ∀ t ∈ Set.Icc (-T) T,
      ‖(zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))
          * (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1) * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1))
        * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t))
            ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x)‖
      ≤ (C * (1 + T) ^ (3 : ℝ) * x ^ (-(3 / 2 - d))) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)) :=
    fun P t ht => norm_dual_summand_le hd hdq hx (fun Y τ hY => hC d Y τ hd hdq hY)
      (abs_le.mpr ⟨ht.1, ht.2⟩) P
  delta dualSeries
  exact continuousOn_tsum (fun P => (continuous_dual_summand hd hdq hx P).continuousOn)
    ((summable_prod_succ_rpow_neg (by norm_num)).mul_left _) hb

/-- Continuity of the residue pair away from height zero. -/
theorem continuousAt_residuePair {d x : ℝ} (hd : 0 < d) (hx : 0 < x) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (residuePair d x) t := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hc1 : Continuous (fun t : ℝ => displacedLinePt d t) := continuous_displacedLinePt d
  have hc2 : Continuous (fun t : ℝ => displacedLinePt d (-t)) := continuous_displacedLinePt_neg d
  -- the two zeta arguments are `1 ∓ 2it`, away from `1` for `t ≠ 0`
  have hz1 : displacedLinePt d (-t) + (1 - displacedLinePt d t) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [displacedLinePt] at this
    exact ht (by linarith)
  have hz2 : displacedLinePt d t + (1 - displacedLinePt d (-t)) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [displacedLinePt] at this
    exact ht (by linarith)
  have hne1 : (1 : ℂ) - displacedLinePt d t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [displacedLinePt] at this
    linarith
  have hne2 : (1 : ℂ) - displacedLinePt d (-t) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [displacedLinePt] at this
    linarith
  unfold residuePair productAFEShiftedResidue
  apply ContinuousAt.add
  · apply ContinuousAt.div _ (continuous_const.sub hc1).continuousAt hne1
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact ((continuous_const.sub hc1).const_cpow (Or.inl hx0)).continuousAt
      · exact (Complex.continuous_exp.comp ((continuous_const.sub hc1).pow 2)).continuousAt
    · have hg1 : Continuous (fun t : ℝ => displacedLinePt d (-t) + (1 - displacedLinePt d t)) :=
        hc2.add (continuous_const.sub hc1)
      exact ContinuousAt.comp (g := riemannZeta)
        (f := fun t : ℝ => displacedLinePt d (-t) + (1 - displacedLinePt d t))
        (differentiableAt_riemannZeta hz1).continuousAt hg1.continuousAt
  · apply ContinuousAt.div _ (continuous_const.sub hc2).continuousAt hne2
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact ((continuous_const.sub hc2).const_cpow (Or.inl hx0)).continuousAt
      · exact (Complex.continuous_exp.comp ((continuous_const.sub hc2).pow 2)).continuousAt
    · have hg2 : Continuous (fun t : ℝ => displacedLinePt d t + (1 - displacedLinePt d (-t))) :=
        hc1.add (continuous_const.sub hc2)
      exact ContinuousAt.comp (g := riemannZeta)
        (f := fun t : ℝ => displacedLinePt d t + (1 - displacedLinePt d (-t)))
        (differentiableAt_riemannZeta hz2).continuousAt hg2.continuousAt

/-! ## Interchange of the window integral and the double series -/

/-- The direct integrand of the pair `(h,k)` and the series pair `P`. -/
def directIntegrand (d x p q η : ℝ) (h k : ℕ) (P : ℕ × ℕ) (t : ℝ) : ℂ :=
  blockWindowC p q η t * ((h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t)))
    * ((P.1 + 1 : ℂ) ^ (-displacedLinePt d t) * (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
      * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x))

/-- The dual integrand of the pair `(h,k)` and the series pair `P`. -/
def dualIntegrand (d x p q η : ℝ) (h k : ℕ) (P : ℕ × ℕ) (t : ℝ) : ℂ :=
  blockWindowC p q η t * ((h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t)))
    * ((zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))
        * (P.1 + 1 : ℂ) ^ (displacedLinePt d t - 1) * (P.2 + 1 : ℂ) ^ (displacedLinePt d (-t) - 1))
      * productAFEDualWeight (displacedLinePt d t) (displacedLinePt d (-t))
          ((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ) * x))

theorem integrable_blockWindowC {p q η : ℝ} (hη : 0 < η) : Integrable (blockWindowC p q η) := by
  have := integrable_window_mul hη (p := p) (q := q) (g := fun _ => (1 : ℂ)) continuousOn_const
  simpa using this

theorem integrable_window_pairCoeff_mul {d p q η : ℝ} (hη : 0 < η) {h k : ℕ} (hh : 0 < h)
    (hk : 0 < k) {g : ℝ → ℂ} (hg : ContinuousOn g (Set.Icc (p - η) (q + η))) :
    Integrable (fun t => blockWindowC p q η t * pairCoeff d h k t * g t) := by
  have := integrable_window_mul hη ((continuous_pairCoeff d hh hk).continuousOn.mul hg)
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.mul_apply]
  ring

theorem integrable_directIntegrand {d x p q η : ℝ} (hη : 0 < η) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (P : ℕ × ℕ) : Integrable (directIntegrand d x p q η h k P) :=
  integrable_window_pairCoeff_mul hη hh hk (continuous_direct_summand d x P).continuousOn

theorem integrable_dualIntegrand {d x p q η : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (P : ℕ × ℕ) :
    Integrable (dualIntegrand d x p q η h k P) :=
  integrable_window_pairCoeff_mul hη hh hk (continuous_dual_summand hd hdq hx P).continuousOn

theorem integral_directIntegrand {d x p q η : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (P : ℕ × ℕ) :
    ∫ t, directIntegrand d x p q η h k P t = directTerm d x p q η h k P := by
  have e : ∀ t, directIntegrand d x p q η h k P t
      = (((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1)) / x))
        * (blockWindowC p q η t * Complex.exp
          (-((Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ)) * t) * I)) :=
    fun t => direct_integrand_eq hh hk P p q η t
  simp_rw [e]
  rw [integral_const_mul]
  rfl

theorem integral_dualIntegrand {d x : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {p q η : ℝ} {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (P : ℕ × ℕ) :
    ∫ t, dualIntegrand d x p q η h k P t = dualTerm d x p q η h k P := by
  have e : ∀ t, dualIntegrand d x p q η h k P t
      = (((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d)) : ℝ) : ℂ))
        * (blockWindowC p q η t * dualCarrierWeight d ((P.1 + 1 : ℝ) * (P.2 + 1) * x) t
            * Complex.exp (-(((Real.log (((P.2 + 1) * h : ℕ) : ℝ)
                - Real.log (((P.1 + 1) * k : ℕ) : ℝ) : ℝ) : ℂ) * t) * I)) :=
    fun t => dual_integrand_eq hd hdq hh hk P p q η t
  simp_rw [e]
  rw [integral_const_mul]
  rfl

theorem norm_directIntegrand_le {d x p q η : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {u : ℕ × ℕ → ℝ}
    (hu : ∀ P t, ‖(P.1 + 1 : ℂ) ^ (-displacedLinePt d t) * (P.2 + 1 : ℂ) ^ (-displacedLinePt d (-t))
        * smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x)‖ ≤ u P) (P : ℕ × ℕ) (t : ℝ) :
    ‖directIntegrand d x p q η h k P t‖
      ≤ ‖blockWindowC p q η t‖ * (((h : ℝ) * k) ^ (-(1 / 2 - d)) * u P) := by
  unfold directIntegrand
  rw [norm_mul, norm_mul, mul_assoc]
  have e : ‖(h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t))‖
      = ((h : ℝ) * k) ^ (-(1 / 2 - d)) := norm_pairCoeff hh hk t
  rw [e]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hu P t) (by positivity)) (norm_nonneg _)

theorem norm_dualIntegrand_le {d x p q η : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {C : ℝ} (hC : ∀ Y τ : ℝ, 0 < Y → ‖dualCarrierWeight d Y τ‖ ≤
        C * (1 + |τ|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) * Y ^ (-(1 / 2 - d + (1 : ℕ))))
    (P : ℕ × ℕ) (t : ℝ) :
    ‖dualIntegrand d x p q η h k P t‖
      ≤ ‖blockWindowC p q η t‖ * (((h : ℝ) * k) ^ (-(1 / 2 - d))
        * ((C * (1 + (q + η)) ^ (3 : ℝ) * x ^ (-(3 / 2 - d)))
          * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)))) := by
  unfold dualIntegrand
  rw [norm_mul, norm_mul, mul_assoc]
  have e : ‖(h : ℂ) ^ (-displacedLinePt d t) * (k : ℂ) ^ (-displacedLinePt d (-t))‖
      = ((h : ℝ) * k) ^ (-(1 / 2 - d)) := norm_pairCoeff hh hk t
  rw [e]
  by_cases ht : t ∈ Set.Icc (p - η) (q + η)
  · have hT : |t| ≤ q + η := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_dual_summand_le hd hdq hx hC hT P) (by positivity))
      (norm_nonneg _)
  · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]

/-- **Interchange for the direct series.** -/
theorem integral_window_pairCoeff_directSeries {d x p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hx : 0 < x) (hη : 0 < η) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ∫ t, blockWindowC p q η t * pairCoeff d h k t * directSeries d x t
      = ∑' P : ℕ × ℕ, directTerm d x p q η h k P := by
  obtain ⟨u, hu, hbound⟩ := exists_direct_majorant hd hd4 hx
  have hFint : ∀ P, Integrable (directIntegrand d x p q η h k P) := fun P =>
    integrable_directIntegrand hη hh hk P
  have hw : Integrable (fun t => ‖blockWindowC p q η t‖) := (integrable_blockWindowC hη).norm
  have hsum : Summable fun P => ∫ t, ‖directIntegrand d x p q η h k P t‖ := by
    refine Summable.of_nonneg_of_le (fun P => integral_nonneg fun t => norm_nonneg _)
      (fun P => ?_) (hu.mul_left ((∫ t, ‖blockWindowC p q η t‖) * ((h : ℝ) * k) ^ (-(1 / 2 - d))))
    calc ∫ t, ‖directIntegrand d x p q η h k P t‖
        ≤ ∫ t, ‖blockWindowC p q η t‖ * (((h : ℝ) * k) ^ (-(1 / 2 - d)) * u P) :=
          integral_mono (hFint P).norm (hw.mul_const _)
            (fun t => norm_directIntegrand_le hh hk hbound P t)
      _ = (∫ t, ‖blockWindowC p q η t‖) * ((h : ℝ) * k) ^ (-(1 / 2 - d)) * u P := by
          rw [integral_mul_const]; ring
  have hpt : (fun t => blockWindowC p q η t * pairCoeff d h k t * directSeries d x t)
      = fun t => ∑' P : ℕ × ℕ, directIntegrand d x p q η h k P t := by
    funext t
    delta directSeries directIntegrand pairCoeff
    rw [← tsum_mul_left]
  rw [hpt, ← integral_tsum_of_summable_integral_norm hFint hsum]
  exact tsum_congr fun P => integral_directIntegrand hh hk P

/-- **Interchange for the dual series.** -/
theorem integral_window_pairCoeff_dualSeries {d x p q η : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (hx : 0 < x) (hη : 0 < η) (hL : 4 ≤ p - η) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ∫ t, blockWindowC p q η t * pairCoeff d h k t * dualSeries d x t
      = ∑' P : ℕ × ℕ, dualTerm d x p q η h k P := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_dualCarrierWeight_le_rightShift (K'' := 1) le_rfl
  have hFint : ∀ P, Integrable (dualIntegrand d x p q η h k P) := fun P =>
    integrable_dualIntegrand hd hdq hx hη hh hk P
  have hw : Integrable (fun t => ‖blockWindowC p q η t‖) := (integrable_blockWindowC hη).norm
  have hsum : Summable fun P => ∫ t, ‖dualIntegrand d x p q η h k P t‖ := by
    refine Summable.of_nonneg_of_le (fun P => integral_nonneg fun t => norm_nonneg _)
      (fun P => ?_) (((summable_prod_succ_rpow_neg (by norm_num : (1 : ℝ) < 2)).mul_left
        ((∫ t, ‖blockWindowC p q η t‖) * ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (C * (1 + (q + η)) ^ (3 : ℝ) * x ^ (-(3 / 2 - d))))))
    calc ∫ t, ‖dualIntegrand d x p q η h k P t‖
        ≤ ∫ t, ‖blockWindowC p q η t‖ * (((h : ℝ) * k) ^ (-(1 / 2 - d))
            * ((C * (1 + (q + η)) ^ (3 : ℝ) * x ^ (-(3 / 2 - d)))
              * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)))) :=
          integral_mono (hFint P).norm (hw.mul_const _)
            (fun t => norm_dualIntegrand_le hd hdq hx hη hL hh hk
              (fun Y τ hY => hC d Y τ hd hdq hY) P t)
      _ = (∫ t, ‖blockWindowC p q η t‖) * ((h : ℝ) * k) ^ (-(1 / 2 - d))
            * (C * (1 + (q + η)) ^ (3 : ℝ) * x ^ (-(3 / 2 - d)))
            * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)) := by
          rw [integral_mul_const]; ring
  have hpt : (fun t => blockWindowC p q η t * pairCoeff d h k t * dualSeries d x t)
      = fun t => ∑' P : ℕ × ℕ, dualIntegrand d x p q η h k P t := by
    funext t
    delta dualSeries dualIntegrand pairCoeff
    rw [← tsum_mul_left]
  rw [hpt, ← integral_tsum_of_summable_integral_norm hFint hsum]
  exact tsum_congr fun P => integral_dualIntegrand hd hdq hh hk P

theorem integral_window_pairCoeff_residuePair (d x p q η : ℝ) (h k : ℕ) :
    ∫ t, blockWindowC p q η t * pairCoeff d h k t * residuePair d x t
      = residueTerm d x p q η h k := rfl

/-! ## The block identity -/

/-- The pointwise expansion of the windowed `‖ζΨ‖²`, valid at every height. -/
theorem window_normSq_eq {d x p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (b : ℕ → ℂ) (N : ℕ)
    (hbreal : ∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) (t : ℝ) :
    blockWindowC p q η t * ((‖riemannZeta (displacedLinePt d t)
        * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, b h * b k
          * (blockWindowC p q η t * pairCoeff d h k t * directSeries d x t
            + blockWindowC p q η t * pairCoeff d h k t * dualSeries d x t
            - blockWindowC p q η t * pairCoeff d h k t * residuePair d x t) := by
  by_cases ht : t ∈ Set.Icc (p - η) (q + η)
  · have ht0 : t ≠ 0 := by
      have := ht.1
      intro h0
      rw [h0] at this
      linarith
    rw [normSq_zeta_mul_edPoly_eq hd hd4 hx ht0 b N hbreal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    delta directSeries dualSeries residuePair pairCoeff
    ring
  · rw [blockWindowC_eq_zero hη ht]
    simp

/-- **The block identity.**  The window integral of `‖ζΨ‖²` on the displaced line is the mollifier
double sum of the direct series, the dual series and the residue term. -/
theorem integral_window_normSq_eq {d x p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) (b : ℕ → ℂ) (N : ℕ)
    (hbreal : ∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) :
    ∫ t, blockWindowC p q η t * ((‖riemannZeta (displacedLinePt d t)
        * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, b h * b k
          * ((∑' P : ℕ × ℕ, directTerm d x p q η h k P)
            + (∑' P : ℕ × ℕ, dualTerm d x p q η h k P) - residueTerm d x p q η h k) := by
  have hsub : Set.Icc (p - η) (q + η) ⊆ Set.Icc (-(q + η)) (q + η) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hI : ∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun t => blockWindowC p q η t * pairCoeff d h k t * directSeries d x t)
      ∧ Integrable (fun t => blockWindowC p q η t * pairCoeff d h k t * dualSeries d x t)
      ∧ Integrable (fun t => blockWindowC p q η t * pairCoeff d h k t * residuePair d x t) := by
    intro h hh k hk
    have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
    have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
    refine ⟨integrable_window_pairCoeff_mul hη hh0 hk0 (continuous_directSeries hd hd4 hx).continuousOn,
      integrable_window_pairCoeff_mul hη hh0 hk0 ((continuousOn_dualSeries hd hd4 hx (q + η)).mono hsub),
      integrable_window_pairCoeff_mul hη hh0 hk0 ?_⟩
    intro t ht
    have ht0 : t ≠ 0 := by
      have := ht.1
      intro h0
      rw [h0] at this
      linarith
    exact (continuousAt_residuePair hd hx ht0).continuousWithinAt
  have hpt : (fun t => blockWindowC p q η t * ((‖riemannZeta (displacedLinePt d t)
        * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ))
      = fun t => ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, b h * b k
          * (blockWindowC p q η t * pairCoeff d h k t * directSeries d x t
            + blockWindowC p q η t * pairCoeff d h k t * dualSeries d x t
            - blockWindowC p q η t * pairCoeff d h k t * residuePair d x t) :=
    funext fun t => window_normSq_eq hd hd4 hx hη hL b N hbreal t
  rw [hpt]
  have hI' : ∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun t => b h * b k
        * (blockWindowC p q η t * pairCoeff d h k t * directSeries d x t
          + blockWindowC p q η t * pairCoeff d h k t * dualSeries d x t
          - blockWindowC p q η t * pairCoeff d h k t * residuePair d x t)) := by
    intro h hh k hk
    exact (((hI h hh k hk).1.add (hI h hh k hk).2.1).sub (hI h hh k hk).2.2).const_mul _
  rw [integral_finsetSum]
  swap
  · intro h hh
    exact integrable_finsetSum _ (fun k hk => hI' h hh k hk)
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [integral_finsetSum _ (fun k hk => hI' h hh k hk)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  rw [integral_const_mul, integral_sub, integral_add]
  · rw [integral_window_pairCoeff_directSeries hd hd4 hx hη hh0 hk0,
      integral_window_pairCoeff_dualSeries hd hd4 hx hη hL hh0 hk0,
      integral_window_pairCoeff_residuePair]
  · exact (hI h hh k hk).1
  · exact (hI h hh k hk).2.1
  · exact (hI h hh k hk).1.add (hI h hh k hk).2.1
  · exact (hI h hh k hk).2.2

end RHTower.ZetaGateProductAFE

end
