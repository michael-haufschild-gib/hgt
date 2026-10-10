import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointConfinement
import GaloisForLFunctions.RHTower.XiRealPartDerivativeCurvesCriterion
import GaloisForLFunctions.RHTower.RectangleLeftHalfPlaneWinding
import GaloisForLFunctions.RHTower.DeBruijnTopZeroVelocity
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The two-port producer and its rectangle edges

For `h > 0` put `c = ½ + h` and `B_h(s) = ξ(s) + ξ(s − 2h)`. Then
`cos(hD)Ξ(z) = B_h(c + iz)/2` (`twoPort_eq_cosProducer`). On the line `Re s = c`,
`ξ(s − 2h) = conj ξ(s)`, so `B_h(c + it) = 2 Re ξ(c + it)` is real (`twoPort_line`).

The edges of a rectangle `[c, d] × [T₁, T₂]` compare `B_h` with `ξ` through the ratio
`B_h/ξ = 1 + ξ(s − 2h)/ξ(s)`.

* `re_logDeriv_xi_pos_of_local`: if no zero `w` of `Ξ` has `(Im w)² ≥ (T − Re w)² + (σ − ½)²`, then
  `Re(ξ'/ξ)(σ + iT) > 0`. This is the Hadamard pair sign law.
* `strictMonoOn_normSq_xi`: a positive Hadamard sign makes `σ ↦ |ξ(σ + iT)|` strictly increasing.
* `normSq_xi_sub_lt_of_shadowFree`: at a height `T` outside every shadow
  `[γ − |β − ½|, γ + |β − ½|]`, the inequality `|ξ(x − 2h + iT)| < |ξ(x + iT)|` holds for every
  `x > c`. On `Re s = 1 + 2h` it holds at every height (`normSq_xi_one_lt`).
* `abs_integral_re_logDeriv_sub_lt_pi`, `abs_integral_im_logDeriv_sub_lt_pi`: where `Re(F/G) > 0`
  along an edge, the argument variations of `F` and `G` along that edge differ by less than `π`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

/-- The two-port producer `B_h(s) = ξ(s) + ξ(s − 2h)`. -/
def twoPort (h : ℝ) (s : ℂ) : ℂ := xi s + xi (s - 2 * h)

theorem differentiable_twoPort (h : ℝ) : Differentiable ℂ (twoPort h) := by
  intro s
  exact (xi_differentiable s).add
    ((xi_differentiable (s - 2 * h)).comp s ((differentiableAt_id).sub_const _))

theorem analyticOnNhd_twoPort (h : ℝ) : AnalyticOnNhd ℂ (twoPort h) univ :=
  (differentiable_twoPort h).differentiableOn.analyticOnNhd isOpen_univ

/-- `cos(hD)Ξ(z) = B_h(½ + h + iz)/2`. -/
theorem twoPort_eq_cosProducer (h : ℝ) (z : ℂ) :
    twoPort h (1 / 2 + h + z * I) = 2 * cosProducer h z := by
  unfold twoPort cosProducer XiC
  have e1 : (1 / 2 : ℂ) + (z + h * I) * I = 1 / 2 + h + z * I - 2 * h := by
    ring_nf; rw [Complex.I_sq]; ring
  have e2 : (1 / 2 : ℂ) + (z - h * I) * I = 1 / 2 + h + z * I := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]; ring

/-- On `Re s = ½ + h` the two-port producer is `2 Re ξ`. -/
theorem twoPort_line (h t : ℝ) :
    twoPort h (((1 / 2 + h : ℝ) : ℂ) + t * I) =
      ((2 * (xi (((1 / 2 + h : ℝ) : ℂ) + t * I)).re : ℝ) : ℂ) := by
  set s : ℂ := ((1 / 2 + h : ℝ) : ℂ) + t * I with hs
  have e : s - 2 * h = 1 - (starRingEnd ℂ) s := by
    rw [hs]; apply Complex.ext <;> simp; ring
  unfold twoPort
  rw [e, xi_one_sub, xi_conj, Complex.add_conj]

theorem twoPort_line_im (h t : ℝ) :
    (twoPort h (((1 / 2 + h : ℝ) : ℂ) + t * I)).im = 0 := by
  rw [twoPort_line]; simp

/-! ## The Hadamard sign at good heights -/

theorem analyticOnNhd_XiC : AnalyticOnNhd ℂ XiC univ := by
  rw [← DeBruijn.cosTransform_riemannKernel_eq_XiC]
  exact DeBruijn.riemannKernel_superExp.differentiable.differentiableOn.analyticOnNhd isOpen_univ

theorem nonempty_zeroCopy_XiC : Nonempty (ZeroCopy XiC) := by
  obtain ⟨a, -, -, -, -, hza, -⟩ := exists_two_distinct_positive_real_XiC_zeros
  obtain ⟨q, -⟩ := DeBruijn.exists_zeroCopy_of_eq_zero analyticOnNhd_XiC XiC_zero_ne hza
  exact ⟨q⟩

/-- **Hadamard pair sign.** If every zero `w` of `Ξ` has `(Im w)² < (T − Re w)² + (σ − ½)²`, then
`Re(ξ'/ξ)(σ + iT) > 0`. -/
theorem re_logDeriv_xi_pos_of_local {σ T : ℝ} (hσ : 1 / 2 < σ)
    (hloc : ∀ w, XiC w = 0 → w.im ^ 2 < (T - w.re) ^ 2 + (σ - 1 / 2) ^ 2) :
    0 < (logDeriv xi ((σ : ℂ) + T * I)).re := by
  obtain ⟨C, hC0, hC⟩ := DeBruijn.riemannKernel_superExp.exists_envelope
  rw [DeBruijn.cosTransform_riemannKernel_eq_XiC] at hC
  have hloc' : ∀ w, XiC w = 0 → w.im ^ 2 < (-T - w.re) ^ 2 + (σ - 1 / 2) ^ 2 := by
    intro w hw
    have h1 := hloc (-w) (by rw [DeBruijn.XiC_neg']; exact hw)
    simp only [Complex.neg_im, Complex.neg_re, neg_sq] at h1
    have : (T - -w.re) ^ 2 = (-T - w.re) ^ 2 := by ring
    linarith
  have hL := im_logDeriv_neg_of_local hC0 analyticOnNhd_XiC XiC_zero_ne DeBruijn.XiC_neg'
    DeBruijn.XiC_conj' hC (x := -T) (h := σ - 1 / 2) (by linarith) hloc' nonempty_zeroCopy_XiC
  set s : ℂ := (σ : ℂ) + T * I with hs
  have hz : (1 / 2 : ℂ) + (((-T : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) * I) * I = 1 - s := by
    rw [hs]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hlog : logDeriv XiC (((-T : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) * I) =
      -(I * logDeriv xi s) := by
    rw [logDeriv_apply, (hasDerivAt_XiC _).deriv, XiC, hz, deriv_xi_one_sub_eq, xi_one_sub,
      logDeriv_apply]
    ring
  rw [hlog] at hL
  simpa [Complex.mul_im] using hL

/-- Zeros of `Ξ` lie in `|Im w| < ½`. -/
theorem abs_im_lt_half_of_XiC_eq_zero {w : ℂ} (hw : XiC w = 0) : |w.im| < 1 / 2 := by
  have hxi : xi (1 / 2 + w * I) = 0 := by rw [← hw, XiC]
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hxi
  have hre : (1 / 2 + w * I).re = 1 / 2 - w.im := by simp; ring
  rw [hre] at h0 h1
  rw [abs_lt]; constructor <;> linarith

/-- A shadow-free height carries no zero of `ξ` off the critical line. -/
theorem xi_ne_zero_of_shadowFree {T : ℝ}
    (hgood : ∀ w, XiC w = 0 → w.im ^ 2 < (T - w.re) ^ 2) {σ : ℝ} :
    xi ((σ : ℂ) + T * I) ≠ 0 := by
  intro h0
  set w : ℂ := ((T : ℝ) : ℂ) - ((σ - 1 / 2 : ℝ) : ℂ) * I with hw
  have hXw : XiC w = 0 := by
    rw [XiC]
    have : (1 / 2 : ℂ) + w * I = (σ : ℂ) + T * I := by
      rw [hw]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [this]; exact h0
  have := hgood w hXw
  simp [hw] at this
  nlinarith [sq_nonneg (σ - 1 / 2)]

/-- `ξ` has no zero with `Re s ≥ 1`. -/
theorem xi_ne_zero_of_one_le {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  intro h0
  have := (xi_zero_re_mem_open_unit h0).2
  linarith

/-! ## Monotonicity of `|ξ|` in `σ` -/

/-- The squared modulus of `ξ` along a horizontal line. -/
theorem hasDerivAt_normSq_xi_horizontal (T σ : ℝ) :
    HasDerivAt (fun u : ℝ => normSq (xi ((u : ℂ) + T * I)))
      (2 * ((deriv xi ((σ : ℂ) + T * I)) * (starRingEnd ℂ) (xi ((σ : ℂ) + T * I))).re) σ := by
  have hpath : HasDerivAt (fun u : ℝ => (u : ℂ) + T * I) 1 σ := by
    simpa using (hasDerivAt_id σ).ofReal_comp.add_const ((T : ℂ) * I)
  have hg : HasDerivAt (fun u : ℝ => xi ((u : ℂ) + T * I)) (deriv xi ((σ : ℂ) + T * I)) σ := by
    have := (xi_differentiable ((σ : ℂ) + T * I)).hasDerivAt.comp σ hpath
    simpa [Function.comp_def] using this
  have hre : HasDerivAt (fun u : ℝ => (xi ((u : ℂ) + T * I)).re)
      (deriv xi ((σ : ℂ) + T * I)).re σ := Complex.reCLM.hasFDerivAt.comp_hasDerivAt σ hg
  have him : HasDerivAt (fun u : ℝ => (xi ((u : ℂ) + T * I)).im)
      (deriv xi ((σ : ℂ) + T * I)).im σ := Complex.imCLM.hasFDerivAt.comp_hasDerivAt σ hg
  have := (hre.mul hre).add (him.mul him)
  have hfun : (fun u : ℝ => normSq (xi ((u : ℂ) + T * I))) = fun u : ℝ =>
      (xi ((u : ℂ) + T * I)).re * (xi ((u : ℂ) + T * I)).re +
        (xi ((u : ℂ) + T * I)).im * (xi ((u : ℂ) + T * I)).im :=
    funext fun u => Complex.normSq_apply _
  rw [hfun]
  refine this.congr_deriv ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/-- **A positive Hadamard sign makes `|ξ|` strictly increasing in `σ`.** -/
theorem strictMonoOn_normSq_xi {σ₀ T : ℝ}
    (hpos : ∀ σ, σ₀ < σ → 0 < (logDeriv xi ((σ : ℂ) + T * I)).re)
    (hne : ∀ σ, σ₀ ≤ σ → xi ((σ : ℂ) + T * I) ≠ 0) :
    StrictMonoOn (fun σ : ℝ => normSq (xi ((σ : ℂ) + T * I))) (Ici σ₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici σ₀)
  · intro σ _
    exact (hasDerivAt_normSq_xi_horizontal T σ).continuousAt.continuousWithinAt
  · intro σ hσ
    rw [interior_Ici, mem_Ioi] at hσ
    rw [(hasDerivAt_normSq_xi_horizontal T σ).deriv]
    set g := xi ((σ : ℂ) + T * I)
    set g' := deriv xi ((σ : ℂ) + T * I)
    have hg : g ≠ 0 := hne σ hσ.le
    have hL := hpos σ hσ
    have hn : 0 < normSq g := Complex.normSq_pos.mpr hg
    have key : (g' * (starRingEnd ℂ) g).re = normSq g * (logDeriv xi ((σ : ℂ) + T * I)).re := by
      rw [logDeriv_apply]
      change (g' * (starRingEnd ℂ) g).re = normSq g * (g' / g).re
      rw [Complex.div_re]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      field_simp
      ring
    rw [key]
    positivity

/-- `|ξ(1 − σ + iT)| = |ξ(σ + iT)|`. -/
theorem normSq_xi_one_sub (σ T : ℝ) :
    normSq (xi (((1 - σ : ℝ) : ℂ) + T * I)) = normSq (xi ((σ : ℂ) + T * I)) := by
  have e : ((1 - σ : ℝ) : ℂ) + T * I = 1 - (starRingEnd ℂ) ((σ : ℂ) + T * I) := by
    apply Complex.ext <;> simp
  rw [e, xi_one_sub, xi_conj, Complex.normSq_conj]

/-- At a shadow-free height, `|ξ(x − 2h + iT)| < |ξ(x + iT)|` for every `x > ½ + h`. -/
theorem normSq_xi_sub_lt_of_shadowFree {h T x : ℝ} (hh : 0 < h)
    (hgood : ∀ w, XiC w = 0 → w.im ^ 2 < (T - w.re) ^ 2) (hx : 1 / 2 + h < x) :
    normSq (xi (((x - 2 * h : ℝ) : ℂ) + T * I)) < normSq (xi ((x : ℂ) + T * I)) := by
  have hmono := strictMonoOn_normSq_xi (σ₀ := 1 / 2) (T := T)
    (fun σ hσ => re_logDeriv_xi_pos_of_local hσ (fun w hw => by
      have := hgood w hw
      have : 0 < (σ - 1 / 2) ^ 2 := by have : 0 < σ - 1 / 2 := by linarith
                                       positivity
      linarith))
    (fun σ _ => xi_ne_zero_of_shadowFree hgood)
  rcases le_or_gt (1 / 2) (x - 2 * h) with hle | hlt
  · exact hmono (mem_Ici.mpr hle) (mem_Ici.mpr (by linarith)) (by linarith)
  · rw [← normSq_xi_one_sub (x - 2 * h) T]
    exact hmono (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (by linarith)

/-- On `Re s ≥ 1`, `|ξ(σ + iT)|` is strictly increasing in `σ` at every height. -/
theorem strictMonoOn_normSq_xi_one (T : ℝ) :
    StrictMonoOn (fun σ : ℝ => normSq (xi ((σ : ℂ) + T * I))) (Ici 1) :=
  strictMonoOn_normSq_xi
    (fun σ hσ => re_logDeriv_xi_pos_of_local (by linarith) (fun w hw => by
      have h1 := abs_im_lt_half_of_XiC_eq_zero hw
      have h2 : w.im ^ 2 < (1 / 2) ^ 2 := by
        have := sq_lt_sq' (by linarith [(abs_lt.mp h1).1]) (abs_lt.mp h1).2
        linarith
      have h3 : (1 / 2 : ℝ) ^ 2 ≤ (σ - 1 / 2) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (T - w.re)]))
    (fun σ hσ => xi_ne_zero_of_one_le (by simp; linarith))

/-- On the right edge `Re s = 1 + 2h`: `|ξ(1 + iT)| < |ξ(1 + 2h + iT)|`. -/
theorem normSq_xi_one_lt {h : ℝ} (hh : 0 < h) (T : ℝ) :
    normSq (xi (((1 + 2 * h - 2 * h : ℝ) : ℂ) + T * I)) <
      normSq (xi (((1 + 2 * h : ℝ) : ℂ) + T * I)) := by
  have := strictMonoOn_normSq_xi_one T (mem_Ici.mpr (by linarith : (1 : ℝ) ≤ 1 + 2 * h - 2 * h))
    (mem_Ici.mpr (by linarith : (1 : ℝ) ≤ 1 + 2 * h)) (by linarith)
  simpa using this

/-! ## The ratio `B_h/ξ` -/

/-- Where `|ξ(s − 2h)| < |ξ(s)|`, the ratio `B_h/ξ` has positive real part. -/
theorem re_twoPort_div_xi_pos {h : ℝ} {s : ℂ}
    (hlt : normSq (xi (s - 2 * h)) < normSq (xi s)) : 0 < (twoPort h s / xi s).re := by
  have hs : xi s ≠ 0 := by
    intro h0; rw [h0, map_zero] at hlt; exact absurd hlt (not_lt.mpr (Complex.normSq_nonneg _))
  have hr : ‖xi (s - 2 * h) / xi s‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hs)]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hlt
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt
  have e : twoPort h s / xi s = 1 + xi (s - 2 * h) / xi s := by
    unfold twoPort; field_simp
  rw [e, Complex.add_re, Complex.one_re]
  have := Complex.re_le_norm (xi (s - 2 * h) / xi s)
  have h2 : -(xi (s - 2 * h) / xi s).re ≤ ‖xi (s - 2 * h) / xi s‖ := by
    have := Complex.abs_re_le_norm (xi (s - 2 * h) / xi s)
    linarith [neg_abs_le (xi (s - 2 * h) / xi s).re]
  linarith

/-- On the line `Re s = ½ + h`, `Re(B_h/ξ) = 2 (Re ξ)²/|ξ|² > 0` when `Re ξ ≠ 0`. -/
theorem re_twoPort_div_xi_line_pos {h t : ℝ}
    (hre : (xi (((1 / 2 + h : ℝ) : ℂ) + t * I)).re ≠ 0) :
    0 < (twoPort h (((1 / 2 + h : ℝ) : ℂ) + t * I) / xi (((1 / 2 + h : ℝ) : ℂ) + t * I)).re := by
  rw [twoPort_line]
  set g := xi (((1 / 2 + h : ℝ) : ℂ) + t * I)
  have hg : g ≠ 0 := fun h0 => hre (by rw [h0]; simp)
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  have hn : 0 < normSq g := Complex.normSq_pos.mpr hg
  have : 0 < 2 * g.re * g.re := by
    have := mul_self_pos.mpr hre; linarith
  rw [show 2 * g.re * g.re / normSq g = (2 * g.re * g.re) / normSq g from rfl]
  positivity

/-! ## Edge comparisons -/

theorem logDeriv_neg_fun (f : ℂ → ℂ) (z : ℂ) : logDeriv (fun w => -f w) z = logDeriv f z := by
  rw [logDeriv_apply, logDeriv_apply, deriv.fun_neg, neg_div_neg_eq]

/-- **Vertical edge.** Where `Re(F/G) > 0` along a vertical segment, the argument variations of `F`
and `G` differ by less than `π`. -/
theorem abs_integral_re_logDeriv_sub_lt_pi {F G : ℂ → ℂ} {x T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hpos : ∀ t ∈ Icc T₁ T₂, 0 < (F ((x : ℂ) + t * I) / G ((x : ℂ) + t * I)).re) :
    |(∫ t in T₁..T₂, (logDeriv F ((x : ℂ) + t * I)).re) -
        (∫ t in T₁..T₂, (logDeriv G ((x : ℂ) + t * I)).re)| < Real.pi := by
  have hu : uIcc T₁ T₂ = Icc T₁ T₂ := uIcc_of_le hT
  have hGne : ∀ t ∈ Icc T₁ T₂, G ((x : ℂ) + t * I) ≠ 0 := by
    intro t ht h0; have := hpos t ht; rw [h0, div_zero] at this; simp at this
  have hFne : ∀ t ∈ Icc T₁ T₂, F ((x : ℂ) + t * I) ≠ 0 := by
    intro t ht h0; have := hpos t ht; rw [h0, zero_div] at this; simp at this
  set g : ℂ → ℂ := fun s => -(F s / G s) with hgdef
  have hgan : ∀ t ∈ uIcc T₁ T₂, AnalyticAt ℂ g ((x : ℂ) + t * I) := by
    intro t ht
    rw [hu] at ht
    have hdiff : DifferentiableOn ℂ g {s | G s ≠ 0} := fun s hs =>
      ((hF s).div (hG s) hs).neg.differentiableWithinAt
    have hopen : IsOpen {s | G s ≠ 0} := isOpen_ne_fun hG.continuous continuous_const
    exact hdiff.analyticAt (hopen.mem_nhds (hGne t ht))
  have hneg : ∀ t ∈ uIcc T₁ T₂, (g ((x : ℂ) + t * I)).re < 0 := by
    intro t ht; rw [hu] at ht; simp only [hgdef, Complex.neg_re]; linarith [hpos t ht]
  have hint := integral_re_logDeriv_vertical_eq_of_re_neg hgan hneg
  have hlog : ∀ t ∈ uIcc T₁ T₂, (logDeriv g ((x : ℂ) + t * I)).re =
      (logDeriv F ((x : ℂ) + t * I)).re - (logDeriv G ((x : ℂ) + t * I)).re := by
    intro t ht
    rw [hu] at ht
    rw [hgdef, logDeriv_neg_fun (fun s => F s / G s),
      logDeriv_div _ (hFne t ht) (hGne t ht) (hF _) (hG _), Complex.sub_re]
  have hcontF : ContinuousOn (fun t : ℝ => (logDeriv F ((x : ℂ) + t * I)).re) (uIcc T₁ T₂) := by
    intro t ht
    rw [hu] at ht
    have hc : ContinuousAt (fun u : ℝ => (x : ℂ) + u * I) t := by fun_prop
    exact (Complex.continuous_re.continuousAt.comp
      ((continuousAt_logDeriv_of_analyticAt (hF.analyticAt _) (hFne t ht)).comp
        (f := fun u : ℝ => (x : ℂ) + u * I) hc)).continuousWithinAt
  have hcontG : ContinuousOn (fun t : ℝ => (logDeriv G ((x : ℂ) + t * I)).re) (uIcc T₁ T₂) := by
    intro t ht
    rw [hu] at ht
    have hc : ContinuousAt (fun u : ℝ => (x : ℂ) + u * I) t := by fun_prop
    exact (Complex.continuous_re.continuousAt.comp
      ((continuousAt_logDeriv_of_analyticAt (hG.analyticAt _) (hGne t ht)).comp
        (f := fun u : ℝ => (x : ℂ) + u * I) hc)).continuousWithinAt
  rw [← intervalIntegral.integral_sub hcontF.intervalIntegrable hcontG.intervalIntegrable,
    ← intervalIntegral.integral_congr hlog, hint]
  have hb : ∀ t ∈ Icc T₁ T₂, |(Complex.log (-g ((x : ℂ) + t * I))).im| < Real.pi / 2 := by
    intro t ht
    rw [Complex.log_im, hgdef]
    simp only [neg_neg]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hpos t ht))
  have h1 := hb T₂ ⟨hT, le_rfl⟩
  have h2 := hb T₁ ⟨le_rfl, hT⟩
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Horizontal edge.** Where `Re(F/G) > 0` along a horizontal segment, the argument variations of
`F` and `G` differ by less than `π`. -/
theorem abs_integral_im_logDeriv_sub_lt_pi {F G : ℂ → ℂ} {c d T : ℝ} (hcd : c ≤ d)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hpos : ∀ x ∈ Icc c d, 0 < (F ((x : ℂ) + T * I) / G ((x : ℂ) + T * I)).re) :
    |(∫ x in c..d, (logDeriv F ((x : ℂ) + T * I)).im) -
        (∫ x in c..d, (logDeriv G ((x : ℂ) + T * I)).im)| < Real.pi := by
  have hu : uIcc c d = Icc c d := uIcc_of_le hcd
  have hGne : ∀ x ∈ Icc c d, G ((x : ℂ) + T * I) ≠ 0 := by
    intro x hx h0; have := hpos x hx; rw [h0, div_zero] at this; simp at this
  have hFne : ∀ x ∈ Icc c d, F ((x : ℂ) + T * I) ≠ 0 := by
    intro x hx h0; have := hpos x hx; rw [h0, zero_div] at this; simp at this
  set g : ℂ → ℂ := fun s => -(F s / G s) with hgdef
  have hgan : ∀ x ∈ uIcc c d, AnalyticAt ℂ g ((x : ℂ) + T * I) := by
    intro x hx
    rw [hu] at hx
    have hdiff : DifferentiableOn ℂ g {s | G s ≠ 0} := fun s hs =>
      ((hF s).div (hG s) hs).neg.differentiableWithinAt
    have hopen : IsOpen {s | G s ≠ 0} := isOpen_ne_fun hG.continuous continuous_const
    exact hdiff.analyticAt (hopen.mem_nhds (hGne x hx))
  have hneg : ∀ x ∈ uIcc c d, (g ((x : ℂ) + T * I)).re < 0 := by
    intro x hx; rw [hu] at hx; simp only [hgdef, Complex.neg_re]; linarith [hpos x hx]
  have hint := integral_im_logDeriv_horizontal_eq_of_re_neg hgan hneg
  have hlog : ∀ x ∈ uIcc c d, (logDeriv g ((x : ℂ) + T * I)).im =
      (logDeriv F ((x : ℂ) + T * I)).im - (logDeriv G ((x : ℂ) + T * I)).im := by
    intro x hx
    rw [hu] at hx
    rw [hgdef, logDeriv_neg_fun (fun s => F s / G s),
      logDeriv_div _ (hFne x hx) (hGne x hx) (hF _) (hG _), Complex.sub_im]
  have hcontF : ContinuousOn (fun x : ℝ => (logDeriv F ((x : ℂ) + T * I)).im) (uIcc c d) := by
    intro x hx
    rw [hu] at hx
    have hc : ContinuousAt (fun u : ℝ => (u : ℂ) + T * I) x := by fun_prop
    exact (Complex.continuous_im.continuousAt.comp
      ((continuousAt_logDeriv_of_analyticAt (hF.analyticAt _) (hFne x hx)).comp
        (f := fun u : ℝ => (u : ℂ) + T * I) hc)).continuousWithinAt
  have hcontG : ContinuousOn (fun x : ℝ => (logDeriv G ((x : ℂ) + T * I)).im) (uIcc c d) := by
    intro x hx
    rw [hu] at hx
    have hc : ContinuousAt (fun u : ℝ => (u : ℂ) + T * I) x := by fun_prop
    exact (Complex.continuous_im.continuousAt.comp
      ((continuousAt_logDeriv_of_analyticAt (hG.analyticAt _) (hGne x hx)).comp
        (f := fun u : ℝ => (u : ℂ) + T * I) hc)).continuousWithinAt
  rw [← intervalIntegral.integral_sub hcontF.intervalIntegrable hcontG.intervalIntegrable,
    ← intervalIntegral.integral_congr hlog, hint]
  have hb : ∀ x ∈ Icc c d, |(Complex.log (-g ((x : ℂ) + T * I))).im| < Real.pi / 2 := by
    intro x hx
    rw [Complex.log_im, hgdef]
    simp only [neg_neg]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hpos x hx))
  have h1 := hb d ⟨hcd, le_rfl⟩
  have h2 := hb c ⟨le_rfl, hcd⟩
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end

end RHTower
