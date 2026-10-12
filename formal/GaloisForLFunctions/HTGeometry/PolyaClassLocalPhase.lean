import GaloisForLFunctions.HTGeometry.PolyaClassPhaseRigidity

/-!
# Local phase representation and local gap rigidity

The phase lemmas of `PolyaClassPhaseRigidity` assume that `G` has no zero on the whole line
`Im z = h`. Here only an interval is needed.

* `exists_phase_rep_Ioo`: if `G` is entire and `G(t + ih) ≠ 0` for `t ∈ [a, b]`, then on `(a, b)`
  `Re G(t + ih) = A(t) cos φ(t)` with `A > 0` and `φ' = −ω`, where `ω` is the phase speed. The phase
  is the imaginary part of a primitive of `G'/G` along the segment.
* `gap_rigidity_of_phase_window_on`: the gap comparison of `gap_rigidity_of_phase_window`, with every
  hypothesis on `A` and `φ` restricted to the window `[X, Y]`.
-/

open Complex Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Local phase representation.** If `G` is entire and has no zero on the segment
`[a, b] + ih`, then on `(a, b)` its real part is `A cos φ` with `A > 0` and `φ' = −ω`. -/
theorem exists_phase_rep_Ioo {G : ℂ → ℂ} (hG : Differentiable ℂ G) {h a b : ℝ} (hab : a < b)
    (hne : ∀ t ∈ Icc a b, G ((t : ℂ) + h * I) ≠ 0) :
    ∃ A φ : ℝ → ℝ, (∀ t ∈ Ioo a b, 0 < A t) ∧
      (∀ t ∈ Ioo a b, HasDerivAt φ (-phaseSpeed G h t) t) ∧
      ∀ t ∈ Ioo a b, (G ((t : ℂ) + h * I)).re = A t * Real.cos (φ t) := by
  set E : ℝ → ℂ := fun t => G ((t : ℂ) + h * I) with hE
  set q : ℝ → ℂ := fun t => deriv G ((t : ℂ) + h * I) / G ((t : ℂ) + h * I) with hq
  have hEder : ∀ t : ℝ, HasDerivAt E (deriv G ((t : ℂ) + h * I)) t := by
    intro t
    have h1 : HasDerivAt (fun z : ℂ => G (z + h * I)) (deriv G ((t : ℂ) + h * I)) (t : ℂ) :=
      ((hG ((t : ℂ) + h * I)).hasDerivAt).comp_add_const (t : ℂ) (h * I)
    exact h1.comp_ofReal
  have hdG : Continuous (deriv G) :=
    continuous_iff_continuousAt.mpr fun z => ((hG.analyticAt z).deriv).continuousAt
  have hline : Continuous (fun t : ℝ => (t : ℂ) + h * I) := by fun_prop
  have hqc : ContinuousOn q (Icc a b) :=
    (hdG.comp hline).continuousOn.div (hG.continuous.comp hline).continuousOn hne
  set L : ℝ → ℂ := fun u => ∫ x in a..u, q x with hLdef
  have hL : ∀ t ∈ Ioo a b, HasDerivAt L (q t) t := by
    intro t ht
    have hint : IntervalIntegrable q MeasureTheory.volume a t :=
      ContinuousOn.intervalIntegrable_of_Icc ht.1.le (hqc.mono (Icc_subset_Icc le_rfl ht.2.le))
    have hmeas : StronglyMeasurableAtFilter q (𝓝 t) :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hqc.mono Ioo_subset_Icc_self) t ht
    have hct : ContinuousAt q t :=
      (hqc t (Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas hct
  -- `E · exp(−L)` is constant on `(a, b)`
  set f : ℝ → ℂ := fun t => E t * Complex.exp (-L t) with hf
  have hfd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t := by
    intro t ht
    have h1 := (hEder t).mul ((hL t ht).neg.cexp)
    have hEt : G ((t : ℂ) + h * I) ≠ 0 := hne t (Ioo_subset_Icc_self ht)
    have e : deriv G ((t : ℂ) + h * I) * Complex.exp (-L t) + G ((t : ℂ) + h * I) *
        (Complex.exp (-L t) * -(deriv G ((t : ℂ) + h * I) / G ((t : ℂ) + h * I))) = 0 := by
      field_simp; ring
    exact h1.congr_deriv e
  set c : ℝ := (a + b) / 2 with hc
  have hcI : c ∈ Ioo a b := ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩
  have hconst : ∀ t ∈ Ioo a b, f t = f c := by
    intro t ht
    refine IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      (fun x hx => (hfd x hx).differentiableAt.differentiableWithinAt) (fun x hx => ?_) ht hcI
    exact (hfd x hx).deriv
  have hEc : E c ≠ 0 := hne c (Ioo_subset_Icc_self hcI)
  refine ⟨fun t => ‖E c‖ * Real.exp (L t - L c).re, fun t => (E c).arg + (L t - L c).im,
    fun t _ => by have := norm_pos_iff.mpr hEc; positivity, fun t ht => ?_, fun t ht => ?_⟩
  · have hi : HasDerivAt (fun t => (L t - L c).im) (q t).im t := by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ((hL t ht).sub_const (L c))
      exact this
    have hq' : (q t).im = -phaseSpeed G h t := by simp [phaseSpeed, hq]
    rw [← hq']
    exact hi.const_add _
  · have hEt : E t = E c * Complex.exp (L t - L c) := by
      have h1 := hconst t ht
      simp only [hf] at h1
      calc E t = E t * Complex.exp (-L t) * Complex.exp (L t) := by
            rw [mul_assoc, ← Complex.exp_add]; simp
        _ = E c * Complex.exp (-L c) * Complex.exp (L t) := by rw [h1]
        _ = E c * Complex.exp (L t - L c) := by
            rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
    have hpolar := Complex.norm_mul_exp_arg_mul_I (E c)
    have : E t = (‖E c‖ : ℂ) * Complex.exp ((E c).arg * I + (L t - L c)) := by
      rw [hEt, Complex.exp_add, ← mul_assoc, hpolar]
    show (E t).re = _
    rw [this, Complex.re_ofReal_mul, Complex.exp_re]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf

/-- **Consecutive zeros enclose phase `π`**, with continuity only on `[a, b]`. -/
theorem phase_drop_eq_pi_of_lt_on {A φ : ℝ → ℝ} {a b : ℝ} (hφc : ContinuousOn φ (Icc a b))
    (hab : a < b) (hlt : φ b < φ a) (ha : Real.cos (φ a) = 0) (hb : Real.cos (φ b) = 0)
    (hno : ∀ c ∈ Ioo a b, A c * Real.cos (φ c) ≠ 0) :
    φ a - φ b = Real.pi := by
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp ha
  obtain ⟨k', hk'⟩ := Real.cos_eq_zero_iff.mp hb
  have hkk : k' < k := by
    rw [hk, hk'] at hlt
    have hpi := Real.pi_pos
    have : ((2 * (k' : ℝ) + 1) * Real.pi / 2) < ((2 * (k : ℝ) + 1) * Real.pi / 2) := hlt
    have : (k' : ℝ) < k := by nlinarith
    exact_mod_cast this
  by_contra hne
  have hk2 : k' ≤ k - 2 := by
    by_contra hcon
    push Not at hcon
    have : k' = k - 1 := by omega
    apply hne
    rw [hk, hk', this]; push_cast; ring
  set v : ℝ := (2 * ((k - 1 : ℤ) : ℝ) + 1) * Real.pi / 2 with hv
  have hpi := Real.pi_pos
  have hv1 : φ b < v := by
    rw [hk', hv]
    have : (k' : ℝ) ≤ k - 2 := by exact_mod_cast hk2
    push_cast; nlinarith
  have hv2 : v < φ a := by rw [hk, hv]; push_cast; nlinarith
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Ioo' hab.le hφc ⟨hv1, hv2⟩
  apply hno c hc
  rw [hcv, hv, Real.cos_eq_zero_iff.mpr ⟨k - 1, rfl⟩, mul_zero]

/-- **Windowed gap rigidity with local data.** As `gap_rigidity_of_phase_window`, with `A > 0` and
`φ' = −ω` assumed only on `[X, Y]`. -/
theorem gap_rigidity_of_phase_window_on {A φ ω : ℝ → ℝ} {h X Y : ℝ} (hh : 0 < h)
    (hA : ∀ t ∈ Icc X Y, 0 < A t) (hφ : ∀ t ∈ Icc X Y, HasDerivAt φ (-ω t) t)
    (hω : ∀ t ∈ Icc X Y, 0 < ω t)
    (hLL : ∀ s ∈ Icc X Y, ∀ t ∈ Icc X Y, ω s ≤ Real.exp (2 * |s - t| / h) * ω t)
    {a b c : ℝ} (haX : X ≤ a) (hcY : c ≤ Y) (hab : a < b) (hbc : b < c)
    (ha : A a * Real.cos (φ a) = 0) (hb : A b * Real.cos (φ b) = 0)
    (hc : A c * Real.cos (φ c) = 0)
    (hno1 : ∀ x ∈ Ioo a b, A x * Real.cos (φ x) ≠ 0)
    (hno2 : ∀ x ∈ Ioo b c, A x * Real.cos (φ x) ≠ 0) :
    c - b ≤ (b - a) * Real.exp (2 * (c - a) / h) ∧
      b - a ≤ (c - b) * Real.exp (2 * (c - a) / h) := by
  have hmem : ∀ x, a ≤ x → x ≤ c → x ∈ Icc X Y := fun x h1 h2 =>
    ⟨by linarith, by linarith⟩
  have hma := hmem a le_rfl (by linarith)
  have hmb := hmem b hab.le hbc.le
  have hmc := hmem c (by linarith) le_rfl
  have hcos : ∀ {x}, x ∈ Icc X Y → A x * Real.cos (φ x) = 0 → Real.cos (φ x) = 0 :=
    fun hx h0 => (mul_eq_zero.mp h0).resolve_left (hA _ hx).ne'
  have hφc : ContinuousOn φ (Icc X Y) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn φ (Icc X Y) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc X Y) hφc fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hφ x (Ioo_subset_Icc_self hx)).deriv]
    linarith [hω x (Ioo_subset_Icc_self hx)]
  have hsub1 : Icc a b ⊆ Icc X Y := Icc_subset_Icc haX (by linarith)
  have hsub2 : Icc b c ⊆ Icc X Y := Icc_subset_Icc (by linarith) hcY
  have h1 := phase_drop_eq_pi_of_lt_on (hφc.mono hsub1) hab (hanti hma hmb hab) (hcos hma ha)
    (hcos hmb hb) hno1
  have h2 := phase_drop_eq_pi_of_lt_on (hφc.mono hsub2) hbc (hanti hmb hmc hbc) (hcos hmb hb)
    (hcos hmc hc) hno2
  obtain ⟨ξ₁, hξ₁, hm1⟩ := exists_hasDerivAt_eq_slope φ (fun t => -ω t) hab (hφc.mono hsub1)
    fun x hx => hφ x (hsub1 (Ioo_subset_Icc_self hx))
  obtain ⟨ξ₂, hξ₂, hm2⟩ := exists_hasDerivAt_eq_slope φ (fun t => -ω t) hbc (hφc.mono hsub2)
    fun x hx => hφ x (hsub2 (Ioo_subset_Icc_self hx))
  have hM1 := hmem ξ₁ hξ₁.1.le (by linarith [hξ₁.2])
  have hM2 := hmem ξ₂ (by linarith [hξ₂.1]) hξ₂.2.le
  have hba : 0 < b - a := by linarith
  have hcb : 0 < c - b := by linarith
  have hw1 : ω ξ₁ * (b - a) = Real.pi := by
    have : -ω ξ₁ = (φ b - φ a) / (b - a) := hm1
    field_simp at this; linarith
  have hw2 : ω ξ₂ * (c - b) = Real.pi := by
    have : -ω ξ₂ = (φ c - φ b) / (c - b) := hm2
    field_simp at this; linarith
  have hdist : |ξ₂ - ξ₁| ≤ c - a := by
    rw [abs_le]; constructor <;> linarith [hξ₁.1, hξ₁.2, hξ₂.1, hξ₂.2]
  set K := Real.exp (2 * (c - a) / h) with hK
  have hE21 : Real.exp (2 * |ξ₂ - ξ₁| / h) ≤ K :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hE12 : Real.exp (2 * |ξ₁ - ξ₂| / h) ≤ K := by rw [abs_sub_comm]; exact hE21
  have hw1p := hω ξ₁ hM1
  have hw2p := hω ξ₂ hM2
  have hL21 : ω ξ₂ ≤ K * ω ξ₁ :=
    (hLL ξ₂ hM2 ξ₁ hM1).trans (mul_le_mul_of_nonneg_right hE21 hw1p.le)
  have hL12 : ω ξ₁ ≤ K * ω ξ₂ :=
    (hLL ξ₁ hM1 ξ₂ hM2).trans (mul_le_mul_of_nonneg_right hE12 hw2p.le)
  constructor
  · have : (c - b) * ω ξ₂ ≤ ((b - a) * K) * ω ξ₂ := by
      have := mul_le_mul_of_nonneg_left hL12 hba.le
      nlinarith
    exact le_of_mul_le_mul_right this hw2p
  · have : (b - a) * ω ξ₁ ≤ ((c - b) * K) * ω ξ₁ := by
      have := mul_le_mul_of_nonneg_left hL21 hcb.le
      nlinarith
    exact le_of_mul_le_mul_right this hw1p

end

end GaloisForLFunctions.HTGeometry
