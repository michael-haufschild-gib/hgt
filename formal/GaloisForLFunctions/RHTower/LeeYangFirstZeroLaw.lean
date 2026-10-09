import Mathlib

/-!
# The first-zero law for Lee–Yang splittings

Let `a, b` be entire functions with

* `a z ≠ 0` and `‖b z‖ ≤ ‖a z‖` whenever `Im z < 0`,
* `‖b t‖ = ‖a t‖` for real `t`,

and let `λ > 0`.  Then `f(t) = a(t) + b(t) e^{−iλt}` vanishes at some real point of
`[−π/λ, π/λ]` (`exists_zero_of_innerSplit`).

This is the shape of every Lee–Yang restriction that is affine in one field `u = e^{−iλt}`:
`P = A + u·B`, where polydisk stability gives `|B| ≤ |A|` inside and the reflected polynomial gives
`|B| = |A|` on the torus.  So a field of frequency `λ` forces a real zero within `π/λ`, whatever
the other fields and couplings.

**Proof.**  Suppose `f` has no zero on the interval.  Then `a ≠ 0` there, and `w = b e^{−iλt}/a`
has modulus one and avoids `−1`, so its principal argument `ψ(t) = arg w(t)` is differentiable.
Below the axis `‖w(t − is)‖ ≤ e^{−λ s}`, while `‖w(t)‖ = 1`; comparing the slopes of
`s ↦ ‖w(t − is)‖²` at `s = 0⁺` gives `ψ'(t) = Im(w'/w) ≤ −λ`.  By the mean value theorem
`ψ(π/λ) ≤ ψ(0) − π` and `ψ(−π/λ) ≥ ψ(0) + π`, impossible for an argument in `(−π, π]`.
-/

open Complex Set Filter Topology

namespace RHTower.LeeYangFirstZero

noncomputable section

/-- The unimodular quotient `w = b e^{−iλz}/a`. -/
def splitQuotient (lam : ℝ) (a b : ℂ → ℂ) (z : ℂ) : ℂ :=
  b z * cexp (-(I * (lam : ℂ) * z)) / a z

theorem norm_cexp_neg_I_mul (lam : ℝ) (z : ℂ) :
    ‖cexp (-(I * (lam : ℂ) * z))‖ = Real.exp (lam * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **Boundary slope.**  If `‖w(t − is)‖ ≤ e^{−λ s}` for `s > 0`, `‖w t‖ = 1` and `w` is
complex-differentiable at `t`, then `Im (w'(t) / w(t)) ≤ −λ`. -/
theorem im_deriv_div_le {lam : ℝ} {w : ℂ → ℂ} {t : ℝ} (hw : DifferentiableAt ℂ w (t : ℂ))
    (hone : ‖w t‖ = 1)
    (hbelow : ∀ s : ℝ, 0 < s → ‖w ((t : ℂ) - s * I)‖ ≤ Real.exp (-(lam * s))) :
    (deriv w t / w t).im ≤ -lam := by
  have hw0 : w t ≠ 0 := by
    intro h; rw [h, norm_zero] at hone; exact zero_ne_one hone
  -- the path `s ↦ t − is`
  have hpath : HasDerivAt (fun s : ℝ => (t : ℂ) - (s : ℂ) * I) (-I) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).const_sub (t : ℂ)
    simpa using h
  have hcomp : HasDerivAt (fun s : ℝ => w ((t : ℂ) - (s : ℂ) * I)) (deriv w t * (-I)) 0 := by
    have hw' : HasDerivAt w (deriv w t) ((t : ℂ) - ((0 : ℝ) : ℂ) * I) := by
      simpa using hw.hasDerivAt
    exact hw'.comp_of_eq (0 : ℝ) hpath (by simp)
  have hsq := hcomp.norm_sq
  set φ : ℝ → ℝ := fun s => ‖w ((t : ℂ) - (s : ℂ) * I)‖ ^ 2 with hφ
  have hφ0 : φ 0 = 1 := by simp [hφ, hone]
  -- the comparison function `e^{−2λ s}`
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(2 * lam) * s)) (-(2 * lam)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_mul (-(2 * lam))).exp
    simpa using h
  have hle : ∀ s : ℝ, 0 < s → φ s ≤ Real.exp (-(2 * lam) * s) := by
    intro s hs
    have h1 := hbelow s hs
    have h2 : ‖w ((t : ℂ) - (s : ℂ) * I)‖ ^ 2 ≤ Real.exp (-(lam * s)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [← Real.exp_nat_mul] at h2
    simp only [hφ]
    convert h2 using 2
    push_cast
    ring
  -- slopes from the right
  have hslope := hsq.tendsto_slope_zero_right
  have hslope' := hexp.tendsto_slope_zero_right
  have hineq : (2 * inner ℝ (w ((t : ℂ) - ((0 : ℝ) : ℂ) * I)) (deriv w t * -I)) ≤ -(2 * lam) := by
    refine le_of_tendsto_of_tendsto hslope hslope' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hφs := hle s hs'
    simp only [zero_add, smul_eq_mul]
    have hpos : 0 < s⁻¹ := inv_pos.mpr hs'
    have h0 : Real.exp (-(2 * lam) * 0) = 1 := by simp
    have := hφ0
    simp only [hφ] at this hφs ⊢
    rw [this, h0]
    exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
  -- identify the inner product
  have hinner : inner ℝ (w ((t : ℂ) - ((0 : ℝ) : ℂ) * I)) (deriv w t * -I) =
      ((starRingEnd ℂ) (w t) * deriv w t).im := by
    rw [Complex.inner]
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hinner] at hineq
  have hnormsq : Complex.normSq (w t) = 1 := by
    rw [← Complex.sq_norm, hone, one_pow]
  have hdiv : deriv w t / w t = (starRingEnd ℂ) (w t) * deriv w t := by
    rw [div_eq_mul_inv, Complex.inv_def, hnormsq, inv_one, Complex.ofReal_one, mul_one,
      mul_comm]
  rw [hdiv]
  linarith

/-- **The first-zero law.** -/
theorem exists_zero_of_innerSplit {lam : ℝ} (hlam : 0 < lam) {a b : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b)
    (hlow : ∀ z : ℂ, z.im < 0 → a z ≠ 0 ∧ ‖b z‖ ≤ ‖a z‖)
    (hreal : ∀ t : ℝ, ‖b t‖ = ‖a t‖) :
    ∃ t ∈ Icc (-(Real.pi / lam)) (Real.pi / lam),
      a t + b t * cexp (-(I * (lam : ℂ) * t)) = 0 := by
  have hpi := Real.pi_pos
  have hT : 0 < Real.pi / lam := div_pos hpi hlam
  by_contra hno
  push Not at hno
  set w := splitQuotient lam a b with hwdef
  set S := Icc (-(Real.pi / lam)) (Real.pi / lam) with hS
  -- `a` does not vanish on the interval
  have ha0 : ∀ t ∈ S, a t ≠ 0 := by
    intro t ht h
    have hb0 : b t = 0 := by
      rw [← norm_eq_zero, hreal t, h, norm_zero]
    exact hno t ht (by rw [h, hb0]; ring)
  have hnormE : ∀ t : ℝ, ‖cexp (-(I * (lam : ℂ) * t))‖ = 1 := fun t => by
    rw [norm_cexp_neg_I_mul]; simp
  have hwone : ∀ t ∈ S, ‖w t‖ = 1 := by
    intro t ht
    rw [hwdef, splitQuotient, norm_div, norm_mul, hnormE, mul_one, hreal t,
      div_self (norm_ne_zero_iff.mpr (ha0 t ht))]
  have hfw : ∀ t ∈ S, a t + b t * cexp (-(I * (lam : ℂ) * t)) = a t * (1 + w t) := by
    intro t ht
    rw [hwdef, splitQuotient]
    field_simp [ha0 t ht]
  have hwne : ∀ t ∈ S, w t ≠ -1 := by
    intro t ht h
    apply hno t ht
    rw [hfw t ht, h]; ring
  have hslit : ∀ t ∈ S, w t ∈ slitPlane := by
    intro t ht
    rw [Complex.mem_slitPlane_iff]
    by_cases him : (w t).im = 0
    · left
      have hn := hwone t ht
      have hsq : (w t).re ^ 2 = 1 := by
        have := Complex.sq_norm (w t)
        rw [hn, Complex.normSq_apply, him] at this
        nlinarith
      rcases sq_eq_one_iff.mp hsq with h | h
      · rw [h]; norm_num
      · exfalso
        apply hwne t ht
        exact Complex.ext (by simp [h]) (by simp [him])
    · right; exact him
  have hwdiff : ∀ t ∈ S, DifferentiableAt ℂ w (t : ℂ) := by
    intro t ht
    rw [hwdef]
    unfold splitQuotient
    exact ((hb.differentiableAt).mul (by fun_prop)).div ha.differentiableAt (ha0 t ht)
  -- below the axis `‖w(t − is)‖ ≤ e^{−λ s}`
  have hbelow : ∀ t ∈ S, ∀ s : ℝ, 0 < s → ‖w ((t : ℂ) - s * I)‖ ≤ Real.exp (-(lam * s)) := by
    intro t _ s hs
    have him : ((t : ℂ) - s * I).im < 0 := by simp; linarith
    obtain ⟨hna, hle⟩ := hlow _ him
    rw [hwdef, splitQuotient, norm_div, norm_mul, norm_cexp_neg_I_mul]
    have him' : ((t : ℂ) - s * I).im = -s := by simp
    rw [him']
    rw [div_le_iff₀ (norm_pos_iff.mpr hna)]
    have : Real.exp (lam * -s) = Real.exp (-(lam * s)) := by ring_nf
    rw [this]
    nlinarith [Real.exp_pos (-(lam * s)), norm_nonneg (b ((t : ℂ) - s * I))]
  -- the argument along the interval
  set ψ : ℝ → ℝ := fun x => (Complex.log (w x)).im with hψ
  have hψderiv : ∀ x ∈ S, HasDerivAt ψ (deriv w x / w x).im x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => w y) (deriv w x) x :=
      (hwdiff x hx).hasDerivAt.comp_ofReal
    have h2 := h1.clog_real (hslit x hx)
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h2)
  have hψle : ∀ x ∈ S, (deriv w x / w x).im ≤ -lam := fun x hx =>
    im_deriv_div_le (hwdiff x hx) (hwone x hx) (hbelow x hx)
  have hcont : ContinuousOn ψ S := fun x hx => (hψderiv x hx).continuousAt.continuousWithinAt
  have hconv : Convex ℝ S := convex_Icc _ _
  have hdiffint : DifferentiableOn ℝ ψ (interior S) := fun x hx =>
    (hψderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hderivle : ∀ x ∈ interior S, deriv ψ x ≤ -lam := fun x hx => by
    rw [(hψderiv x (interior_subset hx)).deriv]
    exact hψle x (interior_subset hx)
  have hmemT : Real.pi / lam ∈ S := ⟨by linarith, le_rfl⟩
  have hmemNT : -(Real.pi / lam) ∈ S := ⟨le_rfl, by linarith⟩
  have hmem0 : (0 : ℝ) ∈ S := ⟨by linarith, hT.le⟩
  have hright := hconv.image_sub_le_mul_sub_of_deriv_le hcont hdiffint hderivle 0 hmem0
    (Real.pi / lam) hmemT hT.le
  have hleft := hconv.image_sub_le_mul_sub_of_deriv_le hcont hdiffint hderivle
    (-(Real.pi / lam)) hmemNT 0 hmem0 (by linarith)
  have hlamT : -lam * (Real.pi / lam - 0) = -Real.pi := by rw [sub_zero]; field_simp
  have hlamT' : -lam * (0 - -(Real.pi / lam)) = -Real.pi := by rw [zero_sub, neg_neg]; field_simp
  rw [hlamT] at hright
  rw [hlamT'] at hleft
  have hlo : -Real.pi < ψ (Real.pi / lam) := by
    simp only [hψ, Complex.log_im]; exact Complex.neg_pi_lt_arg _
  have hhi : ψ (-(Real.pi / lam)) ≤ Real.pi := by
    simp only [hψ, Complex.log_im]; exact Complex.arg_le_pi _
  linarith

/-- **Zero-gap law.**  Under the same hypotheses, every window `[t₀ − π/λ, t₀ + π/λ]` contains a
real zero of `a + b e^{−iλt}`: the real zeros have gaps at most `2π/λ`. -/
theorem exists_zero_of_innerSplit_near {lam : ℝ} (hlam : 0 < lam) {a b : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b)
    (hlow : ∀ z : ℂ, z.im < 0 → a z ≠ 0 ∧ ‖b z‖ ≤ ‖a z‖)
    (hreal : ∀ t : ℝ, ‖b t‖ = ‖a t‖) (t₀ : ℝ) :
    ∃ t ∈ Icc (t₀ - Real.pi / lam) (t₀ + Real.pi / lam),
      a t + b t * cexp (-(I * (lam : ℂ) * t)) = 0 := by
  set c : ℂ := cexp (-(I * (lam : ℂ) * t₀)) with hc
  have hcn : ‖c‖ = 1 := by rw [hc, norm_cexp_neg_I_mul]; simp
  obtain ⟨s, hs, h⟩ := exists_zero_of_innerSplit (a := fun z => a (z + t₀))
    (b := fun z => b (z + t₀) * c) hlam
    (ha.comp (differentiable_id.add_const _)) ((hb.comp (differentiable_id.add_const _)).mul_const _)
    (fun z hz => by
      have hz' : (z + t₀).im < 0 := by simpa using hz
      obtain ⟨h1, h2⟩ := hlow _ hz'
      exact ⟨h1, by rw [norm_mul, hcn, mul_one]; exact h2⟩)
    (fun t => by
      simp only [norm_mul, hcn, mul_one]
      have := hreal (t + t₀)
      push_cast at this
      exact this)
  refine ⟨s + t₀, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
  have hexp : cexp (-(I * (lam : ℂ) * ((s + t₀ : ℝ) : ℂ))) =
      c * cexp (-(I * (lam : ℂ) * (s : ℂ))) := by
    rw [hc, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hexp]
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

end

end RHTower.LeeYangFirstZero
