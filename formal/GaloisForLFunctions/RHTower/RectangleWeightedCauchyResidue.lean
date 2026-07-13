import GaloisForLFunctions.RHTower.RectangleCauchyFormula

/-!
# Weighted argument principle on a rectangle

The ordinary rectangle argument principle counts enclosed zeros.  The weighted form proved here
recovers an arbitrary entire test value at each enclosed zero, with its analytic multiplicity:

`∮ g(z) f'(z)/f(z) dz = 2πi ∑ ord_ρ(f) g(ρ)`.

The theorem is stated on an explicit finite factorization.  It is therefore directly composable
with `exists_multi_peel`, and it avoids any interchange between a contour integral and an infinite
divisor sum.  This is the appropriate analytic bridge from the Xi logarithmic derivative to finite
exhaustions of Guinand--Weil spectral values.
-/

open Complex intervalIntegral Set

namespace RHTower

noncomputable section

private theorem edgePoint_re (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).re = x := by simp

private theorem edgePoint_im (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).im = c := by simp

/-- **Weighted rectangle argument principle.**  Suppose the analytic function under the
logarithmic derivative is presented on a neighbourhood of the closed rectangle as a finite zero
product times an analytic nonvanishing cofactor.  Multiplication by any entire function `g` weights
each enclosed zero by `g` evaluated there. -/
theorem rectIntegral_mul_logDeriv_multi_zero
    {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {g h : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {z₁ z₂ : ℂ} {U : Set ℂ}
    (hin : ∀ i ∈ t, z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧
      z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0) :
    rectIntegral (fun z => g z *
      logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z) z₁ z₂ =
      2 * Real.pi * I * ∑ i ∈ t, (m i : ℂ) * g (ρ i) := by
  classical
  have hlogh : AnalyticOnNhd ℂ (logDeriv h) U := by
    have : logDeriv h = fun z => deriv h z / h z := rfl
    rw [this]
    exact fun z hz => (hh.deriv z hz).div (hh z hz) (hh0 z hz)
  have hgh : AnalyticOnNhd ℂ (fun z => g z * logDeriv h z) U :=
    fun z hz => (hg z (Set.mem_univ z)).mul (hlogh z hz)
  set S : Set ℂ := {z : ℂ | z ∈ U ∧ ∀ i ∈ t, z ≠ ρ i} with hS
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePoint_re]; exact hx,
          by rw [edgePoint_im]; exact left_mem_uIcc⟩), fun i hi he => ?_⟩
    obtain ⟨_, _, hi1, _⟩ := hin i hi
    have := congrArg Complex.im he
    rw [edgePoint_im] at this
    linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePoint_re]; exact hx,
          by rw [edgePoint_im]; exact right_mem_uIcc⟩), fun i hi he => ?_⟩
    obtain ⟨_, _, _, hi2⟩ := hin i hi
    have := congrArg Complex.im he
    rw [edgePoint_im] at this
    linarith
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePoint_re]; exact right_mem_uIcc,
          by rw [edgePoint_im]; exact hy⟩), fun i hi he => ?_⟩
    obtain ⟨_, hi2, _, _⟩ := hin i hi
    have := congrArg Complex.re he
    rw [edgePoint_re] at this
    linarith
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePoint_re]; exact left_mem_uIcc,
          by rw [edgePoint_im]; exact hy⟩), fun i hi he => ?_⟩
    obtain ⟨hi1, _, _, _⟩ := hin i hi
    have := congrArg Complex.re he
    rw [edgePoint_re] at this
    linarith
  have hid0 : ∀ z ∈ S,
      logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z =
        (∑ i ∈ t, (m i : ℂ) * (z - ρ i)⁻¹) + logDeriv h z := by
    rintro z ⟨hzU, hzρ⟩
    have hpne : ∀ i ∈ t, (fun w => (w - ρ i) ^ m i) z ≠ 0 :=
      fun i hi => pow_ne_zero _ (sub_ne_zero.mpr (hzρ i hi))
    rw [logDeriv_mul (f := fun w => ∏ i ∈ t, (w - ρ i) ^ m i) (g := h) z
        (Finset.prod_ne_zero_iff.mpr hpne) (hh0 z hzU) (by fun_prop)
        (hh z hzU).differentiableAt,
      logDeriv_prod hpne (fun i _ => by fun_prop)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [logDeriv_fun_pow (f := fun w => w - ρ i) (by fun_prop) (m i),
      show logDeriv (fun w => w - ρ i) z = (z - ρ i)⁻¹ from by
        rw [logDeriv_apply, show deriv (fun w => w - ρ i) z = 1 from
          ((hasDerivAt_id z).sub_const (ρ i)).deriv, one_div]]
  have hid : ∀ z ∈ S,
      g z * logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z =
        (∑ i ∈ t, (m i : ℂ) * (g z * (z - ρ i)⁻¹)) +
          g z * logDeriv h z := by
    intro z hz
    rw [hid0 z hz, mul_add, Finset.mul_sum]
    apply congrArg₂ (· + ·) ?_ rfl
    apply Finset.sum_congr rfl
    intro i _
    ring
  have IIk : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt →
      (∀ u ∈ uIcc c d, ∀ i ∈ t, pt u ≠ ρ i) →
      ∀ i ∈ t, IntervalIntegrable
        (fun u : ℝ => (m i : ℂ) * (g (pt u) * (pt u - ρ i)⁻¹))
        MeasureTheory.volume c d := by
    intro c d pt hpt hnz i hi
    have hgcont : Continuous g := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (hg z (Set.mem_univ z)).continuousAt
    refine (ContinuousOn.mul continuousOn_const
      ((hgcont.comp hpt).continuousOn.mul
        ((hpt.continuousOn.sub continuousOn_const).inv₀
          (fun u hu => sub_ne_zero.mpr (hnz u hu i hi))))).intervalIntegrable
  have IIsum : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt →
      (∀ u ∈ uIcc c d, ∀ i ∈ t, pt u ≠ ρ i) →
      IntervalIntegrable
        (fun u : ℝ => ∑ i ∈ t,
          (m i : ℂ) * (g (pt u) * (pt u - ρ i)⁻¹))
        MeasureTheory.volume c d :=
    fun pt hpt hnz => by
      refine IntervalIntegrable.congr ?_
        (IntervalIntegrable.sum t (fun i hi => IIk pt hpt hnz i hi))
      intro u _
      simp [Finset.sum_apply]
  have IIh : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt →
      (∀ u ∈ uIcc c d, pt u ∈ U) →
      IntervalIntegrable (fun u : ℝ => g (pt u) * logDeriv h (pt u))
        MeasureTheory.volume c d :=
    fun pt hpt hmem =>
      (hgh.continuousOn.comp hpt.continuousOn hmem).intervalIntegrable
  rw [rectIntegral_congr hid hbot htop hright hleft,
    rectIntegral_add
      (IIsum _ (by fun_prop) (fun x hx => (hbot x hx).2))
      (IIh _ (by fun_prop) (fun x hx => (hbot x hx).1))
      (IIsum _ (by fun_prop) (fun x hx => (htop x hx).2))
      (IIh _ (by fun_prop) (fun x hx => (htop x hx).1))
      (IIsum _ (by fun_prop) (fun y hy => (hright y hy).2))
      (IIh _ (by fun_prop) (fun y hy => (hright y hy).1))
      (IIsum _ (by fun_prop) (fun y hy => (hleft y hy).2))
      (IIh _ (by fun_prop) (fun y hy => (hleft y hy).1)),
    rectIntegral_finsetSum t
      (fun i z => (m i : ℂ) * (g z * (z - ρ i)⁻¹)) z₁ z₂
      (fun i hi => IIk _ (by fun_prop) (fun x hx => (hbot x hx).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun x hx => (htop x hx).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun y hy => (hright y hy).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun y hy => (hleft y hy).2) i hi),
    rectIntegral_eq_zero_of_analyticOnNhd hsub hgh, add_zero]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [rectIntegral_const_mul,
      rectIntegral_cauchyFormula_entire hg (hin i hi).1 (hin i hi).2.1
        (hin i hi).2.2.1 (hin i hi).2.2.2]), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Weighted rectangle zero extraction for an arbitrary analytic carrier.**  If `f` agrees on
an open neighbourhood of the rectangle with the finite zero product times `h`, its weighted
logarithmic-derivative contour integral is the corresponding multiplicity-weighted value sum.
This is the factorization-facing form used after `exists_multi_peel`. -/
theorem rectIntegral_mul_logDeriv_boxCount
    {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {f g h : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {z₁ z₂ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hin : ∀ i ∈ t, z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧
      z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0)
    (hfact : ∀ z ∈ U, f z = (∏ i ∈ t, (z - ρ i) ^ m i) * h z) :
    rectIntegral (fun z => g z * logDeriv f z) z₁ z₂ =
      2 * Real.pi * I * ∑ i ∈ t, (m i : ℂ) * g (ρ i) := by
  have hcongr : ∀ z ∈ U,
      g z * logDeriv f z =
        g z * logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z := by
    intro z hz
    congr 1
    have heq : f =ᶠ[nhds z]
        (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) := by
      filter_upwards [hUopen.mem_nhds hz] with w hw
      exact hfact w hw
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  rw [rectIntegral_congr hcongr
      (fun x hx => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePoint_re]; exact hx,
          by rw [edgePoint_im]; exact left_mem_uIcc⟩))
      (fun x hx => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePoint_re]; exact hx,
          by rw [edgePoint_im]; exact right_mem_uIcc⟩))
      (fun y hy => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePoint_re]; exact right_mem_uIcc,
          by rw [edgePoint_im]; exact hy⟩))
      (fun y hy => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePoint_re]; exact left_mem_uIcc,
          by rw [edgePoint_im]; exact hy⟩))]
  exact rectIntegral_mul_logDeriv_multi_zero t ρ m hg hin hsub hh hh0

end

end RHTower
