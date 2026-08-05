import GaloisForLFunctions.RHTower.RectangleLocalCauchyFormula
import GaloisForLFunctions.RHTower.RectangleWeightedCauchyResidue

/-!
# Local weighted argument principle on a rectangle

The existing weighted argument principle assumes an entire weight.  This exact local version only
assumes the weight analytic on the same neighbourhood as the finite factorization.  It is needed
for principal mass-root tests, which are analytic on a strip but have branch points outside it.
-/

open Complex intervalIntegral Set

namespace RHTower

noncomputable section

private theorem localWeightedEdgePoint_re (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).re = x := by simp

private theorem localWeightedEdgePoint_im (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).im = c := by simp

/-- **Local weighted rectangle argument principle.** -/
theorem rectIntegral_mul_logDeriv_multi_zero_of_analyticOnNhd
    {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {g h : ℂ → ℂ} {z₁ z₂ : ℂ} {U : Set ℂ}
    (hg : AnalyticOnNhd ℂ g U)
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
    fun z hz => (hg z hz).mul (hlogh z hz)
  set S : Set ℂ := {z : ℂ | z ∈ U ∧ ∀ i ∈ t, z ≠ ρ i} with hS
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [localWeightedEdgePoint_re]; exact hx,
          by rw [localWeightedEdgePoint_im]; exact left_mem_uIcc⟩), fun i hi he => ?_⟩
    have := congrArg Complex.im he
    rw [localWeightedEdgePoint_im] at this
    linarith [(hin i hi).2.2.1]
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [localWeightedEdgePoint_re]; exact hx,
          by rw [localWeightedEdgePoint_im]; exact right_mem_uIcc⟩), fun i hi he => ?_⟩
    have := congrArg Complex.im he
    rw [localWeightedEdgePoint_im] at this
    linarith [(hin i hi).2.2.2]
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [localWeightedEdgePoint_re]; exact right_mem_uIcc,
          by rw [localWeightedEdgePoint_im]; exact hy⟩), fun i hi he => ?_⟩
    have := congrArg Complex.re he
    rw [localWeightedEdgePoint_re] at this
    linarith [(hin i hi).2.1]
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [localWeightedEdgePoint_re]; exact left_mem_uIcc,
          by rw [localWeightedEdgePoint_im]; exact hy⟩), fun i hi he => ?_⟩
    have := congrArg Complex.re he
    rw [localWeightedEdgePoint_re] at this
    linarith [(hin i hi).1]
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
      (∀ u ∈ uIcc c d, pt u ∈ U) →
      (∀ u ∈ uIcc c d, ∀ i ∈ t, pt u ≠ ρ i) →
      ∀ i ∈ t, IntervalIntegrable
        (fun u : ℝ => (m i : ℂ) * (g (pt u) * (pt u - ρ i)⁻¹))
        MeasureTheory.volume c d := by
    intro c d pt hpt hmem hnz i hi
    refine (ContinuousOn.mul continuousOn_const
      ((hg.continuousOn.comp hpt.continuousOn hmem).mul
        ((hpt.continuousOn.sub continuousOn_const).inv₀
          (fun u hu => sub_ne_zero.mpr (hnz u hu i hi))))).intervalIntegrable
  have IIsum : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt →
      (∀ u ∈ uIcc c d, pt u ∈ U) →
      (∀ u ∈ uIcc c d, ∀ i ∈ t, pt u ≠ ρ i) →
      IntervalIntegrable
        (fun u : ℝ => ∑ i ∈ t,
          (m i : ℂ) * (g (pt u) * (pt u - ρ i)⁻¹))
        MeasureTheory.volume c d :=
    fun pt hpt hmem hnz => by
      refine IntervalIntegrable.congr ?_
        (IntervalIntegrable.sum t (fun i hi => IIk pt hpt hmem hnz i hi))
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
      (IIsum _ (by fun_prop) (fun x hx => (hbot x hx).1)
        (fun x hx => (hbot x hx).2))
      (IIh _ (by fun_prop) (fun x hx => (hbot x hx).1))
      (IIsum _ (by fun_prop) (fun x hx => (htop x hx).1)
        (fun x hx => (htop x hx).2))
      (IIh _ (by fun_prop) (fun x hx => (htop x hx).1))
      (IIsum _ (by fun_prop) (fun y hy => (hright y hy).1)
        (fun y hy => (hright y hy).2))
      (IIh _ (by fun_prop) (fun y hy => (hright y hy).1))
      (IIsum _ (by fun_prop) (fun y hy => (hleft y hy).1)
        (fun y hy => (hleft y hy).2))
      (IIh _ (by fun_prop) (fun y hy => (hleft y hy).1)),
    rectIntegral_finsetSum t
      (fun i z => (m i : ℂ) * (g z * (z - ρ i)⁻¹)) z₁ z₂
      (fun i hi => IIk _ (by fun_prop) (fun x hx => (hbot x hx).1)
        (fun x hx => (hbot x hx).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun x hx => (htop x hx).1)
        (fun x hx => (htop x hx).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun y hy => (hright y hy).1)
        (fun y hy => (hright y hy).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun y hy => (hleft y hy).1)
        (fun y hy => (hleft y hy).2) i hi),
    rectIntegral_eq_zero_of_analyticOnNhd hsub hgh, add_zero]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [rectIntegral_const_mul,
      rectIntegral_cauchyFormula_of_analyticOnNhd hg hsub
        (hin i hi).1 (hin i hi).2.1 (hin i hi).2.2.1 (hin i hi).2.2.2]),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Factorization-facing local weighted zero extraction.  Both the carrier identity and the
weight only need to hold on one open neighbourhood of the closed rectangle. -/
theorem rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
    {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {f g h : ℂ → ℂ} {z₁ z₂ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
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
        ⟨by rw [localWeightedEdgePoint_re]; exact hx,
          by rw [localWeightedEdgePoint_im]; exact left_mem_uIcc⟩))
      (fun x hx => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [localWeightedEdgePoint_re]; exact hx,
          by rw [localWeightedEdgePoint_im]; exact right_mem_uIcc⟩))
      (fun y hy => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [localWeightedEdgePoint_re]; exact right_mem_uIcc,
          by rw [localWeightedEdgePoint_im]; exact hy⟩))
      (fun y hy => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [localWeightedEdgePoint_re]; exact left_mem_uIcc,
          by rw [localWeightedEdgePoint_im]; exact hy⟩))]
  exact rectIntegral_mul_logDeriv_multi_zero_of_analyticOnNhd
    t ρ m hg hin hsub hh hh0

end

end RHTower
