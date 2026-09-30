import GaloisForLFunctions.RHTower.RectangleLocalWeightedCauchyResidue
import GaloisForLFunctions.RHTower.RectangleLocalCauchyFormula

/-!
# Weighted argument principle with a simple pole inside the rectangle

Let `G = (∏ᵢ (z − ρᵢ)^{mᵢ}) · h` on a neighbourhood `U` of a closed rectangle, with `h` analytic and
nonvanishing on `U` and every `ρᵢ` strictly inside. For every `φ` analytic on `U` and every strict
interior point `s₀` different from the `ρᵢ`,

`∮ φ(z) (z − s₀)⁻¹ G'(z)/G(z) dz = 2πi (Σᵢ mᵢ φ(ρᵢ)/(ρᵢ − s₀) + φ(s₀) G'(s₀)/G(s₀))`
(`rectIntegral_mul_inv_sub_mul_logDeriv_multi_zero`).

The extra pole at `s₀` returns the logarithmic derivative at `s₀` itself. The proof splits
`φ(z)/((z − ρ)(z − s₀))` by partial fractions and applies the local Cauchy formula at each point.
-/

open Complex intervalIntegral Set

namespace RHTower

noncomputable section

private theorem poleEdge_re (x c : ℝ) : ((x : ℂ) + (c : ℂ) * I).re = x := by simp

private theorem poleEdge_im (x c : ℝ) : ((x : ℂ) + (c : ℂ) * I).im = c := by simp

/-- **Weighted argument principle with an interior simple pole of the weight.** -/
theorem rectIntegral_mul_inv_sub_mul_logDeriv_multi_zero
    {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {φ h : ℂ → ℂ} {z₁ z₂ s₀ : ℂ} {U : Set ℂ}
    (hφ : AnalyticOnNhd ℂ φ U)
    (hin : ∀ i ∈ t, z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧
      z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im)
    (hs₀ : z₁.re < s₀.re ∧ s₀.re < z₂.re ∧ z₁.im < s₀.im ∧ s₀.im < z₂.im)
    (hne : ∀ i ∈ t, ρ i ≠ s₀)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0) :
    rectIntegral (fun z => φ z * (z - s₀)⁻¹ *
      logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z) z₁ z₂ =
      2 * Real.pi * I * (∑ i ∈ t, (m i : ℂ) * (φ (ρ i) * (ρ i - s₀)⁻¹) +
        φ s₀ * logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) s₀) := by
  classical
  set c : κ → ℂ := fun i => (m i : ℂ) * (ρ i - s₀)⁻¹ with hc
  have hlogh : AnalyticOnNhd ℂ (logDeriv h) U := by
    have : logDeriv h = fun z => deriv h z / h z := rfl
    rw [this]
    exact fun z hz => (hh.deriv z hz).div (hh z hz) (hh0 z hz)
  set g₀ : ℂ → ℂ := fun z => φ z * (logDeriv h z - ∑ i ∈ t, c i) with hg₀
  have hg₀an : AnalyticOnNhd ℂ g₀ U :=
    fun z hz => (hφ z hz).mul ((hlogh z hz).sub analyticAt_const)
  have hs₀U : s₀ ∈ U := hsub (Complex.mem_reProdIm.mpr
    ⟨by rw [uIcc_of_le (hs₀.1.trans hs₀.2.1).le]; exact ⟨hs₀.1.le, hs₀.2.1.le⟩,
      by rw [uIcc_of_le (hs₀.2.2.1.trans hs₀.2.2.2).le]; exact ⟨hs₀.2.2.1.le, hs₀.2.2.2.le⟩⟩)
  -- the logarithmic derivative of the product off the zeros
  have hid0 : ∀ z, z ∈ U → (∀ i ∈ t, z ≠ ρ i) →
      logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z =
        (∑ i ∈ t, (m i : ℂ) * (z - ρ i)⁻¹) + logDeriv h z := by
    intro z hzU hzρ
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
  -- the boundary avoids the zeros and the pole
  set S : Set ℂ := {z : ℂ | z ∈ U ∧ (∀ i ∈ t, z ≠ ρ i) ∧ z ≠ s₀} with hS
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [poleEdge_re]; exact hx, by rw [poleEdge_im]; exact left_mem_uIcc⟩),
      fun i hi he => ?_, fun he => ?_⟩
    · have := congrArg Complex.im he
      rw [poleEdge_im] at this
      linarith [(hin i hi).2.2.1]
    · have := congrArg Complex.im he
      rw [poleEdge_im] at this
      linarith [hs₀.2.2.1]
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [poleEdge_re]; exact hx, by rw [poleEdge_im]; exact right_mem_uIcc⟩),
      fun i hi he => ?_, fun he => ?_⟩
    · have := congrArg Complex.im he
      rw [poleEdge_im] at this
      linarith [(hin i hi).2.2.2]
    · have := congrArg Complex.im he
      rw [poleEdge_im] at this
      linarith [hs₀.2.2.2]
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [poleEdge_re]; exact right_mem_uIcc, by rw [poleEdge_im]; exact hy⟩),
      fun i hi he => ?_, fun he => ?_⟩
    · have := congrArg Complex.re he
      rw [poleEdge_re] at this
      linarith [(hin i hi).2.1]
    · have := congrArg Complex.re he
      rw [poleEdge_re] at this
      linarith [hs₀.2.1]
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [poleEdge_re]; exact left_mem_uIcc, by rw [poleEdge_im]; exact hy⟩),
      fun i hi he => ?_, fun he => ?_⟩
    · have := congrArg Complex.re he
      rw [poleEdge_re] at this
      linarith [(hin i hi).1]
    · have := congrArg Complex.re he
      rw [poleEdge_re] at this
      linarith [hs₀.1]
  -- partial fractions on the boundary
  have hid : ∀ z ∈ S,
      φ z * (z - s₀)⁻¹ * logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z =
        (∑ i ∈ t, c i * (φ z * (z - ρ i)⁻¹)) + g₀ z * (z - s₀)⁻¹ := by
    rintro z ⟨hzU, hzρ, hzs⟩
    rw [hid0 z hzU hzρ, hg₀]
    have hzs' : z - s₀ ≠ 0 := sub_ne_zero.mpr hzs
    have hterm : ∀ i ∈ t, c i * (φ z * (z - ρ i)⁻¹) - c i * φ z * (z - s₀)⁻¹ =
        φ z * (z - s₀)⁻¹ * ((m i : ℂ) * (z - ρ i)⁻¹) := by
      intro i hi
      have hzρ' : z - ρ i ≠ 0 := sub_ne_zero.mpr (hzρ i hi)
      have hρs : ρ i - s₀ ≠ 0 := sub_ne_zero.mpr (hne i hi)
      rw [hc]
      field_simp
      ring
    have hsum : (∑ i ∈ t, c i * (φ z * (z - ρ i)⁻¹)) -
        (∑ i ∈ t, c i) * φ z * (z - s₀)⁻¹ =
        φ z * (z - s₀)⁻¹ * ∑ i ∈ t, (m i : ℂ) * (z - ρ i)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hterm
    linear_combination (-1 : ℂ) * hsum
  -- edgewise integrability
  have hφc : ContinuousOn φ U := hφ.continuousOn
  have IIk : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ u ∈ uIcc a b, pt u ∈ S) →
      ∀ i ∈ t, IntervalIntegrable (fun u : ℝ => c i * (φ (pt u) * (pt u - ρ i)⁻¹))
        MeasureTheory.volume a b := by
    intro a b pt hpt hS' i hi
    refine (ContinuousOn.mul continuousOn_const
      ((hφc.comp hpt.continuousOn (fun u hu => (hS' u hu).1)).mul
        ((hpt.continuousOn.sub continuousOn_const).inv₀
          (fun u hu => sub_ne_zero.mpr ((hS' u hu).2.1 i hi))))).intervalIntegrable
  have IIsum : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ u ∈ uIcc a b, pt u ∈ S) →
      IntervalIntegrable (fun u : ℝ => ∑ i ∈ t, c i * (φ (pt u) * (pt u - ρ i)⁻¹))
        MeasureTheory.volume a b :=
    fun pt hpt hS' => by
      refine IntervalIntegrable.congr ?_
        (IntervalIntegrable.sum t (fun i hi => IIk pt hpt hS' i hi))
      intro u _
      simp [Finset.sum_apply]
  have II₀ : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ u ∈ uIcc a b, pt u ∈ S) →
      IntervalIntegrable (fun u : ℝ => g₀ (pt u) * (pt u - s₀)⁻¹) MeasureTheory.volume a b :=
    fun pt hpt hS' =>
      ((hg₀an.continuousOn.comp hpt.continuousOn (fun u hu => (hS' u hu).1)).mul
        ((hpt.continuousOn.sub continuousOn_const).inv₀
          (fun u hu => sub_ne_zero.mpr (hS' u hu).2.2))).intervalIntegrable
  rw [rectIntegral_congr hid hbot htop hright hleft,
    rectIntegral_add
      (IIsum _ (by fun_prop) hbot) (II₀ _ (by fun_prop) hbot)
      (IIsum _ (by fun_prop) htop) (II₀ _ (by fun_prop) htop)
      (IIsum _ (by fun_prop) hright) (II₀ _ (by fun_prop) hright)
      (IIsum _ (by fun_prop) hleft) (II₀ _ (by fun_prop) hleft),
    rectIntegral_finsetSum t (fun i z => c i * (φ z * (z - ρ i)⁻¹)) z₁ z₂
      (fun i hi => IIk _ (by fun_prop) hbot i hi)
      (fun i hi => IIk _ (by fun_prop) htop i hi)
      (fun i hi => IIk _ (by fun_prop) hright i hi)
      (fun i hi => IIk _ (by fun_prop) hleft i hi),
    rectIntegral_cauchyFormula_of_analyticOnNhd hg₀an hsub hs₀.1 hs₀.2.1 hs₀.2.2.1 hs₀.2.2.2]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [rectIntegral_const_mul,
      rectIntegral_cauchyFormula_of_analyticOnNhd hφ hsub (hin i hi).1 (hin i hi).2.1
        (hin i hi).2.2.1 (hin i hi).2.2.2])]
  have hs₀ρ : ∀ i ∈ t, s₀ ≠ ρ i := fun i hi h => hne i hi h.symm
  rw [hid0 s₀ hs₀U hs₀ρ, hg₀]
  have hneg : ∀ i ∈ t, (m i : ℂ) * (s₀ - ρ i)⁻¹ = -c i := by
    intro i hi
    have hρs : ρ i - s₀ ≠ 0 := sub_ne_zero.mpr (hne i hi)
    have hsρ : s₀ - ρ i ≠ 0 := sub_ne_zero.mpr (hs₀ρ i hi)
    rw [hc]
    field_simp
    ring
  rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib]
  have e1 : ∑ x ∈ t, c x * (2 * (Real.pi : ℂ) * I * φ (ρ x)) =
      2 * (Real.pi : ℂ) * I * ∑ i ∈ t, (m i : ℂ) * (φ (ρ i) * (ρ i - s₀)⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hc]
    ring
  rw [e1]
  ring

end

end RHTower
