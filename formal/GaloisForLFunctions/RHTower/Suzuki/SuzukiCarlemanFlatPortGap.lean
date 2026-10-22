import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanFlatPortBarrier

/-!
# The exact endpoint gap of the flat Carleman port

Subtracting the endpoint counterterm leaves the tail of the response derivative,

`B_∞ - B(L) = ∫_{M > L} B'(M) dM`,

and since `B'/F → 1` the tail ratio against the profile's own tail tends to one.  With the exact
tail `∫_{M > L} F = 2(√L+1) F(L)` this gives the card's rate

`B_∞ - B(L) = 2 √L F(L) (1 + o(1))`.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

theorem deriv_carlemanLogResponse (L : ℝ) :
    deriv carlemanLogResponse L = carlemanLogResponseDeriv L :=
  (hasDerivAt_carlemanLogResponse L).deriv

theorem measurable_carlemanLogResponseDeriv : Measurable carlemanLogResponseDeriv := by
  have h : carlemanLogResponseDeriv = deriv carlemanLogResponse := by
    funext L
    exact (deriv_carlemanLogResponse L).symm
  rw [h]
  exact measurable_deriv _

theorem carlemanLogResponseDeriv_pos (L : ℝ) : 0 < carlemanLogResponseDeriv L := by
  rw [carlemanLogResponseDeriv]
  apply setIntegral_pos_iff_support_of_nonneg_ae _ (integrableOn_carlemanDerivIntegrand L) |>.mpr
  · have hsupport : Function.support (fun v => flatPortProfile v * logisticKernel (v - L))
        ∩ Ioi (1:ℝ) = Ioi (1:ℝ) := by
      ext v
      constructor
      · intro hv
        exact hv.2
      · intro hv
        refine ⟨?_, hv⟩
        have := mul_pos (flatPortProfile_pos v) (logisticKernel_pos (v - L))
        exact ne_of_gt this
    rw [hsupport, Real.volume_Ioi]
    simp
  · filter_upwards with v
    exact (mul_pos (flatPortProfile_pos v) (logisticKernel_pos (v - L))).le

/-- The response converges to its endpoint counterterm. -/
theorem tendsto_carlemanLogResponse :
    Tendsto carlemanLogResponse atTop (𝓝 carlemanLogResponseLimit) := by
  have hmeas : ∀ᶠ L in atTop, AEStronglyMeasurable
      (fun v => flatPortProfile v * carlemanCutoffFactor L v)
      (volume.restrict (Ioi (1:ℝ))) := by
    filter_upwards with L
    apply Measurable.aestronglyMeasurable
    unfold flatPortProfile carlemanCutoffFactor
    fun_prop
  have hbound : ∀ᶠ L in atTop, ∀ᵐ v ∂(volume.restrict (Ioi (1:ℝ))),
      ‖flatPortProfile v * carlemanCutoffFactor L v‖ ≤ flatPortProfile v := by
    filter_upwards with L
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (flatPortProfile_pos v).le (carlemanCutoffFactor_pos L v).le)]
    have h1 := carlemanCutoffFactor_le_one L v
    nlinarith [flatPortProfile_pos v, carlemanCutoffFactor_pos L v]
  have hlim : ∀ᵐ v ∂(volume.restrict (Ioi (1:ℝ))),
      Tendsto (fun L => flatPortProfile v * carlemanCutoffFactor L v) atTop
        (𝓝 (flatPortProfile v)) := by
    filter_upwards with v
    have hcut : Tendsto (fun L : ℝ => carlemanCutoffFactor L v) atTop (𝓝 1) := by
      have hexp : Tendsto (fun L : ℝ => Real.exp (v - L)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun L : ℝ => v - L) atTop atBot :=
          tendsto_atBot_add_const_left _ v (tendsto_neg_atTop_atBot)
        exact Real.tendsto_exp_atBot.comp h1
      have h2 : Tendsto (fun L : ℝ => (1 + Real.exp (v - L))⁻¹) atTop (𝓝 ((1:ℝ) + 0)⁻¹) := by
        apply Filter.Tendsto.inv₀ _ (by norm_num)
        exact tendsto_const_nhds.add hexp
      simpa [carlemanCutoffFactor] using h2
    have := hcut.const_mul (flatPortProfile v)
    simpa using this
  exact tendsto_integral_filter_of_dominated_convergence _ hmeas hbound
    integrableOn_flatPortProfile_one hlim

/-- Above the comparison threshold the response derivative is integrable on the ray. -/
theorem integrableOn_carlemanLogResponseDeriv_of_le {L₀ L : ℝ} (hL₀ : 0 < L₀)
    (hcomp : ∀ M, L₀ ≤ M → carlemanLogResponseDeriv M ≤ 2 * flatPortProfile M) (hL : L₀ ≤ L) :
    IntegrableOn carlemanLogResponseDeriv (Ioi L) volume := by
  have hpos : 0 < L := lt_of_lt_of_le hL₀ hL
  refine Integrable.mono' ((integrableOn_flatPortProfile L hpos).const_mul 2)
    measurable_carlemanLogResponseDeriv.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with M hM
  rw [Real.norm_eq_abs, abs_of_nonneg (carlemanLogResponseDeriv_pos M).le]
  exact hcomp M (le_trans hL (le_of_lt hM))

/-- **The endpoint gap is the tail of the derivative.** -/
theorem carlemanLogResponse_gap_eq {L₀ L : ℝ} (hL₀ : 0 < L₀)
    (hcomp : ∀ M, L₀ ≤ M → carlemanLogResponseDeriv M ≤ 2 * flatPortProfile M) (hL : L₀ ≤ L) :
    (∫ M in Ioi L, carlemanLogResponseDeriv M)
      = carlemanLogResponseLimit - carlemanLogResponse L := by
  apply integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_carlemanLogResponse L).continuousAt.continuousWithinAt
    (fun M _ => hasDerivAt_carlemanLogResponse M)
    (integrableOn_carlemanLogResponseDeriv_of_le hL₀ hcomp hL)
    tendsto_carlemanLogResponse

/-- **Tail comparison.**  Two positive densities with ratio tending to one have tail integrals
with ratio tending to one. -/
theorem tendsto_tail_integral_ratio {f g : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, 0 < f x)
    (hfint : ∀ L, a ≤ L → IntegrableOn f (Ioi L) volume)
    (hgint : ∀ L, a ≤ L → IntegrableOn g (Ioi L) volume)
    (hfpos : ∀ L, a ≤ L → 0 < ∫ x in Ioi L, f x)
    (hratio : Tendsto (fun x => g x / f x) atTop (𝓝 1)) :
    Tendsto (fun L => (∫ x in Ioi L, g x) / ∫ x in Ioi L, f x) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : (0:ℝ) < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hratio (ε / 2) hhalf
  refine ⟨max N a, fun L hL => ?_⟩
  have hLa : a ≤ L := le_trans (le_max_right N a) hL
  have hLN : N ≤ L := le_trans (le_max_left N a) hL
  have hgf : ∀ x ∈ Ioi L, |g x - f x| ≤ (ε / 2) * f x := by
    intro x hx
    have hxN : N ≤ x := le_trans hLN (le_of_lt hx)
    have := hN x hxN
    rw [Real.dist_eq, abs_lt] at this
    have hfx := hf x
    have hkey : (g x / f x - 1) * f x = g x - f x := by
      field_simp
    rw [abs_le]
    constructor
    · have hmul := mul_lt_mul_of_pos_right this.1 hfx
      rw [hkey] at hmul
      linarith
    · have hmul := mul_lt_mul_of_pos_right this.2 hfx
      rw [hkey] at hmul
      linarith
  have hgfint : IntegrableOn (fun x => g x - f x) (Ioi L) volume :=
    (hgint L hLa).sub (hfint L hLa)
  have hbound : |(∫ x in Ioi L, g x) - ∫ x in Ioi L, f x| ≤ (ε / 2) * ∫ x in Ioi L, f x := by
    rw [← integral_sub (hgint L hLa) (hfint L hLa)]
    calc |∫ x in Ioi L, (g x - f x)| ≤ ∫ x in Ioi L, |g x - f x| := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume.restrict (Ioi L))
            (f := fun x => g x - f x)
      _ ≤ ∫ x in Ioi L, (ε / 2) * f x := by
          refine setIntegral_mono_on hgfint.abs ((hfint L hLa).const_mul _) measurableSet_Ioi ?_
          exact hgf
      _ = (ε / 2) * ∫ x in Ioi L, f x := integral_const_mul _ _
  have hden := hfpos L hLa
  rw [Real.dist_eq]
  have hsub : (∫ x in Ioi L, g x) / (∫ x in Ioi L, f x) - 1
      = ((∫ x in Ioi L, g x) - ∫ x in Ioi L, f x) / ∫ x in Ioi L, f x := by
    field_simp
  rw [hsub, abs_div, abs_of_pos hden, div_lt_iff₀ hden]
  calc |(∫ x in Ioi L, g x) - ∫ x in Ioi L, f x| ≤ (ε / 2) * ∫ x in Ioi L, f x := hbound
    _ < ε * ∫ x in Ioi L, f x := by nlinarith

/-- There is a scale past which the response derivative is at most twice the profile. -/
theorem exists_carlemanDeriv_comparison :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ M, L₀ ≤ M → carlemanLogResponseDeriv M ≤ 2 * flatPortProfile M := by
  have hev : ∀ᶠ L in atTop, carlemanLogResponseDeriv L / flatPortProfile L ≤ 2 :=
    tendsto_carlemanLogResponseDeriv_div.eventually (eventually_le_nhds (by norm_num : (1:ℝ) < 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1), fun M hM => ?_⟩
  have hMN : N ≤ M := le_trans (le_max_left N 1) hM
  have hpos := flatPortProfile_pos M
  have := hN M hMN
  rw [div_le_iff₀ hpos] at this
  linarith

/-- **`(6)`: the exact endpoint-gap rate of the flat Carleman port.** -/
theorem tendsto_carlemanLogResponse_gap :
    Tendsto (fun L => (carlemanLogResponseLimit - carlemanLogResponse L)
      / (2 * Real.sqrt L * flatPortProfile L)) atTop (𝓝 1) := by
  obtain ⟨L₀, hL₀pos, hcomp⟩ := exists_carlemanDeriv_comparison
  have hfpos : ∀ L, L₀ ≤ L → 0 < ∫ x in Ioi L, flatPortProfile x := by
    intro L hL
    have hLpos : 0 < L := lt_of_lt_of_le hL₀pos hL
    rw [integral_Ioi_flatPortProfile hLpos]
    have := Real.sqrt_nonneg L
    positivity
  have hratio := tendsto_tail_integral_ratio (f := flatPortProfile)
    (g := carlemanLogResponseDeriv) (a := L₀) flatPortProfile_pos
    (fun L hL => integrableOn_flatPortProfile L (lt_of_lt_of_le hL₀pos hL))
    (fun L hL => integrableOn_carlemanLogResponseDeriv_of_le hL₀pos hcomp hL)
    hfpos tendsto_carlemanLogResponseDeriv_div
  have hcorr : Tendsto (fun L : ℝ => (Real.sqrt L + 1) / Real.sqrt L) atTop (𝓝 1) := by
    have hinv : Tendsto (fun L : ℝ => (Real.sqrt L)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    have := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℝ))).add hinv
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
    field_simp
  have hprod := hratio.mul hcorr
  rw [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop L₀, eventually_gt_atTop (0:ℝ)] with L hL hLpos
  have hgap := carlemanLogResponse_gap_eq hL₀pos hcomp hL
  have hFtail := integral_Ioi_flatPortProfile hLpos
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hFpos := flatPortProfile_pos L
  rw [← hgap, hFtail, flatPortProfile]
  field_simp

end

end RHTower
