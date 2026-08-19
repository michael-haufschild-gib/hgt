import Mathlib

/-!
# Schur's test for a convolution kernel on a set

The second half of Halász–Montgomery's Lemma 2.6 expands the dual coefficients into a double
integral over `E × E` against the smoothed kernel, and bounds it by the kernel's row and column
masses:

```text
   ‖∫_E ∫_E K(t−u)·conj(A t)·A u du dt‖  ≤  M · ∫_E ‖A‖² ,
   M ≥ sup_t ∫_E ‖K(t−u)‖du   and   M ≥ sup_u ∫_E ‖K(t−u)‖dt .
```

Everything happens on the product space, where the integrands are continuous on a compact
rectangle, so the only analytic input is Fubini.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- **The continuous Schur test on a set.** -/
theorem setIntegral_double_kernel_le {E : Set ℝ} {A K : ℝ → ℂ} {M T : ℝ}
    (hA : Continuous A) (hK : Continuous K) (hEs : E ⊆ Set.Icc (-T) T)
    (hEm : MeasurableSet E)
    (hrow : ∀ t ∈ E, (∫ u in E, ‖K (t - u)‖) ≤ M)
    (hcol : ∀ u ∈ E, (∫ t in E, ‖K (t - u)‖) ≤ M) :
    ‖∫ t in E, ∫ u in E, K (t - u) * (starRingEnd ℂ) (A t) * A u‖
      ≤ M * ∫ t in E, ‖A t‖ ^ 2 := by
  classical
  rcases Set.eq_empty_or_nonempty E with hEe | hEne
  · subst hEe
    simp
  have hcpt : IsCompact (Set.Icc (-T) T ×ˢ Set.Icc (-T) T) := isCompact_Icc.prod isCompact_Icc
  have hsub : E ×ˢ E ⊆ Set.Icc (-T) T ×ˢ Set.Icc (-T) T := Set.prod_mono hEs hEs
  have hKp : Continuous fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ :=
    (hK.comp (continuous_fst.sub continuous_snd)).norm
  have hAf : Continuous fun p : ℝ × ℝ => ‖A p.1‖ := (hA.comp continuous_fst).norm
  have hAs : Continuous fun p : ℝ × ℝ => ‖A p.2‖ := (hA.comp continuous_snd).norm
  set μ : Measure (ℝ × ℝ) := (volume.prod volume).restrict (E ×ˢ E) with hμ
  have hprod : (volume.restrict E).prod (volume.restrict E) = μ := Measure.prod_restrict E E
  have hmk : ∀ g : ℝ × ℝ → ℝ, Continuous g → Integrable g μ := by
    intro g hg
    rw [hμ]
    exact (hg.continuousOn.integrableOn_compact hcpt).mono_set hsub
  -- the original integrand as a product integral
  have hcF : Continuous fun p : ℝ × ℝ => K (p.1 - p.2) * (starRingEnd ℂ) (A p.1) * A p.2 :=
    ((hK.comp (continuous_fst.sub continuous_snd)).mul
      (Complex.continuous_conj.comp (hA.comp continuous_fst))).mul (hA.comp continuous_snd)
  have hFint : Integrable
      (Function.uncurry fun t u : ℝ => K (t - u) * (starRingEnd ℂ) (A t) * A u)
      ((volume.restrict E).prod (volume.restrict E)) := by
    rw [hprod, hμ]
    exact (hcF.continuousOn.integrableOn_compact hcpt).mono_set hsub
  rw [MeasureTheory.integral_integral hFint, hprod]
  -- pass to norms and apply the arithmetic–geometric mean inequality
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hnorm : ∀ p : ℝ × ℝ, ‖K (p.1 - p.2) * (starRingEnd ℂ) (A p.1) * A p.2‖
      = ‖K (p.1 - p.2)‖ * (‖A p.1‖ * ‖A p.2‖) := by
    intro p
    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hnorm)]
  have hamgm : (fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ * (‖A p.1‖ * ‖A p.2‖))
      ≤ fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ * ‖A p.1‖ ^ 2 / 2
        + ‖K (p.1 - p.2)‖ * ‖A p.2‖ ^ 2 / 2 := by
    intro p
    have hk : (0 : ℝ) ≤ ‖K (p.1 - p.2)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖A p.1‖ - ‖A p.2‖), hk]
  have hi₁ : Integrable (fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ * (‖A p.1‖ * ‖A p.2‖)) μ :=
    hmk _ (hKp.mul (hAf.mul hAs))
  have hi₂ : Integrable (fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ * ‖A p.1‖ ^ 2 / 2
      + ‖K (p.1 - p.2)‖ * ‖A p.2‖ ^ 2 / 2) μ :=
    hmk _ (((hKp.mul (hAf.pow 2)).div_const 2).add ((hKp.mul (hAs.pow 2)).div_const 2))
  refine le_trans (MeasureTheory.integral_mono hi₁ hi₂ hamgm) ?_
  -- split the two halves
  have hiL : Integrable (fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ * ‖A p.1‖ ^ 2 / 2) μ :=
    hmk _ ((hKp.mul (hAf.pow 2)).div_const 2)
  have hiR : Integrable (fun p : ℝ × ℝ => ‖K (p.1 - p.2)‖ * ‖A p.2‖ ^ 2 / 2) μ :=
    hmk _ ((hKp.mul (hAs.pow 2)).div_const 2)
  rw [MeasureTheory.integral_add hiL hiR]
  -- the first half: integrate `u` first
  have hAsq : IntegrableOn (fun t : ℝ => ‖A t‖ ^ 2) E :=
    (((hA.norm).pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set hEs
  have hAsq0 : ∀ t : ℝ, (0 : ℝ) ≤ ‖A t‖ ^ 2 := fun t => sq_nonneg _
  obtain ⟨t₀, ht₀⟩ : E.Nonempty := hEne
  have hM0 : (0 : ℝ) ≤ M :=
    le_trans (MeasureTheory.setIntegral_nonneg hEm fun u _ => norm_nonneg _) (hrow t₀ ht₀)
  -- the first half: the row mass
  have hfirst : (∫ p, ‖K (p.1 - p.2)‖ * ‖A p.1‖ ^ 2 / 2 ∂μ)
      ≤ M / 2 * ∫ t in E, ‖A t‖ ^ 2 := by
    have hiL' : Integrable
        (Function.uncurry fun t u : ℝ => ‖K (t - u)‖ * ‖A t‖ ^ 2 / 2)
        ((volume.restrict E).prod (volume.restrict E)) := by rw [hprod]; exact hiL
    have hswap : (∫ p, ‖K (p.1 - p.2)‖ * ‖A p.1‖ ^ 2 / 2 ∂μ)
        = ∫ t in E, ∫ u in E, ‖K (t - u)‖ * ‖A t‖ ^ 2 / 2 := by
      rw [← hprod]
      exact (MeasureTheory.integral_integral hiL').symm
    rw [hswap]
    have hinner : ∀ t : ℝ, (∫ u in E, ‖K (t - u)‖ * ‖A t‖ ^ 2 / 2)
        = (∫ u in E, ‖K (t - u)‖) * (‖A t‖ ^ 2 / 2) := by
      intro t
      rw [← MeasureTheory.integral_mul_const]
      congr 1
      funext u
      ring
    rw [MeasureTheory.setIntegral_congr_fun hEm fun t _ => hinner t]
    have hintF : IntegrableOn (fun t : ℝ => (∫ u in E, ‖K (t - u)‖) * (‖A t‖ ^ 2 / 2)) E := by
      have := hiL'.integral_prod_left
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      exact hinner t
    have hintG : IntegrableOn (fun t : ℝ => M * (‖A t‖ ^ 2 / 2)) E := by
      have := hAsq.const_mul (M / 2)
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      ring
    have hmono := MeasureTheory.setIntegral_mono_on hintF hintG hEm fun t ht => by
      have h1 : (0 : ℝ) ≤ ‖A t‖ ^ 2 / 2 := by positivity
      exact mul_le_mul_of_nonneg_right (hrow t ht) h1
    refine hmono.trans (le_of_eq ?_)
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext t
    ring
  -- the second half: the column mass, after Fubini
  have hsecond : (∫ p, ‖K (p.1 - p.2)‖ * ‖A p.2‖ ^ 2 / 2 ∂μ)
      ≤ M / 2 * ∫ t in E, ‖A t‖ ^ 2 := by
    have hiR' : Integrable
        (Function.uncurry fun t u : ℝ => ‖K (t - u)‖ * ‖A u‖ ^ 2 / 2)
        ((volume.restrict E).prod (volume.restrict E)) := by rw [hprod]; exact hiR
    have hswap : (∫ p, ‖K (p.1 - p.2)‖ * ‖A p.2‖ ^ 2 / 2 ∂μ)
        = ∫ u in E, ∫ t in E, ‖K (t - u)‖ * ‖A u‖ ^ 2 / 2 := by
      rw [← hprod]
      rw [← MeasureTheory.integral_integral hiR']
      exact MeasureTheory.integral_integral_swap hiR'
    rw [hswap]
    have hinner : ∀ u : ℝ, (∫ t in E, ‖K (t - u)‖ * ‖A u‖ ^ 2 / 2)
        = (∫ t in E, ‖K (t - u)‖) * (‖A u‖ ^ 2 / 2) := by
      intro u
      rw [← MeasureTheory.integral_mul_const]
      congr 1
      funext t
      ring
    rw [MeasureTheory.setIntegral_congr_fun hEm fun u _ => hinner u]
    have hswapInt : Integrable
        (Function.uncurry fun u t : ℝ => ‖K (t - u)‖ * ‖A u‖ ^ 2 / 2)
        ((volume.restrict E).prod (volume.restrict E)) := by
      rw [hprod, hμ]
      exact ((((hK.comp (continuous_snd.sub continuous_fst)).norm).mul
        ((hA.comp continuous_fst).norm.pow 2)).div_const 2).continuousOn.integrableOn_compact
          hcpt |>.mono_set hsub
    have hintF : IntegrableOn (fun u : ℝ => (∫ t in E, ‖K (t - u)‖) * (‖A u‖ ^ 2 / 2)) E := by
      have := hswapInt.integral_prod_left
      refine this.congr (Filter.Eventually.of_forall fun u => ?_)
      exact hinner u
    have hintG : IntegrableOn (fun u : ℝ => M * (‖A u‖ ^ 2 / 2)) E := by
      have := hAsq.const_mul (M / 2)
      refine this.congr (Filter.Eventually.of_forall fun u => ?_)
      ring
    have hmono := MeasureTheory.setIntegral_mono_on hintF hintG hEm fun u hu => by
      have h1 : (0 : ℝ) ≤ ‖A u‖ ^ 2 / 2 := by positivity
      exact mul_le_mul_of_nonneg_right (hcol u hu) h1
    refine hmono.trans (le_of_eq ?_)
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext u
    ring
  linarith [hfirst, hsecond]

/-! ## From a two-regime pointwise kernel bound to its mass over a set -/

/-- **The row mass of a kernel with a near-diagonal and a far bound.**  The near-diagonal band has
length two whatever `E` is, so the trivial size is paid only twice; away from the diagonal the
oscillation bound is paid once per unit of `|E|`. -/
theorem setIntegral_norm_kernel_le {E : Set ℝ} {K : ℝ → ℂ} {N C T t : ℝ}
    (hK : Continuous K) (hEs : E ⊆ Set.Icc (-T) T) (hEm : MeasurableSet E)
    (hnear : ∀ v : ℝ, ‖K v‖ ≤ N) (hfar : ∀ u ∈ E, 1 ≤ |t - u| → ‖K (t - u)‖ ≤ C)
    (hC : 0 ≤ C) :
    (∫ u in E, ‖K (t - u)‖) ≤ 2 * N + C * (volume.real E) := by
  classical
  have hN0 : (0 : ℝ) ≤ N := le_trans (norm_nonneg _) (hnear 0)
  set B : Set ℝ := Set.Ioo (t - 1) (t + 1) with hB
  have hBm : MeasurableSet B := measurableSet_Ioo
  have hcK : Continuous fun u : ℝ => ‖K (t - u)‖ :=
    (hK.comp (continuous_const.sub continuous_id)).norm
  have hint : IntegrableOn (fun u : ℝ => ‖K (t - u)‖) E :=
    (hcK.continuousOn.integrableOn_compact isCompact_Icc).mono_set hEs
  have hEfin : volume E ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hEs) measure_Icc_lt_top)
  have hsplit : (∫ u in E ∩ B, ‖K (t - u)‖) + (∫ u in E \ B, ‖K (t - u)‖)
      = ∫ u in E, ‖K (t - u)‖ := MeasureTheory.integral_inter_add_sdiff hBm hint
  -- the near-diagonal band
  have hnearInt : (∫ u in E ∩ B, ‖K (t - u)‖) ≤ 2 * N := by
    have hle : ∀ u ∈ E ∩ B, ‖K (t - u)‖ ≤ N := fun u _ => hnear _
    have hmeas : MeasurableSet (E ∩ B) := hEm.inter hBm
    have hfin : volume (E ∩ B) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
        (lt_top_iff_ne_top.2 hEfin))
    have hconst : IntegrableOn (fun _ : ℝ => N) (E ∩ B) := integrableOn_const hfin (by finiteness)
    have hmono := MeasureTheory.setIntegral_mono_on
      (hint.mono_set Set.inter_subset_left) hconst hmeas hle
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hmono
    refine hmono.trans ?_
    have hBvol : volume B = ENNReal.ofReal 2 := by
      rw [hB, Real.volume_Ioo]
      congr 1
      ring
    have hvol : volume.real (E ∩ B) ≤ 2 := by
      have h1 : volume (E ∩ B) ≤ volume B := measure_mono Set.inter_subset_right
      have h3 := ENNReal.toReal_mono (by rw [hBvol]; exact ENNReal.ofReal_ne_top) h1
      rw [hBvol, ENNReal.toReal_ofReal (by norm_num)] at h3
      exact h3
    nlinarith [hvol, hN0]
  -- the far part
  have hfarInt : (∫ u in E \ B, ‖K (t - u)‖) ≤ C * (volume.real E) := by
    have hle : ∀ u ∈ E \ B, ‖K (t - u)‖ ≤ C := by
      intro u hu
      refine hfar u hu.1 ?_
      have hnb : u ∉ Set.Ioo (t - 1) (t + 1) := hu.2
      rw [Set.mem_Ioo] at hnb
      rcases le_or_gt u (t - 1) with hcase | hcase
      · rw [abs_of_nonneg (by linarith)]; linarith
      · have : t + 1 ≤ u := by
          by_contra hcon
          exact hnb ⟨hcase, by linarith [not_le.1 hcon]⟩
        rw [abs_of_nonpos (by linarith)]; linarith
    have hmeas : MeasurableSet (E \ B) := hEm.diff hBm
    have hfin : volume (E \ B) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono Set.sdiff_subset) (lt_top_iff_ne_top.2 hEfin))
    have hconst : IntegrableOn (fun _ : ℝ => C) (E \ B) := integrableOn_const hfin (by finiteness)
    have hmono := MeasureTheory.setIntegral_mono_on
      (hint.mono_set Set.sdiff_subset) hconst hmeas hle
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hmono
    refine hmono.trans ?_
    have hvol : volume.real (E \ B) ≤ volume.real E :=
      ENNReal.toReal_mono hEfin (measure_mono Set.sdiff_subset)
    nlinarith [hvol, hC]
  linarith [hsplit, hnearInt, hfarInt]

end RHTower.Sieve
