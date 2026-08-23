import GaloisForLFunctions.RHTower.SoninModelBridge
import GaloisForLFunctions.RHTower.BurnolCoPoissonMellinNonvanishing
import GaloisForLFunctions.RHTower.BurnolCompletenessOmit
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Below aperture one the evaluators are not complete

Burnol's Proposition 6.4, second half.  For `a < 1` the co-Poisson subspace of `L_a` is nonzero,
and every co-Poisson Mellin transform carries the factor `ζ(w)` — so the co-Poisson vectors are
orthogonal to every evaluator attached to a zero of `ζ`, and the system of evaluators is *not*
complete.  Together with Propositions 6.1/6.2 (`a > 1`) this pins the aperture threshold at `a = 1`.

## Main results

* `exists_nonzero_zeta_dvd_of_aperture_lt_one`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem isPreconnected_openStrip : IsPreconnected {w : ℂ | 0 < w.re ∧ w.re < 1} := by
  have hconv : Convex ℝ {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    have h1 : Convex ℝ {w : ℂ | 0 < w.re} := convex_halfSpace_re_gt 0
    have h2 : Convex ℝ {w : ℂ | w.re < 1} := convex_halfSpace_re_lt 1
    exact h1.inter h2
  exact hconv.isPreconnected

/-- **Below aperture one the evaluators miss a nonzero vector.** -/
theorem exists_nonzero_zeta_dvd_of_aperture_lt_one {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ (v : SoninL2) (c d : ℂ), v ≠ 0 ∧ v ∈ evenSubspace ∧
      v ∈ centralSoninExtendedCarrier b ∧
      (∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (v : ℝ → ℂ) t = d) ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation b c d v) ρ := by
  classical
  set V : soninExtendedSpace b := coPoissonIndicatorSoninCosine hb hb1.le with hVdef
  set v : SoninL2 := ((V : evenSubspace) : SoninL2) with hvdef
  have hev : v ∈ evenSubspace := (V : evenSubspace).property
  have hmem : v ∈ centralSoninExtendedCarrier b :=
    mem_centralSoninExtendedCarrier_of_mem_soninExtendedSpace hb V.property
  obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hmem
  obtain ⟨d, hd⟩ := ae_eq_of_mem_extended hmem
  -- the transform on the strip
  have hval := (differentiable_extendedMellinNumerator hb hev hc hd).2
  have hstrip : ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 →
      extendedMellinContinuation b c d v w
        = (((b : ℝ) : ℂ) ^ (-w) - ((b : ℝ) : ℂ) ^ w) * (riemannZeta w / w) := by
    intro w hw1 hw2
    have hw0 : 0 < w.re := by linarith
    have hmcf : mellinCompletionFactor w ≠ 0 := mellinCompletionFactor_ne_zero hw0
    have heval := soninMellinEvaluation_coPoissonIndicatorSoninCosine hb hb1.le hw0 hw2
    rw [soninMellinEvaluation] at heval
    have hint : (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-w) * (v : ℝ → ℂ) t)
        = (((b : ℝ) : ℂ) ^ (-w) - ((b : ℝ) : ℂ) ^ w) * (riemannZeta w / w) := by
      have hswap : (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-w) * (v : ℝ → ℂ) t)
          = ∫ t in Ioi (0 : ℝ), (v : ℝ → ℂ) t * soninMellinKernel w t := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [soninMellinKernel]
        ring
      rw [hswap]
      exact mul_left_cancel₀ hmcf heval
    have hnum := hval w hw1 hw2
    have hw0' : w ≠ 0 := by
      intro h; rw [h] at hw0; simp at hw0
    have hw1' : w ≠ 1 := by
      intro h; rw [h] at hw2; simp at hw2
    have hden : w * (1 - w) ≠ 0 := mul_ne_zero hw0' (sub_ne_zero.2 fun h => hw1' h.symm)
    rw [extendedMellinContinuation, ← hnum, hint]
    field_simp
  -- extend the identity to the whole open strip
  set W : ℂ → ℂ := fun w => (((b : ℝ) : ℂ) ^ (-w) - ((b : ℝ) : ℂ) ^ w) * (riemannZeta w / w)
    with hWdef
  have hbne : ((b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hb)
  have hanaW : AnalyticOnNhd ℂ W {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hw; simp at hw
    have hw1 : w ≠ 1 := by
      intro h; rw [h] at hw; simp at hw
    have hpow1 : AnalyticAt ℂ (fun z : ℂ => ((b : ℝ) : ℂ) ^ (-z)) w := by
      have hrw : (fun z : ℂ => ((b : ℝ) : ℂ) ^ (-z))
          = fun z : ℂ => Complex.exp ((-z) * (Real.log b : ℂ)) := by
        funext z
        rw [Complex.cpow_def_of_ne_zero hbne, ← Complex.ofReal_log hb.le]
        ring_nf
      rw [hrw]
      exact AnalyticAt.cexp (analyticAt_id.neg.mul analyticAt_const)
    have hpow2 : AnalyticAt ℂ (fun z : ℂ => ((b : ℝ) : ℂ) ^ z) w := by
      have hrw : (fun z : ℂ => ((b : ℝ) : ℂ) ^ z)
          = fun z : ℂ => Complex.exp (z * (Real.log b : ℂ)) := by
        funext z
        rw [Complex.cpow_def_of_ne_zero hbne, ← Complex.ofReal_log hb.le]
        ring_nf
      rw [hrw]
      exact AnalyticAt.cexp (analyticAt_id.mul analyticAt_const)
    have hζ : AnalyticAt ℂ riemannZeta w := analyticOn_riemannZeta w (by simpa using hw1)
    exact (hpow1.sub hpow2).mul (hζ.div analyticAt_id hw0)
  have hanaM : AnalyticOnNhd ℂ (extendedMellinContinuation b c d v)
      {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hw; simp at hw
    have hw1 : w ≠ 1 := by
      intro h; rw [h] at hw; simp at hw
    exact analyticAt_extendedMellinContinuation_of_ne hb hev hc hd hw0 hw1
  have hz₀ : ((3 : ℂ) / 4) ∈ {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    refine ⟨?_, ?_⟩ <;> · simp only [Set.mem_setOf_eq, Complex.div_re]; norm_num
  have hopen : IsOpen {w : ℂ | 1 / 2 < w.re ∧ w.re < 1} := by
    refine IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev₀ : extendedMellinContinuation b c d v =ᶠ[𝓝 ((3 : ℂ) / 4)] W := by
    filter_upwards [hopen.mem_nhds (show ((3:ℂ)/4) ∈ {w : ℂ | 1 / 2 < w.re ∧ w.re < 1} by
      refine ⟨?_, ?_⟩ <;> · simp only [Set.mem_setOf_eq, Complex.div_re]; norm_num)] with w hw
    exact hstrip w hw.1 hw.2
  have heqOn := hanaM.eqOn_of_preconnected_of_eventuallyEq hanaW isPreconnected_openStrip hz₀ hev₀
  -- the divisibility
  have hvne : v ≠ 0 := by
    intro hzero
    have hae : ((v : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [hzero]
      exact Lp.coeFn_zero _ _ _
    have hre34 : (((3 : ℝ) : ℂ) / 4).re = 3 / 4 := by
      simp only [Complex.div_re]
      norm_num
    have hζ34 : riemannZeta (((3 : ℝ) : ℂ) / 4) ≠ 0 := by
      have h : ((3 : ℝ) : ℂ) / 4 = (((3 / 4 : ℝ)) : ℂ) := by push_cast; ring
      rw [h]
      exact riemannZeta_real_strip_ne_zero (by norm_num) (by norm_num)
    have hne := (soninMellinEvaluation_coPoissonIndicatorSoninCosine_ne_zero_iff hb hb1
      (w := ((3 : ℝ) : ℂ) / 4) (by rw [hre34]; norm_num) (by rw [hre34]; norm_num)).2 hζ34
    refine hne ?_
    rw [soninMellinEvaluation]
    have hint0 : (∫ t in Ioi (0 : ℝ),
        (((coPoissonIndicatorSoninCosine hb hb1.le : soninExtendedSpace b) : evenSubspace) :
          SoninL2) t * soninMellinKernel (((3 : ℝ) : ℂ) / 4) t) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_of_ae hae] with t ht
      show ((v : SoninL2) : ℝ → ℂ) t * soninMellinKernel (((3 : ℝ) : ℂ) / 4) t = 0
      rw [ht]
      simp
    rw [hint0, mul_zero]
  refine ⟨v, c, d, hvne, hev, hmem, hc, hd, ?_⟩
  · intro ρ hzero h1 h2
    have hρstrip : ρ ∈ {w : ℂ | 0 < w.re ∧ w.re < 1} := ⟨h1, h2⟩
    have hρ0 : ρ ≠ 0 := by
      intro h; rw [h] at h1; simp at h1
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h] at h2; simp at h2
    -- the two functions agree near ρ
    have hnear : extendedMellinContinuation b c d v =ᶠ[𝓝[≠] ρ] W := by
      have hopen2 : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} := by
        refine IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
          (isOpen_lt Complex.continuous_re continuous_const)
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [hopen2.mem_nhds hρstrip] with w hw
      exact heqOn hw
    rw [meromorphicOrderAt_congr hnear]
    -- the order of `W`
    have hpre : AnalyticAt ℂ (fun z : ℂ =>
        ((b : ℝ) : ℂ) ^ (-z) - ((b : ℝ) : ℂ) ^ z) ρ := by
      have hpow1 : AnalyticAt ℂ (fun z : ℂ => ((b : ℝ) : ℂ) ^ (-z)) ρ := by
        have hrw : (fun z : ℂ => ((b : ℝ) : ℂ) ^ (-z))
            = fun z : ℂ => Complex.exp ((-z) * (Real.log b : ℂ)) := by
          funext z
          rw [Complex.cpow_def_of_ne_zero hbne, ← Complex.ofReal_log hb.le]
          ring_nf
        rw [hrw]
        exact AnalyticAt.cexp (analyticAt_id.neg.mul analyticAt_const)
      have hpow2 : AnalyticAt ℂ (fun z : ℂ => ((b : ℝ) : ℂ) ^ z) ρ := by
        have hrw : (fun z : ℂ => ((b : ℝ) : ℂ) ^ z)
            = fun z : ℂ => Complex.exp (z * (Real.log b : ℂ)) := by
          funext z
          rw [Complex.cpow_def_of_ne_zero hbne, ← Complex.ofReal_log hb.le]
          ring_nf
        rw [hrw]
        exact AnalyticAt.cexp (analyticAt_id.mul analyticAt_const)
      exact hpow1.sub hpow2
    have hinvz : AnalyticAt ℂ (fun z : ℂ => z⁻¹) ρ := analyticAt_id.inv hρ0
    have hWfun : W = (fun z : ℂ => (((b : ℝ) : ℂ) ^ (-z) - ((b : ℝ) : ℂ) ^ z) * z⁻¹)
        * riemannZeta := by
      funext z
      rw [hWdef, Pi.mul_apply]
      simp only
      rw [div_eq_mul_inv]
      ring
    rw [hWfun]
    rw [meromorphicOrderAt_mul
      (f := fun z : ℂ => (((b : ℝ) : ℂ) ^ (-z) - ((b : ℝ) : ℂ) ^ z) * z⁻¹)
      (g := riemannZeta) (hpre.mul hinvz).meromorphicAt
      (meromorphicAt_riemannZeta_everywhere ρ)]
    have h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt
        (fun z : ℂ => (((b : ℝ) : ℂ) ^ (-z) - ((b : ℝ) : ℂ) ^ z) * z⁻¹) ρ :=
      meromorphicOrderAt_nonneg_of_analyticAt (hpre.mul hinvz)
    calc meromorphicOrderAt riemannZeta ρ
        = 0 + meromorphicOrderAt riemannZeta ρ := by rw [zero_add]
      _ ≤ _ := by gcongr

end

end RHTower
