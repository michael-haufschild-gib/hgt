import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiRealReciprocalField
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.EveryRightZeroReachesAnOutwardZetaRay
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheSquareSeesTheRegularLogDerivative
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge

/-!
# The regular field at a quadratic terminal

The deflated reciprocal sum extends to the zero. Its value is the transverse
field of the other Xi zeros and is bounded below by the reflected terminal
fibre and a logarithmic reserve.
-/

open Finset Filter Set RHTower
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The real transverse field of the Xi divisor at a zero copy. The
totalized terms on its own fibre are zero. -/
def xiTransverseField (p : XiZeroCopy) : ℝ :=
  ∑' q : XiZeroCopy, ((p.1 : ℂ).re - (q.1 : ℂ).re) /
    ‖(p.1 : ℂ) - (q.1 : ℂ)‖ ^ 2

/-- The transverse field is the sum of real reciprocal terms. -/
theorem xiTransverseField_eq_reciprocal_tsum (p : XiZeroCopy) :
    xiTransverseField p = ∑' q : XiZeroCopy, xiRealReciprocal (p.1 : ℂ) 0 q := by
  unfold xiTransverseField
  exact tsum_congr (fun q => (xiRealReciprocal_zero_eq p q).symm)

/-- The transverse field converges absolutely. -/
theorem xiTransverseField_norm_summable (p : XiZeroCopy) :
    Summable (fun q : XiZeroCopy =>
      ‖((p.1 : ℂ).re - (q.1 : ℂ).re) / ‖(p.1 : ℂ) - (q.1 : ℂ)‖ ^ 2‖) := by
  have hsum := xiRealReciprocal_norm_summable (p.1 : ℂ) (h := 0) (by norm_num)
  refine hsum.congr ?_
  intro q
  rw [xiRealReciprocal_zero_eq]

/-- Only copies outside the terminal fibre contribute to the transverse field. -/
theorem xiTransverseField_eq_tsum_otherCopies (p : XiZeroCopy) :
    xiTransverseField p = ∑' q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber p.1},
      ((p.1 : ℂ).re - ((q.1 : XiZeroCopy).1 : ℂ).re) /
        ‖(p.1 : ℂ) - ((q.1 : XiZeroCopy).1 : ℂ)‖ ^ 2 := by
  classical
  let A : Finset XiZeroCopy := xiZeroCopyFiber p.1
  have hsum := xiRealAwayReciprocal_summable p (h := 0) (by norm_num)
  have hzero : (∑ q ∈ A, xiRealAwayReciprocal p 0 q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hq' : q ∈ xiZeroCopyFiber p.1 := by simpa only [A] using hq
    simp only [xiRealAwayReciprocal, if_pos hq']
  have hsplit := hsum.sum_add_tsum_subtype_compl A
  rw [hzero, zero_add] at hsplit
  calc
    xiTransverseField p = ∑' q : XiZeroCopy, xiRealAwayReciprocal p 0 q := by
      rw [xiTransverseField_eq_reciprocal_tsum]
      exact tsum_congr (fun q => (xiRealAwayReciprocal_zero p q).symm)
    _ = ∑' q : {q : XiZeroCopy // q ∉ A}, xiRealAwayReciprocal p 0 q.1 := hsplit.symm
    _ = _ := by
      apply tsum_congr
      intro q
      have hq : q.1 ∉ xiZeroCopyFiber p.1 := by simpa only [A] using q.2
      simp only [xiRealAwayReciprocal, if_neg hq, xiRealReciprocal_zero_eq]

/-- The reflected fibre and a logarithmic band force a positive transverse
field at every right-hand quadratic terminal. The same constant works on
the terminal's outward ray. -/
theorem exists_xiTerminal_transverseField_and_ray_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re →
      (∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
        xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2) →
      (((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p) +
          c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤ xiTransverseField p) ∧
      ∀ h : ℝ, 0 < h → h < 1 / 2 - xiZeroDepth p →
        ((xiZeroCopyFiber p.1).card : ℝ) / h +
          ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
          c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤
            (logDeriv xi ((p.1 : ℂ) + (h : ℂ))).re := by
  obtain ⟨c, hc, hray⟩ := exists_xiTerminal_logDeriv_lower
  refine ⟨c, hc, ?_⟩
  intro p hp hcone
  refine ⟨?_, hray p hp hcone⟩
  have hdepth : xiZeroDepth p = (p.1 : ℂ).re - 1 / 2 := by
    rw [xiZeroDepth, abs_of_pos (sub_pos.mpr hp)]
  have ha : 0 < xiZeroDepth p := by rw [hdepth]; linarith
  have hgap : 0 < 1 / 2 - xiZeroDepth p := by
    have hs := (xi_divisor_support_re_mem_open_unit p.1).2
    rw [hdepth]
    linarith
  have hden : (2 * xiZeroDepth p + 0 : ℝ) ≠ 0 := by positivity
  have hleftContinuous : ContinuousAt
      (fun h : ℝ => ((xiZeroCopyFiber p.1).card : ℝ) /
        (2 * xiZeroDepth p + h) + c * xiZeroDepth p *
          Real.log (|xiZeroHeight p| + 4)) 0 := by
    have hdenContinuous : ContinuousAt (fun h : ℝ => 2 * xiZeroDepth p + h) 0 := by
      fun_prop
    exact (continuousAt_const.div hdenContinuous hden).add continuousAt_const
  have hleft : Tendsto
      (fun h : ℝ => ((xiZeroCopyFiber p.1).card : ℝ) /
        (2 * xiZeroDepth p + h) + c * xiZeroDepth p *
          Real.log (|xiZeroHeight p| + 4))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p) +
        c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4))) := by
    simpa only [add_zero] using hleftContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun h : ℝ => ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q)
      (𝓝[>] (0 : ℝ)) (𝓝 (xiTransverseField p)) := by
    rw [xiTransverseField_eq_reciprocal_tsum]
    exact xiRealAwayReciprocal_tsum_tendsto p
  have heventually : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
        c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤
          ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q := by
    have hltGap : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 / 2 - xiZeroDepth p :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hgap)
    have hltOne : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hltGap, hltOne] with h hh hgap' hone
    change 0 < h at hh
    have habs : |h| ≤ 1 := by rw [abs_of_pos hh]; exact le_of_lt hone
    have hxi := xi_ne_zero_on_terminal_ray p hp hcone hh
    have hsplit := re_logDeriv_xi_sub_fiber_eq_away_tsum p habs hxi
    have hbound := hray p hp hcone h hh hgap'
    linarith only [hsplit, hbound]
  exact le_of_tendsto_of_tendsto hleft hright heventually

/-- At a Xi zero, the zeta logarithmic derivative has an analytic regular
part after subtracting its full multiplicity pole. The simple coefficient
of its square is twice the multiplicity times that regular part. -/
theorem xiZero_exists_zeta_regular_part (p : XiZeroCopy) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B (p.1 : ℂ) ∧
      logDeriv riemannZeta =ᶠ[𝓝[≠] (p.1 : ℂ)]
        (fun z => ((xiZeroCopyFiber p.1).card : ℂ) / (z - (p.1 : ℂ)) + B z) ∧
      GaloisForLFunctions.HTGeometry.laurentCoeff
        (fun z => (logDeriv riemannZeta z) ^ 2) (p.1 : ℂ) (-1) =
          2 * ((xiZeroCopyFiber p.1).card : ℂ) * B (p.1 : ℂ) := by
  let ρ : ℂ := (p.1 : ℂ)
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := xi_divisor_support_re_mem_open_unit p.1
  obtain ⟨R, hR, f, hf, hfne, hlocal⟩ :=
    exists_riemannZeta_normalizedLogDeriv_factorization_of_mem_strip hstrip
  have hball : ρ ∈ Metric.ball ρ R := Metric.mem_ball_self hR
  have hB : AnalyticAt ℂ (logDeriv f) ρ := by
    rw [show logDeriv f = (fun z => deriv f z / f z) by
      funext z
      rw [logDeriv_apply]]
    exact (hf ρ hball).deriv.div (hf ρ hball) (hfne ρ hball)
  have hprincipal : logDeriv riemannZeta =ᶠ[𝓝[≠] ρ]
      (fun z => ((xiZeroCopyFiber p.1).card : ℂ) / (z - ρ) + logDeriv f z) := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds ρ hR), self_mem_nhdsWithin]
      with z hz hzne
    change z ≠ ρ at hzne
    have hfact := hlocal z hz hzne
    rw [← card_xiZeroCopyFiber_eq_order_toNat p.1] at hfact
    have hsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
    field_simp [hsub]
    linear_combination hfact
  have hne : ρ ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.one_re] at hre
    linarith [hstrip.2]
  have hzeta : AnalyticAt ℂ riemannZeta ρ :=
    analyticOn_riemannZeta ρ (by simpa using hne)
  have hmer : MeromorphicAt (logDeriv riemannZeta) ρ := by
    rw [show logDeriv riemannZeta = (fun z => deriv riemannZeta z / riemannZeta z) by
      funext z
      rw [logDeriv_apply]]
    exact hzeta.deriv.meromorphicAt.div hzeta.meromorphicAt
  refine ⟨logDeriv f, hB, hprincipal, ?_⟩
  exact laurentCoeff_square_of_pole_and_regular hmer hB hprincipal

/-- At a right-hand terminal, the transverse field equals the real part of
the regular zeta logarithmic derivative plus the archimedean correction. -/
theorem xiTransverseField_eq_zeta_regular_part (p : XiZeroCopy)
    (hp : 1 / 2 < (p.1 : ℂ).re)
    (hcone : ∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
      xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2)
    {B : ℂ → ℂ} (hB : AnalyticAt ℂ B (p.1 : ℂ))
    (hprincipal : logDeriv riemannZeta =ᶠ[𝓝[≠] (p.1 : ℂ)]
      (fun z => ((xiZeroCopyFiber p.1).card : ℂ) / (z - (p.1 : ℂ)) + B z)) :
    xiTransverseField p = (B (p.1 : ℂ)).re + (logDeriv archFactor (p.1 : ℂ)).re := by
  let ρ : ℂ := (p.1 : ℂ)
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := xi_divisor_support_re_mem_open_unit p.1
  have hdepth : xiZeroDepth p = ρ.re - 1 / 2 := by
    rw [xiZeroDepth, abs_of_pos (sub_pos.mpr hp)]
  have hgap : 0 < 1 / 2 - xiZeroDepth p := by rw [hdepth]; linarith [hstrip.2]
  have harch : AnalyticAt ℂ (logDeriv archFactor) ρ := by
    have hA : AnalyticAt ℂ archFactor ρ := archFactor_analyticOnNhd_re_pos ρ hstrip.1
    rw [show logDeriv archFactor = (fun z => deriv archFactor z / archFactor z) by
      funext z
      rw [logDeriv_apply]]
    exact hA.deriv.div hA (archFactor_ne_zero_strip hstrip)
  have hpathContinuous : ContinuousAt (fun h : ℝ => ρ + (h : ℂ)) 0 := by fun_prop
  have hpath : Tendsto (fun h : ℝ => ρ + (h : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      hpathContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hpathPunctured : Tendsto (fun h : ℝ => ρ + (h : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hpath, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    change ρ + (h : ℂ) ≠ ρ
    intro heq
    have heq' : ρ + (h : ℂ) = ρ + 0 := by simpa only [add_zero] using heq
    have hzero : (h : ℂ) = 0 := add_left_cancel heq'
    have : h = 0 := by exact_mod_cast hzero
    linarith
  have hleft : Tendsto (fun h : ℝ => ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q)
      (𝓝[>] (0 : ℝ)) (𝓝 (xiTransverseField p)) := by
    rw [xiTransverseField_eq_reciprocal_tsum]
    exact xiRealAwayReciprocal_tsum_tendsto p
  have hBlim := hB.continuousAt.tendsto.comp hpath
  have hAlim := harch.continuousAt.tendsto.comp hpath
  have hright : Tendsto (fun h : ℝ => (B (ρ + (h : ℂ))).re +
      (logDeriv archFactor (ρ + (h : ℂ))).re) (𝓝[>] (0 : ℝ))
      (𝓝 ((B ρ).re + (logDeriv archFactor ρ).re)) :=
    ((Complex.continuous_re.tendsto _).comp hBlim).add
      ((Complex.continuous_re.tendsto _).comp hAlim)
  have heq : (fun h : ℝ => ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun h : ℝ => (B (ρ + (h : ℂ))).re +
        (logDeriv archFactor (ρ + (h : ℂ))).re) := by
    have heqPrincipal := hprincipal.comp_tendsto hpathPunctured
    have hltGap : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 / 2 - xiZeroDepth p :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hgap)
    have hltOne : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [heqPrincipal, self_mem_nhdsWithin, hltGap, hltOne]
      with h hprincipal' hh hgap' hone
    change 0 < h at hh
    have habs : |h| ≤ 1 := by rw [abs_of_pos hh]; exact le_of_lt hone
    let s : ℂ := ρ + (h : ℂ)
    have hsre : s.re = ρ.re + h := by dsimp only [s]; simp
    have hs0 : 0 < s.re := by rw [hsre]; linarith only [hp, hh]
    have hs1 : s.re < 1 := by rw [hsre]; rw [hdepth] at hgap'; linarith only [hgap']
    have hsone : s ≠ 1 := by intro heq; rw [heq] at hs1; norm_num at hs1
    have hxi : xi s ≠ 0 := xi_ne_zero_on_terminal_ray p hp hcone hh
    have hzeta : riemannZeta s ≠ 0 := by
      intro hz
      exact hxi ((xi_eq_zero_iff hs0 hsone).mpr hz)
    have hsplit := re_logDeriv_xi_sub_fiber_eq_away_tsum p habs hxi
    have hcompletion := (logDeriv_xi_eq_archFactor_add_of_strip hs0 hs1 hzeta).2
    have hprincipal'' : logDeriv riemannZeta s =
        ((xiZeroCopyFiber p.1).card : ℂ) / (h : ℂ) + B s := by
      change logDeriv riemannZeta (ρ + (h : ℂ)) =
        ((xiZeroCopyFiber p.1).card : ℂ) / ((ρ + (h : ℂ)) - ρ) +
          B (ρ + (h : ℂ)) at hprincipal'
      simpa only [s, add_sub_cancel_left] using hprincipal'
    have hprincipalRe : (logDeriv riemannZeta s).re =
        ((xiZeroCopyFiber p.1).card : ℝ) / h + (B s).re := by
      rw [hprincipal'']
      simp only [Complex.add_re, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]
    have hcompletionRe : (logDeriv xi s).re =
        (logDeriv archFactor s).re + (logDeriv riemannZeta s).re := by
      rw [hcompletion]
      simp only [Complex.add_re]
    change (logDeriv xi s).re - ((xiZeroCopyFiber p.1).card : ℝ) / h = _ at hsplit
    linarith only [hsplit, hcompletionRe, hprincipalRe]
  exact tendsto_nhds_unique hleft (Filter.Tendsto.congr' heq.symm hright)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
