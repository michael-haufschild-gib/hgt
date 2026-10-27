import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalRegularField

/-!+# The arithmetic source field at every Xi zero

The simple Laurent coefficient of `(ζ′/ζ)²`, divided by twice the zero's
multiplicity and completed by the archimedean logarithmic derivative, equals
the absolutely convergent transverse field. Zero isolation suffices for the
local passage; no extremality or simplicity of the zero is required.

On a finite set of multiplicity copies, the work of this arithmetic source is
the transverse pair energy plus the signed interaction with the exterior.
Both terms are retained, so this identity makes no assertion about the sign
of the full source work.
-/

open Finset Filter Set RHTower
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The completed regular part at any Xi zero equals its transverse field. -/
theorem xiTransverseField_eq_regular_part (p : XiZeroCopy)
    {B : ℂ → ℂ} (hB : AnalyticAt ℂ B (p.1 : ℂ))
    (hprincipal : logDeriv riemannZeta =ᶠ[𝓝[≠] (p.1 : ℂ)]
      (fun z => ((xiZeroCopyFiber p.1).card : ℂ) / (z - (p.1 : ℂ)) + B z)) :
    xiTransverseField p = (B (p.1 : ℂ)).re + (logDeriv archFactor (p.1 : ℂ)).re := by
  let ρ : ℂ := (p.1 : ℂ)
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := xi_divisor_support_re_mem_open_unit p.1
  have harch : AnalyticAt ℂ (logDeriv archFactor) ρ := by
    have hA := archFactor_analyticOnNhd_re_pos ρ hstrip.1
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
    have hzero : (h : ℂ) = 0 := add_left_cancel (heq.trans (add_zero ρ).symm)
    have : h = 0 := by exact_mod_cast hzero
    linarith only [hh, this]
  have hisolated : ∀ᶠ z in 𝓝[≠] ρ, xi z ≠ 0 := by
    rcases (xi_differentiable.analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · have hA : AnalyticOnNhd ℂ xi univ := fun z _ => xi_differentiable.analyticAt z
      have hzero := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ ρ) h
      exact False.elim (xi_ne_zero_of_one_le_re (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re)
        (hzero (mem_univ 2)))
    · exact h
  have hleft : Tendsto (fun h : ℝ => ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q)
      (𝓝[>] (0 : ℝ)) (𝓝 (xiTransverseField p)) := by
    rw [xiTransverseField_eq_reciprocal_tsum]
    exact xiRealAwayReciprocal_tsum_tendsto p
  have hright : Tendsto (fun h : ℝ => (B (ρ + (h : ℂ))).re +
      (logDeriv archFactor (ρ + (h : ℂ))).re) (𝓝[>] (0 : ℝ))
      (𝓝 ((B ρ).re + (logDeriv archFactor ρ).re)) :=
    ((Complex.continuous_re.tendsto _).comp (hB.continuousAt.tendsto.comp hpath)).add
      ((Complex.continuous_re.tendsto _).comp (harch.continuousAt.tendsto.comp hpath))
  have heq : (fun h : ℝ => ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun h : ℝ => (B (ρ + (h : ℂ))).re +
        (logDeriv archFactor (ρ + (h : ℂ))).re) := by
    have hltGap : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 - ρ.re :=
      nhdsWithin_le_nhds (eventually_lt_nhds (sub_pos.mpr hstrip.2))
    have hltOne : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 :=
      nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hprincipal.comp_tendsto hpathPunctured,
      hpathPunctured.eventually hisolated, self_mem_nhdsWithin, hltGap, hltOne]
      with h hprincipal' hxi hh hgap hone
    change 0 < h at hh
    have habs : |h| ≤ 1 := by rw [abs_of_pos hh]; exact hone.le
    let s : ℂ := ρ + (h : ℂ)
    have hsre : s.re = ρ.re + h := by simp only [s, Complex.add_re, Complex.ofReal_re]
    have hs0 : 0 < s.re := by rw [hsre]; linarith only [hstrip.1, hh]
    have hs1 : s.re < 1 := by rw [hsre]; linarith only [hgap]
    have hsone : s ≠ 1 := by intro he; rw [he] at hs1; norm_num at hs1
    have hzeta : riemannZeta s ≠ 0 := fun hz => hxi ((xi_eq_zero_iff hs0 hsone).mpr hz)
    have hsplit := re_logDeriv_xi_sub_fiber_eq_away_tsum p habs hxi
    have hcompletion := (logDeriv_xi_eq_archFactor_add_of_strip hs0 hs1 hzeta).2
    have hprincipal'' : logDeriv riemannZeta s =
        ((xiZeroCopyFiber p.1).card : ℂ) / (h : ℂ) + B s := by
      change logDeriv riemannZeta (ρ + (h : ℂ)) =
        ((xiZeroCopyFiber p.1).card : ℂ) / ((ρ + (h : ℂ)) - ρ) + B (ρ + (h : ℂ))
        at hprincipal'
      simpa only [s, add_sub_cancel_left] using hprincipal'
    have hprincipalRe : (logDeriv riemannZeta s).re =
        ((xiZeroCopyFiber p.1).card : ℝ) / h + (B s).re := by
      rw [hprincipal'']
      simp only [Complex.add_re, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]
    have hcompletionRe : (logDeriv xi s).re =
        (logDeriv archFactor s).re + (logDeriv riemannZeta s).re := by
      rw [hcompletion, Complex.add_re]
    change (logDeriv xi s).re - ((xiZeroCopyFiber p.1).card : ℝ) / h = _ at hsplit
    linarith only [hsplit, hcompletionRe, hprincipalRe]
  exact tendsto_nhds_unique hleft (Filter.Tendsto.congr' heq.symm hright)

/-- The Laurent residue of the actual arithmetic square, completed at infinity. -/
def xiSourceField (p : XiZeroCopy) : ℝ :=
  (GaloisForLFunctions.HTGeometry.laurentCoeff
    (fun z => logDeriv riemannZeta z ^ 2) (p.1 : ℂ) (-1) /
      (2 * ((xiZeroCopyFiber p.1).card : ℂ))).re +
    (logDeriv archFactor (p.1 : ℂ)).re

/-- At every Xi zero, the arithmetic square computes the full transverse field,
including all other multiplicity copies. -/
theorem xiSourceField_eq_transverseField (p : XiZeroCopy) :
    xiSourceField p = xiTransverseField p := by
  obtain ⟨B, hB, hprincipal, hres⟩ := xiZero_exists_zeta_regular_part p
  have hm : (xiZeroCopyFiber p.1).card ≠ 0 :=
    Nat.ne_of_gt (Finset.card_pos.mpr ⟨p, mem_xiZeroCopyFiber.mpr rfl⟩)
  have hmC : ((xiZeroCopyFiber p.1).card : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [xiSourceField, hres, xiTransverseField_eq_regular_part p hB hprincipal]
  congr 2
  field_simp

/-- The transverse reciprocal kernel, with zero contribution on a multiplicity fibre. -/
def xiTransverseKernel (p q : XiZeroCopy) : ℝ :=
  ((p.1 : ℂ).re - (q.1 : ℂ).re) / ‖(p.1 : ℂ) - (q.1 : ℂ)‖ ^ 2

theorem xiTransverseKernel_swap (p q : XiZeroCopy) :
    xiTransverseKernel q p = -xiTransverseKernel p q := by
  rw [xiTransverseKernel, xiTransverseKernel, norm_sub_rev]
  ring

/-- The arithmetic source splits into an interior row and an absolutely
convergent exterior row for every finite set of zero copies. -/
theorem xiSourceField_eq_interior_add_exterior (S : Finset XiZeroCopy) (p : XiZeroCopy) :
    xiSourceField p = ∑ q ∈ S, xiTransverseKernel p q +
      ∑' q : {q : XiZeroCopy // q ∉ S}, xiTransverseKernel p q.1 := by
  rw [xiSourceField_eq_transverseField]
  exact ((xiTransverseField_norm_summable p).of_norm.sum_add_tsum_subtype_compl S).symm

/-- The source work is finite transverse energy plus the signed exterior work.
Summation over copies supplies the actual multiplicities without simplicity assumptions. -/
theorem xiSourceField_finite_work (S : Finset XiZeroCopy) :
    ∑ p ∈ S, ((p.1 : ℂ).re - 1 / 2) * xiSourceField p =
      (∑ p ∈ S, ∑ q ∈ S,
        ((p.1 : ℂ).re - (q.1 : ℂ).re) ^ 2 / ‖(p.1 : ℂ) - (q.1 : ℂ)‖ ^ 2) / 2 +
      ∑ p ∈ S, ((p.1 : ℂ).re - 1 / 2) *
        ∑' q : {q : XiZeroCopy // q ∉ S}, xiTransverseKernel p q.1 := by
  simp_rw [xiSourceField_eq_interior_add_exterior S, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  congr 1
  let F : XiZeroCopy → XiZeroCopy → ℝ := fun p q =>
    ((p.1 : ℂ).re - 1 / 2) * xiTransverseKernel p q
  have hswap : (∑ p ∈ S, ∑ q ∈ S, F p q) = ∑ p ∈ S, ∑ q ∈ S, F q p :=
    Finset.sum_comm
  have htwice : 2 * (∑ p ∈ S, ∑ q ∈ S, F p q) =
      ∑ p ∈ S, ∑ q ∈ S, (F p q + F q p) := by
    simp_rw [Finset.sum_add_distrib]
    rw [← hswap, two_mul]
  have hpair : ∀ p q, F p q + F q p =
      ((p.1 : ℂ).re - (q.1 : ℂ).re) ^ 2 / ‖(p.1 : ℂ) - (q.1 : ℂ)‖ ^ 2 := by
    intro p q
    dsimp only [F]
    rw [xiTransverseKernel_swap p q]
    unfold xiTransverseKernel
    ring
  simp_rw [hpair] at htwice
  change (∑ p ∈ S, ∑ q ∈ S, F p q) = _
  linarith only [htwice]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.xiSourceField_eq_transverseField
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.xiSourceField_finite_work
