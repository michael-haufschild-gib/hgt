import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# High zero-free regions bound the logarithmic-derivative jets

Suppose each nontrivial zero has real part at most `β` or ordinate of absolute value at most `H`.
A high disc with left edge at least `β + δ` is at distance at least `δ` from every zero.
The logarithmic-derivative bound away from zeros and Cauchy's estimate give
`‖(ζ'/ζ)⁽ᵏ⁾(σ+it)‖ ≤ k! C log(t+r)/(δ r^k)` on such discs.

The reverse triangle inequality converts this into an explicit exponential lower bound on the
height of a derivative return, retaining its approximation error. Failure of the asymptotic
abscissa law supplies `β < 1`, `H > 0`, and a zero to the right of `β`, while the full high-height
zero-free region, derivative estimates, and transport costs all hold.
-/

open Complex Filter Topology Set Metric
open RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section


/-- Horizontal separation from the bulk and vertical separation from the finite exceptions
control every logarithmic-derivative jet on a high disc. -/
theorem norm_zeta_logDeriv_jet_le_of_separated_zeros
    {β H σ t r δ : ℝ} (hβ : 1 / 2 ≤ β) (hr : 0 < r)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hleft : β + δ + r ≤ σ) (hright : σ + r ≤ 2)
    (hheight : H + r + δ ≤ t) (ht : 4 + r ≤ t)
    (hzeros : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β ∨ |(q.1 : ℂ).im| ≤ H) (k : ℕ) :
    ‖iteratedDeriv k (logDeriv riemannZeta) ((σ : ℂ) + t * I)‖ ≤
      k.factorial * (logDerivZetaConstant * Real.log (t + r) / δ) / r ^ k := by
  let s : ℂ := (σ : ℂ) + t * I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hcoordinates : ∀ z ∈ closedBall s r,
      σ - r ≤ z.re ∧ z.re ≤ σ + r ∧ t - r ≤ z.im ∧ z.im ≤ t + r := by
    intro z hz
    have hn : ‖z - s‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hre := (Complex.abs_re_le_norm (z - s)).trans hn
    have him := (Complex.abs_im_le_norm (z - s)).trans hn
    rw [Complex.sub_re, hsre, abs_le] at hre
    rw [Complex.sub_im, hsim, abs_le] at him
    exact ⟨by linarith [hre.1], by linarith [hre.2],
      by linarith [him.1], by linarith [him.2]⟩
  have hdistance : ∀ z ∈ closedBall s r, ∀ q : XiZeroCopy, δ ≤ ‖z - (q.1 : ℂ)‖ := by
    intro z hz q
    obtain ⟨hzlo, _, hzheight, _⟩ := hcoordinates z hz
    rcases hzeros q with hq | hq
    · have h := Complex.abs_re_le_norm (z - (q.1 : ℂ))
      rw [Complex.sub_re] at h
      exact (by linarith : δ ≤ z.re - (q.1 : ℂ).re).trans ((le_abs_self _).trans h)
    · have h := Complex.abs_im_le_norm (z - (q.1 : ℂ))
      rw [Complex.sub_im] at h
      have hqi := (le_abs_self (q.1 : ℂ).im).trans hq
      exact (by linarith : δ ≤ z.im - (q.1 : ℂ).im).trans ((le_abs_self _).trans h)
  have hregular : ∀ z ∈ closedBall s r, z ≠ 1 ∧ riemannZeta z ≠ 0 := by
    intro z hz
    obtain ⟨hzlo, _, hzheight, _⟩ := hcoordinates z hz
    have hzre : 0 < z.re := by linarith
    have hz1 : z ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.one_im] at him
      linarith
    refine ⟨hz1, fun hζ => ?_⟩
    have hz0 : z ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.zero_re] at hre
      linarith
    have hxi : xi z = 0 := by rw [xi_eq_xiUnit_mul_zeta hz0 hz1 hzre, hζ, mul_zero]
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hd := hdistance z hz q
    rw [hq, sub_self, norm_zero] at hd
    linarith
  have han : AnalyticOnNhd ℂ (logDeriv riemannZeta) (closedBall s r) := by
    intro z hz
    obtain ⟨hz1, hzeta⟩ := hregular z hz
    have ha : AnalyticAt ℂ riemannZeta z := RHTower.analyticAt_riemannZeta hz1
    exact ha.deriv.div ha hzeta
  have hdc : DiffContOnCl ℂ (logDeriv riemannZeta) (ball s r) := by
    exact han.differentiableOn.diffContOnCl_ball (Subset.refl _)
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hdc
  intro z hz
  have hz' : z ∈ closedBall s r := sphere_subset_closedBall hz
  obtain ⟨hzlo, hzup, hzheight, hzheightup⟩ := hcoordinates z hz'
  have hzb := RHTower.norm_logDeriv_zeta_le (σ := z.re) (t := z.im)
    (by linarith) (by linarith) (by linarith) hδ hδ1 (by
      intro q
      simpa only [Complex.re_add_im] using hdistance z hz' q)
  have hlog : Real.log z.im ≤ Real.log (t + r) :=
    Real.log_le_log (by linarith) hzheightup
  have hC : 0 ≤ logDerivZetaConstant := by unfold logDerivZetaConstant; positivity
  have hzsplit : (z.re : ℂ) + z.im * I = z := Complex.re_add_im z
  rw [hzsplit] at hzb
  exact hzb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC) hδ.le)


/-- Transporting a derivative value to a high zero-free disc has an explicit height cost.
The approximation error is retained in the formula; no recurrence assumption is imposed. -/
theorem exp_jet_transport_cost_le_height
    {β H σ t r δ : ℝ} (hβ : 1 / 2 ≤ β) (hr : 0 < r)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hleft : β + δ + r ≤ σ) (hright : σ + r ≤ 2)
    (hheight : H + r + δ ≤ t) (ht : 4 + r ≤ t)
    (hzeros : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β ∨ |(q.1 : ℂ).im| ≤ H)
    (k : ℕ) (z : ℂ) :
    Real.exp (δ * r ^ k / (k.factorial * logDerivZetaConstant) *
      (‖iteratedDeriv k (logDeriv riemannZeta) z‖ -
        ‖iteratedDeriv k (logDeriv riemannZeta) z -
          iteratedDeriv k (logDeriv riemannZeta) ((σ : ℂ) + t * I)‖)) ≤ t + r := by
  have hbound := norm_zeta_logDeriv_jet_le_of_separated_zeros hβ hr hδ hδ1
    hleft hright hheight ht hzeros k
  let A := iteratedDeriv k (logDeriv riemannZeta) z
  let B := iteratedDeriv k (logDeriv riemannZeta) ((σ : ℂ) + t * I)
  have htriangle : ‖A‖ - ‖A - B‖ ≤ ‖B‖ := by
    have h := norm_add_le (A - B) B
    rw [sub_add_cancel] at h
    linarith
  have hC : 0 < logDerivZetaConstant := by unfold logDerivZetaConstant; positivity
  have hfact : (0 : ℝ) < k.factorial := by positivity
  have hweight : 0 ≤ δ * r ^ k / (k.factorial * logDerivZetaConstant) := by positivity
  have hlog : δ * r ^ k / (k.factorial * logDerivZetaConstant) *
      (‖A‖ - ‖A - B‖) ≤ Real.log (t + r) := by
    calc
      _ ≤ δ * r ^ k / (k.factorial * logDerivZetaConstant) * ‖B‖ :=
        mul_le_mul_of_nonneg_left htriangle hweight
      _ ≤ δ * r ^ k / (k.factorial * logDerivZetaConstant) *
          (k.factorial * (logDerivZetaConstant * Real.log (t + r) / δ) / r ^ k) :=
        mul_le_mul_of_nonneg_left hbound hweight
      _ = Real.log (t + r) := by
        field_simp [hδ.ne', hr.ne', hC.ne', hfact.ne']
  exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (by linarith))

/-- Failure of the abscissa law gives high-height jet bounds with a genuine interior abscissa,
even though a zero remains strictly to its right. -/
theorem not_asymptoticAbscissaLaw_has_high_jet_bounds :
    ¬ AsymptoticAbscissaLaw →
      ∃ β H : ℝ, 1 / 2 ≤ β ∧ β < 1 ∧ 0 < H ∧
        (∃ q : XiZeroCopy, β < (q.1 : ℂ).re) ∧
        (∀ s : ℂ, β < s.re → H < |s.im| → riemannZeta s ≠ 0) ∧
        ∀ (σ t r δ : ℝ), 0 < r → 0 < δ → δ ≤ 1 →
          β + δ + r ≤ σ → σ + r ≤ 2 → H + r + δ ≤ t → 4 + r ≤ t →
          ∀ k : ℕ, ‖iteratedDeriv k (logDeriv riemannZeta) ((σ : ℂ) + t * I)‖ ≤
            k.factorial * (logDerivZetaConstant * Real.log (t + r) / δ) / r ^ k ∧
            ∀ z : ℂ,
              Real.exp (δ * r ^ k / (k.factorial * logDerivZetaConstant) *
                (‖iteratedDeriv k (logDeriv riemannZeta) z‖ -
                  ‖iteratedDeriv k (logDeriv riemannZeta) z -
                    iteratedDeriv k (logDeriv riemannZeta) ((σ : ℂ) + t * I)‖)) ≤ t + r := by
  intro hnot
  unfold AsymptoticAbscissaLaw at hnot
  push Not at hnot
  obtain ⟨h, hh, hfin, q, hq⟩ := hnot
  obtain ⟨M, hM⟩ := (hfin.image fun q : XiZeroCopy => |(q.1 : ℂ).im|).bddAbove
  let H : ℝ := max M 0 + 1
  have hβ : (1 / 2 : ℝ) ≤ 1 / 2 + h := by linarith
  have hzeros : ∀ q' : XiZeroCopy,
      (q'.1 : ℂ).re ≤ 1 / 2 + h ∨ |(q'.1 : ℂ).im| ≤ H := by
    intro q'
    by_cases hlow : (q'.1 : ℂ).re ≤ 1 / 2 + h
    · exact Or.inl hlow
    · apply Or.inr
      have hq' : q' ∈ {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re} := lt_of_not_ge hlow
      have hM' : |(q'.1 : ℂ).im| ≤ M := hM ⟨q', hq', rfl⟩
      exact hM'.trans (by dsimp [H]; linarith [le_max_left M 0])
  refine ⟨1 / 2 + h, H, hβ,
    lt_trans hq (xi_divisor_support_re_mem_open_unit q.1).2, by dsimp [H]; positivity,
    ⟨q, hq⟩, ?_, ?_⟩
  · intro z hzre hzim hζ
    by_cases hz1 : 1 ≤ z.re
    · exact riemannZeta_ne_zero_of_one_le_re hz1 hζ
    · obtain ⟨q', hq'⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ
        (by linarith) (lt_of_not_ge hz1)
      rcases hzeros q' with hre | him
      · rw [hq'] at hre
        linarith
      · rw [hq'] at him
        linarith
  · intro σ t r δ hr hδ hδ1 hleft hright hheight ht k
    exact ⟨norm_zeta_logDeriv_jet_le_of_separated_zeros hβ hr hδ hδ1
      hleft hright hheight ht hzeros k,
      fun z => exp_jet_transport_cost_le_height hβ hr hδ hδ1
        hleft hright hheight ht hzeros k z⟩


#print axioms not_asymptoticAbscissaLaw_has_high_jet_bounds

end
end GaloisForLFunctions.ZeroConfigurationGeometry
