import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheRecurrenceDichotomyOfTheTail
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration

/-!
# The asymptotic abscissa law is a transport of tail events

Cut `ζ` at `y`: `ζ = E_y · ζM_y`. The head `E_y` never vanishes on `Re s > 0`, and at real part `σ`
it is at least the **head floor** `Π_{p≤y} (1 + p^{−σ})^{−1}` (`headFloor_le_norm_eulerHead`). So at
a zero `s` of `ζ` the tail `ζM_y` vanishes and `ζ − E_y = −E_y`: a cancellation of the head by the
tail of full amplitude, at every cut.

**Theorem** (`asymptoticAbscissaLaw_iff_tailTransport`). AAL holds iff for every zero `ρ` right of
the line, every `ε > 0` and every height `T` there is a point `s` with `Re s > Re ρ − ε`,
`Im s > T`, at which for every cut `y` the tail vanishes and `|ζ − E_y| = |E_y|` is at least the head
floor. No alignment of the head is required: AAL asks for tail events, not for returns of the
phases `p^{−iτ}`.

**Heights** (`tailTransport_height_mem_tailBad`). The height of such an event is tail-bad at every cut
on the disc spanned by `[Re ρ − ε, 1]`, with tolerance the head floor at `Re ρ − ε`.

**Near-full cancellation is abundant** (`near_full_tail_events_have_positive_density`). At every
point of the strip `½ < Re z < 1`, every cut `y` and every `η > 0`, the heights where the tail
cancels the head up to the fraction `η`, `|ζ − E_y| ≥ (1 − η)|E_y|`, have positive lower density
(Voronin universality with a small constant target). AAL asks for `η = 0` near right zeros.

**Upper bounds only** (`exists_returns_tailBad_and_rare`). The events produced by returns of `ζ` to
itself near a right zero have density zero at a tolerance independent of the cut. So AAL is the
existence of rare events, and every density statement about the tail bounds them from above.
-/

open Complex Filter Topology Metric Set Finset MeasureTheory
open Zeta23

noncomputable section

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

/-- The head floor `Π_{p≤y} (1 + p^{−σ})^{−1}`. -/
def headFloor (y : ℕ) (σ : ℝ) : ℝ := ∏ p ∈ headPrimes y, (1 + (p : ℝ) ^ (-σ))⁻¹

theorem headFloor_pos (y : ℕ) (σ : ℝ) : 0 < headFloor y σ :=
  Finset.prod_pos fun p _ => inv_pos.mpr (by positivity)

/-- The head floor increases with the real part. -/
theorem headFloor_mono (y : ℕ) {σ σ' : ℝ} (h : σ ≤ σ') : headFloor y σ ≤ headFloor y σ' := by
  refine Finset.prod_le_prod (fun p _ => (inv_pos.mpr (by positivity)).le) fun p hp => ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le
  refine inv_anti₀ (by positivity) ?_
  have := Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg h)
  linarith

/-- **The head floor.** On `Re s > 0`, `|E_y(s)| ≥ Π_{p≤y} (1 + p^{−Re s})^{−1}`. -/
theorem headFloor_le_norm_eulerHead (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    headFloor y s.re ≤ ‖RHTower.eulerHead y s‖ := by
  rw [RHTower.eulerHead, norm_prod, headFloor]
  refine Finset.prod_le_prod (fun p _ => (inv_pos.mpr (by positivity)).le) fun p hp => ?_
  have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  rw [norm_inv]
  refine inv_anti₀ (norm_pos_iff.mpr (one_sub_cpow_ne_zero hp2 hs)) ?_
  calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ = 1 + (p : ℝ) ^ (-s.re) := by rw [norm_one, hnorm]

/-- **At a zero the tail cancels the head with full amplitude, at every cut.** -/
theorem tailEvent_of_zero {s : ℂ} (hs : 0 < s.re) (hz : riemannZeta s = 0) (y : ℕ) :
    eulerTail y s = 0 ∧ RHTower.eulerTailFun y s = -RHTower.eulerHead y s ∧
      headFloor y s.re ≤ ‖RHTower.eulerTailFun y s‖ := by
  have htf : RHTower.eulerTailFun y s = -RHTower.eulerHead y s := by
    rw [RHTower.eulerTailFun_eq, hz, zero_sub]
  refine ⟨(eulerTail_eq_zero_iff y hs).mpr hz, htf, ?_⟩
  rw [htf, norm_neg]
  exact headFloor_le_norm_eulerHead y hs

/-- **AAL is the transport of tail events.** -/
theorem asymptoticAbscissaLaw_iff_tailTransport :
    _root_.RHTower.AsymptoticAbscissaLaw ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → ∀ ε > 0, ∀ T : ℝ,
        ∃ s : ℂ, ρ.re - ε < s.re ∧ T < s.im ∧ 0 < s.re ∧ s.re < 1 ∧ ∀ y : ℕ,
          eulerTail y s = 0 ∧ RHTower.eulerTailFun y s = -RHTower.eulerHead y s ∧
            headFloor y s.re ≤ ‖RHTower.eulerTailFun y s‖ := by
  rw [← ZetaAbscissa.zetaZeroConfig_abscissaLaw_iff, abscissaLaw_iff_transport]
  constructor
  · intro hT ρ hρ h12 h1 ε hε T
    have hmem : ρ ∈ zetaZeroConfig.carrier := ⟨hρ, by linarith, h1⟩
    obtain ⟨ρ', ⟨hz, h0, h1'⟩, hre, him⟩ := hT ρ hmem h12 ε hε T
    -- reflect into the upper half-plane by conjugation
    have hconj : riemannZeta (starRingEnd ℂ ρ') = 0 := by
      rw [_root_.riemannZeta_conj, hz, map_zero]
    rcases le_or_gt 0 ρ'.im with hpos | hneg
    · rw [abs_of_nonneg hpos] at him
      exact ⟨ρ', hre, him, h0, h1', tailEvent_of_zero h0 hz⟩
    · rw [abs_of_neg hneg] at him
      refine ⟨starRingEnd ℂ ρ', by rwa [conj_re], by rwa [conj_im], by rwa [conj_re],
        by rwa [conj_re], fun y => ?_⟩
      have h0' : 0 < (starRingEnd ℂ ρ').re := by rwa [conj_re]
      exact tailEvent_of_zero h0' hconj y
  · intro hS ρ hρ h12 ε hε T
    obtain ⟨s, hre, him, h0, h1, hy⟩ := hS ρ hρ.1 h12 hρ.2.2 ε hε T
    have hz : riemannZeta s = 0 := (eulerTail_eq_zero_iff 0 h0).mp (hy 0).1
    exact ⟨s, ⟨hz, h0, h1⟩, hre, him.trans_le (le_abs_self _)⟩

/-- **The height of a transported tail event is tail-bad at every cut**, on the disc spanned by
`[Re ρ − ε, 1]` at that height, with tolerance the head floor at `Re ρ − ε`. -/
theorem tailTransport_height_mem_tailBad {σ : ℝ} (hσ : 0 < σ) {s : ℂ}
    (hs : σ < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0) (y : ℕ) :
    s.im ∈ RHTower.eulerDiscTailBadSet y (((σ + 1) / 2 : ℝ) : ℂ) ((1 - σ) / 2) (headFloor y σ) := by
  refine ⟨(s.re : ℂ), ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · have he : (s.re : ℂ) + (s.im : ℂ) * I = s := re_add_im s
    rw [he]
    have h0 : 0 < s.re := hσ.trans hs
    exact (headFloor_mono y hs.le).trans (tailEvent_of_zero h0 hz y).2.2

/-- **Near-full tail events have positive density.** -/
theorem near_full_tail_events_have_positive_density {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) (y : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ c > 0, ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (c * T) ≤
      volume ({τ : ℝ | (1 - η) * ‖RHTower.eulerHead y (z₀ + τ * I)‖ ≤
        ‖RHTower.eulerTailFun y (z₀ + τ * I)‖} ∩ Icc 0 T) := by
  obtain ⟨r, hr, huniv, -⟩ := tail_recurrence_dichotomy h1 h2
  have hz0 : 0 < z₀.re := by linarith
  set δ : ℝ := η * headFloor y z₀.re / 2 with hδ
  have hδ0 : 0 < δ := by have := headFloor_pos y z₀.re; positivity
  obtain ⟨c, hc, hev⟩ := huniv (fun _ => (δ : ℂ)) analyticOnNhd_const
    (fun _ _ => by exact_mod_cast hδ0.ne') δ hδ0
  refine ⟨c, hc, hev.mono fun T hT => hT.trans (measure_mono ?_)⟩
  rintro τ ⟨hτ, hτT⟩
  refine ⟨?_, hτT⟩
  have hz := hτ z₀ (mem_closedBall_self hr.le)
  have hre : (z₀ + (τ : ℂ) * I).re = z₀.re := by simp
  have hhead := headFloor_le_norm_eulerHead y (s := z₀ + (τ : ℂ) * I) (by rw [hre]; exact hz0)
  rw [hre] at hhead
  have hζ : ‖riemannZeta (z₀ + (τ : ℂ) * I)‖ < 2 * δ := by
    have h := norm_sub_norm_le (riemannZeta (z₀ + (τ : ℂ) * I)) (δ : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg hδ0.le] at h
    linarith
  show (1 - η) * ‖RHTower.eulerHead y (z₀ + τ * I)‖ ≤ ‖RHTower.eulerTailFun y (z₀ + τ * I)‖
  rw [RHTower.eulerTailFun_eq]
  have htri := norm_sub_norm_le (RHTower.eulerHead y (z₀ + (τ : ℂ) * I))
    (riemannZeta (z₀ + (τ : ℂ) * I))
  rw [norm_sub_rev] at htri
  have hsmall : 2 * δ ≤ η * ‖RHTower.eulerHead y (z₀ + (τ : ℂ) * I)‖ := by
    rw [hδ]
    nlinarith [hhead]
  nlinarith

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
