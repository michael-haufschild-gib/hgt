import GaloisForLFunctions.RHTower.XiIntervalLaguerrePolyaRH
import GaloisForLFunctions.RHTower.XiShiftedIntervalLaguerrePolyaRH
import GaloisForLFunctions.RHTower.OrderOneEvenLaguerrePolya
import GaloisForLFunctions.RHTower.CCMEvenFullGroundZeroSumRH

/-!
# Even compactly supported functions with real-rooted transforms: low-frequency convergence to `Φ`
forces RH

Let `f_j` be even integrable functions on `ℝ`, each supported in a bounded interval, with
`∫ f_j ≠ 0` and Fourier–Laplace transforms having only real zeros. Write
`F_j(z) = ∫ conj(f_j(t)) e^{izt} dt`.

**Theorem** (`riemannHypothesis_of_realRooted_paleyWiener_tendstoUniformlyOn_Icc`). If
`F_j(t)/F_j(0) → Ξ(t)/Ξ(0)` uniformly on one interval `[−ε, ε]` (`0 < ε`, `ε² ≤ 32`), then RH holds.

No growth of the supports, no ground-state property and no zero-sum bound is assumed. In the CCM
program (`riemannHypothesis_of_evenFullGrounds_tendstoUniformlyOn_Icc`), the full ground states have
real-rooted transforms whenever they are simple. So CCM's convergence step needs only low-frequency
agreement of the even ground-state profiles with Riemann's distribution `Φ(u)du/Ξ(0)`.

**Proof.** `F_j/F_j(0)` is even, entire, of order one (Paley–Wiener), equal to `1` at `0`, and
real-rooted. So it is Laguerre–Pólya (`OrderOneHadamard.laguerrePolya_of_even_of_realZeros`), and the
low-frequency rigidity of the Laguerre–Pólya class
(`IntervalLaguerrePolya.riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_Icc`) applies.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.LowFrequencyPaleyWiener

open GaloisForLFunctions.HTGeometry RHTower.CCMFullGroundEigen
open RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

noncomputable section

/-- **The normalized transform is Laguerre–Pólya.** -/
theorem laguerrePolya_conjTransform_normalized {A : ℝ} (hA : 0 ≤ A) {f : ℝ → ℂ}
    (hf : Integrable f) (hs : FourierZeroFlip.SupportedIn A f) (heven : ∀ t, f (-t) = f t)
    (h0 : conjTransform f 0 ≠ 0)
    (hreal : ∀ w : ℂ, FourierLaplaceDivision.unitaryLaplace f w = 0 → w.im = 0) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya
      (fun z => conjTransform f z / conjTransform f 0) := by
  set F : ℂ → ℂ := conjTransform f with hFdef
  set g : ℂ → ℂ := fun z => F z / F 0 with hg
  have hFdiff : Differentiable ℂ F := differentiable_conjTransform hA hf hs
  have hgdiff : Differentiable ℂ g := hFdiff.div_const _
  have hg0 : g 0 = 1 := div_self h0
  obtain ⟨K, hK, hbound⟩ := exists_orderOne_bound_conjTransform hA hf
    (bound_support_of_supportedIn hs) h0
  set c : ℝ := |Real.log ‖F 0‖| / Real.log 2 with hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgbound : ∀ z : ℂ, ‖g z‖ ≤ Real.exp ((K + c) * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    intro z
    have hF0pos : 0 < ‖F 0‖ := norm_pos_iff.mpr h0
    have hshape : Real.log 2 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
      have h1 : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
        Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
      have h2 : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
      nlinarith [norm_nonneg z]
    rw [hg, norm_div, div_le_iff₀ hF0pos]
    calc ‖F z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := hbound z
      _ ≤ Real.exp ((K + c) * (1 + ‖z‖) * Real.log (2 + ‖z‖)) * ‖F 0‖ := by
          rw [← Real.exp_log hF0pos, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hcl : -Real.log ‖F 0‖ ≤ c * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
            have : -Real.log ‖F 0‖ ≤ |Real.log ‖F 0‖| := neg_le_abs _
            have hc' : |Real.log ‖F 0‖| = c * Real.log 2 := by
              rw [hc]; field_simp
            rw [hc'] at this
            have hc0 : 0 ≤ c := by positivity
            nlinarith
          nlinarith
  have hgreal : ∀ z, g z = 0 → z.im = 0 := by
    intro z hz
    have hFz : F z = 0 := by
      rw [hg] at hz
      exact (div_eq_zero_iff.mp hz).resolve_right h0
    rw [hFdef, conjTransform_eq_conj_unitaryLaplace, map_eq_zero] at hFz
    have him := hreal _ hFz
    have : ((starRingEnd ℂ) z / (2 * Real.pi : ℂ)).im = -z.im / (2 * Real.pi) := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.div_ofReal_im, Complex.conj_im]
    rw [this] at him
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have := div_eq_zero_iff.mp him
    rcases this with h | h
    · linarith
    · linarith
  refine OrderOneHadamard.laguerrePolya_of_even_of_realZeros (K := K + c) (by positivity)
    (fun z _ => hgdiff.analyticAt z) (by rw [hg0]; exact one_ne_zero)
    (by rw [hg0]; simp) (GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hgdiff
      (by rw [hg0]; exact one_ne_zero : g 0 ≠ 0)) (fun z => ?_) hgbound hgreal
  simp only [hg, hFdef, conjTransform_neg_of_even heven]

/-- **Low-frequency receiver for real-rooted Paley–Wiener functions.** -/
theorem riemannHypothesis_of_realRooted_paleyWiener_tendstoUniformlyOn_Icc
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (f : ℕ → ℝ → ℂ) (hf : ∀ j, Integrable (f j))
    (hs : ∀ j, FourierZeroFlip.SupportedIn (A j) (f j)) (heven : ∀ j t, f j (-t) = f j t)
    (h0 : ∀ j, conjTransform (f j) 0 ≠ 0)
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (f j) w = 0 → w.im = 0)
    {ε : ℝ} (hε : 0 < ε) (hε32 : ε ^ 2 ≤ 32)
    (hconv : TendstoUniformlyOn
      (fun j (t : ℝ) => conjTransform (f j) t / conjTransform (f j) 0)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-ε) ε)) :
    RiemannHypothesis :=
  IntervalLaguerrePolya.riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_Icc
    (fun j => laguerrePolya_conjTransform_normalized (hA j) (hf j) (hs j) (heven j) (h0 j)
      (hreal j)) hε hε32 hconv

/-- **CCM ground states: low-frequency agreement with `Φ` suffices.** Let `u_j` be form-domain
vectors at apertures `a_j` (for instance full ground states, which are real-rooted when simple)
whose physical functions are even, have nonzero mass, and have real-rooted transforms. If their
normalized transforms converge to `Ξ/Ξ(0)` uniformly on one interval `[−ε, ε]`, then RH holds. -/
theorem riemannHypothesis_of_evenFullGrounds_tendstoUniformlyOn_Icc
    (a : ℕ → SuzukiPositiveAperture) (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (heven : ∀ j t, timeRep (a j) (u j) (-t) = timeRep (a j) (u j) t)
    {ε : ℝ} (hε : 0 < ε) (hε32 : ε ^ 2 ≤ 32)
    (hconv : TendstoUniformlyOn
      (fun j (t : ℝ) => conjTransform (timeRep (a j) (u j)) t /
        conjTransform (timeRep (a j) (u j)) 0)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-ε) ε)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_realRooted_paleyWiener_tendstoUniformlyOn_Icc
    (A := fun j => (a j).1) (fun j => (a j).2.le) (fun j => timeRep (a j) (u j))
    (fun j => CCMRealRootedGround.integrable_timeRep (a j) (u j))
    (fun j => CCMRealRootedGround.supportedIn_timeRep (a j) (u j)) heven (fun j => ?_) hreal
    hε hε32 hconv
  rw [← norm_ne_zero_iff]
  have : ‖conjTransform (timeRep (a j) (u j)) 0‖ = ‖∫ t : ℝ, timeRep (a j) (u j) t‖ := by
    simp only [conjTransform, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [integral_conj, Complex.norm_conj]
  rw [this]
  exact norm_ne_zero_iff.mpr (hmass j)

end

end RHTower.LowFrequencyPaleyWiener

namespace RHTower.LowFrequencyPaleyWiener

open GaloisForLFunctions.HTGeometry

/-- **Window receiver for even real-rooted entire functions of order one.** Let `F_n` be even entire
functions with `F_n(0)` real and nonzero, order-one growth envelopes, and only real zeros. If
`F_n → Ξ` uniformly on one real interval `[c − ε, c + ε]` (`ε > 0`), then RH holds.
This covers every producer whose approximants are of this shape: lossless-stack entries,
Paley–Wiener transforms of even real-rooted profiles, and finite-volume characteristic functions. -/
theorem riemannHypothesis_of_evenRealRooted_orderOne_tendstoUniformlyOn
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, AnalyticOnNhd ℂ (F n) univ) (hF0 : ∀ n, F n 0 ≠ 0)
    (hF0re : ∀ n, (F n 0).im = 0) (heven : ∀ n z, F n (-z) = F n z)
    (hbound : ∀ n, ∃ K : ℝ, 0 ≤ K ∧
      ∀ z : ℂ, ‖F n z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hreal : ∀ n z, F n z = 0 → z.im = 0) {c ε : ℝ} (hε : 0 < ε)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => F n t) (fun t : ℝ => XiC t) atTop
      (Icc (c - ε) (c + ε))) :
    RiemannHypothesis := by
  refine IntervalLaguerrePolya.riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_any
    (fun n => ?_) hε hconv
  obtain ⟨K, hK, hb⟩ := hbound n
  have hdiff : Differentiable ℂ (F n) := fun z => (hF n z (mem_univ z)).differentiableAt
  exact OrderOneHadamard.laguerrePolya_of_even_of_realZeros hK (hF n) (hF0 n) (hF0re n)
    (GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hdiff (hF0 n)) (heven n) hb (hreal n)

end RHTower.LowFrequencyPaleyWiener
