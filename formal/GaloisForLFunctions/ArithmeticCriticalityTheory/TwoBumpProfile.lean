import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateCrossTermRepresentation
import GaloisForLFunctions.RHTower.LogWindowPrimeNumberTheorem

/-!
# Two far-apart bumps as a shifted-ground-state test

For an even `g ∈ C²_c(ℝ)` supported in `[−1/4, 1/4]` and a shift `a ≥ 1`, the profile

    u(x) = g(x − a)/m_a(x) + g(−x − a)/m_a(−x)

is even, `C²`, compactly supported, and satisfies `m_a(x) u(x) = g(x − a)` on `x > 0`. The odd test
`Φ(ω_a u)` is therefore `g(x − a) − g(−x − a)`: two copies of `g` at `±a` with opposite signs. Its
cross term is the autocorrelation of `g` at the shift `t − 2a`,

    X_a(u)(t) = ∫_0^t m_a(x) m_a(t−x) u(x) u(t−x) dx = ρ_g(t − 2a),   ρ_g = autoCorr g,

and the prime part of the cross energy is the corpus's smoothed log-window sum
`windowSum Λ (2a) = Σ_{n≥2} Λ(n) n^{−1/2} ρ_g(log n − 2a)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilOneSided

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The two-bump profile `g(x − a)/m_a(x) + g(−x − a)/m_a(−x)`. -/
def twoBumpProfile (g : ℝ → ℝ) (a x : ℝ) : ℝ :=
  g (x - a) / shiftDifference a x + g (-x - a) / shiftDifference a (-x)

theorem twoBumpProfile_neg (g : ℝ → ℝ) (a x : ℝ) :
    twoBumpProfile g a (-x) = twoBumpProfile g a x := by
  unfold twoBumpProfile
  rw [neg_neg]
  ring

theorem contDiff_shiftDifference_two (a : ℝ) : ContDiff ℝ 2 (shiftDifference a) := by
  unfold shiftDifference
  exact (contDiff_riemannKernelReal.comp (contDiff_id.sub contDiff_const)).sub
    (contDiff_riemannKernelReal.comp (contDiff_id.add contDiff_const))

theorem shiftDifference_ne_zero_of_ne {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    shiftDifference a x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hpos := shiftDifference_pos ha (neg_pos.mpr h)
    rw [shiftDifference_neg] at hpos
    exact (by linarith : shiftDifference a x < 0).ne
  · exact (shiftDifference_pos ha h).ne'

/-- `m_a · u = g(· − a)` on the half line. -/
theorem shiftDifference_mul_twoBumpProfile {g : ℝ → ℝ} (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    {a x : ℝ} (ha : 1 ≤ a) (hx : 0 < x) :
    shiftDifference a x * twoBumpProfile g a x = g (x - a) := by
  unfold twoBumpProfile
  rw [hsupp (-x - a) (by rw [abs_of_neg (by linarith)]; linarith), zero_div, add_zero]
  have hne := (shiftDifference_pos (by linarith : 0 < a) hx).ne'
  field_simp

theorem contDiff_twoBumpProfile {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {a : ℝ} (ha : 1 ≤ a) :
    ContDiff ℝ 2 (twoBumpProfile g a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : |x| < a - 1 / 4
  · have hmem : Ioo (-(a - 1 / 4)) (a - 1 / 4) ∈ 𝓝 x :=
      Ioo_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x])
    have hzero : twoBumpProfile g a =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      refine Filter.eventuallyEq_of_mem hmem fun y hy => ?_
      obtain ⟨hy1, hy2⟩ := hy
      unfold twoBumpProfile
      rw [hsupp (y - a) (by rw [abs_of_neg (by linarith)]; linarith),
        hsupp (-y - a) (by rw [abs_of_neg (by linarith)]; linarith)]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hzero
  · rw [not_lt] at hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, abs_zero] at hx
      linarith
    have ha0 : 0 < a := by linarith
    have hm1 := shiftDifference_ne_zero_of_ne ha0 hx0
    have hm2 := shiftDifference_ne_zero_of_ne ha0 (neg_ne_zero.mpr hx0)
    have h1 : ContDiffAt ℝ 2 (fun y => g (y - a) / shiftDifference a y) x :=
      ((hg.comp (contDiff_id.sub contDiff_const)).contDiffAt).div
        (contDiff_shiftDifference_two a).contDiffAt hm1
    have h2 : ContDiffAt ℝ 2 (fun y => g (-y - a) / shiftDifference a (-y)) x :=
      ((hg.comp (contDiff_neg.sub contDiff_const)).contDiffAt).div
        ((contDiff_shiftDifference_two a).comp contDiff_neg).contDiffAt hm2
    exact h1.add h2

theorem hasCompactSupport_twoBumpProfile {g : ℝ → ℝ} (hgc : HasCompactSupport g) (a : ℝ) :
    HasCompactSupport (twoBumpProfile g a) := by
  have h1 : HasCompactSupport fun x => g (x - a) := hgc.comp_homeomorph (Homeomorph.subRight a)
  have h2 : HasCompactSupport fun x => g (-x - a) :=
    hgc.comp_homeomorph ((Homeomorph.neg ℝ).trans (Homeomorph.subRight a))
  have h1' : HasCompactSupport fun x => g (x - a) / shiftDifference a x := by
    refine h1.mono fun x hx => ?_
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    rw [h0, zero_div]
  have h2' : HasCompactSupport fun x => g (-x - a) / shiftDifference a (-x) := by
    refine h2.mono fun x hx => ?_
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    rw [h0, zero_div]
  exact h1'.add h2'

/-- The cross term of the two-bump profile is the autocorrelation of `g` at `t − 2a`. -/
theorem crossShift_twoBumpProfile {g : ℝ → ℝ} (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    (heven : ∀ u, g (-u) = g u) {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    crossShift a (twoBumpProfile g a) t = autoCorr g (t - 2 * a) := by
  have ha0 : 0 < a := by linarith
  unfold crossShift
  have hpt : ∀ x ∈ Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) *
      (twoBumpProfile g a x * twoBumpProfile g a (t - x)) = g (x - a) * g (t - x - a) := by
    intro x hx
    have e1 := shiftDifference_mul_twoBumpProfile hsupp ha hx.1
    have e2 := shiftDifference_mul_twoBumpProfile hsupp ha (sub_pos.mpr hx.2)
    calc shiftDifference a x * shiftDifference a (t - x) *
          (twoBumpProfile g a x * twoBumpProfile g a (t - x))
        = (shiftDifference a x * twoBumpProfile g a x) *
          (shiftDifference a (t - x) * twoBumpProfile g a (t - x)) := by ring
      _ = g (x - a) * g (t - x - a) := by rw [e1, e2]
  rw [setIntegral_congr_fun measurableSet_Ioo hpt]
  have hext : (∫ x in Ioo (0 : ℝ) t, g (x - a) * g (t - x - a)) =
      ∫ x, g (x - a) * g (t - x - a) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    by_contra hne
    have h1 : g (x - a) ≠ 0 := left_ne_zero_of_mul hne
    have h2 : g (t - x - a) ≠ 0 := right_ne_zero_of_mul hne
    have b1 : |x - a| ≤ 1 / 4 := by
      by_contra h
      rw [not_le] at h
      exact h1 (hsupp _ h)
    have b2 : |t - x - a| ≤ 1 / 4 := by
      by_contra h
      rw [not_le] at h
      exact h2 (hsupp _ h)
    obtain ⟨b1l, b1r⟩ := abs_le.mp b1
    obtain ⟨b2l, b2r⟩ := abs_le.mp b2
    exact hx ⟨by linarith, by linarith⟩
  rw [hext]
  have hsub : (∫ x, g (x - a) * g (t - x - a)) = ∫ s, g s * g (t - 2 * a - s) := by
    calc (∫ x, g (x - a) * g (t - x - a))
        = ∫ x, (fun s => g s * g (t - 2 * a - s)) (x - a) := by
          congr 1
          funext x
          simp only
          rw [show t - 2 * a - (x - a) = t - x - a by ring]
      _ = ∫ s, g s * g (t - 2 * a - s) :=
          integral_sub_right_eq_self (fun s => g s * g (t - 2 * a - s)) a
  rw [hsub]
  unfold autoCorr
  congr 1
  funext s
  rw [show t - 2 * a - s = -(s - (t - 2 * a)) by ring, heven]

/-- The prime part of the cross energy of the two-bump profile is the smoothed log-window sum. -/
theorem tsum_atom_autoCorr_eq_windowSum {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {a : ℝ} (ha : 1 ≤ a) :
    (∑' n : ℕ, vonMangoldtAtom n * autoCorr g (Real.log n - 2 * a)) =
      windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (2 * a) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (Real.exp (|2 * a| + 1))
  rw [windowSum_eq_sum hg hgc hsupp _ hM, tsum_eq_sum (s := Finset.range M) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h2
    · unfold windowValue vonMangoldtAtom
      rw [if_pos h2, autoCorr_eq_zero hsupp (x := Real.log n + 2 * a) ?_, add_zero]
      · ring
      · rw [abs_of_pos (by linarith [Real.log_natCast_nonneg n])]
        linarith [Real.log_natCast_nonneg n]
    · rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega)]
      simp
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hMn : Real.exp (|2 * a| + 1) ≤ n := le_trans hM (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hMn
    have hlog : |2 * a| + 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn0]
      exact hMn
    rw [autoCorr_eq_zero hsupp ?_, mul_zero]
    rw [abs_of_pos (by linarith [le_abs_self (2 * a)])]
    linarith [le_abs_self (2 * a)]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
