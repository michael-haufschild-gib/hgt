import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheTailOfAReturnCarriesTheZero
import GaloisForLFunctions.RHTower.ZetaVoroninUniversalityOnSmallDiscs

/-!
# The recurrence dichotomy of the tail

Which members of the orbit of `ζ` are atypical, and why? About every point of the strip there is a disc on which
(Voronin, `RHTower.zeta_orbit_closure_dichotomy`) every target analytic and nonvanishing on the fourfold disc is
approached by `ζ(· + iτ)` on a set of heights of positive lower density, while every target with a zero inside is
approached only on a set of density zero.

**The tail explains the dichotomy** (`zetaTargetReturnSet_subset_eulerDiscTailBadSet`). If `ζ(· + iτ)` is within `m/2`
of a target `g` with a zero inside and `|g| ≥ m` on the circle, then `ζ(· + iτ)` has a zero inside and is at least `m/2`
on the circle. A tail-good height (`|ζ − E_y| < m/4` on the disc) makes the zero-free head `E_y` larger than `m/4` on the
circle, hence, by the maximum principle for `1/E_y`, inside; at the zero `|E_y| = |ζ − E_y| < m/4`. So every height that
approaches a target with a zero is tail-bad at every cut `y`, with the tolerance `m/4` fixed by the target.

**The dichotomy** (`tail_recurrence_dichotomy`). On the universal disc about each point of the strip:
nonvanishing targets are approached at positive density (atypical members of a Bohr set exist in abundance: the tail can
take any nonvanishing shape), and targets with a zero are approached only at heights that are tail-bad at every cut.
The self-target `ζ` is of the second kind exactly at a zero.
-/

open Complex Filter Topology Metric Set Finset MeasureTheory

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- **A zero of the translate is never at a tail-good height.** -/
theorem exists_tailBad_of_zero {c : ℂ} {r m : ℝ} (hr : 0 < r) (hpos : ∀ s ∈ closedBall c r, 0 < s.re)
    {τ : ℝ} {z₀ : ℂ} (hz₀ : z₀ ∈ ball c r) (hzero : riemannZeta (z₀ + τ * I) = 0)
    (hsph : ∀ z ∈ sphere c r, m / 2 ≤ ‖riemannZeta (z + τ * I)‖) (y : ℕ) :
    τ ∈ RHTower.eulerDiscTailBadSet y c r (m / 4) := by
  by_contra hgood
  have hgood' : ∀ z ∈ closedBall c r, ‖RHTower.eulerTailFun y (z + τ * I)‖ < m / 4 := by
    intro z hz
    by_contra hc
    exact hgood ⟨z, hz, not_lt.mp hc⟩
  have hz₀c : z₀ ∈ closedBall c r := ball_subset_closedBall hz₀
  have hm0 : 0 < m := by
    have h1 := hgood' z₀ hz₀c
    have h2 := norm_nonneg (RHTower.eulerTailFun y (z₀ + τ * I))
    linarith
  set f : ℂ → ℂ := fun z => eulerMollifier y (z + τ * I) with hf
  have hshift : ∀ z ∈ closedBall c r, 0 < (z + τ * I).re := fun z hz => by
    have : (z + τ * I).re = z.re := by simp
    rw [this]
    exact hpos z hz
  have hsphere : ∀ z ∈ sphere c r, ‖f z‖ ≤ 4 / m := by
    intro z hz
    have hzc : z ∈ closedBall c r := sphere_subset_closedBall hz
    have h5 : m / 4 < ‖RHTower.eulerHead y (z + τ * I)‖ := by
      have h6 := hgood' z hzc
      rw [RHTower.eulerTailFun_eq] at h6
      have h7 := norm_sub_norm_le (riemannZeta (z + τ * I))
        (riemannZeta (z + τ * I) - RHTower.eulerHead y (z + τ * I))
      rw [sub_sub_cancel] at h7
      linarith [hsph z hz]
    have hfz : ‖f z‖ = ‖RHTower.eulerHead y (z + τ * I)‖⁻¹ := by
      rw [hf, eulerHead_eq_inv, norm_inv, inv_inv]
    rw [hfz, inv_le_comm₀ (by linarith) (by positivity), inv_div]
    exact h5.le
  have hdiff : Differentiable ℂ f := (differentiable_eulerMollifier y).comp (differentiable_id.add_const _)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := c) (r := r))
    hdiff.diffContOnCl (C := 4 / m) (by rw [frontier_ball c hr.ne']; exact hsphere) (z := z₀) (subset_closure hz₀)
  have hsmall := hgood' z₀ hz₀c
  rw [RHTower.eulerTailFun_eq, hzero, zero_sub, norm_neg] at hsmall
  have hpos0 : 0 < ‖RHTower.eulerHead y (z₀ + τ * I)‖ :=
    norm_pos_iff.mpr (eulerHead_ne_zero y (hshift z₀ hz₀c))
  have hfz₀ : ‖f z₀‖ = ‖RHTower.eulerHead y (z₀ + τ * I)‖⁻¹ := by
    rw [hf, eulerHead_eq_inv, norm_inv, inv_inv]
  rw [hfz₀] at hmax
  have : 4 / m < ‖RHTower.eulerHead y (z₀ + τ * I)‖⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hpos0, inv_div]
    exact hsmall
  linarith

/-- **Targets with a zero are approached only at tail-bad heights, at every cut.** -/
theorem zetaTargetReturnSet_subset_eulerDiscTailBadSet {g : ℂ → ℂ} {c : ℂ} {r m : ℝ} (hr : 0 < r)
    (hpos : ∀ s ∈ closedBall c r, 0 < s.re) (hre : ∀ s ∈ closedBall c r, s.re < 1)
    (hw : ∃ w ∈ ball c r, g w = 0) (hm : ∀ z ∈ sphere c r, m ≤ ‖g z‖) (y : ℕ) :
    RHTower.zetaTargetReturnSet g (closedBall c r) (m / 2) ⊆ RHTower.eulerDiscTailBadSet y c r (m / 4) := by
  intro τ hτ
  obtain ⟨z₀, hz₀, hzero⟩ := RHTower.exists_zero_of_mem_zetaTargetReturnSet hr hre hw hm le_rfl hτ
  refine exists_tailBad_of_zero hr hpos hz₀ hzero (fun z hz => ?_) y
  have h1 := hτ z (sphere_subset_closedBall hz)
  have h2 := hm z hz
  have h3 := norm_sub_norm_le (g z) (g z - riemannZeta (z + τ * I))
  rw [sub_sub_cancel, norm_sub_rev] at h3
  linarith

/-- **The recurrence dichotomy of the tail.** About every point of the strip there is a disc on which every nonvanishing
target is approached at positive lower density, and every target with a zero is approached only at heights that are
tail-bad at every cut, on a set of density zero. -/
theorem tail_recurrence_dichotomy {z₀ : ℂ} (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ r > 0,
      (∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball z₀ (4 * r)) → (∀ z ∈ ball z₀ (4 * r), g z ≠ 0) →
        ∀ ε > 0, ∃ c > 0, ∀ᶠ T : ℝ in atTop,
          ENNReal.ofReal (c * T) ≤ volume (RHTower.zetaTargetReturnSet g (closedBall z₀ r) ε ∩ Icc 0 T)) ∧
      (∀ g : ℂ → ℂ, (∃ w ∈ ball z₀ r, g w = 0) → ∀ m : ℝ, (∀ z ∈ sphere z₀ r, m ≤ ‖g z‖) →
        (∀ y : ℕ, RHTower.zetaTargetReturnSet g (closedBall z₀ r) (m / 2) ⊆
          RHTower.eulerDiscTailBadSet y z₀ r (m / 4)) ∧
        ∀ κ > 0, ∀ᶠ T : ℝ in atTop,
          volume (RHTower.zetaTargetReturnSet g (closedBall z₀ r) (m / 2) ∩ Icc 0 T) ≤ ENNReal.ofReal (κ * T)) := by
  obtain ⟨r, hr, hr0, hr1, huniv⟩ := RHTower.exists_radius_zeta_universal h1 h2
  have hball : ∀ s ∈ closedBall z₀ r, z₀.re - r ≤ s.re ∧ s.re ≤ z₀.re + r := by
    intro s hs
    have h := abs_re_le_norm (s - z₀)
    rw [mem_closedBall, dist_eq_norm] at hs
    rw [sub_re] at h
    constructor <;> linarith [abs_le.mp (h.trans hs)]
  refine ⟨r, hr, huniv, fun g hw m hm => ⟨fun y => ?_, fun κ hκ => ?_⟩⟩
  · exact zetaTargetReturnSet_subset_eulerDiscTailBadSet hr (fun s hs => by linarith [(hball s hs).1])
      (fun s hs => by linarith [(hball s hs).2]) hw hm y
  · exact RHTower.eventually_volume_zetaTargetReturnSet_le hr (by linarith) (by linarith) hw hm le_rfl hκ

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
