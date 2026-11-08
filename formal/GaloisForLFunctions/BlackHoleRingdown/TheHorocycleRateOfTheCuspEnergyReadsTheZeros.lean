import GaloisForLFunctions.BlackHoleRingdown.TheRankinSelbergContinuation
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# The horocycle rate of the cusp energy reads the zeros

Let `g` be a cusp form of the modular horizon, `m(y) = ∫_{-1/2}^{1/2} |g(x+iy)|² dx` its energy along the
closed horocycle of height `y`, and `Λ_g(s) = ∫_𝒟 |g|² E*(s - ½)` its completed Rankin–Selberg function.

**Theorem** (`completedRS_eq_zero_of_rate`). If `|m(y) - c| ≤ C y^α` on `(0, 1]`, then `Λ_g(s₀) = 0` at
every `s₀` with `Re s₀ > 1 - α` and `ξ(2s₀) = 0`. Equivalently (`completedRS_half_eq_zero_of_rate`): every
zero `ρ` of `ζ` with `Re ρ > 2 - 2α` has `Λ_g(ρ/2) = 0`. Contrapositively (`not_rate_of_ne_zero`), a zero
`ρ` with `Λ_g(ρ/2) ≠ 0` caps the rate of equidistribution of `|g|²` at `y^{1 - Re ρ/2}`: below the
critical exponent `3/4` exactly when `ρ` is off the critical line.

**Proof.** For `Re s > 1` the Mellin transform `∫_0^∞ m(y) y^{s-2} dy` is `(2π)^{-s}G(s) Σ|ρ(n)|²|n|^{-s}`
(Rankin–Selberg unfolding), so `Λ_g(s) = ξ(2s)/(2s(2s-1)) · 𝓜m(s - 1)` for `Re s > 1`, `Im s ≠ 0`. Write
`m = c 1_{(0,1]} + r`: `𝓜(c 1_{(0,1]})(s - 1) = c/(s - 1)`, and `r = O(y^α)` at `0`, `r = O(e^{-2πy})` at `∞`,
so `𝓜r(s - 1)` is holomorphic on `Re s > 1 - α`. The identity theorem on the quarter planes
`Re s > 1 - α`, `±Im s > 0` gives `Λ_g(s) = ξ(2s)/(2s(2s-1)) (𝓜r(s - 1) + c/(s - 1))` there, which vanishes
where `ξ(2s)` does. `ξ` has no real zeros, so every zero of `ξ(2s)` lies in one of the two quarter planes.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

namespace CuspHR

open HeckeCusp CuspL CuspRSC

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-- The horocycle mass `m(y)` as a complex profile. -/
def mass (g : UpperHalfPlane → ℂ) (y : ℝ) : ℂ := (WeylUpper.slice g y : ℂ)

theorem continuousOn_mass (hg : g ∈ cuspSpace lamE) : ContinuousOn (mass g) (Ioi 0) :=
  Complex.continuous_ofReal.comp_continuousOn (CuspRSI.continuousOn_slice_pos hg)

theorem mellinConvergent_mass (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (mass g) (s - 1) := by
  have hI := CuspRSI.integrableOn_slice_weight hg hρ0 hρ hs
  refine Integrable.mono' hI ?_ ?_
  · have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1 - 1) * mass g t) (Ioi 0) := by
      refine ContinuousOn.mul (fun t (ht : 0 < t) => ?_) (continuousOn_mass hg)
      exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.2 ht)).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [smul_eq_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, mass, Complex.norm_real,
      Real.norm_of_nonneg (WeylUpper.slice_nonneg _)]
    simp only [sub_re, one_re]
    rw [show s.re - 1 - 1 = s.re - 2 by ring, mul_comm]

/-- **The Mellin transform of the horocycle mass** is `(2π)^{-s} G(s) Σ |ρ(n)|² |n|^{-s}`, `Re s > 1`. -/
theorem mellin_mass (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    mellin (mass g) (s - 1) = (2 * Real.pi : ℂ) ^ (-s) * CuspRSI.gammaFactor (nu lamE) s *
      ∑' n : ℤ, ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  rw [← tsum_mul_left]
  have h := (CuspRSI.hasSum_mellin_slice hg hρ0 hρ hs).congr_fun
    (g := fun n : ℤ => (2 * Real.pi : ℂ) ^ (-s) * CuspRSI.gammaFactor (nu lamE) s *
      (((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s))) fun n => by
    rw [ofReal_mul (2 * Real.pi) |(n : ℝ)|, mul_cpow_ofReal_nonneg (by positivity) (abs_nonneg _)]
    push_cast
    ring
  rw [h.tsum_eq]
  unfold mellin mass
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, show s - 1 - 1 = s - 2 by ring]

/-- `Λ_g(s) = ξ(2s)/(2s(2s-1)) · 𝓜m(s - 1)` for `Re s > 1`, `Im s ≠ 0`. -/
theorem completedRS_eq_mellin (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re)
    (him : s.im ≠ 0) :
    completedRS g s = xi (2 * s) / (2 * s * (2 * s - 1)) * mellin (mass g) (s - 1) := by
  rw [completedRS_eq hg hρ0 hρ hs him, mellin_mass hg hρ0 hρ hs]

/-- **A horocycle rate `y^α` forces `Λ_g` to vanish at the zeros of `ξ(2s)` with `Re s > 1 - α`.** -/
theorem completedRS_eq_zero_of_rate (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {α c C : ℝ}
    (hrate : ∀ y : ℝ, 0 < y → y ≤ 1 → |WeylUpper.slice g y - c| ≤ C * y ^ α)
    {s₀ : ℂ} (hs₀ : 1 - α < s₀.re) (hz : xi (2 * s₀) = 0) : completedRS g s₀ = 0 := by
  -- `s₀` is not real
  have him₀ : s₀.im ≠ 0 := by
    intro h
    have e : 2 * s₀ = ((2 * s₀.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
    exact xi_ne_zero_of_real _ (e ▸ hz)
  set ind : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun _ => (c : ℂ) with hind
  set rem : ℝ → ℂ := fun y => mass g y - ind y with hrem
  obtain ⟨D, hD0, hD⟩ := CuspRS.slice_le_decay hg hρ0 hρ
  have hindM : ∀ w : ℂ, 0 < w.re → MellinConvergent ind w ∧ mellin ind w = c / w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hasMellin_one_Ioc hw
    have hind_smul : ind = fun y => (c : ℂ) • (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) y := by
      funext y
      by_cases hy : y ∈ Ioc (0 : ℝ) 1 <;> simp [hind, hy]
    rw [hind_smul]
    refine ⟨h1.const_smul (c : ℂ), ?_⟩
    rw [mellin_const_smul, h2, smul_eq_mul]
    ring
  have hAint : IntegrableOn (mass g) (Ioi 0) := by
    have h := mellinConvergent_mass hg hρ0 hρ (s := 2) (by norm_num)
    refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
    norm_num
  have hindint : IntegrableOn ind (Ioi 0) := by
    have := (hindM 1 one_pos).1
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    norm_num
  -- the Mellin transform of `m` splits
  have hsplit : ∀ s : ℂ, 1 < s.re → mellin (mass g) (s - 1) = mellin rem (s - 1) + c / (s - 1) := by
    intro s hs
    have hw : 0 < (s - 1).re := by simp; linarith
    have hAM := mellinConvergent_mass hg hρ0 hρ hs
    obtain ⟨hiM, hiV⟩ := hindM (s - 1) hw
    have hgM : MellinConvergent rem (s - 1) := by
      refine (hAM.sub hiM).congr_fun (fun y _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, hrem, smul_sub]
    rw [← hiV, mellin, mellin, mellin, ← integral_add hgM hiM]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hrem, smul_sub, sub_add_cancel]
  -- decay of the remainder
  have hg_top : rem =O[atTop] fun t => Real.exp (-(2 * Real.pi) * t) := by
    refine IsBigO.of_bound D ?_
    filter_upwards [eventually_gt_atTop 1] with y hy
    have hy1 : y ∉ Ioc (0 : ℝ) 1 := fun h => (not_le.2 hy) h.2
    have hind0 : ind y = 0 := indicator_of_notMem hy1 _
    rw [show rem y = mass g y - ind y from rfl, hind0, sub_zero, mass, Complex.norm_real,
      Real.norm_of_nonneg (WeylUpper.slice_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 := hD y hy.le
    have h2 : y * Real.exp (-(4 * Real.pi) * y) ≤ Real.exp (-(2 * Real.pi) * y) := by
      have hey : y ≤ Real.exp (2 * Real.pi * y) := by
        have := Real.add_one_le_exp (2 * Real.pi * y)
        nlinarith [Real.pi_gt_three]
      calc y * Real.exp (-(4 * Real.pi) * y) ≤
            Real.exp (2 * Real.pi * y) * Real.exp (-(4 * Real.pi) * y) :=
            mul_le_mul_of_nonneg_right hey (Real.exp_pos _).le
        _ = Real.exp (-(2 * Real.pi) * y) := by rw [← Real.exp_add]; congr 1; ring
    calc _ ≤ D * (y * Real.exp (-(4 * Real.pi) * y)) := h1
      _ ≤ D * Real.exp (-(2 * Real.pi) * y) := mul_le_mul_of_nonneg_left h2 hD0
  have hg_bot : rem =O[𝓝[>] 0] (· ^ (-(-α))) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    have hy1 : y ∈ Ioc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg hy.1.le _)]
    rw [show rem y = mass g y - ind y from rfl, hind, indicator_of_mem hy1, mass, ← ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact hrate y hy.1 hy.2.le
  have hgint : LocallyIntegrableOn rem (Ioi 0) := (hAint.sub hindint).locallyIntegrableOn
  -- the continuation
  set F : ℂ → ℂ := fun s => xi (2 * s) / (2 * s * (2 * s - 1)) * (mellin rem (s - 1) + c / (s - 1))
    with hF
  have hdiffF : ∀ s : ℂ, 1 - α < s.re → s.im ≠ 0 → DifferentiableAt ℂ F s := by
    intro s hs him
    have h0 : s ≠ 0 := fun h => him (by rw [h]; simp)
    have h1 : s ≠ 1 := fun h => him (by rw [h]; simp)
    have h2 : 2 * s - 1 ≠ 0 := fun h => him (by
      have := congrArg Complex.im h; simp at this; linarith)
    have hden : 2 * s * (2 * s - 1) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero h0) h2
    have hmr : DifferentiableAt ℂ (mellin rem) (s - 1) :=
      mellin_differentiableAt_of_isBigO_rpow_exp (by positivity) hgint hg_top hg_bot
        (by simp; linarith)
    have hxi : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s)) s :=
      (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) s
    have hA := DifferentiableAt.comp (g := mellin rem) (f := fun s : ℂ => s - 1) s hmr
      (differentiableAt_id.sub_const 1)
    have hB : DifferentiableAt ℂ (fun s : ℂ => (c : ℂ) / (s - 1)) s :=
      (differentiableAt_const (c : ℂ)).div (by fun_prop) (sub_ne_zero.2 h1)
    have hC : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s) / (2 * s * (2 * s - 1))) s :=
      hxi.div (by fun_prop) hden
    exact hC.mul (hA.add hB)
  have hdiffΛ : ∀ s : ℂ, s.im ≠ 0 → DifferentiableAt ℂ (completedRS g) s := by
    intro s him
    have hmem : s ∈ ({0, 1 / 2, 1} : Set ℂ)ᶜ := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨fun h => him (by rw [h]; simp), fun h => him (by rw [h]; simp),
        fun h => him (by rw [h]; simp)⟩
    have hopen : IsOpen (({0, 1 / 2, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
    exact (differentiableOn_completedRS hg hρ0 hρ).differentiableAt (hopen.mem_nhds hmem)
  have hEqRight : ∀ s : ℂ, 1 < s.re → s.im ≠ 0 → completedRS g s = F s := by
    intro s hs him
    rw [completedRS_eq_mellin hg hρ0 hρ hs him, hsplit s hs]
  -- identity theorem on a quarter plane
  have key : ∀ W : Set ℂ, IsOpen W → IsPreconnected W → (∀ s ∈ W, 1 - α < s.re ∧ s.im ≠ 0) →
      ∀ z₀ ∈ W, 1 < z₀.re → EqOn (completedRS g) F W := by
    intro W hW hWc hWs z₀ hz₀ hz₀re
    have hfΛ : AnalyticOnNhd ℂ (completedRS g) W := DifferentiableOn.analyticOnNhd
      (fun s hs => (hdiffΛ s (hWs s hs).2).differentiableWithinAt) hW
    have hfF : AnalyticOnNhd ℂ F W := DifferentiableOn.analyticOnNhd
      (fun s hs => (hdiffF s (hWs s hs).1 (hWs s hs).2).differentiableWithinAt) hW
    have hev : completedRS g =ᶠ[𝓝 z₀] F := by
      have hopen : IsOpen ({s : ℂ | 1 < s.re} ∩ W) :=
        (isOpen_lt continuous_const continuous_re).inter hW
      filter_upwards [hopen.mem_nhds ⟨hz₀re, hz₀⟩] with s hs
      exact hEqRight s hs.1 (hWs s hs.2).2
    exact hfΛ.eqOn_of_preconnected_of_eventuallyEq hfF hWc hz₀ hev
  have hval : completedRS g s₀ = F s₀ := by
    rcases lt_or_gt_of_ne him₀ with hneg | hpos
    · set W : Set ℂ := {s | 1 - α < s.re ∧ s.im < 0}
      have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_im continuous_const)
      have hWc : IsPreconnected W :=
        ((convex_halfSpace_re_gt (1 - α)).inter (convex_halfSpace_im_lt 0)).isPreconnected
      have hre : (((max (1 - α) 1 + 1 : ℝ) : ℂ) - I).re = max (1 - α) 1 + 1 := by simp
      refine key W hW hWc (fun s hs => ⟨hs.1, hs.2.ne⟩) (((max (1 - α) 1 + 1 : ℝ) : ℂ) - I)
        ⟨?_, by simp⟩ ?_ ⟨hs₀, hneg⟩
      · rw [hre]; linarith [le_max_left (1 - α) 1]
      · rw [hre]; linarith [le_max_right (1 - α) 1]
    · set W : Set ℂ := {s | 1 - α < s.re ∧ 0 < s.im}
      have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_const continuous_im)
      have hWc : IsPreconnected W :=
        ((convex_halfSpace_re_gt (1 - α)).inter (convex_halfSpace_im_gt 0)).isPreconnected
      have hre : (((max (1 - α) 1 + 1 : ℝ) : ℂ) + I).re = max (1 - α) 1 + 1 := by simp
      refine key W hW hWc (fun s hs => ⟨hs.1, hs.2.ne'⟩) (((max (1 - α) 1 + 1 : ℝ) : ℂ) + I)
        ⟨?_, by simp⟩ ?_ ⟨hs₀, hpos⟩
      · rw [hre]; linarith [le_max_left (1 - α) 1]
      · rw [hre]; linarith [le_max_right (1 - α) 1]
  rw [hval, hF]
  simp only [hz, zero_div, zero_mul]

/-- **The zeros of `ζ` and the rate.** If `|m(y) - c| ≤ C y^α` on `(0, 1]`, then every zero `ρ` of `ζ`
with `Re ρ > max(0, 2 - 2α)` has `Λ_g(ρ/2) = 0`. -/
theorem completedRS_half_eq_zero_of_rate (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {α c C : ℝ}
    (hrate : ∀ y : ℝ, 0 < y → y ≤ 1 → |WeylUpper.slice g y - c| ≤ C * y ^ α)
    {z : ℂ} (hζ : riemannZeta z = 0) (hpos : 0 < z.re) (hre : 2 - 2 * α < z.re) :
    completedRS g (z / 2) = 0 := by
  have hxi : xi z = 0 := by
    refine xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.2 ⟨hζ, fun n hn => ?_⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  refine completedRS_eq_zero_of_rate hg hρ0 hρ hrate (by simp; linarith) ?_
  rwa [show 2 * (z / 2) = z by ring]

/-- **A zero visible to `Λ_g` caps the rate**: if `ζ(ρ) = 0`, `Re ρ > 0` and `Λ_g(ρ/2) ≠ 0`, then no bound
`|m(y) - c| ≤ C y^α` on `(0, 1]` holds with `α > 1 - Re ρ/2`. -/
theorem not_rate_of_ne_zero (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {z : ℂ} (hζ : riemannZeta z = 0)
    (hpos : 0 < z.re) (hne : completedRS g (z / 2) ≠ 0) {α : ℝ} (hα : 1 - z.re / 2 < α) (c C : ℝ) :
    ¬ ∀ y : ℝ, 0 < y → y ≤ 1 → |WeylUpper.slice g y - c| ≤ C * y ^ α := fun hrate =>
  hne (completedRS_half_eq_zero_of_rate hg hρ0 hρ hrate hζ hpos (by linarith))

end CuspHR

end GaloisForLFunctions.BlackHoleRingdown
