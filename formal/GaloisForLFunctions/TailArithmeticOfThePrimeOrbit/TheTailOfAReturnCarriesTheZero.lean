import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMissingInputOfTransport
import GaloisForLFunctions.RHTower.EulerProductDiscUniformCarlsonTail

/-!
# The tail of a return carries the zero

Cut `ζ` at `y`: `ζ = E_y · (ζ M_y)`, with the head `E_y = Π_{p≤y}(1 − p^{−s})^{−1}` and the Euler mollifier
`M_y = Π_{p≤y}(1 − p^{−s})`. On `Re s > 0` the head never vanishes (`eulerMollifier_ne_zero`), so the zeros of `ζ` are
exactly the zeros of the **tail** `ζ M_y` (`eulerTail_eq_zero_iff`), at every cut.

* **The tail of a bounded return** (`IsPhaseReturn.tendsto_eulerTail`). Along a phase return the head converges to the
  head (`IsPhaseReturn.tendsto_eulerMollifier`): its phases return. With bounded translates on a domain joining a point to
  `Re s > 1`, `ζ(s + iτ_j) → ζ(s)` there, so the tail converges to `ζ M_y`, which vanishes at the zero: the zero is
  carried by the tail at every cut, and the head stays at its nonzero value (`IsPhaseReturn.tendsto_zero_tail`). The
  tail-bad amplitude `|ζ − E_y|` at the transported zero tends to `|E_y(ρ)|`.
* **A return at a zero is tail-bad at every cut** (`zetaReturnSet_subset_eulerDiscTailBadSet`). Let `|ζ| ≥ m` on a circle
  about a zero `ρ`. If `ζ(· + iτ)` returns to `ζ` within `m/2` on the disc, the translate has a zero inside. If it were
  also tail-good, `|ζ − E_y| < m/4` on the disc, then `|E_y| > m/4` on the circle and, by the maximum principle for the
  entire function `M_y = 1/E_y`, `|E_y| ≥ m/4` inside, while `|E_y| = |ζ − E_y| < m/4` at the zero. So every such return
  is a tail-bad height, for every `y`, with a tolerance `m/4` independent of `y`.
* **So returns at a zero have density zero** (`eventually_volume_zetaReturnSet_le`), by the Euler tail law: the tail-bad
  heights have density tending to zero with the cut.

Typical aligned heights are tail-good: `ζ(· + iτ) ≈ E_y(· + iτ)`, which is zero-free. A bounded return at a right zero
is a height where the tail cancels the head at the zero; it must be tail-bad at every cut.
-/

open Complex Filter Topology Metric Set Finset MeasureTheory

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- The primes up to `y`, as in the Euler head. -/
abbrev headPrimes (y : ℕ) : Finset ℕ := (range (y + 1)).filter Nat.Prime

/-- The Euler mollifier `M_y(s) = Π_{p≤y} (1 − p^{−s})`. -/
def eulerMollifier (y : ℕ) (s : ℂ) : ℂ := ∏ n ∈ headPrimes y, (1 - (n : ℂ) ^ (-s))

/-- The tail `ζ M_y = ζ/E_y`. -/
def eulerTail (y : ℕ) (s : ℂ) : ℂ := riemannZeta s * eulerMollifier y s

theorem eulerHead_eq_inv (y : ℕ) (s : ℂ) : RHTower.eulerHead y s = (eulerMollifier y s)⁻¹ := by
  rw [RHTower.eulerHead, eulerMollifier, Finset.prod_inv_distrib]

theorem one_sub_cpow_ne_zero {n : ℕ} (hn : 2 ≤ n) {s : ℂ} (hs : 0 < s.re) : 1 - (n : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (n : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s).re :=
    Complex.norm_natCast_cpow_of_pos (by omega) (-s)
  rw [h1, norm_one, Complex.neg_re] at h2
  have h3 : (n : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by linarith)
  linarith

theorem eulerMollifier_ne_zero (y : ℕ) {s : ℂ} (hs : 0 < s.re) : eulerMollifier y s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun n hn => one_sub_cpow_ne_zero (Finset.mem_filter.mp hn).2.two_le hs

theorem eulerHead_ne_zero (y : ℕ) {s : ℂ} (hs : 0 < s.re) : RHTower.eulerHead y s ≠ 0 := by
  rw [eulerHead_eq_inv]
  exact inv_ne_zero (eulerMollifier_ne_zero y hs)

/-- **The zeros are the tail's.** -/
theorem eulerTail_eq_zero_iff (y : ℕ) {s : ℂ} (hs : 0 < s.re) : eulerTail y s = 0 ↔ riemannZeta s = 0 := by
  unfold eulerTail
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (eulerMollifier_ne_zero y hs)
  · intro h
    rw [h, zero_mul]

theorem differentiable_eulerMollifier (y : ℕ) : Differentiable ℂ (eulerMollifier y) := by
  have hfun : eulerMollifier y = ∏ n ∈ headPrimes y, fun s : ℂ => (1 - (n : ℂ) ^ (-s)) := by
    funext s
    rw [eulerMollifier, Finset.prod_apply]
  rw [hfun, ← differentiableOn_univ]
  refine DifferentiableOn.finsetProd fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_filter.mp hn).2.two_le
    exact_mod_cast (by omega : n ≠ 0)
  exact (differentiableOn_const _).sub (differentiableOn_id.neg.const_cpow (Or.inl hn0))

/-! ## Along a return the head returns -/

open ArithmeticAuxiliaryDynamics

theorem cpow_neg_add_mul_I {n : ℕ} (hn : n ≠ 0) (s : ℂ) (τ : ℝ) :
    (n : ℂ) ^ (-(s + τ * I)) = (n : ℂ) ^ (-s) * (n : ℂ) ^ (-((τ : ℂ) * I)) := by
  rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn)]

/-- **The head returns along a phase return.** -/
theorem IsPhaseReturn.tendsto_eulerMollifier {τ : ℕ → ℝ} (h : IsPhaseReturn τ) (y : ℕ) (s : ℂ) :
    Tendsto (fun j => eulerMollifier y (s + τ j * I)) atTop (𝓝 (eulerMollifier y s)) := by
  unfold eulerMollifier
  refine tendsto_finsetProd _ fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_filter.mp hn).2.two_le
  have hn0 : n ≠ 0 := by omega
  have hphase : Tendsto (fun j => (n : ℂ) ^ (-((τ j : ℂ) * I))) atTop (𝓝 1) := by
    have h1 := h.phase (n - 1)
    have hcast : (((n - 1 : ℕ) : ℝ) + 1 : ℝ) = (n : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have h2 : (fun j => phaseDefect τ j (n - 1)) = fun j => (n : ℂ) ^ (-((τ j : ℂ) * I)) - 1 := by
      funext j
      rw [phaseDefect, hcast]
      push_cast
      rfl
    rw [h2] at h1
    have := h1.add_const 1
    simpa using this
  have h3 : Tendsto (fun j => 1 - (n : ℂ) ^ (-s) * (n : ℂ) ^ (-((τ j : ℂ) * I))) atTop
      (𝓝 (1 - (n : ℂ) ^ (-s) * 1)) := (hphase.const_mul _).const_sub _
  rw [mul_one] at h3
  refine h3.congr fun j => ?_
  rw [cpow_neg_add_mul_I hn0]

/-- **The tail of a bounded return** converges to the tail. -/
theorem IsPhaseReturn.tendsto_eulerTail {τ : ℕ → ℝ} (h : IsPhaseReturn τ) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hbd : TranslatesBoundedOn τ U) (y : ℕ) {s : ℂ} (hs : s ∈ U) :
    Tendsto (fun j => eulerTail y (s + τ j * I)) atTop (𝓝 (eulerTail y s)) := by
  have hζ := (h.tendstoLocallyUniformlyOn hUo hUc hUim hs₀ hs₀1 hbd).tendsto_at hs
  exact hζ.mul (h.tendsto_eulerMollifier y s)

/-- **The tail carries the zero, the head does not.** At a zero `ρ` of `ζ` in the domain, with `Re ρ > 0`, the tail of
the translate tends to `0` at every cut while the head tends to `E_y(ρ) ≠ 0`; the tail-bad amplitude `|ζ − E_y|` at the
transported point tends to `|E_y(ρ)|`. -/
theorem IsPhaseReturn.tendsto_zero_tail {τ : ℕ → ℝ} (h : IsPhaseReturn τ) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hbd : TranslatesBoundedOn τ U) (y : ℕ) {ρ : ℂ} (hρU : ρ ∈ U) (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) :
    Tendsto (fun j => eulerTail y (ρ + τ j * I)) atTop (𝓝 0) ∧
      Tendsto (fun j => RHTower.eulerHead y (ρ + τ j * I)) atTop (𝓝 (RHTower.eulerHead y ρ)) ∧
      RHTower.eulerHead y ρ ≠ 0 ∧
      Tendsto (fun j => ‖RHTower.eulerTailFun y (ρ + τ j * I)‖) atTop (𝓝 ‖RHTower.eulerHead y ρ‖) := by
  have ht := h.tendsto_eulerTail hUo hUc hUim hs₀ hs₀1 hbd y hρU
  rw [show eulerTail y ρ = 0 from (eulerTail_eq_zero_iff y hρ0).mpr hρ] at ht
  have hM := h.tendsto_eulerMollifier y ρ
  have hhead : Tendsto (fun j => RHTower.eulerHead y (ρ + τ j * I)) atTop (𝓝 (RHTower.eulerHead y ρ)) := by
    simp_rw [eulerHead_eq_inv]
    exact hM.inv₀ (eulerMollifier_ne_zero y hρ0)
  have hζ := (h.tendstoLocallyUniformlyOn hUo hUc hUim hs₀ hs₀1 hbd).tendsto_at hρU
  rw [hρ] at hζ
  refine ⟨ht, hhead, eulerHead_ne_zero y hρ0, ?_⟩
  have hdiff := (hζ.sub hhead).norm
  rw [zero_sub, norm_neg] at hdiff
  refine hdiff.congr fun j => ?_
  rw [RHTower.eulerTailFun_eq]

/-! ## A return at a zero is tail-bad at every cut -/

/-- **A return at a zero is tail-bad at every cut.** -/
theorem zetaReturnSet_subset_eulerDiscTailBadSet {ρ : ℂ} {r m : ℝ} (hr : 0 < r)
    (hpos : ∀ s ∈ closedBall ρ r, 0 < s.re) (hre : ∀ s ∈ closedBall ρ r, s.re < 1) (hρ : riemannZeta ρ = 0)
    (hm : ∀ z ∈ sphere ρ r, m ≤ ‖riemannZeta z‖) (y : ℕ) :
    RHTower.zetaReturnSet (closedBall ρ r) (m / 2) ⊆ RHTower.eulerDiscTailBadSet y ρ r (m / 4) := by
  intro τ hτ
  by_contra hgood
  have hgood' : ∀ z ∈ closedBall ρ r, ‖RHTower.eulerTailFun y (z + τ * I)‖ < m / 4 := by
    intro z hz
    by_contra hc
    exact hgood ⟨z, hz, not_lt.mp hc⟩
  have hm0 : 0 < m := by
    have := hτ ρ (mem_closedBall_self hr.le)
    have h0 := norm_nonneg (riemannZeta (ρ + τ * I) - riemannZeta ρ)
    linarith
  obtain ⟨z₀, hz₀, hzero⟩ := RHTower.exists_zero_of_mem_zetaReturnSet hr hre hρ hm hτ
  set f : ℂ → ℂ := fun z => eulerMollifier y (z + τ * I) with hf
  have hshift : ∀ z ∈ closedBall ρ r, 0 < (z + τ * I).re := fun z hz => by
    have : (z + τ * I).re = z.re := by simp
    rw [this]
    exact hpos z hz
  -- On the circle the head is larger than `m/4`, so `f = 1/E_y` is at most `4/m`.
  have hsphere : ∀ z ∈ sphere ρ r, ‖f z‖ ≤ 4 / m := by
    intro z hz
    have hzc : z ∈ closedBall ρ r := sphere_subset_closedBall hz
    have h1 : m / 2 ≤ ‖riemannZeta (z + τ * I)‖ := by
      have h2 := hτ z hzc
      have h3 := hm z hz
      have h4 := norm_sub_norm_le (riemannZeta z) (riemannZeta z - riemannZeta (z + τ * I))
      rw [sub_sub_cancel] at h4
      rw [norm_sub_rev] at h2
      linarith
    have h5 : m / 4 < ‖RHTower.eulerHead y (z + τ * I)‖ := by
      have h6 := hgood' z hzc
      rw [RHTower.eulerTailFun_eq] at h6
      have h7 := norm_sub_norm_le (riemannZeta (z + τ * I)) (riemannZeta (z + τ * I) - RHTower.eulerHead y (z + τ * I))
      rw [sub_sub_cancel] at h7
      linarith
    have hfz : ‖f z‖ = ‖RHTower.eulerHead y (z + τ * I)‖⁻¹ := by
      rw [hf, eulerHead_eq_inv, norm_inv, inv_inv]
    rw [hfz]
    have hpos' : 0 < ‖RHTower.eulerHead y (z + τ * I)‖ := by linarith
    rw [inv_le_comm₀ hpos' (by positivity)]
    rw [inv_div]
    exact h5.le
  -- The maximum principle for the entire function `f`.
  have hdiff : Differentiable ℂ f := (differentiable_eulerMollifier y).comp (differentiable_id.add_const _)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := ρ) (r := r))
    hdiff.diffContOnCl (C := 4 / m) (by rw [frontier_ball ρ hr.ne']; exact hsphere)
    (z := z₀) (subset_closure hz₀)
  -- At the zero the head is the tail, smaller than `m/4`.
  have hz₀c : z₀ ∈ closedBall ρ r := ball_subset_closedBall hz₀
  have hsmall := hgood' z₀ hz₀c
  rw [RHTower.eulerTailFun_eq, hzero, zero_sub, norm_neg] at hsmall
  have hne := eulerHead_ne_zero y (hshift z₀ hz₀c)
  have hpos0 : 0 < ‖RHTower.eulerHead y (z₀ + τ * I)‖ := norm_pos_iff.mpr hne
  have hfz₀ : ‖f z₀‖ = ‖RHTower.eulerHead y (z₀ + τ * I)‖⁻¹ := by
    rw [hf, eulerHead_eq_inv, norm_inv, inv_inv]
  rw [hfz₀] at hmax
  have : 4 / m < ‖RHTower.eulerHead y (z₀ + τ * I)‖⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hpos0, inv_div]
    exact hsmall
  linarith

/-- **Returns at a right zero have density zero.** Every zero `ρ` with `½ < Re ρ < 1` has an isolating disc of radius
`r` and a tolerance `m/2` at which the return heights are tail-bad at every cut, and so occupy at most `δ T` of `[0, T]`
for every `δ > 0` and all large `T`. -/
theorem exists_returns_tailBad_and_rare {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1) :
    ∃ r m : ℝ, 0 < r ∧ 0 < m ∧
      (∀ y : ℕ, RHTower.zetaReturnSet (closedBall ρ r) (m / 2) ⊆ RHTower.eulerDiscTailBadSet y ρ r (m / 4)) ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ T : ℝ in atTop,
        volume (RHTower.zetaReturnSet (closedBall ρ r) (m / 2) ∩ Icc 0 T) ≤ ENNReal.ofReal (δ * T) := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h2; simp at h2
  set r₀ := min ((ρ.re - 1 / 2) / 3) ((1 - ρ.re) / 3) with hr₀
  have hr₀pos : 0 < r₀ := lt_min (by linarith) (by linarith)
  obtain ⟨r, m, hr, hrr, -, hm0, hm⟩ := exists_isolating_circle hρ1 hρ (U := univ) Filter.univ_mem hr₀pos
  have hr1 : r < (ρ.re - 1 / 2) / 3 := lt_of_lt_of_le hrr (min_le_left _ _)
  have hr2 : r < (1 - ρ.re) / 3 := lt_of_lt_of_le hrr (min_le_right _ _)
  have hball : ∀ s ∈ closedBall ρ r, ρ.re - r ≤ s.re ∧ s.re ≤ ρ.re + r := by
    intro s hs
    have h := abs_re_le_norm (s - ρ)
    rw [mem_closedBall, dist_eq_norm] at hs
    rw [sub_re] at h
    constructor <;> linarith [abs_le.mp (h.trans hs)]
  have hpos : ∀ s ∈ closedBall ρ r, 0 < s.re := fun s hs => by linarith [(hball s hs).1]
  have hre : ∀ s ∈ closedBall ρ r, s.re < 1 := fun s hs => by linarith [(hball s hs).2]
  have hsub := fun y => zetaReturnSet_subset_eulerDiscTailBadSet hr hpos hre hρ hm y
  refine ⟨r, m, hr, hm0, hsub, fun δ hδ => ?_⟩
  obtain ⟨y, hy⟩ := (RHTower.eventually_eventually_volume_eulerDiscTailBadSet_le hr (by linarith) (by linarith)
    (ε := m / 4) (by positivity) hδ).exists
  filter_upwards [hy] with T hT
  exact (measure_mono (Set.inter_subset_inter_left _ (hsub y))).trans hT

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
