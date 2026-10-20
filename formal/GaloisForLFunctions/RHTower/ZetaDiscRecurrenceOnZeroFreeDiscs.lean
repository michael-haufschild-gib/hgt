import GaloisForLFunctions.RHTower.EulerProductDiscUniformCarlsonTail
import GaloisForLFunctions.RHTower.UniformEulerTargetDensityOnZeroFreeDiscs
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse

/-!
# Fixed-base recurrence of `ζ` on zero-free discs, and the local form of Bagchi's criterion

Bagchi's fixed-base recurrence of `ζ` on a closed disc `K` of the right half-strip
(`ZetaDiscStronglyRecurrentOn K`: every `ε`-self-return set has positive lower density) holds
unconditionally when `ζ` has no zero on a slightly larger disc:

* the Euler-target heights, at which `E_y(· + iτ)` is within `ε/2` of `ζ` on `K`, have lower
  density at least `c` uniformly in `y ≥ y₁` (universality of the finite Euler products);
* the Euler tail law makes the heights at which `|ζ − E_y| ≥ ε/2` somewhere on `K` of upper
  density at most `c/2` for `y` large;
* the difference of the two sets lies in the `ε`-self-return set of `ζ`.

Through the equivalence of disc recurrence with uniform head-target density, the Abel base-point
pole is paid on every small zero-free disc.  Since self-returns around an off-line zero have
density zero, the Riemann hypothesis is equivalent to local disc recurrence at every point of the
strip (`riemannHypothesis_iff_forall_exists_zetaDiscStronglyRecurrentOn`).
-/

open Complex Filter Topology Metric MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## Euler-target heights that are tail-good are self-return heights -/

theorem eulerTargetReturnSet_diff_eulerDiscTailBadSet_subset_zetaReturnSet (y : ℕ) (c : ℂ)
    (r ε ε' : ℝ) :
    eulerTargetReturnSet y riemannZeta (closedBall c r) ε \ eulerDiscTailBadSet y c r ε' ⊆
      zetaReturnSet (closedBall c r) (ε' + ε) := by
  rintro τ ⟨htarget, hgood⟩ z hz
  have htail : ‖eulerTailFun y (z + τ * I)‖ < ε' := by
    by_contra hcon
    exact hgood ⟨z, hz, not_lt.mp hcon⟩
  have hh := htarget z hz
  have hid : riemannZeta (z + τ * I) - riemannZeta z =
      eulerTailFun y (z + τ * I) + (eulerPhaseProduct y 1 (z + τ * I) - riemannZeta z) := by
    unfold eulerTailFun
    ring
  rw [hid]
  exact (norm_add_le _ _).trans_lt (add_lt_add htail hh)

/-! ## Recurrence on zero-free discs -/

/-- **Fixed-base recurrence of `ζ` on a zero-free disc.**  In the disc coordinate `z = z₀ + ρ q`
with `K = {|z − z₀| ≤ ρ r₁}`: if `ζ` has no zero on `|z − z₀| < ρ R₂`, `R₂ > 1`, inside `Re z < 1`,
and `K` has the margins `1/2 < Re z₀ − 2ρ r₁`, `Re z₀ + 2ρ r₁ < 1`, then `ζ` is strongly recurrent
on `K`. -/
theorem zetaDiscStronglyRecurrentOn_of_zeroFree (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : 3 * ρ < 1 - z₀.re)
    {R₂ : ℝ} (hR₂ : 1 < R₂) (hR₂1 : z₀.re + ρ * R₂ < 1)
    (hζ : ∀ z ∈ ball z₀ (ρ * R₂), riemannZeta z ≠ 0)
    {r₁ : ℝ} (hr₁0 : 0 < r₁) (hr₁ : r₁ < 1)
    (h0 : 1 / 2 < z₀.re - 2 * (ρ * r₁)) (h1 : z₀.re + 2 * (ρ * r₁) < 1) :
    ZetaDiscStronglyRecurrentOn (closedBall z₀ (ρ * r₁)) := by
  intro ε hε
  obtain ⟨c, hc, y₁, hy₁⟩ := exists_uniform_pos_density_eulerTargetReturnSet_zeta z₀ hρ hσ hρσ₁
    hρσ₂ hR₂ hR₂1 hζ hr₁0.le hr₁ (half_pos hε)
  have hbad := eventually_eventually_volume_eulerDiscTailBadSet_le (by positivity : 0 < ρ * r₁)
    h0 h1 (half_pos hε) (half_pos hc)
  obtain ⟨y, hy, hyb⟩ := ((eventually_ge_atTop y₁).and hbad).exists
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [hy₁ y hy, hyb, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub := eulerTargetReturnSet_diff_eulerDiscTailBadSet_subset_zetaReturnSet y z₀ (ρ * r₁)
    (ε / 2) (ε / 2)
  rw [add_halves] at hsub
  exact (ofReal_half_le_volume_diff_inter hc hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub))

/-- Strong recurrence passes to subsets. -/
theorem zetaDiscStronglyRecurrentOn_mono {K K' : Set ℂ} (h : K' ⊆ K)
    (hK : ZetaDiscStronglyRecurrentOn K) : ZetaDiscStronglyRecurrentOn K' := by
  intro ε hε
  obtain ⟨κ, hκ, hT⟩ := hK ε hε
  refine ⟨κ, hκ, hT.mono fun T hT => hT.trans (measure_mono (inter_subset_inter_left _ ?_))⟩
  intro τ hτ z hz
  exact hτ z (h hz)

/-- **Every locally zero-free point of the strip carries a recurrent disc**, with the margins
`1/2 < Re z₀ − 2r` and `Re z₀ + 2r < 1`. -/
theorem exists_zetaDiscStronglyRecurrentOn_of_zeroFree {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) {R : ℝ} (hR : 0 < R) (hζ : ∀ z ∈ ball z₀ R, riemannZeta z ≠ 0) :
    ∃ r > 0, 1 / 2 < z₀.re - 2 * r ∧ z₀.re + 2 * r < 1 ∧
      ZetaDiscStronglyRecurrentOn (closedBall z₀ r) := by
  set ρ : ℝ := min (R / 4) (min ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 8)) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hρR : ρ ≤ R / 4 := min_le_left _ _
  have hρ1 : ρ ≤ (z₀.re - 1 / 2) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ (1 - z₀.re) / 8 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ * (1 / 2), by positivity, by linarith, by linarith, ?_⟩
  exact zetaDiscStronglyRecurrentOn_of_zeroFree z₀ hρ h1.le (by linarith) (by linarith)
    (R₂ := 2) (by norm_num) (by linarith) (fun z hz => hζ z (ball_subset_ball (by linarith) hz))
    (by norm_num) (by norm_num) (by linarith) (by linarith)

/-- **The Abel base-point pole is paid on zero-free discs**: around every locally zero-free point
of the strip there is a disc on which the head-target heights have uniformly positive lower
density. -/
theorem exists_headTargetUniformlyDense_of_zeroFree {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) {R : ℝ} (hR : 0 < R) (hζ : ∀ z ∈ ball z₀ R, riemannZeta z ≠ 0) :
    ∃ r > 0, 1 / 2 < z₀.re - 2 * r ∧ z₀.re + 2 * r < 1 ∧
      HeadTargetUniformlyDense (closedBall z₀ r) := by
  obtain ⟨r, hr, hr0, hr1, hrec⟩ := exists_zetaDiscStronglyRecurrentOn_of_zeroFree h1 h2 hR hζ
  exact ⟨r, hr, hr0, hr1,
    (zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense hr hr0 hr1).mp hrec⟩

/-! ## The local form of Bagchi's criterion -/

/-- Under RH, `ζ` has no zero on the open disc of radius `Re z₀ − 1/2` about `z₀`. -/
theorem riemannZeta_ne_zero_on_ball_of_riemannHypothesis (hRH : RiemannHypothesis) (z₀ : ℂ) :
    ∀ z ∈ ball z₀ (z₀.re - 1 / 2), riemannZeta z ≠ 0 := by
  intro z hz
  refine (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) z ?_
  rw [mem_ball, dist_eq_norm] at hz
  have h := abs_le.mp (Complex.abs_re_le_norm (z - z₀))
  rw [Complex.sub_re] at h
  linarith [h.1]

/-- **Self-returns around an off-line zero exclude local recurrence.** -/
theorem riemannZeta_ne_zero_of_exists_zetaDiscStronglyRecurrentOn {ρ₀ : ℂ} (h1 : 1 / 2 < ρ₀.re)
    (h2 : ρ₀.re < 1) (h : ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall ρ₀ r)) :
    riemannZeta ρ₀ ≠ 0 := by
  intro hρ0
  obtain ⟨r, hr, hrec⟩ := h
  obtain ⟨r', hr', hr'r, hr2, hr3, m, hm0, hm⟩ := exists_zetaIsolatingDisc_le h1 h2 hr
  have hrec' : ZetaDiscStronglyRecurrentOn (closedBall ρ₀ r') :=
    zetaDiscStronglyRecurrentOn_mono (closedBall_subset_closedBall hr'r) hrec
  obtain ⟨κ, hκ, hfreq⟩ := hrec' (m / 2) (half_pos hm0)
  have hzero := eventually_volume_zetaReturnSet_le_of_zero hr' hr2 hr3 hρ0 hm le_rfl (half_pos hκ)
  obtain ⟨T, hT1, hT2, hT0⟩ := (hfreq.and (hzero.and (eventually_gt_atTop (0 : ℝ)))).exists
  have h := hT1.trans hT2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  nlinarith [mul_pos hκ hT0]

/-- **Local Bagchi criterion.**  The Riemann hypothesis holds if and only if every point of the
right half-strip carries a closed disc on which `ζ` is strongly recurrent. -/
theorem riemannHypothesis_iff_forall_exists_zetaDiscStronglyRecurrentOn :
    RiemannHypothesis ↔ ∀ z₀ : ℂ, 1 / 2 < z₀.re → z₀.re < 1 →
      ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall z₀ r) := by
  constructor
  · intro hRH z₀ h1 h2
    obtain ⟨r, hr, -, -, hrec⟩ := exists_zetaDiscStronglyRecurrentOn_of_zeroFree h1 h2
      (by linarith) (riemannZeta_ne_zero_on_ball_of_riemannHypothesis hRH z₀)
    exact ⟨r, hr, hrec⟩
  · intro h
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro z₀ h1 h2
    exact riemannZeta_ne_zero_of_exists_zetaDiscStronglyRecurrentOn h1 h2 (h z₀ h1 h2)

/-- **Local Bagchi criterion, head-target form.**  The Riemann hypothesis holds if and only if every
point of the right half-strip carries a closed disc, with the margins `1/2 < Re z₀ − 2r` and
`Re z₀ + 2r < 1`, on which the head-target heights have uniformly positive lower density. -/
theorem riemannHypothesis_iff_forall_exists_headTargetUniformlyDense :
    RiemannHypothesis ↔ ∀ z₀ : ℂ, 1 / 2 < z₀.re → z₀.re < 1 →
      ∃ r > 0, 1 / 2 < z₀.re - 2 * r ∧ z₀.re + 2 * r < 1 ∧
        HeadTargetUniformlyDense (closedBall z₀ r) := by
  constructor
  · intro hRH z₀ h1 h2
    exact exists_headTargetUniformlyDense_of_zeroFree h1 h2 (by linarith)
      (riemannZeta_ne_zero_on_ball_of_riemannHypothesis hRH z₀)
  · intro h
    rw [riemannHypothesis_iff_forall_exists_zetaDiscStronglyRecurrentOn]
    intro z₀ h1 h2
    obtain ⟨r, hr, hr0, hr1, hU⟩ := h z₀ h1 h2
    exact ⟨r, hr, (zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense hr hr0 hr1).mpr hU⟩

end RHTower
