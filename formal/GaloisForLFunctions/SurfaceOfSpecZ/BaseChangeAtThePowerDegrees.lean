import GaloisForLFunctions.SurfaceOfSpecZ.TheTraceZetaFunctionAtThePowerDegrees
import GaloisForLFunctions.RHTower.LandauRelativeRigidity

/-!
# Base change: the traces at the degrees `nᵏ` decide RH from one side

On a curve over `𝔽_q`, the counts over the extensions `𝔽_{q^{kn}}` determine the eigenvalues `α^k` and
hence `|α|`: RH is invariant under base change. Over `ℤ` the gap method of `SparseDegreesDecideRH`
loses this: the degrees `nᵏ` have gaps `x^{1−1/k}`, which bound the width only by `½ − 1/k`
(`HasseWeilAtThePrimeDegreesBoundsTheWidth`). The multiplicative structure restores it.

**Theorem** (`riemannHypothesis_iff_bddBelow_powerDegrees`). For every `k ≥ 1` there is `r₀` such that
for every box spline `U_1^{⋆(r+1)}`, `r ≥ r₀`: RH holds iff the traces at the degrees `nᵏ` are bounded
below, `2 Re S(k log n) ≥ −K` for all `n ≥ 1` — an upper bound on the smoothed point counts of the
planes `⟨Γ_1, Γ_{nᵏ}⟩` only.

**Proof.** The Dirichlet series of `2 Re S(k log n) + K + 1 ≥ 1` is `Z_k(s) + (K + 1)ζ(s)`
(`TheTraceZetaFunctionAtThePowerDegrees`), continued to `1 < Re s < 2 + k/2` off the poles `1 + kz`.
None of these is real, since `ζ` has no real zero in the strip, so Landau's theorem for nonnegative
Dirichlet series (`RHTower.gdSeries_no_continuation_at_abscissa`) puts the abscissa at `1`. An
off-line zero `½ + z₀`, rightmost on its horizontal line, gives a pole `1 + kz₀` of residue
`e_{z₀} ≠ 0` with `Re > 1`; along the ray `1 + kz₀ + t` the convergent series stays bounded while
`e_{z₀}ζ(1 + t)` blows up.
-/

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open GaloisForLFunctions.HTGeometry

/-! ### The spline of order `r` -/

theorem traceCoeff_im_ne_zero {r : ℕ} {x : ℂ} (hx : traceCoeff r x ≠ 0) : x.im ≠ 0 := by
  intro him
  rcases mem_of_evenCoeff_ne_zero hx with h | h
  · exact not_mem_carrier_of_im_eq_zero h (by simp [him])
  · exact not_mem_carrier_of_im_eq_zero h (by simp [him])

theorem traceCoeff_sees {r : ℕ} (hr : 3 ≤ r) {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    (hre : 1 / 2 < ρ.re) : traceCoeff r (ρ - 1 / 2) ≠ 0 :=
  evenCoeff_sub_half_ne_zero_of_conj_symm zetaZeroConfig (contDiff_boxSpline_two hr).continuous
    (hasCompactSupport_boxSpline r) (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
    (paperFT_boxSpline_ne_zero one_pos r (im_gammaOf_ne_zero (by linarith)))

/-- `|2 Re S(v)| ≤ 2L e^{v/2}` for `v ≥ 0`, `L = Σ |F(z)|`. -/
theorem abs_two_re_lagStructure_le {r : ℕ} (hr : 3 ≤ r) {v : ℝ} (hv : 0 ≤ v) :
    |2 * (lagStructure zetaZeroConfig (boxSpline 1 r) v).re| ≤
      2 * (∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z‖) * Real.exp (v / 2) := by
  have hb := contDiff_boxSpline_two hr
  have hbs := boxSpline_support (r := 1) one_pos r
  obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig hb hbs v
  have hle : ‖lagStructure zetaZeroConfig (boxSpline 1 r) v‖ ≤
      (∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z‖) * Real.exp (v / 2) := by
    rw [he, ← tsum_mul_right]
    refine (norm_tsum_le_tsum_norm hs.norm).trans (Summable.tsum_le_tsum
      (fun z => norm_lagCoeff_mul_exp_le z (le_of_eq (abs_of_nonneg hv))) hs.norm
      ((summable_norm_lagCoeff zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
        hb hbs).mul_right _))
  have := Complex.abs_re_le_norm (lagStructure zetaZeroConfig (boxSpline 1 r) v)
  rw [abs_mul, abs_two]
  nlinarith

/-! ### The nonnegative Dirichlet series -/

section Landau

variable {r k : ℕ} (K : ℝ)

/-- The coefficients `2 Re S(k log n) + K + 1` at `n = j + 1`. -/
def powerCoeff (r k : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  2 * (lagStructure zetaZeroConfig (boxSpline 1 r) (k * Real.log (j + 1))).re + K + 1

/-- The frequencies `log n`. -/
def powerFreq (j : ℕ) : ℝ := Real.log (j + 1)

theorem powerFreq_nonneg (j : ℕ) : 0 ≤ powerFreq j :=
  Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j])

theorem cexp_neg_mul_powerFreq (s : ℂ) (j : ℕ) :
    Complex.exp (-(s * (powerFreq j : ℂ))) = ((j : ℂ) + 1) ^ (-s) := by
  rw [natCast_add_one_cpow_eq, powerFreq]; congr 1; ring

theorem real_exp_neg_mul_powerFreq (σ : ℝ) (j : ℕ) :
    Real.exp (-(σ * powerFreq j)) = ((j : ℝ) + 1) ^ (-σ) := by
  rw [Real.rpow_def_of_pos (by positivity), powerFreq]; ring_nf

/-- The candidate continuation `Z_k(s) + (K + 1) ζ(s)`. -/
def powerZeta (r k : ℕ) (K : ℝ) (s : ℂ) : ℂ :=
  traceZetaOf (traceCoeff r) k s + ((K + 1 : ℝ) : ℂ) * riemannZeta s

theorem gdSeries_powerCoeff_eq (hr : 3 ≤ r) {s : ℂ} (hs : 1 + k / 2 < s.re) :
    gdSeries (powerCoeff r k K) powerFreq s = powerZeta r k K s := by
  obtain ⟨hsum, heq⟩ := traceDirichlet_eq hr k hs
  have hs1 : 1 < s.re := by linarith [show (0 : ℝ) ≤ (k : ℝ) / 2 by positivity]
  have hz : Summable fun n : ℕ => ((n : ℂ) + 1) ^ (-s) := by
    have := Complex.summable_one_div_nat_cpow.mpr hs1
    have h2 := (summable_nat_add_iff 1).mpr this
    refine h2.congr fun n => ?_
    push_cast
    rw [Complex.cpow_neg, one_div]
  unfold gdSeries powerZeta
  have hterm : ∀ j : ℕ, ((powerCoeff r k K j : ℝ) : ℂ) * Complex.exp (-(s * (powerFreq j : ℂ))) =
      ((2 * (lagStructure zetaZeroConfig (boxSpline 1 r) (k * Real.log (j + 1))).re : ℝ) : ℂ) *
        ((j : ℂ) + 1) ^ (-s) + ((K + 1 : ℝ) : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
    intro j
    rw [cexp_neg_mul_powerFreq, powerCoeff]
    push_cast
    ring
  rw [tsum_congr hterm, hsum.tsum_add (hz.mul_left _), heq, tsum_mul_left,
    zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  congr 2
  refine tsum_congr fun n => ?_
  rw [Complex.cpow_neg, one_div]

end Landau

/-! ### Analytic tools -/

/-- `Z_k + (K + 1)ζ` is holomorphic on a ball around every non-pole `s₀`, `1 < Re s₀ < 2 + k/2`. -/
theorem exists_ball_differentiableOn_powerZeta {r N k : ℕ} (hr : 3 ≤ r) (hN : N + 2 ≤ 2 * (r + 1))
    (hk : 1 ≤ k) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ σ t : ℝ, |σ| ≤ 3 + k → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N) (K : ℝ)
    {s₀ : ℂ} (hs1 : 1 < s₀.re) (hs2 : s₀.re < 2 + k / 2)
    (hpole : ∀ z, traceCoeff r z ≠ 0 → s₀ ≠ 1 + k * z) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (powerZeta r k K) (ball s₀ ρ) := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set P : Set ℂ := {z | traceCoeff r z ≠ 0 ∧ |(k : ℝ) * z.im - s₀.im| ≤ 1} with hPdef
  have hP : P.Finite := by
    refine (finite_traceCoeff_height r (|s₀.im| + 1)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hz0, ?_⟩
    have hkz : |(k : ℝ) * z.im| ≤ |s₀.im| + 1 := by
      have := abs_le.mp hzim
      rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)] at hkz
    calc |z.im| ≤ k * |z.im| := le_mul_of_one_le_left (abs_nonneg _) hk'
      _ ≤ _ := hkz
  obtain ⟨δ, hδ0, hδ1, hδP⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ P, δ ≤ ‖s₀ - (1 + k * z)‖ := by
    rcases P.eq_empty_or_nonempty with hPe | hPne
    · exact ⟨1, one_pos, le_rfl, by simp [hPe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hP.toFinset.exists_min_image (fun z => ‖s₀ - (1 + k * z)‖)
        (by simpa using hPne)
      have hz₁' := hP.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 + k * z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hP.mem_toFinset.mpr hz))⟩
  set ρ := min δ (min (s₀.re - 1) (2 + k / 2 - s₀.re)) / 2 with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]; exact half_pos (lt_min hδ0 (lt_min (by linarith) (by linarith)))
  have hρδ : ρ < δ := by
    rw [hρdef]; have := min_le_left δ (min (s₀.re - 1) (2 + k / 2 - s₀.re)); linarith
  have hρ1 : ρ < s₀.re - 1 := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (2 + k / 2 - s₀.re))).trans (min_le_left _ _)
    linarith
  have hρ2 : ρ < 2 + k / 2 - s₀.re := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (2 + k / 2 - s₀.re))).trans (min_le_right _ _)
    linarith
  refine ⟨ρ, hρ0, fun s hs => ?_⟩
  rw [mem_ball, dist_eq_norm] at hs
  have hre : |s.re - s₀.re| < ρ := lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀)) hs
  have him : |s.im - s₀.im| < ρ := lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (s - s₀)) hs
  have hs1' : 1 < s.re := by linarith [(abs_lt.mp hre).1]
  have hs2' : s.re < 2 + k / 2 := by linarith [(abs_lt.mp hre).2]
  have hnp : ∀ z, traceCoeff r z ≠ 0 → s ≠ 1 + k * z := by
    intro z hz h
    have hzim : s.im = k * z.im := by have := congrArg Complex.im h; simp at this; linarith
    have hzP : z ∈ P := ⟨hz, by rw [← hzim]; linarith [abs_lt.mp him, hδ1, hρδ]⟩
    have h1 := hδP z hzP
    rw [← h, norm_sub_rev] at h1
    linarith
  have h1 := differentiableAt_traceZetaOf hr hN hk hC0 hC (c := traceCoeff r) (fun _ => le_rfl)
    hs1' hs2' hnp
  have h2 : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (fun h => by rw [h] at hs1'; simp at hs1')
  exact (h1.add (h2.const_mul _)).differentiableWithinAt

/-- **The identity theorem along a ray.** -/
theorem eqOn_ray_of_eventually {f g : ℂ → ℂ} {p : ℂ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hf : ∀ t ∈ Ioo a b, AnalyticAt ℂ f (p + t)) (hg : ∀ t ∈ Ioo a b, AnalyticAt ℂ g (p + t))
    (hfg : ∀ t ∈ Ioo c b, f (p + t) = g (p + t)) :
    ∀ t ∈ Ioo a b, f (p + t) = g (p + t) := by
  have hℓ : ∀ t : ℝ, AnalyticAt ℝ (fun t : ℝ => p + (t : ℂ)) t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => f (p + t)) (Ioo a b) := fun t ht =>
    AnalyticAt.comp (g := f) (f := fun t : ℝ => p + (t : ℂ)) (hf t ht).restrictScalars (hℓ t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => g (p + t)) (Ioo a b) := fun t ht =>
    AnalyticAt.comp (g := g) (f := fun t : ℝ => p + (t : ℂ)) (hg t ht).restrictScalars (hℓ t)
  set t₀ := (c + b) / 2 with ht₀def
  have ht₀ : t₀ ∈ Ioo a b := ⟨by rw [ht₀def]; linarith, by rw [ht₀def]; linarith⟩
  have hev : (fun t : ℝ => f (p + t)) =ᶠ[𝓝 t₀] (fun t : ℝ => g (p + t)) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by rw [ht₀def]; linarith : c < t₀)
      (by rw [ht₀def]; linarith : t₀ < b)) fun t ht => hfg t ht
  intro t ht
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_Ioo ht₀ hev ht

/-- **From the real segment to the half-ball.** Two functions holomorphic on
`ball σc ρ ∩ {Re > σc}` that agree on the real points there agree on it. -/
theorem eqOn_halfBall {f g : ℂ → ℂ} {σc ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ s ∈ ball (σc : ℂ) ρ, σc < s.re → AnalyticAt ℂ f s)
    (hg : ∀ s ∈ ball (σc : ℂ) ρ, σc < s.re → AnalyticAt ℂ g s)
    (hfg : ∀ t : ℝ, σc < t → t < σc + ρ → f t = g t) :
    ∀ s ∈ ball (σc : ℂ) ρ, σc < s.re → f s = g s := by
  set U : Set ℂ := ball (σc : ℂ) ρ ∩ {s | σc < s.re} with hU
  have hconv : Convex ℝ U := by
    refine (convex_ball _ _).inter ?_
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
    have hm : σc < min x.re y.re := lt_min hx hy
    have hsum : a * min x.re y.re + b * min x.re y.re = min x.re y.re := by
      rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left (min_le_left x.re y.re) ha,
      mul_le_mul_of_nonneg_left (min_le_right x.re y.re) hb]
  have hfU : AnalyticOnNhd ℂ f U := fun s hs => hf s hs.1 hs.2
  have hgU : AnalyticOnNhd ℂ g U := fun s hs => hg s hs.1 hs.2
  set z₀ : ℂ := ((σc + ρ / 2 : ℝ) : ℂ) with hz₀
  have hz₀U : z₀ ∈ U := by
    refine ⟨?_, by simp [hz₀]; linarith⟩
    rw [mem_ball, dist_eq_norm, hz₀, show ((σc + ρ / 2 : ℝ) : ℂ) - (σc : ℂ) = ((ρ / 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have htend : Tendsto (fun t : ℝ => ((σc + ρ / 2 + t : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => ((σc + ρ / 2 + t : ℝ) : ℂ)) (𝓝 0) (𝓝 (((σc + ρ / 2 + 0 : ℝ)) : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
      simpa [hz₀] using (this.mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hz₀]
      intro h
      have := congrArg Complex.re h
      simp at this
      exact ht this
  have hfreq : ∃ᶠ s in 𝓝[≠] z₀, f s = g s := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    have hball : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| < ρ / 2 := by
      have : ∀ᶠ t : ℝ in 𝓝 0, |t| < ρ / 2 := by
        have := Metric.ball_mem_nhds (0 : ℝ) (half_pos hρ)
        filter_upwards [this] with t ht
        simpa [Real.dist_eq] using ht
      exact this.filter_mono nhdsWithin_le_nhds
    filter_upwards [hball] with t ht
    have h := abs_lt.mp ht
    exact hfg _ (by linarith) (by linarith)
  intro s hs hre
  exact hfU.eqOn_of_preconnected_of_frequently_eq hgU hconv.isPreconnected hz₀U hfreq ⟨hs, hre⟩

/-- **The pole of `ζ` at `1`.** `|ζ(1 + t)| ≥ 1/(2t)` for small `t > 0`. -/
theorem exists_zeta_one_add_ge : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
    1 / (2 * t) ≤ ‖riemannZeta (1 + t)‖ := by
  have hres := riemannZeta_residue_one
  have htend : Tendsto (fun t : ℝ => (1 + (t : ℂ))) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => (1 + (t : ℂ))) (𝓝 0) (𝓝 (1 + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      exact (lt_irrefl _ (this ▸ ht : (0 : ℝ) < 0))
  have h2 := hres.comp htend
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖((1 + (t : ℂ)) - 1) * riemannZeta (1 + t) - 1‖ < 1 / 2 := by
    have := Metric.tendsto_nhds.mp h2 (1 / 2) (by norm_num)
    filter_upwards [this] with t ht
    simpa [dist_eq_norm] using ht
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
  have h := hδev (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htδ) ht0
  rw [show (1 + (t : ℂ)) - 1 = (t : ℂ) by ring] at h
  have hn : 1 / 2 ≤ ‖(t : ℂ) * riemannZeta (1 + t)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * riemannZeta (1 + t))
    rw [norm_one, norm_sub_rev] at this
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at hn
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem summable_add_one_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable fun j : ℕ => ((j : ℝ) + 1) ^ (-p) := by
  have h1 := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hp)
  refine h1.congr fun n => ?_
  push_cast
  rw [Real.rpow_neg (by positivity)]

theorem not_summable_add_one_rpow_neg {p : ℝ} (hp : p ≤ 1) :
    ¬ Summable fun j : ℕ => ((j : ℝ) + 1) ^ (-p) := by
  intro h
  have h1 : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ p)⁻¹ := h.congr fun n => by
    push_cast; rw [Real.rpow_neg (by positivity)]
  have := Real.summable_nat_rpow_inv.mp ((summable_nat_add_iff 1).mp h1)
  linarith

/-- **Base change at the power degrees.** For every `k ≥ 1` there is `r₀` such that for every box
spline `U_1^{⋆(r+1)}`, `r ≥ r₀`, RH holds iff the traces `2 Re S(k log n)` of the smoothed Frobenius
graphs of degree `nᵏ` are bounded below. -/
theorem riemannHypothesis_iff_bddBelow_powerDegrees {k : ℕ} (hk : 1 ≤ k) :
    ∃ r₀ : ℕ, 3 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r → (RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 r) (k * Real.log n)).re) := by
  classical
  obtain ⟨C, N, hC0, hC⟩ := RHTower.exists_bound_norm_riemannZeta_strip (3 + k)
  refine ⟨max 3 N, le_max_left _ _, fun r hr0 => ?_⟩
  have hr : 3 ≤ r := (le_max_left _ _).trans hr0
  have hN : N + 2 ≤ 2 * (r + 1) := by have := (le_max_right 3 N).trans hr0; omega
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hb := contDiff_boxSpline_two hr
  have hbs := boxSpline_support (r := 1) one_pos r
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  constructor
  · -- under RH the lag structure is bounded
    intro hRH
    have hon := riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH
    set L₀ := ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z‖ with hL₀
    refine ⟨2 * L₀, fun n _ => ?_⟩
    set v : ℝ := k * Real.log n
    obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff zetaZeroConfig hZ hb hbs v
    have hterm : ∀ z, ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z * cexp (z * v)‖ =
        ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z‖ := by
      intro z
      by_cases hz : lagCoeff zetaZeroConfig (boxSpline 1 r) z = 0
      · simp [hz]
      have hmem : (1 / 2 + z) ∈ zetaZeroConfig.carrier := by
        by_contra h; exact hz (by rw [lagCoeff, Set.indicator_of_notMem h])
      have hre : z.re = 0 := by have := hon _ hmem; simp at this; linarith
      rw [norm_mul, Complex.norm_exp]
      simp [hre]
    have hle : ‖lagStructure zetaZeroConfig (boxSpline 1 r) v‖ ≤ L₀ := by
      rw [he]
      calc ‖∑' z, lagCoeff zetaZeroConfig (boxSpline 1 r) z * cexp (z * v)‖
          ≤ ∑' z, ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z * cexp (z * v)‖ :=
            norm_tsum_le_tsum_norm hs.norm
        _ = L₀ := tsum_congr hterm
    have h1 := (Complex.abs_re_le_norm (lagStructure zetaZeroConfig (boxSpline 1 r) v)).trans hle
    linarith [(abs_le.mp h1).1]
  · rintro ⟨K, hK⟩
    by_contra hRH
    set a := powerCoeff r k K with ha_def
    have ha1 : ∀ j, 1 ≤ a j := by
      intro j
      have := hK (j + 1) (Nat.succ_pos j)
      simp only [ha_def, powerCoeff]
      push_cast at this
      linarith
    have ha : ∀ j, 0 ≤ a j := fun j => zero_le_one.trans (ha1 j)
    have hlam : ∀ j, 0 ≤ powerFreq j := powerFreq_nonneg
    have htw : ∀ σ j, gdTwistTerm a powerFreq σ 0 j = a j * ((j : ℝ) + 1) ^ (-σ) := by
      intro σ j; rw [gdTwistTerm, pow_zero, mul_one, real_exp_neg_mul_powerFreq]
    set L₀ := ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z‖ with hL₀
    have hL0 : 0 ≤ L₀ := tsum_nonneg fun _ => norm_nonneg _
    -- convergence right of `1 + k/2`, divergence left of `1`
    have hsumHigh : ∀ σ : ℝ, 1 + k / 2 < σ → Summable (gdTwistTerm a powerFreq σ 0) := by
      intro σ hσ
      have hg1 := summable_add_one_rpow_neg (p := σ - k / 2) (by linarith)
      have hg2 := summable_add_one_rpow_neg (p := σ) (by linarith [show (0 : ℝ) ≤ k / 2 by positivity])
      refine Summable.of_nonneg_of_le (fun j => gdTwistTerm_nonneg ha hlam σ 0 j) (fun j => ?_)
        ((hg1.mul_left (2 * L₀)).add (hg2.mul_left (|K| + 1)))
      rw [htw]
      have hlog : 0 ≤ (k : ℝ) * Real.log (j + 1) := mul_nonneg (Nat.cast_nonneg _) (powerFreq_nonneg j)
      have habs := abs_two_re_lagStructure_le hr hlog
      have hexp : Real.exp ((k : ℝ) * Real.log (j + 1) / 2) = ((j : ℝ) + 1) ^ ((k : ℝ) / 2) := by
        rw [Real.rpow_def_of_pos (by positivity)]; ring_nf
      rw [hexp] at habs
      have haj : a j ≤ 2 * L₀ * ((j : ℝ) + 1) ^ ((k : ℝ) / 2) + (|K| + 1) := by
        simp only [ha_def, powerCoeff]
        linarith [(abs_le.mp habs).2, le_abs_self K]
      have hpos : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
      calc a j * ((j : ℝ) + 1) ^ (-σ)
          ≤ (2 * L₀ * ((j : ℝ) + 1) ^ ((k : ℝ) / 2) + (|K| + 1)) * ((j : ℝ) + 1) ^ (-σ) :=
            mul_le_mul_of_nonneg_right haj hpos
        _ = 2 * L₀ * ((j : ℝ) + 1) ^ (-(σ - k / 2)) + (|K| + 1) * ((j : ℝ) + 1) ^ (-σ) := by
            rw [add_mul, mul_assoc, ← Real.rpow_add (by positivity),
              show (k : ℝ) / 2 + -σ = -(σ - k / 2) by ring]
    have hdivLow : ∀ σ : ℝ, σ ≤ 1 → ¬ Summable (gdTwistTerm a powerFreq σ 0) := by
      intro σ hσ hs
      apply not_summable_add_one_rpow_neg hσ
      refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) hs
      rw [htw]
      have := ha1 j
      have hpos : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
      nlinarith
    -- the abscissa
    set S : Set ℝ := {σ | Summable (gdTwistTerm a powerFreq σ 0)} with hSdef
    have hS2 : (1 + k / 2 + 1 / 8 : ℝ) ∈ S := hsumHigh _ (by linarith)
    have hSne : S.Nonempty := ⟨_, hS2⟩
    have hSbdd : BddBelow S := ⟨1, fun σ hσ => by
      by_contra h; exact hdivLow σ (le_of_lt (not_le.mp h)) hσ⟩
    set σc := sInf S with hσcdef
    have hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a powerFreq σ 0) := by
      intro σ hσ
      obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hSne hσ
      exact summable_gdTwistTerm_of_le ha hlam hσ'S hlt.le
    have hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a powerFreq σ 0) := fun σ hσ hs =>
      absurd (csInf_le hSbdd hs) (not_le.mpr hσ)
    have hσc2 : σc ≤ 1 + k / 2 + 1 / 8 := csInf_le hSbdd hS2
    -- analyticity
    have hgdAn : ∀ s : ℂ, σc < s.re → AnalyticAt ℂ (gdSeries a powerFreq) s := by
      intro s hs
      have hopen : IsOpen {w : ℂ | σc < w.re} := isOpen_lt continuous_const Complex.continuous_re
      refine DifferentiableOn.analyticAt (s := {w : ℂ | σc < w.re}) (fun w hw => ?_)
        (hopen.mem_nhds hs)
      have hw' : σc < w.re := hw
      exact (RHTower.differentiableAt_gdSeries ha hlam (hsum ((σc + w.re) / 2) (by linarith))
        (by linarith)).differentiableWithinAt
    have hGAn : ∀ s : ℂ, 1 < s.re → s.re < 2 + k / 2 →
        (∀ z, traceCoeff r z ≠ 0 → s ≠ 1 + k * z) → AnalyticAt ℂ (powerZeta r k K) s := by
      intro s h1 h2 hp
      obtain ⟨ρ, hρ, hd⟩ := exists_ball_differentiableOn_powerZeta hr hN hk hC0 hC K h1 h2 hp
      exact hd.analyticAt (ball_mem_nhds s hρ)
    have hrealNoPole : ∀ t : ℝ, ∀ z, traceCoeff r z ≠ 0 → (t : ℂ) ≠ 1 + k * z := by
      intro t z hz h
      have him := congrArg Complex.im h
      rw [Complex.ofReal_im, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.natCast_re,
        Complex.natCast_im, zero_mul, add_zero, zero_add] at him
      have : z.im = 0 := by
        rcases mul_eq_zero.mp him.symm with h0 | h0
        · linarith
        · exact h0
      exact traceCoeff_im_ne_zero hz this
    have hagreeHigh : ∀ s : ℂ, 1 + k / 2 < s.re →
        gdSeries a powerFreq s = powerZeta r k K s := fun s hs => gdSeries_powerCoeff_eq K hr hs
    -- Landau: the abscissa is at most `1`
    have hσc : σc ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have h2 : σc < 2 + k / 2 := by linarith
      obtain ⟨ρ, hρ, hG⟩ := exists_ball_differentiableOn_powerZeta hr hN hk hC0 hC K
        (s₀ := (σc : ℂ)) (by simpa using hgt) (by simpa using h2)
        (fun z hz => hrealNoPole σc z hz)
      have hreal : ∀ t ∈ Ioo σc (2 + k / 2),
          gdSeries a powerFreq ((0 : ℂ) + t) = powerZeta r k K ((0 : ℂ) + t) := by
        refine eqOn_ray_of_eventually (a := σc) (c := 1 + k / 2 + 1 / 4) (b := 2 + k / 2)
          (by linarith) (by linarith) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
        · rw [zero_add]; exact hgdAn _ (by simpa using ht.1)
        · rw [zero_add]
          exact hGAn _ (by simpa using hgt.trans ht.1) (by simpa using ht.2)
            (fun z hz => hrealNoPole t z hz)
        · rw [zero_add]; exact hagreeHigh _ (by simp; linarith [ht.1])
      have hhalf := eqOn_halfBall (f := powerZeta r k K) (g := gdSeries a powerFreq) hρ
        (fun s hs _ => hG.analyticAt (isOpen_ball.mem_nhds hs))
        (fun s _ hs => hgdAn s hs)
        (fun t ht1 _ => by
          rcases lt_or_ge t (2 + k / 2) with htb | htb
          · have := hreal t ⟨ht1, htb⟩; rw [zero_add] at this; exact this.symm
          · exact (hagreeHigh _ (by simp; linarith)).symm)
      exact RHTower.gdSeries_no_continuation_at_abscissa ha hlam hsum hdiv hρ hG
        (fun s hs hre => hhalf s hs hre)
    -- an off-line zero, rightmost on its line
    have hoff : ∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re := by
      by_contra h; push Not at h; exact hRH (riemannHypothesis_of_forall_re_le h)
    obtain ⟨ρ₁, hρ₁, hρ₁re⟩ := hoff
    set z₁ := ρ₁ - 1 / 2 with hz₁def
    have hz₁ : traceCoeff r z₁ ≠ 0 := traceCoeff_sees hr hρ₁ hρ₁re
    set Lset := (finite_evenCoeff_line zetaZeroConfig (boxSpline 1 r) z₁.im).toFinset with hLset
    obtain ⟨z₀, hz₀L, hmax⟩ := Lset.exists_max_image Complex.re
      ⟨z₁, (Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩⟩
    obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
    have hre₀ : z₁.re ≤ z₀.re := hmax z₁ ((Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩)
    have hz₁re : 0 < z₁.re := by simp [hz₁def]; linarith
    have hz₀re : z₀.re ≤ 1 / 2 := (abs_le.mp (abs_re_le_of_traceCoeff_ne_zero hz₀)).2
    set s₀ : ℂ := 1 + k * z₀ with hs₀def
    have hs₀re : s₀.re = 1 + k * z₀.re := by simp [hs₀def]
    have hs₀1 : 1 < s₀.re := by rw [hs₀re]; nlinarith
    have hs₀2 : s₀.re ≤ 1 + k / 2 := by rw [hs₀re]; nlinarith
    set T : ℝ := 2 + k / 2 - s₀.re with hTdef
    have hT : 1 ≤ T := by rw [hTdef]; linarith
    have hqre : ∀ t : ℝ, (s₀ + t).re = s₀.re + t := fun t => by simp
    -- no pole to the right of `1 + k z₀` on its line
    have hray : ∀ t : ℝ, 0 < t → ∀ z, traceCoeff r z ≠ 0 → s₀ + t ≠ 1 + k * z := by
      intro t ht z hz h
      have him := congrArg Complex.im h
      have hre := congrArg Complex.re h
      simp [hs₀def] at him hre
      have hzim : z.im = z₀.im := by
        rcases him with h0 | h0
        · exact h0.symm
        · omega
      have hzre : k * z.re = k * z₀.re + t := by linarith
      have hle := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hz, hzim.trans him₀⟩)
      nlinarith
    have hGray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ (powerZeta r k K) (s₀ + t) := fun t ht =>
      hGAn _ (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.2]) (hray t ht.1)
    have hgdray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ (gdSeries a powerFreq) (s₀ + t) := fun t ht =>
      hgdAn _ (by rw [hqre]; linarith [ht.1])
    have hagreeRay : ∀ t ∈ Ioo 0 T, gdSeries a powerFreq (s₀ + t) = powerZeta r k K (s₀ + t) :=
      eqOn_ray_of_eventually (c := 1 + k / 2 - s₀.re + 1 / 2) (by linarith) (by linarith)
        hgdray hGray (fun t ht => hagreeHigh _ (by rw [hqre]; linarith [ht.1]))
    -- split off the pole
    set c' : ℂ → ℂ := fun z => if z = z₀ then 0 else traceCoeff r z with hc'def
    have hc' : ∀ z, ‖c' z‖ ≤ ‖traceCoeff r z‖ := fun z => by
      simp only [hc'def]; split_ifs <;> simp
    have hsplit : ∀ t ∈ Ioo 0 T, powerZeta r k K (s₀ + t) =
        traceCoeff r z₀ * riemannZeta (1 + t) +
          (traceZetaOf c' k (s₀ + t) + ((K + 1 : ℝ) : ℂ) * riemannZeta (s₀ + t)) := by
      intro t ht
      have hsm := summable_traceZetaOf_terms hr hN hk hC0 hC (c := traceCoeff r) (fun _ => le_rfl)
        (s := s₀ + t) (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.2])
      unfold powerZeta traceZetaOf
      rw [hsm.tsum_eq_add_tsum_ite z₀]
      have h1 : (s₀ + t) - k * z₀ = 1 + t := by rw [hs₀def]; ring
      have h2 : ∑' z, (if z = z₀ then 0 else traceCoeff r z * riemannZeta (s₀ + t - k * z)) =
          ∑' z, c' z * riemannZeta (s₀ + t - k * z) :=
        tsum_congr fun z => by simp only [hc'def]; split_ifs <;> simp
      rw [h1, h2]
      ring
    set R : ℂ → ℂ := fun s => traceZetaOf c' k s + ((K + 1 : ℝ) : ℂ) * riemannZeta s with hRdef
    have hs₀ne : s₀ ≠ 1 := fun h => by rw [h] at hs₀1; simp at hs₀1
    have hRcont : ContinuousAt R s₀ := by
      have hp : ∀ z, c' z ≠ 0 → s₀ ≠ 1 + k * z := by
        intro z hz h
        have hzz : z ≠ z₀ := fun e => hz (by simp [hc'def, e])
        apply hzz
        have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
        have : (k : ℂ) * z₀ = k * z := by rw [hs₀def] at h; linear_combination h
        exact (mul_left_cancel₀ hk0 this).symm
      have h1 := differentiableAt_traceZetaOf hr hN hk hC0 hC hc' hs₀1 (by linarith) hp
      exact (h1.add ((differentiableAt_riemannZeta hs₀ne).const_mul _)).continuousAt
    have hgdcont : ContinuousAt (gdSeries a powerFreq) s₀ := (hgdAn s₀ (by linarith)).continuousAt
    set H : ℂ → ℂ := fun s => gdSeries a powerFreq s - R s with hHdef
    have hHcont : ContinuousAt H s₀ := hgdcont.sub hRcont
    have hHray : ∀ t ∈ Ioo 0 T, H (s₀ + t) = traceCoeff r z₀ * riemannZeta (1 + t) := by
      intro t ht
      simp only [hHdef, hRdef]
      rw [hagreeRay t ht, hsplit t ht]
      ring
    -- the pole of `ζ` at `1` against continuity
    obtain ⟨δ₁, hδ₁, hδ₁H⟩ := Metric.continuousAt_iff.mp hHcont 1 one_pos
    obtain ⟨δ₂, hδ₂, hζ⟩ := exists_zeta_one_add_ge
    set A := ‖traceCoeff r z₀‖ with hAdef
    have hA : 0 < A := norm_pos_iff.mpr hz₀
    set B := ‖H s₀‖ + 1 with hBdef
    have hB : 0 < B := by positivity
    set t := min (min δ₁ δ₂) (min T (A / (2 * (B + 1)))) / 2 with htdef
    have hm0 : 0 < min (min δ₁ δ₂) (min T (A / (2 * (B + 1)))) :=
      lt_min (lt_min hδ₁ hδ₂) (lt_min (by linarith) (by positivity))
    have ht0 : 0 < t := by rw [htdef]; positivity
    have htle : t < min (min δ₁ δ₂) (min T (A / (2 * (B + 1)))) := by rw [htdef]; linarith
    have htδ₁ : t < δ₁ := htle.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have htδ₂ : t < δ₂ := htle.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have htT : t < T := htle.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have htA : t < A / (2 * (B + 1)) := htle.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have h1 := hHray t ⟨ht0, htT⟩
    have h2 : dist (H (s₀ + t)) (H s₀) < 1 := hδ₁H (by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact htδ₁)
    have h3 := hζ t ht0 htδ₂
    have h4 : A / (2 * t) ≤ ‖H (s₀ + t)‖ := by
      rw [h1, norm_mul]
      calc A / (2 * t) = A * (1 / (2 * t)) := by ring
        _ ≤ A * ‖riemannZeta (1 + t)‖ := mul_le_mul_of_nonneg_left h3 hA.le
    have h5 : ‖H (s₀ + t)‖ < ‖H s₀‖ + 1 := by
      have := norm_sub_norm_le (H (s₀ + t)) (H s₀)
      rw [dist_eq_norm] at h2
      linarith
    have h6 : B + 1 < A / (2 * t) := by
      rw [lt_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ (by positivity)] at htA
      nlinarith
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
