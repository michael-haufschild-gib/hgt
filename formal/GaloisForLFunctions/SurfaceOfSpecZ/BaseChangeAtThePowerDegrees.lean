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
    (hf t ht).restrictScalars.comp (hℓ t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => g (p + t)) (Ioo a b) := fun t ht =>
    (hg t ht).restrictScalars.comp (hℓ t)
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
    nlinarith
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
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhdsWithin_iff.mp hev
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

/-- **Base change at the power degrees.** -/
theorem riemannHypothesis_iff_bddBelow_powerDegrees {k : ℕ} (hk : 1 ≤ k) :
    ∃ r₀ : ℕ, 3 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r → (RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 r) (k * Real.log n)).re) := by
  sorry

end GaloisForLFunctions.SurfaceOfSpecZ
