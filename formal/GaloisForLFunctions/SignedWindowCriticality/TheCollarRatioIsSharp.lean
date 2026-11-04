import GaloisForLFunctions.SignedWindowCriticality.TheLightConeOfACollarCarriesItsReflection
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UnitInterval

/-!
# The collar ratio is sharp

The light cone of a collar carries a prime anti-diagonal on odd tests at the ratio
`2Λ(n)n^{−1/2}e^{h}` (`TheLightConeOfACollarCarriesItsReflection`). That bound comes from the first
regional Legendre gap `2H₁ = 2`, attained by the linear profile, which does not vanish at the collar
ends. Here the gap is shown to be the infimum on admissible profiles, and the ratio sharp.

* **Edge layers are cheap** (`regionalLogEnergy_le_of_layer`). A profile bounded by `1`, `K`-Lipschitz
  and supported in the edge layer `1 − r < |s|` has regional energy at most
  `2(K²η² + 4/η)·|layer|` for every `η > 0`.
* **The Legendre gap is the infimum on admissible odd profiles** (`exists_odd_profile_ratio_lt`).
  For every `ε > 0` there is an odd `C²` profile vanishing off `(−1, 1)` with
  `E(φ) ≤ (2 + ε)‖φ‖²`: cut the linear profile at the edges, `φ = s·χ_δ(s)`, and let `δ → 0`; the
  cut costs `O(δ^{1/2})` in energy because the logarithmic kernel gives the edge points no capacity.
* **Cauchy–Schwarz for the regional pairing** (`abs_regionalLogPair_le`).
* **The collar light cone is at most the regional energy** (`two_mul_collarLevyEnergy_le`):
  `2A_C ≤ (1 + 4h)E_C`, the companion of `e^{−h}E_C ≤ 2A_C`.
* **The collar ratio is sharp** (`exists_kick_add_collarLevyEnergy_neg`). For a weight `w`, a lag
  `ℓ`, a thin collar `0 < h = a − ℓ/2 < ℓ/2` and `λ > 0` with `λ(1 + 4h) < 2w`, an odd `C²` test
  supported in `[−a, a]` has `−2w∫f(t)f(t + ℓ) + λA_C(f) < 0`. With the bound
  `−2w∫f(t)f(t + ℓ) + 2we^{h}A_C(f) ≥ 0` the best constant lies in `[2w/(1 + 4h), 2we^{h}]`.
* **Prime `3`** (`exists_prime_three_collar_unpaid`). For `a ∈ (log 3/2, log 3/2 + 1/40]` the
  archimedean jumps inside the collar of `3` do not pay its anti-diagonal on some odd test.

So no constant below `2` bounds the reflection pairing by the regional energy on profiles that
vanish at the collar ends, and the thin-collar ratio `2Λ(n)n^{−1/2}` of the packed path is exact:
the collar alone pays its prime exactly when `2Λ(n)n^{−1/2} < 1` in the thin limit.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.LatticeSectionTheory GaloisForLFunctions.SelectivePositivityAndThresholdLaws

local notation "ν" => volume.restrict (Icc (-1 : ℝ) 1)

/-! ### A Lipschitz edge cut-off -/

theorem exists_lipschitz_smoothTransition :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b : ℝ,
      |Real.smoothTransition a - Real.smoothTransition b| ≤ L * |a - b| := by
  obtain ⟨K, hK⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0 : ℝ) 1) isCompact_Icc
  refine ⟨K, K.coe_nonneg, fun a b => ?_⟩
  rw [← Real.smoothTransition.projIcc (x := a), ← Real.smoothTransition.projIcc (x := b)]
  have h := hK.dist_le_mul (projIcc (0 : ℝ) 1 zero_le_one a : ℝ) (projIcc (0 : ℝ) 1 zero_le_one a).2
    (projIcc (0 : ℝ) 1 zero_le_one b : ℝ) (projIcc (0 : ℝ) 1 zero_le_one b).2
  rw [Real.dist_eq, Real.dist_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Set.abs_projIcc_sub_projIcc zero_le_one) K.coe_nonneg)

/-- The edge cut-off: `1` where `1 − s² ≥ δ`, `0` where `1 − s² ≤ δ/2`. -/
def edgeCut (δ s : ℝ) : ℝ := Real.smoothTransition (2 * ((1 - s ^ 2) / δ) - 1)

theorem contDiff_edgeCut (δ : ℝ) : ContDiff ℝ 2 (edgeCut δ) :=
  (Real.smoothTransition.contDiff (n := 2)).comp (by fun_prop)

theorem edgeCut_nonneg (δ s : ℝ) : 0 ≤ edgeCut δ s := Real.smoothTransition.nonneg _

theorem edgeCut_le_one (δ s : ℝ) : edgeCut δ s ≤ 1 := Real.smoothTransition.le_one _

theorem edgeCut_neg (δ s : ℝ) : edgeCut δ (-s) = edgeCut δ s := by
  simp only [edgeCut, neg_sq]

theorem edgeCut_eq_one {δ s : ℝ} (hδ : 0 < δ) (h : δ ≤ 1 - s ^ 2) : edgeCut δ s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : 1 ≤ (1 - s ^ 2) / δ := (le_div_iff₀ hδ).mpr (by linarith)
  linarith

theorem edgeCut_eq_zero {δ s : ℝ} (hδ : 0 < δ) (h : 1 - s ^ 2 ≤ δ / 2) : edgeCut δ s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : (1 - s ^ 2) / δ ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by linarith)
  linarith

theorem edgeCut_eq_one_of_abs_le {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : |s| ≤ 1 - δ) :
    edgeCut δ s = 1 := by
  apply edgeCut_eq_one hδ
  have h := pow_le_pow_left₀ (abs_nonneg s) hs 2
  rw [sq_abs] at h
  nlinarith

theorem edgeCut_lipschitz {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ a b : ℝ, |Real.smoothTransition a - Real.smoothTransition b| ≤ L * |a - b|)
    {δ : ℝ} (hδ : 0 < δ) {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |edgeCut δ x - edgeCut δ y| ≤ 4 * L / δ * |x - y| := by
  have e : (2 * ((1 - x ^ 2) / δ) - 1) - (2 * ((1 - y ^ 2) / δ) - 1) =
      2 / δ * ((y + x) * (y - x)) := by field_simp; ring
  have hxy : |y + x| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  calc |edgeCut δ x - edgeCut δ y|
      ≤ L * |(2 * ((1 - x ^ 2) / δ) - 1) - (2 * ((1 - y ^ 2) / δ) - 1)| := hL _ _
    _ = L * (2 / δ * (|y + x| * |x - y|)) := by
        rw [e, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / δ), abs_sub_comm y x]
    _ ≤ L * (2 / δ * (2 * |x - y|)) := by
        gcongr
    _ = 4 * L / δ * |x - y| := by ring

/-! ### Edge layers have small regional energy -/

theorem volume_real_layer_le {r : ℝ} (hr : 0 ≤ r) :
    volume.real ({x : ℝ | 1 - r < |x|} ∩ Icc (-1 : ℝ) 1) ≤ 2 * r := by
  have hsub : {x : ℝ | 1 - r < |x|} ∩ Icc (-1 : ℝ) 1 ⊆ Icc (-1) (-1 + r) ∪ Icc (1 - r) 1 := by
    intro x ⟨hx, hxI⟩
    simp only [mem_setOf_eq] at hx
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx; right; exact ⟨hx.le, hxI.2⟩
    · rw [abs_of_neg h0] at hx; left; exact ⟨hxI.1, by linarith⟩
  calc volume.real ({x : ℝ | 1 - r < |x|} ∩ Icc (-1 : ℝ) 1)
      ≤ volume.real (Icc (-1 : ℝ) (-1 + r) ∪ Icc (1 - r) 1) :=
        measureReal_mono hsub (measure_union_lt_top measure_Icc_lt_top measure_Icc_lt_top).ne
    _ ≤ volume.real (Icc (-1 : ℝ) (-1 + r)) + volume.real (Icc (1 - r : ℝ) 1) :=
        measureReal_union_le _ _
    _ = 2 * r := by
        rw [Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Icc_of_le (by linarith)]
        ring

/-- **Edge layers are cheap.** -/
theorem regionalLogEnergy_le_of_layer {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {K r η : ℝ}
    (hη : 0 < η)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |G x| ≤ 1)
    (hL : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1, |G x - G y| ≤ K * |x - y|)
    (hz : ∀ x ∈ Icc (-1 : ℝ) 1, |x| ≤ 1 - r → G x = 0) :
    regionalLogEnergy G ≤
      2 * (K ^ 2 * η ^ 2 + 4 / η) * volume.real ({x : ℝ | 1 - r < |x|} ∩ Icc (-1 : ℝ) 1) := by
  set S : Set ℝ := {x : ℝ | 1 - r < |x|}
  have hSm : MeasurableSet S := measurableSet_lt measurable_const continuous_abs.measurable
  set T : Set (ℝ × ℝ) := {q | |q.1 - q.2| < η}
  have hTm : MeasurableSet T := measurableSet_lt (by fun_prop) measurable_const
  set h : ℝ × ℝ → ℝ := fun p => K ^ 2 * η / 2 * T.indicator (fun _ => (1 : ℝ)) p + 2 / η
  set B : ℝ × ℝ → ℝ := fun p => S.indicator (fun _ => (1 : ℝ)) p.1 * h p
  have hT01 : ∀ p, 0 ≤ T.indicator (fun _ => (1 : ℝ)) p ∧ T.indicator (fun _ => (1 : ℝ)) p ≤ 1 :=
    fun p => ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) p,
      Set.indicator_le_self' (fun _ _ => zero_le_one) p⟩
  have hS01 : ∀ x, 0 ≤ S.indicator (fun _ => (1 : ℝ)) x ∧ S.indicator (fun _ => (1 : ℝ)) x ≤ 1 :=
    fun x => ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) x,
      Set.indicator_le_self' (fun _ _ => zero_le_one) x⟩
  have hh0 : ∀ p, 0 ≤ h p := fun p => by
    have := (hT01 p).1; simp only [h]; positivity
  have hhle : ∀ p, h p ≤ K ^ 2 * η / 2 + 2 / η := fun p => by
    have := mul_le_mul_of_nonneg_left (hT01 p).2 (by positivity : (0 : ℝ) ≤ K ^ 2 * η / 2)
    simp only [h]; linarith
  have hhswap : ∀ p : ℝ × ℝ, h p.swap = h p := fun p => by
    simp only [h, T, Set.indicator, mem_setOf_eq, Prod.fst_swap, Prod.snd_swap, abs_sub_comm]
  have hB0 : ∀ p, 0 ≤ B p := fun p => mul_nonneg (hS01 _).1 (hh0 p)
  -- the integrand is dominated by `B + B∘swap` on the square
  have hpt : ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
      (G p.1 - G p.2) * (G p.1 - G p.2) / (2 * |p.1 - p.2|) ≤ B p + B p.swap := by
    rintro p ⟨hp1, hp2⟩
    have hφh : (G p.1 - G p.2) * (G p.1 - G p.2) / (2 * |p.1 - p.2|) ≤ h p := by
      by_cases hΔ : p.1 = p.2
      · rw [hΔ]; simp only [sub_self, mul_zero, zero_div]; exact hh0 p
      · have ht : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr hΔ)
        rw [div_le_iff₀ (by positivity)]
        by_cases hη' : |p.1 - p.2| < η
        · have hind : T.indicator (fun _ => (1 : ℝ)) p = 1 :=
            Set.indicator_of_mem (show p ∈ T from hη') _
          have hsq : (G p.1 - G p.2) * (G p.1 - G p.2) ≤ K ^ 2 * |p.1 - p.2| ^ 2 := by
            have := hL p.1 hp1 p.2 hp2
            rw [← abs_mul_self, abs_mul]; nlinarith [abs_nonneg (G p.1 - G p.2)]
          have h1 : K ^ 2 * |p.1 - p.2| ^ 2 ≤ K ^ 2 * η * |p.1 - p.2| := by
            have := mul_le_mul_of_nonneg_left hη'.le
              (mul_nonneg (sq_nonneg K) (abs_nonneg (p.1 - p.2)))
            nlinarith
          have h2 : 0 ≤ 2 / η * (2 * |p.1 - p.2|) := by positivity
          simp only [h, hind]
          nlinarith [hsq, h1, h2]
        · push Not at hη'
          have hsq : (G p.1 - G p.2) * (G p.1 - G p.2) ≤ 4 := by
            have h1 := hb p.1 hp1
            have h2 := hb p.2 hp2
            have : |G p.1 - G p.2| ≤ 2 := by
              calc |G p.1 - G p.2| ≤ |G p.1| + |G p.2| := abs_sub _ _
                _ ≤ 2 := by linarith
            rw [← abs_mul_self, abs_mul]; nlinarith [abs_nonneg (G p.1 - G p.2)]
          have h2η : 2 / η * (2 * |p.1 - p.2|) ≥ 4 := by
            rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hη]; nlinarith
          have := (hT01 p).1
          simp only [h]
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg K) hη.le) this]
    by_cases hS : p.1 ∈ S ∨ p.2 ∈ S
    · rcases hS with hS | hS
      · have : B p = h p := by simp only [B, Set.indicator_of_mem hS, one_mul]
        linarith [hB0 p.swap]
      · have : B p.swap = h p := by
          simp only [B, Prod.fst_swap, Set.indicator_of_mem hS, one_mul, hhswap]
        linarith [hB0 p]
    · push Not at hS
      have h1 : G p.1 = 0 := hz p.1 hp1 (by simpa [S] using hS.1)
      have h2 : G p.2 = 0 := hz p.2 hp2 (by simpa [S] using hS.2)
      rw [h1, h2]; simp only [sub_self, mul_zero, zero_div]
      linarith [hB0 p, hB0 p.swap]
  -- integrability
  have hBm : Measurable B :=
    ((measurable_const.indicator hSm).comp measurable_fst).mul
      (((measurable_const.indicator hTm).const_mul _).add measurable_const)
  have hBb : ∀ p, ‖B p‖ ≤ K ^ 2 * η / 2 + 2 / η := fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hB0 p)]
    calc B p ≤ 1 * h p := mul_le_mul_of_nonneg_right (hS01 _).2 (hh0 p)
      _ ≤ K ^ 2 * η / 2 + 2 / η := by rw [one_mul]; exact hhle p
  have hBi : Integrable B ((ν).prod ν) :=
    Integrable.of_bound hBm.aestronglyMeasurable _ (Eventually.of_forall hBb)
  have hBsi : Integrable (fun p : ℝ × ℝ => B p.swap) ((ν).prod ν) :=
    Integrable.of_bound (hBm.comp measurable_swap).aestronglyMeasurable _
      (Eventually.of_forall fun p => hBb p.swap)
  have hφi := regionalLogPair_integrable hG hG
  -- `E(G) ≤ ∫(B + B∘swap) = 2∫B`
  have hmono : regionalLogEnergy G ≤ ∫ p, (B p + B p.swap) ∂((ν).prod ν) := by
    unfold regionalLogEnergy regionalLogPair
    refine integral_mono_ae hφi (hBi.add hBsi) ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact hpt p hp
  rw [integral_add hBi hBsi, integral_prod_swap (f := B)] at hmono
  -- the inner integral of `B`
  have hrow : ∀ x : ℝ, (∫ y, B (x, y) ∂ν) ≤
      S.indicator (fun _ => (1 : ℝ)) x * (K ^ 2 * η ^ 2 + 4 / η) := by
    intro x
    have hball : ∀ y, T.indicator (fun _ => (1 : ℝ)) (x, y) =
        (Metric.ball x η).indicator (fun _ => (1 : ℝ)) y := fun y => by
      simp only [T, Set.indicator, mem_setOf_eq, Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    have hint : (∫ y, h (x, y) ∂ν) ≤ K ^ 2 * η ^ 2 + 4 / η := by
      have hi1 : Integrable (fun y => K ^ 2 * η / 2 *
          (Metric.ball x η).indicator (fun _ => (1 : ℝ)) y) ν :=
        ((integrable_const (1 : ℝ)).indicator measurableSet_ball).const_mul _
      have e : (fun y => h (x, y)) = fun y => K ^ 2 * η / 2 *
          (Metric.ball x η).indicator (fun _ => (1 : ℝ)) y + 2 / η := by
        funext y; simp only [h, hball]
      rw [e, integral_add hi1 (integrable_const _), integral_const_mul,
        integral_indicator_const _ measurableSet_ball, integral_const]
      have hb1 : (volume.restrict (Icc (-1 : ℝ) 1)).real (Metric.ball x η) ≤ 2 * η := by
        rw [measureReal_restrict_apply measurableSet_ball]
        calc volume.real (Metric.ball x η ∩ Icc (-1 : ℝ) 1) ≤ volume.real (Metric.ball x η) :=
              measureReal_mono inter_subset_left measure_ball_lt_top.ne
          _ = 2 * η := Real.volume_real_ball hη.le
      have hb2 : (volume.restrict (Icc (-1 : ℝ) 1)).real univ = 2 := by
        rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter,
          Real.volume_real_Icc_of_le (by norm_num)]; norm_num
      simp only [smul_eq_mul, hb2]
      have hKη : 0 ≤ K ^ 2 * η / 2 := by positivity
      have h1 := mul_le_mul_of_nonneg_left hb1 hKη
      have e1 : K ^ 2 * η / 2 * (2 * η) = K ^ 2 * η ^ 2 := by ring
      have e2 : 2 * (2 / η) = 4 / η := by ring
      rw [mul_one, e2]
      linarith
    have e : (∫ y, B (x, y) ∂ν) = S.indicator (fun _ => (1 : ℝ)) x * ∫ y, h (x, y) ∂ν := by
      simp only [B]; exact integral_const_mul _ _
    rw [e]
    exact mul_le_mul_of_nonneg_left hint (hS01 x).1
  have hrowm : Measurable fun x => ∫ y, B (x, y) ∂ν :=
    hBm.stronglyMeasurable.integral_prod_right'.measurable
  have hrowi : Integrable (fun x => ∫ y, B (x, y) ∂ν) ν := hBi.integral_prod_left
  have hcmp : (∫ x, ∫ y, B (x, y) ∂ν ∂ν) ≤
      ∫ x, S.indicator (fun _ => (1 : ℝ)) x * (K ^ 2 * η ^ 2 + 4 / η) ∂ν :=
    integral_mono hrowi (((integrable_const (1 : ℝ)).indicator hSm).mul_const _) hrow
  have hval : (∫ x, S.indicator (fun _ => (1 : ℝ)) x * (K ^ 2 * η ^ 2 + 4 / η) ∂ν) =
      (K ^ 2 * η ^ 2 + 4 / η) * volume.real (S ∩ Icc (-1 : ℝ) 1) := by
    rw [integral_mul_const, integral_indicator_const _ hSm, measureReal_restrict_apply hSm]
    simp only [smul_eq_mul, mul_one]
    ring
  rw [integral_prod B hBi] at hmono
  rw [hval] at hcmp
  linarith

/-! ### Cauchy–Schwarz for the regional pairing -/

theorem regionalLogEnergy_const_mul (t : ℝ) (G : ℝ → ℝ) :
    regionalLogEnergy (fun x => t * G x) = t ^ 2 * regionalLogEnergy G := by
  unfold regionalLogEnergy regionalLogPair
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun p => by simp only; ring)

theorem regionalLogPair_const_mul (t : ℝ) (F G : ℝ → ℝ) :
    regionalLogPair F (fun x => t * G x) = t * regionalLogPair F G := by
  unfold regionalLogPair
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun p => by simp only; ring)

/-- **Cauchy–Schwarz for the regional pairing.** -/
theorem abs_regionalLogPair_le {F G : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) :
    |regionalLogPair F G| ≤ Real.sqrt (regionalLogEnergy F) * Real.sqrt (regionalLogEnergy G) := by
  have hq : ∀ t : ℝ, 0 ≤ regionalLogEnergy G * (t * t) + (-2 * regionalLogPair F G) * t +
      regionalLogEnergy F := by
    intro t
    have h := regionalLogEnergy_sub hF (contDiff_const.mul hG : ContDiff ℝ 1 fun x => t * G x)
    rw [regionalLogEnergy_const_mul, regionalLogPair_const_mul] at h
    have h0 := regionalLogEnergy_nonneg (fun x => F x - t * G x)
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hsq : regionalLogPair F G ^ 2 ≤ regionalLogEnergy F * regionalLogEnergy G := by nlinarith
  rw [← Real.sqrt_mul (regionalLogEnergy_nonneg F)]
  exact Real.abs_le_sqrt hsq

/-! ### The Legendre gap is the infimum on admissible odd profiles -/

/-- The cut linear profile `s·χ_δ(s)`. -/
def cutLinear (δ s : ℝ) : ℝ := s * edgeCut δ s

theorem contDiff_cutLinear (δ : ℝ) : ContDiff ℝ 2 (cutLinear δ) :=
  contDiff_id.mul (contDiff_edgeCut δ)

theorem cutLinear_neg (δ s : ℝ) : cutLinear δ (-s) = -cutLinear δ s := by
  simp only [cutLinear, edgeCut_neg]; ring

theorem cutLinear_eq_zero {δ s : ℝ} (hδ : 0 < δ) (hs : 1 ≤ |s|) : cutLinear δ s = 0 := by
  have h := pow_le_pow_left₀ (by norm_num) hs 2
  rw [sq_abs, one_pow] at h
  simp only [cutLinear, edgeCut_eq_zero hδ (by linarith : 1 - s ^ 2 ≤ δ / 2), mul_zero]

/-- **The Legendre gap is the infimum on admissible odd profiles.** -/
theorem exists_odd_profile_ratio_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 2 φ ∧ (∀ s, φ (-s) = -φ s) ∧ (∀ s, 1 ≤ |s| → φ s = 0) ∧
      0 < ∫ s in Icc (-1 : ℝ) 1, φ s ^ 2 ∧
      regionalLogEnergy φ ≤ (2 + ε) * ∫ s in Icc (-1 : ℝ) 1, φ s ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_smoothTransition
  -- the sequence `δ = x⁴`, `η = x³`, `x = 1/(n + 1)`
  set x : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hx0 : ∀ n, 0 < x n := fun n => by simp only [x]; positivity
  have hx1 : ∀ n, x n ≤ 1 := fun n => by
    simp only [x]; rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hxt : Tendsto x atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set G : ℕ → ℝ → ℝ := fun n s => s * (1 - edgeCut (x n ^ 4) s)
  have hGc : ∀ n, ContDiff ℝ 1 (G n) := fun n =>
    contDiff_id.mul (contDiff_const.sub ((contDiff_edgeCut _).of_le (by norm_num)))
  -- energy of the layer
  have hGE : ∀ n, regionalLogEnergy (G n) ≤ 4 * ((x n ^ 4 + 4 * L) ^ 2 * x n ^ 2) + 16 * x n := by
    intro n
    have hδ : 0 < x n ^ 4 := by have := hx0 n; positivity
    have hδ1 : x n ^ 4 ≤ 1 := pow_le_one₀ (hx0 n).le (hx1 n)
    have hK : 0 ≤ 1 + 4 * L / x n ^ 4 := by positivity
    have h := regionalLogEnergy_le_of_layer (G := G n) (K := 1 + 4 * L / x n ^ 4) (hGc n)
      (pow_pos (hx0 n) 3)
      (r := x n ^ 4)
      (fun s hs => by
        simp only [G, abs_mul]
        have h1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
        have h2 : |1 - edgeCut (x n ^ 4) s| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [edgeCut_nonneg (x n ^ 4) s, edgeCut_le_one (x n ^ 4) s]
        nlinarith [abs_nonneg s, abs_nonneg (1 - edgeCut (x n ^ 4) s)])
      (fun s hs t ht => by
        have hc := edgeCut_lipschitz hL0 hL hδ hs ht
        have e : G n s - G n t = (s - t) * (1 - edgeCut (x n ^ 4) s) +
            t * (edgeCut (x n ^ 4) t - edgeCut (x n ^ 4) s) := by simp only [G]; ring
        rw [e]
        have h1 : |1 - edgeCut (x n ^ 4) s| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [edgeCut_nonneg (x n ^ 4) s, edgeCut_le_one (x n ^ 4) s]
        have h2 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
        calc |(s - t) * (1 - edgeCut (x n ^ 4) s) + t * (edgeCut (x n ^ 4) t - edgeCut (x n ^ 4) s)|
            ≤ |s - t| * |1 - edgeCut (x n ^ 4) s| +
                |t| * |edgeCut (x n ^ 4) t - edgeCut (x n ^ 4) s| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ |s - t| * 1 + 1 * (4 * L / x n ^ 4 * |s - t|) := by
              gcongr
              rw [abs_sub_comm]; exact hc
          _ = (1 + 4 * L / x n ^ 4) * |s - t| := by ring)
      (fun s _ hs => by
        simp only [G, edgeCut_eq_one_of_abs_le hδ hδ1 hs, sub_self, mul_zero])
    have hv := volume_real_layer_le hδ.le
    have hc0 : 0 ≤ 2 * ((1 + 4 * L / x n ^ 4) ^ 2 * (x n ^ 3) ^ 2 + 4 / x n ^ 3) := by positivity
    have := h.trans (mul_le_mul_of_nonneg_left hv hc0)
    have e : 2 * ((1 + 4 * L / x n ^ 4) ^ 2 * (x n ^ 3) ^ 2 + 4 / x n ^ 3) * (2 * x n ^ 4) =
        4 * ((x n ^ 4 + 4 * L) ^ 2 * x n ^ 2) + 16 * x n := by
      have := hx0 n; field_simp; ring
    linarith
  have hGt : Tendsto (fun n => regionalLogEnergy (G n)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => 4 * ((x n ^ 4 + 4 * L) ^ 2 * x n ^ 2) + 16 * x n) atTop (𝓝 0) := by
      have hc : Continuous fun y : ℝ => 4 * ((y ^ 4 + 4 * L) ^ 2 * y ^ 2) + 16 * y := by fun_prop
      have := (hc.tendsto 0).comp hxt
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun n => regionalLogEnergy_nonneg _) hGE
  -- energy and mass of the cut profile
  have hid : ContDiff ℝ 1 (fun s : ℝ => s) := contDiff_id
  have hEφ : ∀ n, regionalLogEnergy (cutLinear (x n ^ 4)) ≤
      4 / 3 + regionalLogEnergy (G n) +
        2 * (Real.sqrt (4 / 3) * Real.sqrt (regionalLogEnergy (G n))) := by
    intro n
    have e : cutLinear (x n ^ 4) = fun s => s - G n s := by
      funext s; simp only [cutLinear, G]; ring
    rw [e, regionalLogEnergy_sub hid (hGc n), regionalLogEnergy_id]
    have hcs := abs_regionalLogPair_le hid (hGc n)
    rw [regionalLogEnergy_id] at hcs
    linarith [neg_abs_le (regionalLogPair (fun s => s) (G n))]
  have hmass : ∀ n, 2 * (1 - x n ^ 4) ^ 3 / 3 ≤ ∫ s in Icc (-1 : ℝ) 1, cutLinear (x n ^ 4) s ^ 2 := by
    intro n
    have hδ : 0 < x n ^ 4 := by have := hx0 n; positivity
    have hδ1 : x n ^ 4 ≤ 1 := pow_le_one₀ (hx0 n).le (hx1 n)
    set c := 1 - x n ^ 4
    have hc0 : 0 ≤ c := by simp only [c]; linarith
    have hsub : Icc (-c) c ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by linarith) (by linarith)
    have hcont : Continuous fun s => cutLinear (x n ^ 4) s ^ 2 :=
      ((contDiff_cutLinear _).continuous).pow 2
    calc 2 * c ^ 3 / 3 = ∫ s in Icc (-c) c, s ^ 2 := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
            integral_pow]; ring
      _ = ∫ s in Icc (-c) c, cutLinear (x n ^ 4) s ^ 2 := by
          refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
          have habs : |s| ≤ c := abs_le.mpr ⟨hs.1, hs.2⟩
          simp only [cutLinear, edgeCut_eq_one_of_abs_le hδ hδ1 habs, mul_one]
      _ ≤ ∫ s in Icc (-1 : ℝ) 1, cutLinear (x n ^ 4) s ^ 2 :=
          setIntegral_mono_set hcont.integrableOn_Icc
            (Eventually.of_forall fun s => sq_nonneg _) (Eventually.of_forall hsub)
  -- the ratio tends to `2`
  have hU : Tendsto (fun n => 4 / 3 + regionalLogEnergy (G n) +
      2 * (Real.sqrt (4 / 3) * Real.sqrt (regionalLogEnergy (G n)))) atTop (𝓝 (4 / 3)) := by
    have := ((tendsto_const_nhds (x := (4 / 3 : ℝ))).add hGt).add
      ((hGt.sqrt.const_mul (Real.sqrt (4 / 3))).const_mul 2)
    simpa using this
  have hM : Tendsto (fun n => (2 + ε) * (2 * (1 - x n ^ 4) ^ 3 / 3)) atTop
      (𝓝 ((2 + ε) * (2 / 3))) := by
    have hc : Continuous fun y : ℝ => (2 + ε) * (2 * (1 - y ^ 4) ^ 3 / 3) := by fun_prop
    have := (hc.tendsto 0).comp hxt
    simpa [Function.comp_def] using this
  have hlt : 4 / 3 < (2 + ε) * (2 / 3) := by nlinarith
  have hev := (hU.eventually (gt_mem_nhds (show 4 / 3 < (4 / 3 + (2 + ε) * (2 / 3)) / 2 by linarith))).and
    (hM.eventually (lt_mem_nhds (show (4 / 3 + (2 + ε) * (2 / 3)) / 2 < (2 + ε) * (2 / 3) by linarith)))
  obtain ⟨n, hn1, hn2⟩ := hev.exists
  refine ⟨cutLinear (x n ^ 4), contDiff_cutLinear _, cutLinear_neg _,
    fun s hs => cutLinear_eq_zero (by have := hx0 n; positivity) hs, ?_, ?_⟩
  · have := hmass n
    have hpos : 0 < 2 * (1 - x n ^ 4) ^ 3 / 3 := by
      have : x n ^ 4 < 1 ∨ x n ^ 4 = 1 := lt_or_eq_of_le (pow_le_one₀ (hx0 n).le (hx1 n))
      rcases this with h | h
      · have : 0 < 1 - x n ^ 4 := by linarith
        positivity
      · -- `x n ^ 4 = 1` only at `n = 0`; use the eventual bound instead
        nlinarith [hn2, hn1, regionalLogEnergy_nonneg (G n)]
    linarith
  · have h1 := hEφ n
    have h2 := mul_le_mul_of_nonneg_left (hmass n) (by linarith : (0 : ℝ) ≤ 2 + ε)
    linarith

/-! ### The physical collar -/

/-- The regional energy only sees the reference collar. -/
theorem regionalLogEnergy_congr {F G : ℝ → ℝ} (h : ∀ s ∈ Icc (-1 : ℝ) 1, F s = G s) :
    regionalLogEnergy F = regionalLogEnergy G := by
  unfold regionalLogEnergy regionalLogPair
  refine integral_congr_ae ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  rw [h p.1 hp.1, h p.2 hp.2]

/-- **The collar light cone is at most the regional energy, up to `1 + 4h`.**
`2A_C(f) ≤ (1 + 4h)E_C(f)`, since `ω(t) ≤ (1 + 2t)/(2t)`. -/
theorem two_mul_collarLevyEnergy_le {h : ℝ} (hh : 0 < h) (c : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    2 * collarLevyEnergy c h f ≤ (1 + 4 * h) * collarLogEnergy c h f := by
  obtain ⟨K, hK0, hK⟩ := collar_lipschitz hf c h
  have hfc := hf.continuous
  set ω := _root_.RHTower.archLevyDensity
  have hdist : ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h), |u - v| ≤ 2 * h :=
    fun u hu v hv => by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have hpt : ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h),
      ω |u - v| * (f u - f v) ^ 2 ≤ (1 + 4 * h) * ((f u - f v) ^ 2 / (2 * |u - v|)) := by
    intro u hu v hv
    by_cases huv : u = v
    · subst huv; simp
    · have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
      have hωt := archLevyDensity_mul_le ht
      have hd := hdist u hu v hv
      have hω : ω |u - v| ≤ (1 + 4 * h) / (2 * |u - v|) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      calc ω |u - v| * (f u - f v) ^ 2 ≤ (1 + 4 * h) / (2 * |u - v|) * (f u - f v) ^ 2 :=
            mul_le_mul_of_nonneg_right hω (sq_nonneg _)
        _ = (1 + 4 * h) * ((f u - f v) ^ 2 / (2 * |u - v|)) := by ring
  have hbL : ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h),
      |(f u - f v) ^ 2 / (2 * |u - v|)| ≤ K ^ 2 * h := by
    intro u hu v hv
    by_cases huv : u = v
    · subst huv; simp; positivity
    · have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
      have hL := hK u hu v hv
      have hsq : (f u - f v) ^ 2 ≤ K ^ 2 * |u - v| ^ 2 := by
        rw [← sq_abs (f u - f v)]
        nlinarith [abs_nonneg (f u - f v)]
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
      nlinarith [hdist u hu v hv, sq_nonneg K]
  have hbA : ∀ u ∈ Icc (c - h) (c + h), ∀ v ∈ Icc (c - h) (c + h),
      |ω |u - v| * (f u - f v) ^ 2| ≤ K ^ 2 * (1 + 4 * h) * h := by
    intro u hu v hv
    by_cases huv : u = v
    · subst huv; simp; positivity
    · have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
      have hL := hK u hu v hv
      have hsq : (f u - f v) ^ 2 ≤ K ^ 2 * |u - v| ^ 2 := by
        rw [← sq_abs (f u - f v)]
        nlinarith [abs_nonneg (f u - f v)]
      have hω0 : 0 ≤ ω |u - v| := (RHTower.archLevyDensity_pos ht).le
      have hωt := archLevyDensity_mul_le ht
      have hd := hdist u hu v hv
      rw [abs_of_nonneg (mul_nonneg hω0 (sq_nonneg _))]
      calc ω |u - v| * (f u - f v) ^ 2 ≤ ω |u - v| * (K ^ 2 * |u - v| ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hω0
        _ = K ^ 2 * |u - v| * (ω |u - v| * |u - v|) := by ring
        _ ≤ K ^ 2 * |u - v| * ((1 + 2 * |u - v|) / 2) :=
            mul_le_mul_of_nonneg_left hωt (by positivity)
        _ ≤ K ^ 2 * (2 * h) * ((1 + 2 * (2 * h)) / 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hd (sq_nonneg K)) (by linarith)
              (by positivity) (by positivity)
        _ = K ^ 2 * (1 + 4 * h) * h := by ring
  have hmL : ∀ u, Measurable fun v => (f u - f v) ^ 2 / (2 * |u - v|) := fun u =>
    ((continuous_const.sub hfc).pow 2).measurable.div
      (continuous_const.mul (continuous_const.sub continuous_id).abs).measurable
  have hmA : ∀ u, Measurable fun v => ω |u - v| * (f u - f v) ^ 2 := fun u =>
    (RHTower.measurable_archLevyDensity.comp
      (continuous_const.sub continuous_id).abs.measurable).mul
      ((continuous_const.sub hfc).pow 2).measurable
  have hin : ∀ u ∈ Icc (c - h) (c + h),
      (∫ v in Icc (c - h) (c + h), ω |u - v| * (f u - f v) ^ 2) ≤
        (1 + 4 * h) * ∫ v in Icc (c - h) (c + h), (f u - f v) ^ 2 / (2 * |u - v|) := by
    intro u hu
    rw [← integral_const_mul]
    exact setIntegral_mono_on (integrableOn_collar_of_bound (hmA u) (hbA u hu))
      ((integrableOn_collar_of_bound (hmL u) (hbL u hu)).const_mul _) measurableSet_Icc
      fun v hv => hpt u hu v hv
  have hcp : Continuous fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2 := by fun_prop
  have hcd : Continuous fun p : ℝ × ℝ => 2 * |p.1 - p.2| := by fun_prop
  have hca : Continuous fun p : ℝ × ℝ => |p.1 - p.2| := by fun_prop
  have hjL : Measurable fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2 / (2 * |p.1 - p.2|) :=
    hcp.measurable.div hcd.measurable
  have hjA : Measurable fun p : ℝ × ℝ => ω |p.1 - p.2| * (f p.1 - f p.2) ^ 2 :=
    (RHTower.measurable_archLevyDensity.comp hca.measurable).mul hcp.measurable
  have hrowL : Measurable fun u => ∫ v in Icc (c - h) (c + h), (f u - f v) ^ 2 / (2 * |u - v|) :=
    by exact hjL.stronglyMeasurable.integral_prod_right'.measurable
  have hrowA : Measurable fun u => ∫ v in Icc (c - h) (c + h), ω |u - v| * (f u - f v) ^ 2 :=
    by exact hjA.stronglyMeasurable.integral_prod_right'.measurable
  have hvol : volume.real (Icc (c - h) (c + h)) = 2 * h := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hrbL : ∀ u ∈ Icc (c - h) (c + h),
      |∫ v in Icc (c - h) (c + h), (f u - f v) ^ 2 / (2 * |u - v|)| ≤ K ^ 2 * h * (2 * h) := by
    intro u hu
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (c - h) (c + h))
      measure_Icc_lt_top (C := K ^ 2 * h) fun v hv => by
        rw [Real.norm_eq_abs]; exact hbL u hu v hv
    rw [Real.norm_eq_abs, hvol] at this
    linarith
  have hrbA : ∀ u ∈ Icc (c - h) (c + h),
      |∫ v in Icc (c - h) (c + h), ω |u - v| * (f u - f v) ^ 2| ≤
        K ^ 2 * (1 + 4 * h) * h * (2 * h) := by
    intro u hu
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (c - h) (c + h))
      measure_Icc_lt_top (C := K ^ 2 * (1 + 4 * h) * h) fun v hv => by
        rw [Real.norm_eq_abs]; exact hbA u hu v hv
    rw [Real.norm_eq_abs, hvol] at this
    linarith
  unfold collarLogEnergy collarLevyEnergy
  rw [← integral_const_mul]
  have := setIntegral_mono_on (integrableOn_collar_of_bound hrowA hrbA)
    ((integrableOn_collar_of_bound hrowL hrbL).const_mul _) measurableSet_Icc hin
  linarith

/-- The odd test on the collar `[c − h, c + h]` built from a reference profile. -/
def collarOddTest (φ : ℝ → ℝ) (c h : ℝ) (u : ℝ) : ℝ := φ ((u - c) / h) - φ ((-u - c) / h)

/-- **The collar ratio is sharp.** For a prime-like weight `w`, a lag `ℓ`, a thin collar
`0 < h = a − ℓ/2 < ℓ/2` and `λ > 0` with `λ(1 + 4h) < 2w`, there is an odd `C²` test supported in
`[−a, a]` with `−2w∫f(t)f(t + ℓ)dt + λA_C(f) < 0`: the collar's light cone, even scaled by `λ`, does
not pay the anti-diagonal. -/
theorem exists_kick_add_collarLevyEnergy_neg {w ℓ a lam : ℝ} (hlam : 0 < lam) (hℓa : ℓ / 2 < a)
    (hthin : a - ℓ / 2 < ℓ / 2) (hratio : lam * (1 + 4 * (a - ℓ / 2)) < 2 * w) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ (∀ x, f (-x) = -f x) ∧ (∀ x, x ∉ Icc (-a) a → f x = 0) ∧
      -2 * w * (∫ t, f t * f (t + ℓ)) + lam * collarLevyEnergy (ℓ / 2) (a - ℓ / 2) f < 0 := by
  have hh : 0 < a - ℓ / 2 := by linarith
  have hc : a - ℓ / 2 < ℓ / 2 := hthin
  have hc0 : 0 < ℓ / 2 := by linarith
  have hca : ℓ / 2 + (a - ℓ / 2) = a := by ring
  have hℓ : ℓ = 2 * (ℓ / 2) := by ring
  set h := a - ℓ / 2 with hhdef
  set c := ℓ / 2 with hcdef
  have hD : 0 < lam * (1 + 4 * h) := by positivity
  set ε := (4 * w / (lam * (1 + 4 * h)) - 2) / 2
  have hε : 0 < ε := by
    simp only [ε]
    have : 2 < 4 * w / (lam * (1 + 4 * h)) := by rw [lt_div_iff₀ hD]; linarith
    linarith
  obtain ⟨φ, hφ, hodd, hφz, hmass, hE⟩ := exists_odd_profile_ratio_lt hε
  set f := collarOddTest φ c h
  have hfc : ContDiff ℝ 2 f :=
    (hφ.comp ((contDiff_id.sub contDiff_const).div_const _)).sub
      (hφ.comp ((contDiff_neg.sub contDiff_const).div_const _))
  have hfodd : ∀ x, f (-x) = -f x := fun x => by
    simp only [f, collarOddTest, neg_neg]; ring
  -- the two halves of `f` live on `C` and `−C`
  have hφz' : ∀ t, 1 < |t| → φ t = 0 := fun t ht => hφz t ht.le
  have hout : ∀ u, c + h < |u| → f u = 0 := by
    intro u hu
    have h1 : 1 < |(u - c) / h| ∧ 1 < |(-u - c) / h| := by
      rcases lt_abs.mp hu with hu | hu
      · constructor
        · exact lt_abs.mpr (Or.inl ((lt_div_iff₀ hh).mpr (by linarith)))
        · exact lt_abs.mpr (Or.inr (by rw [neg_div', lt_div_iff₀ hh]; linarith))
      · constructor
        · exact lt_abs.mpr (Or.inr (by rw [neg_div', lt_div_iff₀ hh]; linarith))
        · exact lt_abs.mpr (Or.inl ((lt_div_iff₀ hh).mpr (by linarith)))
    simp only [f, collarOddTest, hφz' _ h1.1, hφz' _ h1.2, sub_self]
  have hC : ∀ u ∈ Icc (c - h) (c + h), f u = φ ((u - c) / h) := by
    intro u hu
    have h1 : 1 < |(-u - c) / h| :=
      lt_abs.mpr (Or.inr (by rw [neg_div', lt_div_iff₀ hh]; linarith [hu.1]))
    simp only [f, collarOddTest, hφz' _ h1, sub_zero]
  have hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0 := by
    intro x hx
    apply hout
    rw [hca]
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
    · exact lt_of_lt_of_le hx (le_abs_self x)
  -- the prime term is `−2wh‖φ‖²`
  have hcorr := integral_mul_shift_eq_neg_antidiagonal hfodd ℓ
  have hanti : (∫ s, f s * f (ℓ - s)) = ∫ s in Icc (c - h) (c + h), f s * f (ℓ - s) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_).symm
    simp only [mem_Icc, not_and_or, not_le] at hs
    rcases hs with hs | hs
    · by_cases hs' : c + h < |s|
      · rw [hout s hs', zero_mul]
      · push Not at hs'
        have : c + h < |ℓ - s| := lt_of_lt_of_le (by rw [hℓ]; linarith [neg_abs_le s])
          (le_abs_self _)
        rw [hout (ℓ - s) this, mul_zero]
    · rw [hout s (lt_of_lt_of_le hs (le_abs_self s)), zero_mul]
  have hresc := collar_rescale hh.le c (fun s => f s * f (ℓ - s))
  have hpt : ∀ t ∈ Icc (-1 : ℝ) 1, f (c + h * t) * f (ℓ - (c + h * t)) = -φ t ^ 2 := by
    intro t ht
    have hm1 : c + h * t ∈ Icc (c - h) (c + h) :=
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    have hm2 : ℓ - (c + h * t) ∈ Icc (c - h) (c + h) :=
      ⟨by rw [hℓ]; nlinarith [ht.2], by rw [hℓ]; nlinarith [ht.1]⟩
    rw [hC _ hm1, hC _ hm2]
    have e1 : (c + h * t - c) / h = t := by field_simp; ring
    have e2 : (ℓ - (c + h * t) - c) / h = -t := by rw [hℓ]; field_simp; ring
    rw [e1, e2, hodd]; ring
  have hkick : -2 * w * (∫ t, f t * f (t + ℓ)) =
      -(2 * w * h) * ∫ t in Icc (-1 : ℝ) 1, φ t ^ 2 := by
    rw [hcorr, hanti, ← hresc]
    have : (∫ t in Icc (-1 : ℝ) 1, (fun s => f s * f (ℓ - s)) (c + h * t)) =
        ∫ t in Icc (-1 : ℝ) 1, -φ t ^ 2 :=
      setIntegral_congr_fun measurableSet_Icc fun t ht => hpt t ht
    rw [this, integral_neg]
    ring
  -- the collar light cone is at most `(1 + 4h)h E(φ)/2`
  have hf1 : ContDiff ℝ 1 f := hfc.of_le (by norm_num)
  have hA := two_mul_collarLevyEnergy_le hh c hf1
  have hEC := collarLogEnergy_eq hh c hf1
  have hEφ : regionalLogEnergy (fun s => f (c + h * s)) = regionalLogEnergy φ := by
    apply regionalLogEnergy_congr
    intro t ht
    have hm1 : c + h * t ∈ Icc (c - h) (c + h) :=
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    rw [hC _ hm1]
    congr 1
    field_simp
    ring
  rw [hEφ] at hEC
  -- conclusion
  have hD2 : lam * (1 + 4 * h) * (2 + ε) = lam * (1 + 4 * h) + 2 * w := by
    simp only [ε]; field_simp; ring
  have hM := hmass
  set M := ∫ t in Icc (-1 : ℝ) 1, φ t ^ 2
  refine ⟨f, hfc, hfodd, hsupp, ?_⟩
  rw [hkick]
  have hAC : lam * collarLevyEnergy c h f ≤ lam * ((1 + 4 * h) * (h * regionalLogEnergy φ)) / 2 := by
    rw [← hEC]
    have := mul_le_mul_of_nonneg_left hA hlam.le
    linarith
  have hEb : lam * ((1 + 4 * h) * (h * regionalLogEnergy φ)) ≤
      lam * ((1 + 4 * h) * (h * ((2 + ε) * M))) := by
    have : 0 ≤ lam * ((1 + 4 * h) * h) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hE this]
  have key : lam * ((1 + 4 * h) * (h * ((2 + ε) * M))) = h * M * (lam * (1 + 4 * h) + 2 * w) := by
    rw [← hD2]; ring
  have hneg : h * M * (lam * (1 + 4 * h) - 2 * w) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hh hM) (by linarith)
  nlinarith [hAC, hEb, key, hneg]

/-- **The collar of the prime `3` cannot pay its own frustration.** For every half-width
`a ∈ (log 3/2, log 3/2 + 1/40]` there is an odd `C²` test supported in `[−a, a]` whose prime-`3` term
is not paid by the archimedean jumps inside its collar: `−2w₃∫f(t)f(t + log 3)dt + A_C(f) < 0`. -/
theorem exists_prime_three_collar_unpaid {a : ℝ} (ha : Real.log 3 / 2 < a)
    (ha' : a ≤ Real.log 3 / 2 + 1 / 40) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ (∀ x, f (-x) = -f x) ∧ (∀ x, x ∉ Icc (-a) a → f x = 0) ∧
      -2 * (Real.log 3 / Real.sqrt 3) * (∫ t, f t * f (t + Real.log 3)) +
        collarLevyEnergy (Real.log 3 / 2) (a - Real.log 3 / 2) f < 0 := by
  have hl : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hs : Real.sqrt 3 < 1.7321 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := by positivity
  have hw : 1 * (1 + 4 * (a - Real.log 3 / 2)) < 2 * (Real.log 3 / Real.sqrt 3) := by
    rw [mul_div_assoc', lt_div_iff₀ hs0]
    nlinarith
  obtain ⟨f, h1, h2, h3, h4⟩ := exists_kick_add_collarLevyEnergy_neg (w := Real.log 3 / Real.sqrt 3)
    (ℓ := Real.log 3) one_pos ha (by linarith) hw
  exact ⟨f, h1, h2, h3, by simpa using h4⟩

end GaloisForLFunctions.SignedWindowCriticality

end
