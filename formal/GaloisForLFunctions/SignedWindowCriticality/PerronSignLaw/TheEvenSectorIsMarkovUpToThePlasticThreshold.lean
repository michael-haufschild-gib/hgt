import GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.TheWindowEdgeCarriesTheNewestPrime
import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.RetainedVarianceAndHalfWindowBandBelowLogFour
import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalFinitePartAndBroadClassification
import GaloisForLFunctions.RHTower.CHMDOddHarmonicIdentityAndPolarDoobAbsorption

/-!
# The even sector is Markov up to the plastic threshold

For a half-window test `f` vanishing off `[−c, 0]` the even sector of Weil's form on `[−c, c]` is
`E(f) = W(f) + 𝓗₀(f)` (`evenBandWeights`; for `2c < log 2` no prime acts). In kernel form
`E(f) = Γ‖f‖² + 𝒥(f) + (∫ f h)² − Σ_j (∫ f e_j)²` with `h(u) = 2cosh(u/2)`, `e_j(u) = e^{(2j+1/2)u}`,
`Σ_j e_j(u) e_j(v) = ω(−u − v)` the trivial-zero kernel and `𝒥` the Lévy jump energy. Under the
contraction `f ↦ |f|`,
`E(f) − E(|f|) = ∬ D(u,v) [ω(|u − v|) + ω(−u − v) − 4cosh(u/2)cosh(v/2)] du dv`,
`D(u,v) = |f(u)||f(v)| − f(u)f(v) ≥ 0`: the pole is the only anti-Markov term, and it is paid by
the Lévy jumps together with the trivial-zero squares.

* `four_mul_cosh_mul_cosh_le` — for `p, q ∈ [0, t_*]`, `p ≠ q`:
  `4cosh(p/2)cosh(q/2) ≤ ω(|p − q|) + ω(p + q)`. Mode by mode
  `e^{−α|p−q|} + e^{−α(p+q)} = 2e^{−αM}cosh(αm) ≥ 2e^{−αM}cosh(m/2)` (`M, m` the max and min,
  `α = 2j + 1/2`), so the sum is at least `2cosh(m/2) ω(M) ≥ 4cosh(m/2)cosh(M/2)` below the
  plastic threshold `t_* = log ρ`, where `ω(t_*) = 2cosh(t_*/2)`.
* `evenSector_abs_le` — **the even sector is Markov for `c ≤ t_*`**: `E(|f|) ≤ E(f)`.
* `evenKernel_neg_of_threshold_lt` — the range is sharp: for `c > t_*` the kernel is negative at
  the pair (window edge, centre) `(−c, 0)`.
-/

open Real MeasureTheory Set Filter Topology Zeta23
open scoped CompactlySupported ENNReal
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole
open _root_.RHTower.WeilLevyCoshCrossover

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw

open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.RHTower (screwSignThreshold)
open SpacingScaleHarmonicAnalysis

/-! ### 1. The kernel inequality below the plastic threshold -/

/-- The modes `e^{−(2j+1/2)x}` of `ω(x)` are summable for `x > 0`. -/
lemma summable_levyModes {x : ℝ} (hx : 0 < x) :
    Summable fun j : ℕ => Real.exp (-((2 * (j : ℝ) + 1 / 2) * x)) := by
  have h : (fun j : ℕ => Real.exp (-((2 * (j : ℝ) + 1 / 2) * x))) =
      fun j : ℕ => Real.exp (-(x / 2)) * Real.exp (-(2 * x)) ^ j := by
    funext j
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  rw [h]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by linarith))).mul_left _

/-- One mode pair: `e^{−α|p−q|} + e^{−α(p+q)} ≥ 2e^{−α max(p,q)} cosh(min(p,q)/2)` for `α ≥ 1/2`. -/
lemma mode_pair_ge {α p q : ℝ} (hα : 1 / 2 ≤ α) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    2 * Real.exp (-(α * max p q)) * Real.cosh (min p q / 2) ≤
      Real.exp (-(α * |p - q|)) + Real.exp (-(α * (p + q))) := by
  have hm : 0 ≤ min p q := le_min hp hq
  have h1 : |p - q| = max p q - min p q := by
    rcases le_total p q with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]
  have h2 : p + q = max p q + min p q := by
    rcases le_total p q with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]
  have hc : Real.cosh (min p q / 2) ≤ Real.cosh (α * min p q) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (div_nonneg hm (by norm_num)),
      abs_of_nonneg (mul_nonneg (by linarith) hm)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hα) hm]
  have hid : Real.exp (-(α * |p - q|)) + Real.exp (-(α * (p + q))) =
      2 * Real.exp (-(α * max p q)) * Real.cosh (α * min p q) := by
    rw [h1, h2, Real.cosh_eq,
      show -(α * (max p q - min p q)) = -(α * max p q) + α * min p q by ring,
      show -(α * (max p q + min p q)) = -(α * max p q) + -(α * min p q) by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [hid]
  have h := mul_le_mul_of_nonneg_left hc
    (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-(α * max p q)))
  linarith

/-- **The even kernel below the plastic threshold**: for `p, q ∈ [0, t_*]`, `p ≠ q`,
`4cosh(p/2)cosh(q/2) ≤ ω(|p − q|) + ω(p + q)`. -/
theorem four_mul_cosh_mul_cosh_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpt : p ≤ screwSignThreshold) (hqt : q ≤ screwSignThreshold) (hpq : p ≠ q) :
    4 * Real.cosh (p / 2) * Real.cosh (q / 2) ≤
      archLevyDensity |p - q| + archLevyDensity (p + q) := by
  have hd : 0 < |p - q| := abs_pos.mpr (sub_ne_zero.mpr hpq)
  have hM : 0 < max p q := by
    rcases lt_or_gt_of_ne hpq with h | h
    · exact lt_max_of_lt_right (by linarith)
    · exact lt_max_of_lt_left (by linarith)
  have hs : 0 < p + q := by
    rcases lt_or_gt_of_ne hpq with h | h <;> linarith
  rw [_root_.RHTower.archLevyDensity_eq_tsum hd, _root_.RHTower.archLevyDensity_eq_tsum hs,
    ← (summable_levyModes hd).tsum_add (summable_levyModes hs)]
  have hmodes : ∀ j : ℕ, 2 * Real.cosh (min p q / 2) *
      Real.exp (-((2 * (j : ℝ) + 1 / 2) * max p q)) ≤
      Real.exp (-((2 * (j : ℝ) + 1 / 2) * |p - q|)) +
        Real.exp (-((2 * (j : ℝ) + 1 / 2) * (p + q))) := fun j => by
    have h := mode_pair_ge (α := 2 * (j : ℝ) + 1 / 2)
      (by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith) hp hq
    linarith
  have hsum := Summable.tsum_le_tsum hmodes ((summable_levyModes hM).mul_left _)
    ((summable_levyModes hd).add (summable_levyModes hs))
  rw [tsum_mul_left, ← _root_.RHTower.archLevyDensity_eq_tsum hM] at hsum
  have hω := two_mul_cosh_le_archLevyDensity_of_le_threshold hM (max_le hpt hqt)
  have hcc : Real.cosh (p / 2) * Real.cosh (q / 2) =
      Real.cosh (max p q / 2) * Real.cosh (min p q / 2) := by
    rcases le_total p q with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]
  have hcm := Real.cosh_pos (min p q / 2)
  calc 4 * Real.cosh (p / 2) * Real.cosh (q / 2)
      = 2 * Real.cosh (min p q / 2) * (2 * Real.cosh (max p q / 2)) := by
        rw [mul_assoc, hcc]; ring
    _ ≤ 2 * Real.cosh (min p q / 2) * archLevyDensity (max p q) :=
        mul_le_mul_of_nonneg_left hω (by positivity)
    _ ≤ _ := hsum

/-- **Sharpness**: for `c > t_*` the even kernel is negative at the pair `(p, q) = (c, 0)`
(window edge against centre), `ω(c) + ω(c) < 4cosh(c/2)cosh(0)`. -/
theorem evenKernel_neg_of_threshold_lt {c : ℝ} (hc : screwSignThreshold < c) :
    archLevyDensity |c - 0| + archLevyDensity (c + 0) <
      4 * Real.cosh (c / 2) * Real.cosh (0 / 2) := by
  have ht0 : 0 < screwSignThreshold := lt_trans (by norm_num) screwSignThreshold_gt
  have hc0 : 0 < c := lt_trans ht0 hc
  rw [sub_zero, add_zero, abs_of_pos hc0, zero_div, Real.cosh_zero, mul_one]
  have h1 : archLevyDensity c < archLevyDensity screwSignThreshold :=
    CHMDPolar.strictAntiOn_archLevyDensity_Ioi ht0 hc0 hc
  have h2 := archLevyDensity_screwSignThreshold
  have h3 : Real.cosh (screwSignThreshold / 2) < Real.cosh (c / 2) := by
    rw [Real.cosh_lt_cosh, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  linarith

/-! ### 2. Weil's form on a short half-window -/

/-- No prime meets a test supported in `[−c, c]` with `2c < log 2`:
`W(F) = Γ‖F‖² + 𝒥(F) + 2(∫ e^{u/2}F)(∫ e^{−u/2}F)`. -/
lemma weilQuad_eq_of_short {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) {c : ℝ}
    (hc : 2 * c < Real.log 2) (hFs : ∀ x, c < |x| → F x = 0)
    (hJ : IntegrableOn (fun x => (autocorr F 0 - autocorr F x) * archLevySinhWeight x) (Ioi 0)) :
    weilQuad F = EF.gammaBracket 0 * autocorr F 0 + biScaleLevyEnergy F +
      2 * ((∫ u, Real.exp (u / 2) * F u) * ∫ u, Real.exp (-(u / 2)) * F u) := by
  let Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF⟩, hFc⟩
  have hfull := re_weilFullFunctional_eq_of_compact_finite_jump Fc hJ
  change weilQuad F = EF.gammaBracket 0 * autocorr F 0 + biScaleLevyEnergy F -
    2 * fullPairing (autocorr F) at hfull
  have hprime : (∑' n : ℕ, primeTerm (autocorr F) n) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    by_cases h2 : 2 ≤ n
    · have hlog : 2 * c < |Real.log n| := by
        have h2' : (2 : ℝ) ≤ n := by exact_mod_cast h2
        have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2'
        rw [abs_of_nonneg (le_trans (Real.log_nonneg (by norm_num)) hl)]
        linarith
      have hz : autocorr F (Real.log n) = 0 := autocorr_eq_zero_of_far hFs hlog
      simp only [SignedPrimePolar.primeTerm, if_pos h2, hz, mul_zero]
    · simp only [SignedPrimePolar.primeTerm, if_neg h2]
  have hpolar := integral_polar_autocorr_eq_moments Fc
  change (∫ x in Ici (0 : ℝ), polarDensity x * autocorr F x) =
    (∫ u, Real.exp (u / 2) * F u) * (∫ u, Real.exp (-(u / 2)) * F u) at hpolar
  rw [fullPairing, hprime, hpolar] at hfull
  rw [hfull]; ring

/-! ### 3. The contraction defect -/

/-- The defect `D(u, v) = |f(u)||f(v)| − f(u)f(v)` of `f ↦ |f|` on the pair `(u, v)`. -/
def pairDefect (f : ℝ → ℝ) (u v : ℝ) : ℝ := |f u| * |f v| - f u * f v

lemma pairDefect_nonneg (f : ℝ → ℝ) (u v : ℝ) : 0 ≤ pairDefect f u v := by
  unfold pairDefect
  rw [← abs_mul]; linarith [le_abs_self (f u * f v)]

lemma pairDefect_eq_zero_of_left {f : ℝ → ℝ} {u v : ℝ} (h : f u = 0) :
    pairDefect f u v = 0 := by
  simp [pairDefect, h]

lemma pairDefect_eq_zero_of_right {f : ℝ → ℝ} {u v : ℝ} (h : f v = 0) :
    pairDefect f u v = 0 := by
  simp [pairDefect, h]

/-- The weight `h(u) = 2cosh(u/2)` of the pole. -/
def coshWeight (u : ℝ) : ℝ := 2 * Real.cosh (u / 2)

/-- The trivial-zero modes `e_j(u) = e^{(2j+1/2)u}`. -/
def expWeight (j : ℕ) (u : ℝ) : ℝ := Real.exp ((2 * (j : ℝ) + 1 / 2) * u)

lemma integrable_weighted_shift {F k : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hk : Continuous k) (x : ℝ) :
    Integrable fun u => F u * k u * (F (u + x) * k (u + x)) :=
  (by fun_prop : Continuous fun u => F u * k u * (F (u + x) * k (u + x))).integrable_of_hasCompactSupport
    (hFc.mono fun u hu h0 => hu (by simp [h0]))

lemma integrable_pairDefect_shift {f k : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hk : Continuous k) (x : ℝ) :
    Integrable fun u => pairDefect f u (u + x) * (k u * k (u + x)) :=
  (by unfold pairDefect; fun_prop :
      Continuous fun u => pairDefect f u (u + x) * (k u * k (u + x))).integrable_of_hasCompactSupport
    (hfc.mono fun u hu h0 => hu (by simp only [pairDefect_eq_zero_of_left h0, zero_mul]))

/-- `∫ D(u, u + x) k(u) k(u + x) du` is the autocorrelation gap of `|f|·k` and `f·k`. -/
lemma integral_pairDefect_shift {f k : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hk : Continuous k) (x : ℝ) :
    (∫ u, pairDefect f u (u + x) * (k u * k (u + x))) =
      autocorr (fun u => |f u| * k u) x - autocorr (fun u => f u * k u) x := by
  unfold autocorr
  rw [← integral_sub (integrable_weighted_shift hf.abs hfc.abs hk x)
    (integrable_weighted_shift hf hfc hk x)]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only [pairDefect]; ring)

lemma integrable_pairDefect_shift' {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : ℝ) : Integrable fun u => pairDefect f u (u + x) :=
  (by unfold pairDefect; fun_prop :
      Continuous fun u => pairDefect f u (u + x)).integrable_of_hasCompactSupport
    (hfc.mono fun u hu h0 => hu (pairDefect_eq_zero_of_left h0))

/-- `∫ D(u, u + x) du = A_{|f|}(x) − A_f(x)`. -/
lemma integral_pairDefect_shift' {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : ℝ) :
    (∫ u, pairDefect f u (u + x)) = autocorr (fun u => |f u|) x - autocorr f x := by
  unfold autocorr pairDefect
  rw [← integral_sub
    ((by fun_prop : Continuous fun u => |f u| * |f (u + x)|).integrable_of_hasCompactSupport
      (hfc.mono fun u hu h0 => hu (by simp [h0])))
    ((by fun_prop : Continuous fun u => f u * f (u + x)).integrable_of_hasCompactSupport
      (hfc.mono fun u hu h0 => hu (by simp [h0])))]

/-- `(∫ G)² = 2 ∫_0^∞ (G ⋆ G̃)(x) dx` for continuous compactly supported `G`. -/
lemma sq_integral_eq_two_mul_integral_autocorr {G : ℝ → ℝ} (hG : Continuous G)
    (hGc : HasCompactSupport G) :
    (∫ u, G u) ^ 2 = 2 * ∫ x in Ioi (0 : ℝ), autocorr G x := by
  have h := integral_autocorr_eq_sq_integral (⟨⟨G, hG⟩, hGc⟩ : C_c(ℝ, ℝ))
  change (∫ x, autocorr G x) = (∫ u, G u) ^ 2 at h
  rw [← h, ← integral_comp_abs (f := autocorr G)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  rcases le_total 0 x with hx | hx
  · simp only [abs_of_nonneg hx]
  · simp only [abs_of_nonpos hx, autocorr_neg]

lemma continuous_autocorr' {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G) :
    Continuous (autocorr G) :=
  continuous_autocorr_compact (⟨⟨G, hG⟩, hGc⟩ : C_c(ℝ, ℝ))

lemma integrable_autocorr' {G : ℝ → ℝ} (hG : Continuous G) {R : ℝ}
    (hGs : ∀ x, R < |x| → G x = 0) : Integrable (autocorr G) := by
  have hGc : HasCompactSupport G :=
    HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx =>
      hGs x (lt_of_not_ge fun h => hx (abs_le.mp h))
  refine (continuous_autocorr' hG hGc).integrable_of_hasCompactSupport ?_
  exact HasCompactSupport.intro (isCompact_Icc (a := -(2 * R + 1)) (b := 2 * R + 1)) fun x hx =>
    autocorr_eq_zero_of_far hGs (by
      by_contra h
      exact hx (abs_le.mp (le_trans (not_lt.mp h) (by linarith))))

/-! ### 4. The Lévy energy of the contraction -/

lemma integrableOn_levy_abs {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hJf : IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) (Ioi 0)) :
    IntegrableOn (fun x => (autocorr (fun u => |f u|) 0 - autocorr (fun u => |f u|) x) *
      archLevySinhWeight x) (Ioi 0) := by
  have hg : Continuous fun u => |f u| := hf.abs
  have hgc : HasCompactSupport fun u => |f u| := hfc.abs
  have hle : ∀ x, 0 ≤ autocorr (fun u => |f u|) 0 - autocorr (fun u => |f u|) x ∧
      autocorr (fun u => |f u|) 0 - autocorr (fun u => |f u|) x ≤
        autocorr f 0 - autocorr f x := by
    intro x
    have e1 := integral_sub_shift_sq hgc hg x
    have e2 := integral_sub_shift_sq hfc hf x
    have hshift (F : ℝ → ℝ) (hF : Continuous F) (hFc : HasCompactSupport F) :
        Integrable fun u => (F u - F (u + x)) ^ 2 := by
      have hcs : HasCompactSupport (fun u => F (u + x)) :=
        hFc.comp_homeomorph (Homeomorph.addRight x)
      have hcs2 : HasCompactSupport (fun u => (F u - F (u + x)) ^ 2) :=
        (hFc.sub hcs).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
      exact (by fun_prop : Continuous fun u => (F u - F (u + x)) ^ 2
        ).integrable_of_hasCompactSupport hcs2
    have hn : 0 ≤ ∫ u, (|f u| - |f (u + x)|) ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hm : (∫ u, (|f u| - |f (u + x)|) ^ 2) ≤ ∫ u, (f u - f (u + x)) ^ 2 := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) (hshift _ hf hfc)
        (Eventually.of_forall fun u => ?_)
      have h := abs_abs_sub_abs_le_abs_sub (f u) (f (u + x))
      have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs, sq_abs] at h'
    constructor <;> linarith
  have hmeas : AEStronglyMeasurable
      (fun x => (autocorr (fun u => |f u|) 0 - autocorr (fun u => |f u|) x) *
        archLevySinhWeight x) (volume.restrict (Ioi 0)) :=
    ((continuous_const.sub (continuous_autocorr' hg hgc)).continuousOn.mul
      continuousOn_archLevySinhWeight_pos_halfLine).aestronglyMeasurable measurableSet_Ioi
  refine hJf.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hw := (archLevySinhWeight_pos hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hle x).1 hw)]
  exact mul_le_mul_of_nonneg_right (hle x).2 hw

/-- `𝒥(f) − 𝒥(|f|) = 2 ∫_0^∞ ω(x) (A_{|f|}(x) − A_f(x)) dx`. -/
lemma levy_sub_eq {f : ℝ → ℝ}
    (hJf : IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) (Ioi 0))
    (hJg : IntegrableOn (fun x => (autocorr (fun u => |f u|) 0 - autocorr (fun u => |f u|) x) *
      archLevySinhWeight x) (Ioi 0)) :
    biScaleLevyEnergy f - biScaleLevyEnergy (fun u => |f u|) =
      2 * ∫ x in Ioi (0 : ℝ), archLevyDensity x *
        (autocorr (fun u => |f u|) x - autocorr f x) := by
  have h0 : autocorr (fun u => |f u|) 0 = autocorr f 0 := by
    unfold autocorr; simp only [add_zero, abs_mul_abs_self]
  unfold biScaleLevyEnergy
  rw [← integral_sub hJf hJg, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [h0, archLevySinhWeight, exp_half_div_sinh_eq hx]
  ring

/-! ### 5. The trivial-zero moments -/

/-- The trivial-zero moment `ν_j(F) = ∫ F(u) e^{(2j+1/2)u} du`. -/
def expMoment (F : ℝ → ℝ) (j : ℕ) : ℝ := ∫ u, F u * expWeight j u

lemma abs_expMoment_le {F : ℝ → ℝ} {c B : ℝ} (hc : 0 ≤ c)
    (hB : ∀ u, |F u| ≤ B) (h0 : ∀ u, 0 < u → F u = 0) (hl : ∀ u, u < -c → F u = 0) (j : ℕ) :
    |expMoment F j| ≤ B / (2 * (j : ℝ) + 1 / 2) := by
  set α : ℝ := 2 * (j : ℝ) + 1 / 2 with hα
  have hαpos : 0 < α := by positivity
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hpt : ∀ u, |F u * expWeight j u| ≤
      (Icc (-c) 0).indicator (fun u => B * Real.exp (α * u)) u := by
    intro u
    by_cases hu : u ∈ Icc (-c) 0
    · rw [indicator_of_mem hu, abs_mul, expWeight, ← hα, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hB u) (Real.exp_pos _).le
    · rw [indicator_of_notMem hu]
      have hF0 : F u = 0 := by
        simp only [mem_Icc, not_and_or, not_le] at hu
        rcases hu with h | h
        · exact hl u h
        · exact h0 u h
      simp [hF0]
  have hint : Integrable ((Icc (-c) 0).indicator fun u => B * Real.exp (α * u)) :=
    ((by fun_prop : Continuous fun u : ℝ => B * Real.exp (α * u)).integrableOn_Icc
      ).integrable_indicator measurableSet_Icc
  have hval : (∫ u, (Icc (-c) 0).indicator (fun u => B * Real.exp (α * u)) u) =
      B * ((Real.exp (α * 0) - Real.exp (α * -c)) / α) := by
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => Real.exp (α * u) / α)
        (fun u _ => by
          have hα0 : α ≠ 0 := hαpos.ne'
          have h1 : HasDerivAt (fun u : ℝ => α * u) α u := by
            simpa using (hasDerivAt_id u).const_mul α
          have h := h1.exp.div_const α
          exact h.congr_deriv (by rw [mul_div_assoc, div_self hα0, mul_one]))
        ((by fun_prop : Continuous fun u : ℝ => Real.exp (α * u)).intervalIntegrable _ _)]
    ring
  have hle : (Real.exp (α * 0) - Real.exp (α * -c)) / α ≤ 1 / α := by
    rw [mul_zero, Real.exp_zero]
    exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (α * -c)]) hαpos.le
  calc |expMoment F j| ≤ ∫ u, |F u * expWeight j u| := abs_integral_le_integral_abs
    _ ≤ ∫ u, (Icc (-c) 0).indicator (fun u => B * Real.exp (α * u)) u :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = B * ((Real.exp (α * 0) - Real.exp (α * -c)) / α) := hval
    _ ≤ B * (1 / α) := mul_le_mul_of_nonneg_left hle hB0
    _ = B / α := by ring

lemma summable_expMoment_sq {F : ℝ → ℝ} (hF : Continuous F) {c B : ℝ} (hc : 0 ≤ c)
    (hB : ∀ u, |F u| ≤ B) (h0 : ∀ u, 0 < u → F u = 0) (hl : ∀ u, u < -c → F u = 0) :
    Summable fun j => expMoment F j ^ 2 := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hS : Summable fun j : ℕ => 4 * B ^ 2 * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hS
  have h := abs_expMoment_le hc hB h0 hl j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hα : ((j : ℝ) + 1) / 2 ≤ 2 * (j : ℝ) + 1 / 2 := by
    have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith
  have h2 : B / (2 * (j : ℝ) + 1 / 2) ≤ 2 * B / ((j : ℝ) + 1) := by
    calc B / (2 * (j : ℝ) + 1 / 2) ≤ B / (((j : ℝ) + 1) / 2) :=
          div_le_div_of_nonneg_left hB0 (by positivity) hα
      _ = 2 * B / ((j : ℝ) + 1) := by field_simp
  have h3 : |expMoment F j| ≤ 2 * B / ((j : ℝ) + 1) := h.trans h2
  have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [sq_abs] at h4
  calc expMoment F j ^ 2 ≤ (2 * B / ((j : ℝ) + 1)) ^ 2 := h4
    _ = 4 * B ^ 2 * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) := by push_cast; field_simp; ring

/-! ### 6. The defect inequality -/

/-- Pointwise kernel bound on the pair `(u, u + x)`, `x > 0`. -/
lemma pairDefect_kernel_le {c : ℝ} (hct : c ≤ screwSignThreshold) {f : ℝ → ℝ}
    (h0 : ∀ u, 0 < u → f u = 0) (hl : ∀ u, u < -c → f u = 0) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ENNReal.ofReal (pairDefect f u (u + x) * (coshWeight u * coshWeight (u + x))) ≤
      ENNReal.ofReal (archLevyDensity x * pairDefect f u (u + x)) +
        ∑' j, ENNReal.ofReal (pairDefect f u (u + x) * (expWeight j u * expWeight j (u + x))) := by
  by_cases hD : pairDefect f u (u + x) = 0
  · rw [hD, zero_mul, ENNReal.ofReal_zero]; exact zero_le
  have hfu : f u ≠ 0 := fun h => hD (pairDefect_eq_zero_of_left h)
  have hfv : f (u + x) ≠ 0 := fun h => hD (pairDefect_eq_zero_of_right h)
  have hu0 : u ≤ 0 := not_lt.mp fun h => hfu (h0 u h)
  have huc : -c ≤ u := not_lt.mp fun h => hfu (hl u h)
  have hv0 : u + x ≤ 0 := not_lt.mp fun h => hfv (h0 _ h)
  have hvc : -c ≤ u + x := not_lt.mp fun h => hfv (hl _ h)
  have hk := four_mul_cosh_mul_cosh_le (p := -u) (q := -(u + x)) (by linarith) (by linarith)
    (by linarith) (by linarith) (by intro h; linarith)
  have habs : |-u - -(u + x)| = x := by
    rw [show -u - -(u + x) = x by ring, abs_of_pos hx]
  have hsum : 0 < -u + -(u + x) := by linarith
  have hmodes : ∀ j : ℕ, Real.exp (-((2 * (j : ℝ) + 1 / 2) * (-u + -(u + x)))) =
      expWeight j u * expWeight j (u + x) := fun j => by
    unfold expWeight; rw [← Real.exp_add]; congr 1; ring
  rw [habs, _root_.RHTower.archLevyDensity_eq_tsum hsum] at hk
  simp only [hmodes] at hk
  have hS : Summable fun j : ℕ => expWeight j u * expWeight j (u + x) := by
    have h := summable_levyModes hsum
    simp only [hmodes] at h
    exact h
  have hD0 := pairDefect_nonneg f u (u + x)
  have hew : ∀ j, 0 ≤ pairDefect f u (u + x) * (expWeight j u * expWeight j (u + x)) :=
    fun j => mul_nonneg hD0 (by unfold expWeight; positivity)
  have hcw : coshWeight u * coshWeight (u + x) =
      4 * Real.cosh (-u / 2) * Real.cosh (-(u + x) / 2) := by
    unfold coshWeight; rw [neg_div, Real.cosh_neg, neg_div, Real.cosh_neg]; ring
  rw [← ENNReal.ofReal_tsum_of_nonneg hew (hS.mul_left _),
    ← ENNReal.ofReal_add (mul_nonneg (archLevyDensity_pos hx).le hD0) (tsum_nonneg hew)]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left, hcw]
  calc pairDefect f u (u + x) * (4 * Real.cosh (-u / 2) * Real.cosh (-(u + x) / 2))
      ≤ pairDefect f u (u + x) * (archLevyDensity x +
          ∑' j, expWeight j u * expWeight j (u + x)) := mul_le_mul_of_nonneg_left hk hD0
    _ = _ := by ring

/-- Lag by lag: `Δ_h(x) ≤ ω(x) Δ_1(x) + Σ_j Δ_{e_j}(x)` in `[0, ∞]`. -/
lemma perLag_le {c : ℝ} (hct : c ≤ screwSignThreshold) {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (h0 : ∀ u, 0 < u → f u = 0) (hl : ∀ u, u < -c → f u = 0)
    {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (∫ u, pairDefect f u (u + x) * (coshWeight u * coshWeight (u + x))) ≤
      ENNReal.ofReal (archLevyDensity x * ∫ u, pairDefect f u (u + x)) +
        ∑' j, ENNReal.ofReal
          (∫ u, pairDefect f u (u + x) * (expWeight j u * expWeight j (u + x))) := by
  have hcw : Continuous coshWeight := by unfold coshWeight; fun_prop
  have hew (j : ℕ) : Continuous (expWeight j) := by unfold expWeight; fun_prop
  have hnn (k : ℝ → ℝ) (hk : ∀ u, 0 ≤ k u) : ∀ u, 0 ≤ pairDefect f u (u + x) * (k u * k (u + x)) :=
    fun u => mul_nonneg (pairDefect_nonneg f u (u + x)) (mul_nonneg (hk u) (hk (u + x)))
  have hcos : ∀ u, 0 ≤ coshWeight u := fun u => by unfold coshWeight; positivity
  have hexp (j : ℕ) : ∀ u, 0 ≤ expWeight j u := fun u => by unfold expWeight; positivity
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_pairDefect_shift hf hfc hcw x)
      (Eventually.of_forall (hnn _ hcos)),
    ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal ((integrable_pairDefect_shift' hf hfc x).const_mul _)
      (Eventually.of_forall fun u => mul_nonneg (archLevyDensity_pos hx).le
        (pairDefect_nonneg f u (u + x)))]
  have hsum : (∑' j, ENNReal.ofReal
      (∫ u, pairDefect f u (u + x) * (expWeight j u * expWeight j (u + x)))) =
      ∫⁻ u, ∑' j, ENNReal.ofReal (pairDefect f u (u + x) * (expWeight j u * expWeight j (u + x))) := by
    rw [lintegral_tsum fun j => ((by unfold pairDefect expWeight; fun_prop :
      Continuous fun u => pairDefect f u (u + x) * (expWeight j u * expWeight j (u + x))
        ).measurable.ennreal_ofReal.aemeasurable)]
    refine tsum_congr fun j => ?_
    exact ofReal_integral_eq_lintegral_ofReal (integrable_pairDefect_shift hf hfc (hew j) x)
      (Eventually.of_forall (hnn _ (hexp j)))
  rw [hsum, ← lintegral_add_left ((by unfold pairDefect; fun_prop :
    Continuous fun u => archLevyDensity x * pairDefect f u (u + x)).measurable.ennreal_ofReal)]
  exact lintegral_mono fun u => pairDefect_kernel_le hct h0 hl hx u

/-- **The defect inequality**: for `f` vanishing off `[−c, 0]`, `c ≤ t_*`,
`(∫|f|h)² − (∫ f h)² ≤ (𝒥(f) − 𝒥(|f|)) + Σ_j (ν_j(|f|)² − ν_j(f)²)`. -/
theorem pole_defect_le {c : ℝ} (hc0 : 0 ≤ c) (hct : c ≤ screwSignThreshold) {f : ℝ → ℝ}
    (hf : Continuous f) (h0 : ∀ u, 0 < u → f u = 0) (hl : ∀ u, u < -c → f u = 0)
    (hJf : IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) (Ioi 0)) :
    (∫ u, |f u| * coshWeight u) ^ 2 - (∫ u, f u * coshWeight u) ^ 2 ≤
      (biScaleLevyEnergy f - biScaleLevyEnergy (fun u => |f u|)) +
        ∑' j, (expMoment (fun u => |f u|) j ^ 2 - expMoment f j ^ 2) := by
  have hfs : ∀ x, c < |x| → f x = 0 := fun x hx => by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx; exact h0 x (by linarith)
    · rw [abs_of_neg h] at hx; exact hl x (by linarith)
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) fun x hx =>
      hfs x (lt_of_not_ge fun h => hx (abs_le.mp h))
  have hg : Continuous fun u => |f u| := hf.abs
  have hgs : ∀ x, c < |x| → |f x| = 0 := fun x hx => by rw [hfs x hx, abs_zero]
  have hcw : Continuous coshWeight := by unfold coshWeight; fun_prop
  have hew (j : ℕ) : Continuous (expWeight j) := by unfold expWeight; fun_prop
  have hJg := integrableOn_levy_abs hf hfc hJf
  -- weighted squares as half-line autocorrelation integrals
  have hws (k : ℝ → ℝ) (hk : Continuous k) :
      (∫ u, |f u| * k u) ^ 2 - (∫ u, f u * k u) ^ 2 =
        2 * ∫ x in Ioi (0 : ℝ), (∫ u, pairDefect f u (u + x) * (k u * k (u + x))) := by
    rw [sq_integral_eq_two_mul_integral_autocorr (G := fun u => |f u| * k u) (hg.mul hk)
        (hfc.mono fun u hu h0 => hu (by simp [h0])),
      sq_integral_eq_two_mul_integral_autocorr (G := fun u => f u * k u) (hf.mul hk)
        (hfc.mono fun u hu h0 => hu (by simp [h0])), ← mul_sub,
      ← integral_sub
        (integrable_autocorr' (G := fun u => |f u| * k u) (hg.mul hk) (R := c)
          fun x hx => by simp [hgs x hx]).integrableOn
        (integrable_autocorr' (G := fun u => f u * k u) (hf.mul hk) (R := c)
          fun x hx => by simp [hfs x hx]).integrableOn]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ =>
      (integral_pairDefect_shift hf hfc hk x).symm
  have hgap (k : ℝ → ℝ) (hk : Continuous k) (hk0 : ∀ u, 0 ≤ k u) (x : ℝ) :
      0 ≤ ∫ u, pairDefect f u (u + x) * (k u * k (u + x)) :=
    integral_nonneg fun u => mul_nonneg (pairDefect_nonneg f u (u + x))
      (mul_nonneg (hk0 u) (hk0 (u + x)))
  have hgapI (k : ℝ → ℝ) (hk : Continuous k) :
      IntegrableOn (fun x => ∫ u, pairDefect f u (u + x) * (k u * k (u + x))) (Ioi 0) := by
    have h := ((integrable_autocorr' (G := fun u => |f u| * k u) (hg.mul hk) (R := c)
      fun x hx => by simp [hgs x hx]).sub (integrable_autocorr' (G := fun u => f u * k u)
      (hf.mul hk) (R := c) fun x hx => by simp [hfs x hx])).integrableOn (s := Ioi (0 : ℝ))
    refine h.congr_fun (fun x _ => (integral_pairDefect_shift hf hfc hk x).symm) measurableSet_Ioi
  have hcont (k : ℝ → ℝ) (hk : Continuous k) :
      Continuous fun x => ∫ u, pairDefect f u (u + x) * (k u * k (u + x)) := by
    have h := (continuous_autocorr' (G := fun u => |f u| * k u) (hg.mul hk)
      (hfc.mono fun u hu h0 => hu (by simp [h0]))).sub
      (continuous_autocorr' (G := fun u => f u * k u) (hf.mul hk)
        (hfc.mono fun u hu h0 => hu (by simp [h0])))
    exact h.congr fun x => (integral_pairDefect_shift hf hfc hk x).symm
  have hcos0 : ∀ u, 0 ≤ coshWeight u := fun u => by unfold coshWeight; positivity
  have hexp0 (j : ℕ) : ∀ u, 0 ≤ expWeight j u := fun u => by unfold expWeight; positivity
  -- the Lévy gap
  have hlevy : biScaleLevyEnergy f - biScaleLevyEnergy (fun u => |f u|) =
      2 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, pairDefect f u (u + x) := by
    rw [levy_sub_eq hJf hJg]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    exact congrArg (fun t => archLevyDensity x * t) (integral_pairDefect_shift' hf hfc x).symm
  have hlevyI : IntegrableOn
      (fun x => archLevyDensity x * ∫ u, pairDefect f u (u + x)) (Ioi 0) := by
    have h := (hJf.sub hJg).const_mul (1 / 2 : ℝ)
    refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
    have h00 : autocorr (fun u => |f u|) 0 = autocorr f 0 := by
      unfold autocorr; simp only [add_zero, abs_mul_abs_self]
    show (1 / 2 : ℝ) * ((autocorr f 0 - autocorr f x) * archLevySinhWeight x -
        (autocorr (fun u => |f u|) 0 - autocorr (fun u => |f u|) x) * archLevySinhWeight x) =
      archLevyDensity x * ∫ u, pairDefect f u (u + x)
    rw [integral_pairDefect_shift' hf hfc x, archLevySinhWeight, exp_half_div_sinh_eq hx, h00]
    ring
  have hgap1 (x : ℝ) : 0 ≤ ∫ u, pairDefect f u (u + x) :=
    integral_nonneg fun u => pairDefect_nonneg f u (u + x)
  have hcont1 : Continuous fun x => ∫ u, pairDefect f u (u + x) :=
    ((continuous_autocorr' hg hfc.abs).sub (continuous_autocorr' hf hfc)).congr fun x =>
      (integral_pairDefect_shift' hf hfc x).symm
  -- summability of the moment gaps
  obtain ⟨B, hB⟩ : ∃ B, ∀ u, |f u| ≤ B := by
    obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hf  -- ‖f u‖ ≤ B
    exact ⟨B, fun u => by simpa [Real.norm_eq_abs] using hB u⟩
  have hSg := summable_expMoment_sq hg hc0 (B := B) (fun u => by rw [abs_abs]; exact hB u)
    (fun u hu => by rw [h0 u hu, abs_zero]) (fun u hu => by rw [hl u hu, abs_zero])
  have hSf := summable_expMoment_sq hf hc0 hB h0 hl
  have hmom (j : ℕ) : expMoment (fun u => |f u|) j ^ 2 - expMoment f j ^ 2 =
      2 * ∫ x in Ioi (0 : ℝ), (∫ u, pairDefect f u (u + x) *
        (expWeight j u * expWeight j (u + x))) := hws (expWeight j) (hew j)
  have hmom0 (j : ℕ) : 0 ≤ expMoment (fun u => |f u|) j ^ 2 - expMoment f j ^ 2 := by
    rw [hmom j]
    exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun x _ =>
      hgap _ (hew j) (hexp0 j) x)
  have hlev0 : 0 ≤ biScaleLevyEnergy f - biScaleLevyEnergy (fun u => |f u|) := by
    rw [hlevy]
    exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (archLevyDensity_pos hx).le (hgap1 x))
  have hRHS0 : 0 ≤ (biScaleLevyEnergy f - biScaleLevyEnergy (fun u => |f u|)) +
      ∑' j, (expMoment (fun u => |f u|) j ^ 2 - expMoment f j ^ 2) :=
    add_nonneg hlev0 (tsum_nonneg hmom0)
  have eL : ENNReal.ofReal ((∫ u, |f u| * coshWeight u) ^ 2 - (∫ u, f u * coshWeight u) ^ 2) =
      2 * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
        (∫ u, pairDefect f u (u + x) * (coshWeight u * coshWeight (u + x))) := by
    rw [hws coshWeight hcw, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ofReal_integral_eq_lintegral_ofReal (hgapI _ hcw)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => hgap _ hcw hcos0 x)]
  have eJ : ENNReal.ofReal (biScaleLevyEnergy f - biScaleLevyEnergy (fun u => |f u|)) =
      2 * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
        (archLevyDensity x * ∫ u, pairDefect f u (u + x)) := by
    rw [hlevy, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ofReal_integral_eq_lintegral_ofReal hlevyI
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
          mul_nonneg (archLevyDensity_pos hx).le (hgap1 x))]
  have eM (j : ℕ) : ENNReal.ofReal (expMoment (fun u => |f u|) j ^ 2 - expMoment f j ^ 2) =
      2 * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
        (∫ u, pairDefect f u (u + x) * (expWeight j u * expWeight j (u + x))) := by
    rw [hmom j, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ofReal_integral_eq_lintegral_ofReal (hgapI _ (hew j))
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => hgap _ (hew j) (hexp0 j) x)]
  rw [← ENNReal.ofReal_le_ofReal_iff hRHS0, ENNReal.ofReal_add hlev0 (tsum_nonneg hmom0),
    ENNReal.ofReal_tsum_of_nonneg hmom0 (hSg.sub hSf), eL, eJ]
  simp only [eM]
  rw [ENNReal.tsum_mul_left, ← mul_add]
  gcongr
  have hmeasJ : Measurable fun x => ENNReal.ofReal (archLevyDensity x * ∫ u, pairDefect f u (u + x)) :=
    (measurable_archLevyDensity.mul hcont1.measurable).ennreal_ofReal
  rw [← lintegral_tsum fun j => ((hcont _ (hew j)).measurable.ennreal_ofReal.aemeasurable),
    ← lintegral_add_left hmeasJ]
  exact setLIntegral_mono' measurableSet_Ioi fun x hx => perLag_le hct hf hfc h0 hl hx

/-! ### 7. The even sector under the contraction -/

/-- The even sector of a half-window test in kernel form:
`W(F) + 𝓗₀(F) = Γ‖F‖² + 𝒥(F) + (∫ F h)² − Σ_j ν_j(F)²`. -/
lemma evenSector_eq {F : ℝ → ℝ} (hF : Continuous F) {c : ℝ} (hc0 : 0 ≤ c)
    (hct : c ≤ screwSignThreshold) (h0 : ∀ u, 0 < u → F u = 0) (hl : ∀ u, u < -c → F u = 0)
    (hJ : IntegrableOn (fun x => (autocorr F 0 - autocorr F x) * archLevySinhWeight x) (Ioi 0)) :
    weilQuad F + collarHankel 0 F = EF.gammaBracket 0 * autocorr F 0 + biScaleLevyEnergy F +
      (∫ u, F u * coshWeight u) ^ 2 - ∑' j, expMoment F j ^ 2 := by
  have hFs : ∀ x, c < |x| → F x = 0 := fun x hx => by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx; exact h0 x (by linarith)
    · rw [abs_of_neg h] at hx; exact hl x (by linarith)
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) fun x hx =>
      hFs x (lt_of_not_ge fun h => hx (abs_le.mp h))
  have hlog : 2 * c < Real.log 2 := by
    have := screwSignThreshold_lt
    linarith [Real.log_two_gt_d9]
  rw [weilQuad_eq_of_short hF hFc hlog hFs hJ]
  obtain ⟨B, hB⟩ : ∃ B, ∀ u, |F u| ≤ B := by
    obtain ⟨B, hB⟩ := hFc.exists_bound_of_continuous hF
    exact ⟨B, fun u => by simpa [Real.norm_eq_abs] using hB u⟩
  have hS := summable_expMoment_sq hF hc0 hB h0 hl
  have hint (k : ℝ → ℝ) (hk : Continuous k) : Integrable fun u => F u * k u :=
    (hF.mul hk).integrable_of_hasCompactSupport (hFc.mono fun u hu h0 => hu (by simp [h0]))
  have hP : (∫ u, Real.exp (u / 2) * F u) = expMoment F 0 := by
    unfold expMoment expWeight
    exact integral_congr_ae (Eventually.of_forall fun u => by
      beta_reduce; simp only [Nat.cast_zero, mul_zero, zero_add]; rw [mul_comm]; congr 2; ring)
  have hM : leftMoment F (1 / 2) = ∫ u, Real.exp (-(u / 2)) * F u := by
    unfold leftMoment
    exact integral_congr_ae (Eventually.of_forall fun u => by
      beta_reduce; rw [mul_comm]; congr 2; ring)
  have hT (k : ℕ) : leftMoment F (trivialExponent k) = expMoment F (k + 1) := by
    unfold leftMoment expMoment expWeight trivialExponent
    exact integral_congr_ae (Eventually.of_forall fun u => by
      beta_reduce; push_cast; congr 2; ring)
  have hQ : (∫ u, F u * coshWeight u) = expMoment F 0 + ∫ u, Real.exp (-(u / 2)) * F u := by
    rw [← hP, ← integral_add
      ((hint (fun u => Real.exp (u / 2)) (by fun_prop)).congr
        (Eventually.of_forall fun u => mul_comm _ _))
      ((hint (fun u => Real.exp (-(u / 2))) (by fun_prop)).congr
        (Eventually.of_forall fun u => mul_comm _ _))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [coshWeight, Real.cosh_eq]; ring
  unfold collarHankel
  simp only [Real.exp_zero, mul_zero, zero_mul, one_mul, hM, hT]
  rw [hS.tsum_eq_zero_add, hQ, hP]
  ring

/-- **The even sector is Markov below the plastic threshold.** For `0 ≤ c ≤ t_*` and every `C²`
test `f` vanishing off `[−c, 0]`, `W(|f|) + 𝓗₀(|f|) ≤ W(f) + 𝓗₀(f)`. -/
theorem evenSector_abs_le {c : ℝ} (hc0 : 0 ≤ c) (hct : c ≤ screwSignThreshold) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (h0 : ∀ u, 0 < u → f u = 0) (hl : ∀ u, u < -c → f u = 0) :
    weilQuad (fun u => |f u|) + collarHankel 0 (fun u => |f u|) ≤
      weilQuad f + collarHankel 0 f := by
  have hfs : ∀ x, c < |x| → f x = 0 := fun x hx => by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx; exact h0 x (by linarith)
    · rw [abs_of_neg h] at hx; exact hl x (by linarith)
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) fun x hx =>
      hfs x (lt_of_not_ge fun h => hx (abs_le.mp h))
  have hJf := integrableOn_biScaleLevyIntegrand hf hfc
  have hJg := integrableOn_levy_abs hf.continuous hfc hJf
  have hg := hf.continuous.abs
  obtain ⟨B, hB⟩ : ∃ B, ∀ u, |f u| ≤ B := by
    obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hf.continuous
    exact ⟨B, fun u => by simpa [Real.norm_eq_abs] using hB u⟩
  have hSg := summable_expMoment_sq hg hc0 (B := B) (fun u => by rw [abs_abs]; exact hB u)
    (fun u hu => by rw [h0 u hu, abs_zero]) (fun u hu => by rw [hl u hu, abs_zero])
  have hSf := summable_expMoment_sq hf.continuous hc0 hB h0 hl
  rw [evenSector_eq hf.continuous hc0 hct h0 hl hJf,
    evenSector_eq hg hc0 hct (fun u hu => by rw [h0 u hu, abs_zero])
      (fun u hu => by rw [hl u hu, abs_zero]) hJg]
  have hdef := pole_defect_le hc0 hct hf.continuous h0 hl hJf
  have h00 : autocorr (fun u => |f u|) 0 = autocorr f 0 := by
    unfold autocorr; simp only [add_zero, abs_mul_abs_self]
  rw [hSg.tsum_sub hSf] at hdef
  rw [h00]
  linarith

end GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw

end
