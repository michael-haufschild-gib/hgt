import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheCriticalExponent
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.TwoPrimeCatalanSeparationAndContinuumTowerObstruction
import GaloisForLFunctions.RHTower.PolarConeAbelRigidity
import GaloisForLFunctions.RHTower.WeilPositivityImaginaryQuadraticConductorLaw
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction

/-!
# The gauge becomes visible at the critical exponent

A twisted explicit formula replaces the prime weights `Λ(n)` by `λ(n)`, `|λ(n)| ≤ Λ(n)`: sign twins,
the Liouville twin `(−1)^{Ω(n)} Λ(n)`, any truncation. Its quadratic form on real tests is
`Q_λ(f) = Re W_λ(f, f)` (`weilQuadTw`), and it differs from `ζ`'s by finitely many prime lags on
a window (`weilQuadTw_eq`).

* **Continuity** (`weilQuadTw_add_le`): `Q_λ` moves in the Lévy norm like `Q`, the extra lags costing
  at most `4 P_R (2‖f‖₂‖d‖₂ + ‖d‖₂²)`.
* **The overlap law for every twist** (`weilPositive_iff_atomicFamilies_nonneg`): for dilations `κ`
  of overlap growth — widths `1/κ_N` with overlap ratio beating `√(log N)`, e.g. `N^{−θ}`, `θ < 1` —
  `Q_λ ≥ 0` on every real test iff, for all large `N`, `Q_λ ≥ 0` on the atomic families of width
  `1/κ_N`.
* **Every twin that fails is seen** (`atomicFamilies_negative_iff`): a twist `|λ| ≤ Λ` is negative on
  those atomic families for infinitely many `N` iff it is not Weil positive. Unconditional instances:
  the Liouville twin, from its certified ground eigenvalue `< −3/10` at aperture `23/40`
  (`liouville_atomicFamilies_negative`); the scalings `cΛ`, `−1 ≤ c < 1`
  (`scaled_atomicFamilies_negative`); the quadratic mixtures `Λ(1 − t + tχ)`, `0 < t ≤ 1`, `χ` real
  primitive (`quadraticMix_atomicFamilies_negative`).

At the spacing (width `≤ c₀ δ_N`) every twist satisfies the stability law with `ζ`'s constants
(`TheSpacingScaleLawIsUniversal`); under overlap growth every twist that fails anywhere fails on the
atomic families, while `ζ` holds there iff RH. On `ζ`'s side the separation is the Riemann hypothesis
(`riemannHypothesis_imp_liouville_separation`).
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower Zeta23
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### Twisted forms -/

/-- The twisted prime coefficient `λ(n)/√n` on `n ≥ 2`. -/
def twistCoeff (lam : ℕ → ℝ) (n : ℕ) : ℝ := if 2 ≤ n then lam n / Real.sqrt n else 0

/-- The two Hecke pairings `∫ f(t) f(t − log n) + ∫ f(t) f(t + log n)` of a real test. -/
def pairing (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∫ t, f t * f (t - Real.log n)) + ∫ t, f t * f (t + Real.log n)

/-- **The twisted quadratic form** `Q_λ(f) = Re W_λ(f, f)` on real tests. -/
def weilQuadTw (lam : ℕ → ℝ) (f : ℝ → ℝ) : ℝ :=
  (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re

theorem weilTest_lags (f : ℝ → ℝ) (n : ℕ) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (Real.log n) +
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-Real.log n) = (pairing f n : ℂ) := by
  rw [weilTest_ofReal_ofReal_eq, weilTest_ofReal_ofReal_eq, pairing]
  push_cast
  simp only [sub_neg_eq_add]

theorem pairing_eq_zero {R : ℝ} {f : ℝ → ℝ} (hf : SupportedIn R f) {n : ℕ}
    (hn : n ∉ Finset.range (lagRange R)) : pairing f n = 0 := by
  have hn' : lagRange R ≤ n := by simpa using hn
  have hl := two_mul_lt_abs_log_of_lagRange_le hn'
  have e1 : ∀ t, f t * f (t - Real.log n) = 0 := fun t => by
    rw [sub_eq_add_neg]
    exact mul_shift_eq_zero_of_supportedIn hf hf (by rwa [abs_neg]) t
  have e2 : ∀ t, f t * f (t + Real.log n) = 0 := fun t => mul_shift_eq_zero_of_supportedIn hf hf hl t
  simp [pairing, e1, e2]

/-- **The twist moves finitely many lags**: on a window,
`Q_λ(f) = Q(f) + Σ_{n < K_R} (Λ(n)/√n − λ(n)/√n) · pairing_n(f)`. -/
theorem weilQuadTw_eq (lam : ℕ → ℝ) {R : ℝ} {f : ℝ → ℝ} (hf : SupportedIn R f) :
    weilQuadTw lam f = weilQuad f + ∑ n ∈ Finset.range (lagRange R),
      (vonMangoldtAtom n - twistCoeff lam n) * pairing f n := by
  have hvan : ∀ (c : ℕ → ℝ), ∀ n ∉ Finset.range (lagRange R), ((c n : ℝ) : ℂ) *
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (Real.log n) +
        EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-Real.log n)) = 0 := by
    intro c n hn
    rw [weilTest_lags, pairing_eq_zero hf hn]
    simp
  unfold weilQuadTw weilQuad weilFullFunctional
  rw [tsum_eq_sum (hvan fun n => if 2 ≤ n then lam n / Real.sqrt n else 0),
    tsum_eq_sum (hvan fun n => if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
      else 0)]
  simp only [weilTest_lags, Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have : ∀ n ∈ Finset.range (lagRange R), (vonMangoldtAtom n - twistCoeff lam n) * pairing f n =
      (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) * pairing f n -
        (if 2 ≤ n then lam n / Real.sqrt n else 0) * pairing f n := fun n _ => by
    unfold vonMangoldtAtom twistCoeff; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
  ring

/-- **Translation invariance** of the twisted form. -/
theorem weilQuadTw_comp_sub (lam : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ) :
    weilQuadTw lam (fun u => f (u - c)) = weilQuadTw lam f := by
  unfold weilQuadTw
  have h : EF.weilTest (fun u => (f (u - c) : ℂ)) (fun u => (f (u - c) : ℂ)) =
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) := by
    funext y
    have := ArithmeticCastelnuovoSeveri.weilTest_translate c c (fun u => (f u : ℂ))
      (fun u => (f u : ℂ)) y
    simp only [sub_self, sub_zero] at this
    exact this
  rw [h]

/-! ### Continuity of twisted forms -/

variable {f d : ℝ → ℝ}

/-- One lag moves by `L²` amounts: `|pairing_n(f + d) − pairing_n(f)| ≤ 2(2‖f‖‖d‖ + ‖d‖²)`. -/
theorem abs_pairing_add_sub_le (hf : Continuous f) (hfc : HasCompactSupport f) (hd : Continuous d)
    (hdc : HasCompactSupport d) (n : ℕ) :
    |pairing (fun u => f u + d u) n - pairing f n| ≤
      2 * (2 * (Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) + ∫ u, d u ^ 2) := by
  set nf := Real.sqrt (∫ u, f u ^ 2)
  set nd := Real.sqrt (∫ u, d u ^ 2)
  have hnd2 : nd * nd = ∫ u, d u ^ 2 := Real.mul_self_sqrt (integral_nonneg fun u => sq_nonneg _)
  have hlag : ∀ c : ℝ, |(∫ t, (f t + d t) * (f (t + c) + d (t + c))) - ∫ t, f t * f (t + c)| ≤
      2 * (nf * nd) + nd * nd := by
    intro c
    have i1 : Integrable fun t => f t * d (t + c) :=
      (hf.mul (hd.comp (continuous_add_const c))).integrable_of_hasCompactSupport hfc.mul_right
    have i2 : Integrable fun t => d t * f (t + c) :=
      (hd.mul (hf.comp (continuous_add_const c))).integrable_of_hasCompactSupport hdc.mul_right
    have i3 : Integrable fun t => d t * d (t + c) :=
      (hd.mul (hd.comp (continuous_add_const c))).integrable_of_hasCompactSupport hdc.mul_right
    have i0 : Integrable fun t => f t * f (t + c) :=
      (hf.mul (hf.comp (continuous_add_const c))).integrable_of_hasCompactSupport hfc.mul_right
    have e : (∫ t, (f t + d t) * (f (t + c) + d (t + c))) - ∫ t, f t * f (t + c) =
        (∫ t, f t * d (t + c)) + (∫ t, d t * f (t + c)) + ∫ t, d t * d (t + c) := by
      rw [show (fun t => (f t + d t) * (f (t + c) + d (t + c))) =
          fun t => f t * f (t + c) + (f t * d (t + c) + d t * f (t + c) + d t * d (t + c)) by
        funext t; ring,
        integral_add (f := fun t => f t * f (t + c))
          (g := fun t => f t * d (t + c) + d t * f (t + c) + d t * d (t + c)) i0 ((i1.add i2).add i3),
        integral_add (f := fun t => f t * d (t + c) + d t * f (t + c))
          (g := fun t => d t * d (t + c)) (i1.add i2) i3,
        integral_add (f := fun t => f t * d (t + c)) (g := fun t => d t * f (t + c)) i1 i2]
      ring
    rw [e]
    have b1 := abs_integral_mul_shift_le hf hfc hd hdc c
    have b2 := abs_integral_mul_shift_le hd hdc hf hfc c
    have b3 := abs_integral_mul_shift_le hd hdc hd hdc c
    calc _ ≤ |∫ t, f t * d (t + c)| + |∫ t, d t * f (t + c)| + |∫ t, d t * d (t + c)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ nf * nd + nd * nf + nd * nd := add_le_add (add_le_add b1 b2) b3
      _ = 2 * (nf * nd) + nd * nd := by ring
  have hm := hlag (-Real.log n)
  have hp := hlag (Real.log n)
  simp only [← sub_eq_add_neg] at hm
  rw [hnd2] at hm hp
  unfold pairing
  rw [show ∀ a b c e : ℝ, a + b - (c + e) = (a - c) + (b - e) by intros; ring]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- **Continuity of twisted forms** in the Lévy norm. -/
theorem weilQuadTw_add_le {lam : ℕ → ℝ} (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n)
    {R : ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hd : ContDiff ℝ 2 d)
    (hdc : HasCompactSupport d) (hfR : SupportedIn R f) (hdR : SupportedIn R d) :
    weilQuadTw lam (fun u => f u + d u) ≤ weilQuadTw lam f +
      (2 * |gammaHardyPhaseRate 0| * (2 * (Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) +
          ∫ u, d u ^ 2) +
        (2 * (Real.sqrt (levyEnergy f) * Real.sqrt (levyEnergy d)) + levyEnergy d) +
        2 * primeMass R * (2 * (Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) +
          ∫ u, d u ^ 2) +
        4 * Real.cosh (R / 2) * (|coshHalfMoment f| + |sinhHalfMoment f|) * (∫ u, |d u|) +
        4 * Real.cosh (R / 2) ^ 2 * (∫ u, |d u|) ^ 2) +
      4 * primeMass R * (2 * (Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) +
          ∫ u, d u ^ 2) := by
  have hQ := weilQuad_add_le hf hfc hd hdc hfR hdR
  rw [weilQuadTw_eq lam (supportedIn_add hfR hdR), weilQuadTw_eq lam hfR]
  set X := 2 * (Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) + ∫ u, d u ^ 2
  have hcoef : ∀ n, |vonMangoldtAtom n - twistCoeff lam n| ≤ 2 * vonMangoldtAtom n := by
    intro n
    unfold vonMangoldtAtom twistCoeff
    split_ifs
    · have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
      rw [← sub_div, abs_div, abs_of_pos hs]
      rw [div_le_iff₀ hs, show 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        Real.sqrt n = 2 * ArithmeticFunction.vonMangoldt n by field_simp]
      have := hlam n
      have h0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      calc |(ArithmeticFunction.vonMangoldt n : ℝ) - lam n| ≤
            |(ArithmeticFunction.vonMangoldt n : ℝ)| + |lam n| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg h0]; linarith
    · simp
  have hextra : ∑ n ∈ Finset.range (lagRange R), (vonMangoldtAtom n - twistCoeff lam n) *
        pairing (fun u => f u + d u) n -
      ∑ n ∈ Finset.range (lagRange R), (vonMangoldtAtom n - twistCoeff lam n) * pairing f n ≤
      4 * primeMass R * X := by
    rw [← Finset.sum_sub_distrib, primeMass, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [← mul_sub]
    have h1 := abs_pairing_add_sub_le hf.continuous hfc hd.continuous hdc n
    calc (vonMangoldtAtom n - twistCoeff lam n) * (pairing (fun u => f u + d u) n - pairing f n)
        ≤ |(vonMangoldtAtom n - twistCoeff lam n) * (pairing (fun u => f u + d u) n - pairing f n)| :=
          le_abs_self _
      _ = |vonMangoldtAtom n - twistCoeff lam n| *
          |pairing (fun u => f u + d u) n - pairing f n| := abs_mul _ _
      _ ≤ (2 * vonMangoldtAtom n) * (2 * X) :=
          mul_le_mul (hcoef n) h1 (abs_nonneg _) (by linarith [vonMangoldtAtom_nonneg' n])
      _ = 4 * vonMangoldtAtom n * X := by ring
  linarith

/-! ### The critical exponent for every twist -/

variable {φ : ℝ → ℝ} {κ : ℕ → ℝ}

/-- **The critical exponent law for every twist**: for `|λ| ≤ Λ`, a `C²` profile `φ` supported in
`[−1, 1]` with `∫ φ = 1`, and dilations `κ` of overlap growth: `Q_λ ≥ 0` on every real test iff, for
all large `N`, `Q_λ ≥ 0` on the atomic families of width `1/κ_N`. -/
theorem weilPositive_iff_atomicFamilies_nonneg {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) (hφ : ContDiff ℝ 2 φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowth κ) :
    (∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ weilQuadTw lam g) ↔
      ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, 0 ≤ weilQuadTw lam (atomicTest N x (dilate (κ N) φ)) := by
  constructor
  · intro hpos
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ hφ1 hk N x
    exact hpos _ h2 hc
  · intro H
    by_contra hneg0
    push Not at hneg0
    obtain ⟨g, hg, hgc, hneg⟩ := hneg0
    obtain ⟨R0, hR0⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    set R := max R0 0
    have hR : 0 ≤ R := le_max_right _ _
    have hgR : SupportedIn R g := fun u hu => by
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hR0 hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_max_left R0 0]
    obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
    have hM' : ∀ t, |g t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
    obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
    have hL : ∀ u v, |g u - g v| ≤ C * |u - v| := fun u v => by
      simpa [Real.dist_eq] using hC.dist_le_mul u v
    set B := blockSize R
    have hB : 1 ≤ B := by
      have h := Nat.le_ceil (1 + Real.exp (2 * R))
      have : (1 : ℝ) ≤ B := by
        have := Real.exp_pos (2 * R)
        simp only [B, blockSize] at h ⊢
        linarith
      exact_mod_cast this
    obtain ⟨he, hV⟩ := tendsto_synth hκ hB (∫ s, |φ s|) (∫ s, |deriv φ s|)
      (∫ s, |deriv (deriv φ) s|) M C (R + 3)
    have hErr := tendsto_weilErr g (R + 3) he hV
    -- the extra lags vanish with the error
    set P := primeMass (R + 3)
    have hX : Tendsto (fun n : ℕ => 4 * P * (2 * (Real.sqrt (∫ u, g u ^ 2) *
        (Real.sqrt (2 * (R + 3)) * synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M C
          (κ (n * B)) n)) + 2 * (R + 3) * synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M C
          (κ (n * B)) n ^ 2)) atTop (𝓝 0) := by
      have := (((((he.const_mul (Real.sqrt (2 * (R + 3)))).const_mul
        (Real.sqrt (∫ u, g u ^ 2))).const_mul 2).add ((he.pow 2).const_mul (2 * (R + 3)))).const_mul
        (4 * P))
      simpa using this
    have hTot := hErr.add hX
    rw [add_zero] at hTot
    have h1 := hTot.eventually (gt_mem_nhds (show (0 : ℝ) < -weilQuadTw lam g by linarith))
    have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
    have h2 := hNB.eventually H
    have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
    obtain ⟨n, hn1, hn2, hk, hn3⟩ := (h1.and (h2.and (h3.and (eventually_ge_atTop 1)))).exists
    obtain ⟨x, D, hx, hD2, hDc, hDsupp, hsqD, hN2, hLev, hN1⟩ :=
      exists_synthesis hφ hφ1 hφint hg hR hgR hM' hL hn3 hk
    have hgR3 : SupportedIn (R + 3) g := fun u hu => hgR u (by linarith)
    have hbound := weilQuadTw_add_le hlam hg hgc hD2 hDc hgR3 hDsupp
    have hmono := weilErr_mono (F := g) hsqD hN2 hLev (integral_nonneg fun u => abs_nonneg _) hN1
    have hX' : 4 * P * (2 * (Real.sqrt (∫ u, g u ^ 2) * Real.sqrt (∫ u, D u ^ 2)) + ∫ u, D u ^ 2) ≤
        4 * P * (2 * (Real.sqrt (∫ u, g u ^ 2) *
          (Real.sqrt (2 * (R + 3)) * synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M C
            (κ (n * B)) n)) + 2 * (R + 3) * synthErr (∫ s, |φ s|)
              (∫ s, |deriv φ s|) M C (κ (n * B)) n ^ 2) := by
      have hP : 0 ≤ P := primeMass_nonneg _
      gcongr
    have hval := hn2 x
    rw [hx, weilQuadTw_comp_sub lam (fun u => g u + D u)] at hval
    linarith

/-! ### The Liouville twin -/

/-- `|(−1)^{Ω(n)} Λ(n)| ≤ Λ(n)`. -/
theorem abs_liouvilleTwistedVonMangoldt_le (n : ℕ) :
    |SquareRootThreshold.liouvilleTwistedVonMangoldt n| ≤ ArithmeticFunction.vonMangoldt n := by
  unfold SquareRootThreshold.liouvilleTwistedVonMangoldt
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- **The Liouville twin is not Weil positive**: some real test has `Q_λ < 0` (its Rayleigh
quotient on the window of aperture `23/40` is below `−3/10`). -/
theorem exists_liouville_negative :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      weilQuadTw SquareRootThreshold.liouvilleTwistedVonMangoldt g < 0 := by
  obtain ⟨hbdd, hlt⟩ :=
    SelectivePositivityAndThresholdLaws.liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths
  have hne : (SelectivePositivityAndThresholdLaws.liouvilleWindowRayleighSet (23 / 40)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    unfold SelectivePositivityAndThresholdLaws.liouvilleWindowGroundEigenvalue at hlt
    rw [h, Real.sInf_empty] at hlt
    norm_num at hlt
  obtain ⟨q, hq, hqlt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨F, hF, hFc, -, hF2, rfl⟩ := hq
  refine ⟨F, hF, hFc, ?_⟩
  have : (weilFullFunctional SquareRootThreshold.liouvilleTwistedVonMangoldt
      (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re < 0 := by
    have h := (div_lt_iff₀ hF2).mp (hqlt.trans (by norm_num : -(3 / 10 : ℝ) < 0))
    linarith
  exact this

/-- **The Liouville twin fails under overlap growth**: for dilations `κ` of overlap growth, for
infinitely many `N`, some atomic test of width `1/κ_N` has negative Liouville form. -/
theorem liouville_atomicFamilies_negative (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowth κ) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, weilQuadTw SquareRootThreshold.liouvilleTwistedVonMangoldt
      (atomicTest N x (dilate (κ N) φ)) < 0 := by
  have h := (weilPositive_iff_atomicFamilies_nonneg abs_liouvilleTwistedVonMangoldt_le hφ hφ1 hφint
    hκ).not.mp (fun hpos => by
      obtain ⟨g, hg, hgc, hneg⟩ := exists_liouville_negative
      exact absurd (hpos g hg hgc) (not_le.mpr hneg))
  rw [Filter.not_eventually] at h
  refine h.mono fun N hN => ?_
  push Not at hN
  exact hN

/-- **Under RH overlap growth separates `ζ` from the Liouville twin**: for dilations `κ` of overlap
growth, for all large `N` Weil's form is nonnegative on the atomic families of width `1/κ_N`, and for
infinitely many of these `N` the Liouville form is negative on one of them. -/
theorem riemannHypothesis_imp_liouville_separation (hRH : RiemannHypothesis) (hφ : ContDiff ℝ 2 φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowth κ) :
    (∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N x (dilate (κ N) φ))) ∧
      ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, weilQuadTw SquareRootThreshold.liouvilleTwistedVonMangoldt
        (atomicTest N x (dilate (κ N) φ)) < 0 :=
  ⟨(riemannHypothesis_iff_atomicFamilies_nonneg_of_growth hκ hφ hφ1 hφint).mp hRH,
    liouville_atomicFamilies_negative hφ hφ1 hφint hκ⟩

/-! ### Which twins are seen -/

/-- A pole-free complex test of negative symbol energy refutes full-cone Weil positivity. -/
theorem not_weilPositiveFull_of_symbol_neg {lam : ℕ → ℝ}
    (h : ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (Complex.I / 2) = 0 ∧ paperFT f (-(Complex.I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0) :
    ¬ WeilPositiveFull lam := by
  obtain ⟨a, ha, f, hf, hfs, hp, hm, hneg⟩ := h
  intro hW
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  rw [EvenSector.integral_weilAtomSymbol_eq_two_pi_mul_re ha hf hfs hp hm] at hneg
  have := mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) (hW f hf hfc)
  linarith

/-- **A bounded twist is seen under overlap growth iff it is not Weil positive**: for `|λ| ≤ Λ` and
dilations `κ` of overlap growth, some atomic test of width `1/κ_N` has `Q_λ < 0` for infinitely many
`N` iff `λ` violates Weil positivity on some test. -/
theorem atomicFamilies_negative_iff {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) (hφ : ContDiff ℝ 2 φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowth κ) :
    (∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw lam (atomicTest N x (dilate (κ N) φ)) < 0) ↔ ¬ WeilPositiveFull lam := by
  have h := weilPositive_iff_atomicFamilies_nonneg hlam hφ hφ1 hφint hκ
  have hreal : WeilPositiveFull lam ↔
      ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ weilQuadTw lam g :=
    ⟨fun hW g hg hgc => hW _ (Complex.ofRealCLM.contDiff.comp hg) (hgc.comp_left Complex.ofReal_zero),
      fun hpos => WeilSpectral.weilPositiveFull_of_real hpos⟩
  rw [hreal, h, Filter.not_eventually]
  simp only [not_forall, not_le]

/-- **The scalings are seen**: for `−1 ≤ c < 1` the twist `cΛ` is negative on atomic families of
width `1/κ_N` for infinitely many `N`, for dilations `κ` of overlap growth. -/
theorem scaled_atomicFamilies_negative {c : ℝ} (hc1 : -1 ≤ c) (hc2 : c < 1)
    (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowth κ) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, weilQuadTw (fun n => c * ArithmeticFunction.vonMangoldt n)
      (atomicTest N x (dilate (κ N) φ)) < 0 := by
  have hlam : ∀ n, |c * ArithmeticFunction.vonMangoldt n| ≤ ArithmeticFunction.vonMangoldt n :=
    fun n => by
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
        (abs_le.mpr ⟨hc1, hc2.le⟩)
  exact (atomicFamilies_negative_iff hlam hφ hφ1 hφint hκ).mpr
    (not_weilPositiveFull_of_symbol_neg (scaled_vonMangoldt_weilAtomSymbol_not_nonneg hc2.ne))

/-- **The quadratic mixtures are seen**: for a real primitive character `χ` of conductor `q > 1`
and `0 < t ≤ 1`, the twist `Λ(n)(1 − t + tχ(n))` is negative on atomic families of width `1/κ_N`
for infinitely many `N`, for dilations `κ` of overlap growth. -/
theorem quadraticMix_atomicFamilies_negative {q : ℕ} [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowth κ) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re))
        (atomicTest N x (dilate (κ N) φ)) < 0 := by
  have hlam : ∀ n, |ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re)| ≤
      ArithmeticFunction.vonMangoldt n := fun n => by
    have hr := (Complex.abs_re_le_norm (χ (n : ZMod q))).trans (χ.norm_le_one _)
    rw [abs_le] at hr
    rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    refine mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (abs_le.mpr ⟨?_, ?_⟩) <;>
      nlinarith [hr.1, hr.2]
  exact (atomicFamilies_negative_iff hlam hφ hφ1 hφint hκ).mpr
    (not_weilPositiveFull_of_symbol_neg (quadraticMix_weilAtomSymbol_not_nonneg hq hprim hreal ht0))

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
