import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheOverlapLawAtEveryRoot
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeBecomesVisibleAtTheCriticalExponent
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold

/-!
# The gauge at every root

The Euler–Maclaurin synthesis (`TheOverlapLawAtEveryRoot`) carries every form that is translation
invariant and continuous under small Lipschitz perturbations — a *stable form* — from fixed tests
to the atomic families of overlap growth of any order. Weil's form, its bounded twists and the
Markov form are stable, so the statements of the critical exponent
(`TheGaugeBecomesVisibleAtTheCriticalExponent`, `ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold`)
hold at overlap ratio `(log N)^ε` for smooth profiles; the pole hyperplane is `ThePoleAtEveryRoot`.

* **Stable forms** (`StableForm`, `stableForm_weilQuad`, `stableForm_weilQuadTw`,
  `stableForm_markovQuad`).
* **Transfer** (`exists_smooth_neg_of_stable`, `frequently_atomicTest_neg_of_stable`,
  `nonneg_iff_atomicFamilies_nonneg_of_stable`): a stable form is nonnegative on all tests iff it
  is eventually nonnegative on the atomic families of overlap growth of any order.
* **The gauge at every root** (`atomicFamilies_negative_iff_of_growthPow`): a bounded twist is seen
  by the atomic families of overlap growth of any order iff it is not Weil positive — the Liouville
  twin, the scalings `cΛ`, `c < 1`, the quadratic mixtures; under RH `ζ` separates from all of them
  at overlap ratio `(log N)^ε`.
* **The Markov form at every root** (`markov_atomicFamilies_negative_of_growthPow`): `M < 0` on some
  atomic test for infinitely many `N`, unconditionally, at every overlap growth of finite order.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower
open scoped Real ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### Stable forms -/

/-- A **stable form**: a functional on real tests, invariant under translation of `C²` tests with
compact support, which a `C²` perturbation supported in `[−R′, R′]` with `|D| ≤ e` and Lipschitz
constant `L_D` moves by at most `Err(e, synthLevy R′ e L_D k)`, `Err → 0` along sequences. -/
def StableForm (Φ : (ℝ → ℝ) → ℝ) : Prop :=
  (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ c, Φ (fun u => f (u - c)) = Φ f) ∧
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → ∀ R' : ℝ, 0 ≤ R' → SupportedIn R' F →
    ∃ Err : ℝ → ℝ → ℝ,
      (∀ e V : ℕ → ℝ, Tendsto e atTop (𝓝 0) → Tendsto V atTop (𝓝 0) →
        Tendsto (fun n => Err (e n) (V n)) atTop (𝓝 0)) ∧
      ∀ (D : ℝ → ℝ) (e LD k : ℝ), ContDiff ℝ 2 D → SupportedIn R' D → (∀ u, |D u| ≤ e) →
        (∀ u v, |D u - D v| ≤ LD * |u - v|) → 1 ≤ k →
          Φ (fun u => F u + D u) ≤ Φ F + Err e (synthLevy R' e LD k)

/-- Weil's form is stable. -/
theorem stableForm_weilQuad : StableForm weilQuad :=
  ⟨fun f _ _ c => weilQuad_comp_sub f c, fun F hF hFc R' hR' hFR =>
    ⟨weilErr F R', fun _ _ he hV => tendsto_weilErr F R' he hV,
      fun _ _ _ _ hD hDR he hLD hk => weilQuad_add_le_of_lip hF hFc hFR hD hDR hR' he hLD hk⟩⟩

/-- Every twist `|λ| ≤ Λ` gives a stable form: the extra lags cost `4P(2‖F‖₂‖D‖₂ + ‖D‖₂²)`. -/
theorem stableForm_weilQuadTw {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) : StableForm (weilQuadTw lam) := by
  refine ⟨fun f _ _ c => weilQuadTw_comp_sub lam f c, fun F hF hFc R' hR' hFR => ?_⟩
  set P := primeMass R'
  refine ⟨fun e V => weilErr F R' e V +
    4 * P * (2 * (Real.sqrt (∫ u, F u ^ 2) * (Real.sqrt (2 * R') * e)) + 2 * R' * e ^ 2),
    fun e V he hV => ?_, fun D e LD k hD hDR he hLD hk => ?_⟩
  · have hx := ((((he.const_mul (Real.sqrt (2 * R'))).const_mul
      (Real.sqrt (∫ u, F u ^ 2))).const_mul 2).add ((he.pow 2).const_mul (2 * R'))).const_mul
      (4 * P)
    have := (tendsto_weilErr F R' he hV).add hx
    simpa using this
  · obtain ⟨hDc, hsqD, hN2, hLev, hN0, hN1⟩ := perturbation_norms hD hDR hR' he hLD hk
    have hb := weilQuadTw_add_le hlam hF hFc hD hDc hFR hDR
    have hm := weilErr_mono (F := F) hsqD hN2 hLev hN0 hN1
    have hP : 0 ≤ P := primeMass_nonneg _
    have hX : 4 * P * (2 * (Real.sqrt (∫ u, F u ^ 2) * Real.sqrt (∫ u, D u ^ 2)) + ∫ u, D u ^ 2) ≤
        4 * P * (2 * (Real.sqrt (∫ u, F u ^ 2) * (Real.sqrt (2 * R') * e)) + 2 * R' * e ^ 2) := by
      gcongr
    linarith

/-- The Markov form is stable: the pole moments cost
`2(e^{R′/2}(|m₋| + |m₊|)‖D‖₁ + e^{R′}‖D‖₁²)`. -/
theorem stableForm_markovQuad : StableForm markovQuad := by
  refine ⟨fun f hf hfc c => markovQuad_comp_sub hf hfc c, fun F hF hFc R' hR' hFR => ?_⟩
  set m := |poleMomentNeg F| + |poleMomentPos F|
  refine ⟨fun e V => weilErr F R' e V + 2 * (Real.exp (R' / 2) * m * (2 * R' * e) +
    Real.exp R' * (2 * R' * e) ^ 2), fun e V he hV => ?_, fun D e LD k hD hDR he hLD hk => ?_⟩
  · have := (tendsto_weilErr F R' he hV).add ((((he.const_mul (2 * R')).const_mul
      (Real.exp (R' / 2) * m)).add (((he.const_mul (2 * R')).pow 2).const_mul
        (Real.exp R'))).const_mul 2)
    simpa using this
  · obtain ⟨hDc, hsqD, hN2, hLev, hN0, hN1⟩ := perturbation_norms hD hDR hR' he hLD hk
    have hb := markovQuad_add_le hF hFc hD hDc hFR hDR
    have hmono := weilErr_mono (F := F) hsqD hN2 hLev hN0 hN1
    have hm0 : 0 ≤ m := by positivity
    have hpm : 2 * (Real.exp (R' / 2) * m * (∫ u, |D u|) + Real.exp R' * (∫ u, |D u|) ^ 2) ≤
        2 * (Real.exp (R' / 2) * m * (2 * R' * e) + Real.exp R' * (2 * R' * e) ^ 2) := by
      gcongr
    linarith

/-! ### Transfer to the atomic families -/

section Transfer

variable {Φ : (ℝ → ℝ) → ℝ} {φ : ℝ → ℝ}

/-- **Smooth negative tests for a stable form**: a stable form negative on a `C²` test is negative
on a smooth one, its mollification by a dilated smooth profile. -/
theorem exists_smooth_neg_of_stable (hΦ : StableForm Φ) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hneg : Φ g < 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ Φ G < 0 := by
  obtain ⟨R, M, L, hR, hgR, hgM, hgL⟩ := exists_test_bounds hg hgc
  obtain ⟨Err, hErr, hle⟩ := hΦ.2 g hg hgc (R + 1) (by linarith)
    (fun u hu => hgR u (by linarith))
  obtain ⟨he, hV, -, -⟩ := tendsto_mollifyErr L (∫ s, |φ s|) M (∫ s, |deriv φ s|) (R + 1)
  obtain ⟨n, hn1, hn2⟩ := (((hErr _ _ he hV).eventually (gt_mem_nhds
    (show (0 : ℝ) < -Φ g by linarith))).and (eventually_ge_atTop 1)).exists
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn2
  refine ⟨mollify g φ n, contDiff_mollify hφ hφ1 hg.continuous (by linarith),
    hasCompactSupport_of_vanishes (mollify_supportedIn hφ1 hgR hn), ?_⟩
  obtain ⟨hD2, hDR, hsup, hlip⟩ := mollify_perturbation hφ hφ1 hφint hg hgR hgM hgL hn
  have h := hle _ _ _ _ hD2 hDR hsup hlip hn
  have he' : (fun u => g u + (mollify g φ n u - g u)) = mollify g φ n := by funext u; ring
  rw [he'] at h
  linarith

/-- Bounds `M_l ≥ 0` on every derivative of a smooth test with compact support. -/
theorem exists_iteratedDeriv_bounds {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    ∃ M : ℕ → ℝ, (∀ l, 0 ≤ M l) ∧ ∀ l t, |iteratedDeriv l G t| ≤ M l := by
  have hbd : ∀ l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv l G t| ≤ C := fun l => by
    obtain ⟨C, hC⟩ := (hasCompactSupport_iteratedDeriv hGc l).exists_bound_of_continuous
      (hG.continuous_iteratedDeriv l (natCast_le_infty l))
    exact ⟨max C 0, le_max_right _ _, fun t =>
      (by simpa [Real.norm_eq_abs] using hC t : |iteratedDeriv l G t| ≤ C).trans
        (le_max_left _ _)⟩
  choose M hM0 hM using hbd
  exact ⟨M, hM0, hM⟩

/-- **A stable form negative on a smooth test is negative on the atomic families**: for every smooth
profile and every dilation sequence of overlap growth of some order `q`, some atomic test of width
`1/κ_N` has `Φ < 0` for infinitely many `N`. -/
theorem frequently_atomicTest_neg_of_stable (hΦ : StableForm Φ) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) {κ : ℕ → ℝ} {q : ℕ}
    (hκ : OverlapGrowthPow q κ) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (hneg : Φ G < 0) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, Φ (atomicTest N x (dilate (κ N) φ)) < 0 := by
  have hG2 : ContDiff ℝ 2 G := hG.of_le (natCast_le_infty 2)
  obtain ⟨R, -, -, hR, hGR, -, -⟩ := exists_test_bounds hG2 hGc
  obtain ⟨M, hM0, hM⟩ := exists_iteratedDeriv_bounds hG hGc
  obtain ⟨Err, hErr, hle⟩ := hΦ.2 G hG2 hGc (R + 1) (by linarith)
    (fun u hu => hGR u (by linarith))
  have hκ' : OverlapGrowthPow (2 * (2 * q + 2)) κ := hκ.mono (by omega)
  set B := blockSize R
  have hB : 1 ≤ B := one_le_blockSize R
  obtain ⟨he, hV, -, -⟩ := tendsto_em hκ' hB (M := M) (A := fun j => ∫ s, |iteratedDeriv j φ s|)
    (R' := R + 1)
  have h1 := (hErr _ _ he hV).eventually (gt_mem_nhds (show (0 : ℝ) < -Φ G by linarith))
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨n, hn1, hk, hn3, hna⟩ :=
    (h1.and (h3.and ((eventually_ge_atTop 2).and (eventually_ge_atTop a)))).exists
  refine ⟨n * B, hna.trans (Nat.le_mul_of_pos_right n hB), ?_⟩
  obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ :=
    exists_emSynthesis hφ hφ1 hφint hG hGR hM hM0 hn3 hk q
  refine ⟨x, ?_⟩
  rw [hx, hΦ.1 _ (hG2.add hD2) (hGc.add (hasCompactSupport_of_vanishes hDR))]
  have := hle D _ _ _ hD2 hDR hsup hlip hk
  linarith

/-- **The transfer law**: for a stable form, every smooth profile and every dilation sequence of
overlap growth of some order, `Φ ≥ 0` on all `C²` tests with compact support iff `Φ` is eventually
nonnegative on the atomic families of width `1/κ_N`. -/
theorem nonneg_iff_atomicFamilies_nonneg_of_stable (hΦ : StableForm Φ) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) {κ : ℕ → ℝ} {q : ℕ}
    (hκ : OverlapGrowthPow q κ) :
    (∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ Φ g) ↔
      ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, 0 ≤ Φ (atomicTest N x (dilate (κ N) φ)) := by
  constructor
  · intro hpos
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem (hφ.of_le (natCast_le_infty 2)) hφ1 hk N x
    exact hpos _ h2 hc
  · intro H
    by_contra hneg0
    push Not at hneg0
    obtain ⟨g, hg, hgc, hneg⟩ := hneg0
    obtain ⟨G, hG, hGc, hGneg⟩ := exists_smooth_neg_of_stable hΦ hφ hφ1 hφint hg hgc hneg
    have hfr := frequently_atomicTest_neg_of_stable hΦ hφ hφ1 hφint hκ hG hGc hGneg
    obtain ⟨N, ⟨x, hx⟩, hN⟩ := (hfr.and_eventually H).exists
    exact absurd (hN x) (not_le.mpr hx)

end Transfer

/-! ### The gauge and the Markov form at every root -/

section EveryRoot

variable {φ : ℝ → ℝ} {κ : ℕ → ℝ} {q : ℕ}

/-- **Weil positivity of a twist at every root**: for `|λ| ≤ Λ`, every smooth profile and every
dilation sequence of overlap growth of some order, `Q_λ ≥ 0` on all tests iff `Q_λ` is eventually
nonnegative on the atomic families of width `1/κ_N`. -/
theorem weilPositive_iff_atomicFamilies_nonneg_of_growthPow {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) :
    (∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ weilQuadTw lam g) ↔
      ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, 0 ≤ weilQuadTw lam (atomicTest N x (dilate (κ N) φ)) :=
  nonneg_iff_atomicFamilies_nonneg_of_stable (stableForm_weilQuadTw hlam) hφ hφ1 hφint hκ

/-- **A bounded twist is seen at every root iff it is not Weil positive**: for `|λ| ≤ Λ`, every
smooth profile and every dilation sequence of overlap growth of some order, some atomic test of
width `1/κ_N` has `Q_λ < 0` for infinitely many `N` iff `λ` violates Weil positivity. -/
theorem atomicFamilies_negative_iff_of_growthPow {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) :
    (∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw lam (atomicTest N x (dilate (κ N) φ)) < 0) ↔ ¬ WeilPositiveFull lam := by
  have h := weilPositive_iff_atomicFamilies_nonneg_of_growthPow hlam hφ hφ1 hφint hκ
  have hreal : WeilPositiveFull lam ↔
      ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ weilQuadTw lam g :=
    ⟨fun hW g hg hgc => hW _ (Complex.ofRealCLM.contDiff.comp hg)
      (hgc.comp_left Complex.ofReal_zero),
      fun hpos => WeilSpectral.weilPositiveFull_of_real hpos⟩
  rw [hreal, h, Filter.not_eventually]
  simp only [not_forall, not_le]

/-- **The Liouville twin fails at every root**. -/
theorem liouville_atomicFamilies_negative_of_growthPow (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, weilQuadTw SquareRootThreshold.liouvilleTwistedVonMangoldt
      (atomicTest N x (dilate (κ N) φ)) < 0 := by
  obtain ⟨g, hg, hgc, hneg⟩ := exists_liouville_negative
  obtain ⟨G, hG, hGc, hGneg⟩ := exists_smooth_neg_of_stable
    (stableForm_weilQuadTw abs_liouvilleTwistedVonMangoldt_le) hφ hφ1 hφint hg hgc hneg
  exact frequently_atomicTest_neg_of_stable
    (stableForm_weilQuadTw abs_liouvilleTwistedVonMangoldt_le) hφ hφ1 hφint hκ hG hGc hGneg

/-- **Under RH, `ζ` separates from the Liouville twin at every root**: at overlap growth of any
order, Weil's form is eventually nonnegative on the atomic families and the Liouville form is
negative on them for infinitely many `N`. -/
theorem riemannHypothesis_imp_liouville_separation_of_growthPow (hRH : RiemannHypothesis)
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    (hκ : OverlapGrowthPow q κ) :
    (∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N x (dilate (κ N) φ))) ∧
      ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, weilQuadTw SquareRootThreshold.liouvilleTwistedVonMangoldt
        (atomicTest N x (dilate (κ N) φ)) < 0 :=
  ⟨(riemannHypothesis_iff_atomicFamilies_nonneg_of_growthPow hκ hφ hφ1 hφint).mp hRH,
    liouville_atomicFamilies_negative_of_growthPow hφ hφ1 hφint hκ⟩

/-- **The scalings are seen at every root**: `cΛ`, `−1 ≤ c < 1`. -/
theorem scaled_atomicFamilies_negative_of_growthPow {c : ℝ} (hc1 : -1 ≤ c) (hc2 : c < 1)
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    (hκ : OverlapGrowthPow q κ) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, weilQuadTw (fun n => c * ArithmeticFunction.vonMangoldt n)
      (atomicTest N x (dilate (κ N) φ)) < 0 := by
  have hlam : ∀ n, |c * ArithmeticFunction.vonMangoldt n| ≤ ArithmeticFunction.vonMangoldt n :=
    fun n => by
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
        (abs_le.mpr ⟨hc1, hc2.le⟩)
  exact (atomicFamilies_negative_iff_of_growthPow hlam hφ hφ1 hφint hκ).mpr
    (not_weilPositiveFull_of_symbol_neg (scaled_vonMangoldt_weilAtomSymbol_not_nonneg hc2.ne))

/-- **The quadratic mixtures are seen at every root**: `Λ(n)(1 − t + tχ(n))`, `χ` real primitive of
conductor `> 1`, `0 < t ≤ 1`. -/
theorem quadraticMix_atomicFamilies_negative_of_growthPow {r : ℕ} [NeZero r] (hr : 1 < r)
    {χ : DirichletCharacter ℂ r} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod r)).re))
        (atomicTest N x (dilate (κ N) φ)) < 0 := by
  have hlam : ∀ n, |ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod r)).re)| ≤
      ArithmeticFunction.vonMangoldt n := fun n => by
    have h := (Complex.abs_re_le_norm (χ (n : ZMod r))).trans (χ.norm_le_one _)
    rw [abs_le] at h
    rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    refine mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (abs_le.mpr ⟨?_, ?_⟩) <;>
      nlinarith [h.1, h.2]
  exact (atomicFamilies_negative_iff_of_growthPow hlam hφ hφ1 hφint hκ).mpr
    (not_weilPositiveFull_of_symbol_neg (quadraticMix_weilAtomSymbol_not_nonneg hr hprim hreal ht0))

/-- **The Markov form fails at every root, unconditionally**: for every smooth profile and every
dilation sequence of overlap growth of some order, `M < 0` on some atomic test of width `1/κ_N` for
infinitely many `N`. -/
theorem markov_atomicFamilies_negative_of_growthPow (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, markovQuad (atomicTest N x (dilate (κ N) φ)) < 0 := by
  obtain ⟨g, hg, hgc, hneg⟩ := exists_markovQuad_neg
  obtain ⟨G, hG, hGc, hGneg⟩ :=
    exists_smooth_neg_of_stable stableForm_markovQuad hφ hφ1 hφint hg hgc hneg
  exact frequently_atomicTest_neg_of_stable stableForm_markovQuad hφ hφ1 hφint hκ hG hGc hGneg

end EveryRoot

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
