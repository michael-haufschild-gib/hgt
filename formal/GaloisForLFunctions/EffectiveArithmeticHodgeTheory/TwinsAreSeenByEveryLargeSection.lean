import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheExplicitSchedulesReachTheIndex

/-!
# Twins are seen by every large section

SSHA proves the gauge law of the Gevrey window: a bounded twin `λ`, `|λ| ≤ Λ`, is negative on some
atomic test of width `1/κ_N` for **infinitely many** `N` iff it is not Weil positive
(`atomicFamilies_negative_iff_of_gevrey`). The Euler–Maclaurin synthesis lives on the horizons
`nB`, so the conclusion is intermittent. Along every residue class `N = nB + ρ` the shifted
schedule keeps Gevrey overlap growth, and finitely many classes cover all large `N`
(`overlapGrowthGevrey_shift`, `eventually_of_residues`). So the conclusion holds **for all large
`N`**:

* **Stable forms** (`eventually_atomicTest_neg_of_stable_gevrey`). A stable form negative on one
  `C²` test is negative on some atomic test of every large horizon.
* **The gauge law, eventually** (`eventually_negative_iff_of_gevrey`). A bounded twin is seen by
  every large section of the Gevrey schedule iff it is not Weil positive.
* **The Liouville twin** (`liouville_eventually_negative_of_gevrey`) is seen by every large section,
  unconditionally; under RH, `ζ` is nonnegative on every large section while its twin is negative
  on every large section (`riemannHypothesis_imp_liouville_separation_of_gevrey`).

Selectivity in the finite sections is therefore not intermittent: from some horizon on, every
section separates `ζ` from a twin that fails Weil positivity.
-/

open MeasureTheory Set Filter Topology RHTower
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

open SpacingScaleHarmonicAnalysis
open ArithmeticElectrostatics (atomicTest)

variable {φ : ℝ → ℝ} {A Bφ s : ℝ} {κ : ℕ → ℝ}

/-- **A stable form negative on one test is negative on every large section** of a Gevrey
schedule. -/
theorem eventually_atomicTest_neg_of_stable_gevrey {Φ : (ℝ → ℝ) → ℝ} (hΦ : StableForm Φ)
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hs : 0 ≤ s)
    (hBφ : 0 ≤ Bφ) (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * (q.factorial : ℝ) ^ s)
    (hκ : OverlapGrowthGevrey s κ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hneg : Φ g < 0) :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, Φ (atomicTest N x (dilate (κ N) φ)) < 0 := by
  obtain ⟨G, M, b, hG, hGc, hM0, hb, hGM, hGneg⟩ :=
    exists_gevrey_neg_of_stable hΦ hφ hφ1 hφint hBφ hA hg hgc hneg
  have hG2 : ContDiff ℝ 2 G := hG.of_le (natCast_le_infty 2)
  obtain ⟨R, -, -, hR, hGR, -, -⟩ := exists_test_bounds hG2 hGc
  obtain ⟨Err, hErr, hle⟩ := hΦ.2 G hG2 hGc (R + 1) (by linarith)
    (fun u hu => hGR u (by linarith))
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simpa using this
  have hB : 1 ≤ blockSize R := SpacingScaleHarmonicAnalysis.one_le_blockSize R
  refine eventually_of_residues (B := blockSize R) (by omega) fun ρ _ => ?_
  have hκρ := overlapGrowthGevrey_shift hκ ρ
  obtain ⟨he, hV⟩ := tendsto_gevrey hs hκρ hB (M := M) (b := b) (A := A) (Bφ := Bφ)
    (A0 := ∫ s, |φ s|) (mul_nonneg hM0 hA0) hb hBφ (fun l => M * b ^ l * (l.factorial : ℝ) ^ s)
    (fun q => ∫ s, |iteratedDeriv q φ s|) (R + 1)
  have h1 := (hErr _ _ he hV).eventually (gt_mem_nhds (show (0 : ℝ) < -Φ G by linarith))
  have hk : Tendsto (fun n => κ (n * blockSize R + ρ)) atTop atTop :=
    hκρ.1.comp (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id)
  filter_upwards [h1, hk.eventually_ge_atTop 1, eventually_ge_atTop 2] with n hn hk1 hn2
  obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ := exists_gevreySynthesis hφ hφ1 hφint hG hGR hM0 hb
    hBφ hs hGM hA hn2 hk1 (gevOrder (κ (n * blockSize R + ρ)))
  refine ⟨fun l => if l ≤ n * blockSize R then x l else 0, ?_⟩
  rw [← atomicTest_extend (Nat.le_add_right _ ρ), hx,
    hΦ.1 _ (hG2.add hD2) (hGc.add (hasCompactSupport_of_vanishes hDR))]
  have := hle D _ _ _ hD2 hDR hsup hlip hk1
  linarith

/-- A twin that is not Weil positive is negative on some real `C²` compactly supported test. -/
theorem exists_real_neg_of_not_weilPositiveFull {lam : ℕ → ℝ} (h : ¬ WeilPositiveFull lam) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ weilQuadTw lam g < 0 := by
  by_contra hall
  push Not at hall
  exact h (WeilSpectral.weilPositiveFull_of_real fun g hg hgc => hall g hg hgc)

/-- **The gauge law of the Gevrey window, eventually.** A bounded twin is negative on some atomic
test of every large horizon iff it is not Weil positive. -/
theorem eventually_negative_iff_of_gevrey {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hs : 0 ≤ s) (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * (q.factorial : ℝ) ^ s)
    (hκ : OverlapGrowthGevrey s κ) :
    (∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw lam (atomicTest N x (dilate (κ N) φ)) < 0) ↔ ¬ WeilPositiveFull lam := by
  refine ⟨fun h => (atomicFamilies_negative_iff_of_gevrey hlam hφ hφ1 hφint hs hBφ hA hκ).mp
    h.frequently, fun h => ?_⟩
  obtain ⟨g, hg, hgc, hneg⟩ := exists_real_neg_of_not_weilPositiveFull h
  exact eventually_atomicTest_neg_of_stable_gevrey (stableForm_weilQuadTw hlam) hφ hφ1 hφint hs
    hBφ hA hκ hg hgc hneg

/-- **The Liouville twin is seen by every large section** of a Gevrey schedule. -/
theorem liouville_eventually_negative_of_gevrey (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hs : 0 ≤ s) (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * (q.factorial : ℝ) ^ s)
    (hκ : OverlapGrowthGevrey s κ) :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, weilQuadTw SquareRootThreshold.liouvilleTwistedVonMangoldt
      (atomicTest N x (dilate (κ N) φ)) < 0 := by
  obtain ⟨g, hg, hgc, hneg⟩ := exists_liouville_negative
  exact eventually_atomicTest_neg_of_stable_gevrey
    (stableForm_weilQuadTw abs_liouvilleTwistedVonMangoldt_le) hφ hφ1 hφint hs hBφ hA hκ hg hgc hneg

/-- **Under RH, every large section separates `ζ` from its Liouville twin**: Weil's form is
nonnegative on all atomic tests and the Liouville form is negative on one, at every large
horizon of the Gevrey schedule. -/
theorem riemannHypothesis_imp_liouville_separation_of_gevrey (hRH : RiemannHypothesis)
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hs : 0 ≤ s)
    (hBφ : 0 ≤ Bφ) (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * (q.factorial : ℝ) ^ s)
    (hκ : OverlapGrowthGevrey s κ) :
    ∀ᶠ N : ℕ in atTop, (∀ x : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N x (dilate (κ N) φ))) ∧
      ∃ x : ℕ → ℝ, weilQuadTw SquareRootThreshold.liouvilleTwistedVonMangoldt
        (atomicTest N x (dilate (κ N) φ)) < 0 :=
  ((riemannHypothesis_iff_atomicFamilies_nonneg_of_gevrey hφ hφ1 hφint hs hBφ hA hκ).mp hRH).and
    (liouville_eventually_negative_of_gevrey hφ hφ1 hφint hs hBφ hA hκ)

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
