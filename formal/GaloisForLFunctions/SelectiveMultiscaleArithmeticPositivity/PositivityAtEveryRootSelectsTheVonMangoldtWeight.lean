import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeAtEveryRoot
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional

/-!
# Positivity at every root selects the von Mangoldt weight

The atomic receiver holds at every root: for a bounded weight `|λ| ≤ Λ`, a smooth profile `φ` and
dilations `κ_N` of overlap growth of some finite order, `Q_λ ≥ 0` on all tests iff `Q_λ` is eventually
nonnegative on the atomic families of width `1/κ_N`
(`weilPositive_iff_atomicFamilies_nonneg_of_growthPow`). The full Weil cone is `{Λ}` under RH and
empty otherwise (`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`). Together:

* **Selection** (`atomicPositiveAt_iff`): a bounded weight is eventually atomic-positive at some root
  iff RH holds and the weight is `Λ` on `n ≥ 2`.
* **Twin-blind positivity is impossible** (`not_forall_atomicPositiveAt`,
  `not_atomicPositiveAt_liouville`): no family of bounded weights containing a weight different from
  `Λ` is uniformly atomic-positive at a root. An inequality proved for every bounded twist of a family
  that contains the Liouville twin cannot reach an RH-complete atomic family.
* **One weight, one root** (`riemannHypothesis_of_atomicPositiveAt`): atomic positivity of any single
  bounded weight at any single root is RH.

So atomic positivity at a root is not a property a family of twins can share: it singles out `Λ`.
A positivity proof must use a property of `Λ` that its bounded twists lack.
-/

noncomputable section

open Filter RHTower
open scoped ContDiff

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- **Atomic positivity at a root**: `Q_λ` is eventually nonnegative on all atomic tests of the
dilated profile `κ_N φ(κ_N ·)`, width `1/κ_N`, at the points `log n`, `n ≤ N`. -/
def AtomicPositiveAt (lam : ℕ → ℝ) (φ : ℝ → ℝ) (κ : ℕ → ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, 0 ≤ weilQuadTw lam (atomicTest N x (dilate (κ N) φ))

variable {φ : ℝ → ℝ} {κ : ℕ → ℝ} {q : ℕ}

/-- Full Weil positivity of a weight is positivity on real `C²` tests with compact support. -/
theorem weilPositiveFull_iff_real {lam : ℕ → ℝ} :
    WeilPositiveFull lam ↔
      ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ weilQuadTw lam g :=
  ⟨fun hW _ hg hgc => hW _ (Complex.ofRealCLM.contDiff.comp hg) (hgc.comp_left Complex.ofReal_zero),
    fun hpos => WeilSpectral.weilPositiveFull_of_real hpos⟩

/-- **Selection at every root**: a bounded weight is eventually atomic-positive at a root of finite
overlap order iff RH holds and the weight is the von Mangoldt function on `n ≥ 2`. -/
theorem atomicPositiveAt_iff {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) :
    AtomicPositiveAt lam φ κ ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  rw [← WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt,
    weilPositiveFull_iff_real, weilPositive_iff_atomicFamilies_nonneg_of_growthPow hlam hφ hφ1 hφint hκ]
  rfl

/-- **One weight, one root**: atomic positivity of a single bounded weight at a single root of
finite overlap order implies RH. -/
theorem riemannHypothesis_of_atomicPositiveAt {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ)
    (h : AtomicPositiveAt lam φ κ) : RiemannHypothesis :=
  ((atomicPositiveAt_iff hlam hφ hφ1 hφint hκ).mp h).1

/-- **Twin-blind atomic positivity is impossible**: if a family of bounded weights contains one
weight that differs from `Λ` at some `n ≥ 2`, the family is not uniformly atomic-positive at any
root of finite overlap order. -/
theorem not_forall_atomicPositiveAt {F : Set (ℕ → ℝ)}
    (hF : ∀ lam ∈ F, ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) {lam₀ : ℕ → ℝ}
    (h₀ : lam₀ ∈ F) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hne : lam₀ n₀ ≠ ArithmeticFunction.vonMangoldt n₀) :
    ¬ ∀ lam ∈ F, AtomicPositiveAt lam φ κ := fun h =>
  hne (((atomicPositiveAt_iff (hF lam₀ h₀) hφ hφ1 hφint hκ).mp (h lam₀ h₀)).2 n₀ hn₀)

/-- **The Liouville twin is never atomic-positive**: at every root of finite overlap order. -/
theorem not_atomicPositiveAt_liouville (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) :
    ¬ AtomicPositiveAt SquareRootThreshold.liouvilleTwistedVonMangoldt φ κ := by
  intro h
  have h2 := ((atomicPositiveAt_iff abs_liouvilleTwistedVonMangoldt_le hφ hφ1 hφint hκ).mp h).2 2
    le_rfl
  rw [SquareRootThreshold.liouvilleTwistedVonMangoldt_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat] at h2
  linarith [Real.log_pos one_lt_two]

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
