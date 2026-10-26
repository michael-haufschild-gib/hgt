import GaloisForLFunctions.ArithmeticPositiveDuality.ArithmeticCorrelationGeometry.TheThresholdIsThePriceOfTheArchimedeanLine
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Multiplicative amplification loses linearly

**The amplification specification.** For each order `k` let `R_k` be an observable that a zero of
depth `δ` forces to grow at rate at least `kδ` along an unbounded range of `R`, while arithmetic
bounds its growth by `b_k`. Taking `R → ∞` at fixed `k` gives `kδ ≤ b_k`
(`mul_le_of_frequently_of_eventually`), and then `k → ∞` gives `δ ≤ 0` as soon as `b_k/k → 0`
(`nonpos_of_sublinear_loss`). The two limits are taken in this order; the comparison itself is
elementary. The content is the **loss law** `b_k = o(k)`.

**Multiplicative amplification cannot supply it.**

* **Gauge Jensen** (`pow_sum_normSq_le_gauge_moment`). On the gauge torus, a probability space,
  `(∫|D|²)^k ≤ ∫|D|^{2k}`. Hence the multiplicative energy of every product order dominates the
  `k`-th power of the coefficient energy (`pow_sum_normSq_le_sum_normSq_powCoeff`):
  `Σ_N |a^{*k}(N)|² ≥ (Σ_n |a_n|²)^k`, with equality for a single atom
  (`sum_normSq_powCoeff_single`). Any bound routed through gauge moments of order `k` therefore
  has growth exponent at least `k` times that of order one: the loss is at least linear.
* **The archimedean line below the threshold inherits it**
  (`windowed_pow_ge_of_threshold`): windowed `2k`-th moments are gauge moments there.
* **Relative powers move the gauge point; external powers commute with it.** The pointwise
  (Euler-factor-wise) `k`-th power of the twist `χ_x` is `χ_{kx}` (`twist_nsmul`); the trivial gauge
  point — the coefficient system of `ζ` — is fixed, so relative powers of `ζ` are `ζ`. Dirichlet
  convolution commutes with every twist (`twisted_dirichletConv`), so external products stay in
  the gauge class of their factors and see the same zeros.

A sublinear loss law must therefore come from gauge-charged structure — near-incidences beyond
the square-root threshold — or from a correspondence with a fixed budget, the mechanism of Weil's
theorem (`ArithmeticOrientationGeometry.hasseWeilAt_of_eventually_bounded`).
-/

open MeasureTheory Finset Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry ArithmeticKunnethTheory SquareRootThreshold _root_.RHTower.WeilRegular

/-! ### The comparison -/

/-- **Fixed order: detection is bounded by the loss.** A rate `d` reached frequently and a rate `b`
never exceeded eventually satisfy `d ≤ b`. -/
theorem le_of_frequently_of_eventually {G : ℝ → ℝ} {d b : ℝ}
    (hdet : ∀ ε > 0, ∃ᶠ R in atTop, (d - ε) * R ≤ G R)
    (hbd : ∀ ε > 0, ∀ᶠ R in atTop, G R ≤ (b + ε) * R) : d ≤ b := by
  by_contra hlt
  push Not at hlt
  set ε := (d - b) / 3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨R, hdR, hbR, hR⟩ :=
    ((hdet ε hε0).and_eventually ((hbd ε hε0).and (eventually_gt_atTop 0))).exists
  have := hdR.trans hbR
  have h2 : d - ε ≤ b + ε := le_of_mul_le_mul_right this hR
  rw [hε] at h2
  linarith

/-- **The order of limits.** If for every `k ≥ 1` the growth `G k` of the order-`k` observable
reaches `kδ` frequently and stays below `b_k` eventually, then `kδ ≤ b_k`. -/
theorem mul_le_of_frequently_of_eventually {G : ℕ → ℝ → ℝ} {δ : ℝ} {b : ℕ → ℝ}
    (hdet : ∀ k, ∀ ε > 0, ∃ᶠ R in atTop, (k * δ - ε) * R ≤ G k R)
    (hbd : ∀ k, ∀ ε > 0, ∀ᶠ R in atTop, G k R ≤ (b k + ε) * R) (k : ℕ) : k * δ ≤ b k :=
  le_of_frequently_of_eventually (hdet k) (hbd k)

/-- **A sublinear loss law excludes every positive depth.** -/
theorem nonpos_of_sublinear_loss {δ : ℝ} {b : ℕ → ℝ} (hcmp : ∀ k : ℕ, k * δ ≤ b k)
    (hsub : Tendsto (fun k : ℕ => b k / k) atTop (𝓝 0)) : δ ≤ 0 := by
  have hδ : ∀ᶠ k : ℕ in atTop, δ ≤ b k / k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [le_div_iff₀ hk0, mul_comm]
    exact hcmp k
  exact ge_of_tendsto hsub hδ

/-- **A linear loss law gives nothing beyond order one.** With `b_k = k b₁` the comparison only
returns `δ ≤ b₁`, and every `δ ≤ b₁` is consistent with it. -/
theorem linear_loss_consistent (δ b₁ : ℝ) (h : δ ≤ b₁) (k : ℕ) : (k : ℝ) * δ ≤ k * b₁ :=
  mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)

/-! ### Gauge Jensen -/

/-- **Gauge Jensen.** The gauge `2k`-th moment dominates the `k`-th power of the mean square. -/
theorem pow_sum_normSq_le_gauge_moment {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (a : ℕ → ℂ) (k : ℕ) :
    (∑ n ∈ s, ‖a n‖ ^ 2) ^ k ≤ ∫ x, ‖twistSum s a x‖ ^ (2 * k) ∂gaugeHaar := by
  have hcont : Continuous fun x => ‖twistSum s a x‖ ^ 2 := (continuous_twistSum s a).norm.pow 2
  have hint : Integrable (fun x => ‖twistSum s a x‖ ^ 2) gaugeHaar :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintk : Integrable (fun x => (‖twistSum s a x‖ ^ 2) ^ k) gaugeHaar :=
    (hcont.pow k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJ := (convexOn_pow k).map_integral_le (μ := gaugeHaar) (f := fun x => ‖twistSum s a x‖ ^ 2)
    (continuous_pow k).continuousOn isClosed_Ici
    (Eventually.of_forall fun x => Set.mem_Ici.mpr (sq_nonneg _)) hint hintk
  rw [integral_normSq_twistSum hs] at hJ
  simpa [← pow_mul] using hJ

/-- **The multiplicative energy of order `k` dominates the `k`-th power of the energy.** -/
theorem pow_sum_normSq_le_sum_normSq_powCoeff {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (a : ℕ → ℂ)
    (k : ℕ) :
    (∑ n ∈ s, ‖a n‖ ^ 2) ^ k ≤ ∑ N ∈ ArithmeticKunnethTheory.powSupport s k, ‖powCoeff s a k N‖ ^ 2 := by
  rw [← integral_normSq_twistSum_pow hs]
  exact pow_sum_normSq_le_gauge_moment hs a k

/-- Equality for a single atom: the loss law is exactly linear there. -/
theorem sum_normSq_powCoeff_single {n : ℕ} (a : ℕ → ℂ) (k : ℕ) :
    ∑ N ∈ ArithmeticKunnethTheory.powSupport {n} k, ‖powCoeff {n} a k N‖ ^ 2 =
      (∑ m ∈ ({n} : Finset ℕ), ‖a m‖ ^ 2) ^ k := by
  classical
  have hpi : Fintype.piFinset (fun _ : Fin k => ({n} : Finset ℕ)) = {fun _ => n} := by
    ext t
    simp only [Fintype.mem_piFinset, Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h i => by rw [h]⟩
  have hsupp : ArithmeticKunnethTheory.powSupport {n} k = {n ^ k} := by
    rw [ArithmeticKunnethTheory.powSupport, hpi, Finset.image_singleton]
    simp
  rw [hsupp, Finset.sum_singleton, Finset.sum_singleton, powCoeff, hpi]
  rw [Finset.filter_singleton, if_pos (by simp)]
  simp [norm_pow, ← pow_mul, mul_comm]

/-- **Below the threshold the archimedean line loses linearly too.** -/
theorem windowed_pow_ge_of_threshold {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Set.Icc (-r) r) {s : Finset ℕ} {X : ℕ} (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ X)
    (c : ℕ → ℂ) {k : ℕ} (hthr : 2 * r * ((X : ℝ) ^ k) ≤ 1) :
    ∃ M : ℝ, (∫ t, ‖η t‖ ^ 2) * (∑ n ∈ s, ‖c n‖ ^ 2) ^ k ≤ M ∧
      ∫ ξ : ℝ, pairTransform η ξ * (expSum s c logFreq ξ * conj (expSum s c logFreq ξ)) ^ k =
        (M : ℂ) := by
  refine ⟨(∫ t, ‖η t‖ ^ 2) * ∫ x, ‖twistSum s c x‖ ^ (2 * k) ∂gaugeHaar, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (pow_sum_normSq_le_gauge_moment (fun n hn => by have := (hs n hn).1; omega) c k)
      (integral_nonneg fun t => by positivity)
  · rw [windowed_pow_eq_gauge_of_threshold hη hηs hs c hthr, Complex.ofReal_mul]

/-! ### Relative and external powers on the gauge torus -/

/-- **Relative powers move the gauge point.** The pointwise `k`-th power of `χ_x` is `χ_{kx}`. -/
theorem twist_nsmul (k : ℕ) (x : GaugeTorus) (n : ℕ) : twist (k • x) n = twist x n ^ k := by
  induction k with
  | zero =>
    rw [zero_smul, pow_zero, twist, torusCharacter_apply]
    exact Finset.prod_eq_one fun i _ => by simp only [Pi.zero_apply]; exact fourier_eval_zero _
  | succ k ih => rw [succ_nsmul, twist_add, ih, pow_succ]

/-- The trivial gauge point — the coefficient system of `ζ` — is fixed by every relative power. -/
theorem twist_nsmul_zero (k : ℕ) (n : ℕ) : twist (k • (0 : GaugeTorus)) n = 1 := by
  rw [smul_zero, twist, torusCharacter_apply]
  exact Finset.prod_eq_one fun i _ => by simp only [Pi.zero_apply]; exact fourier_eval_zero _

/-- **External products commute with every twist.** Dirichlet convolution of twisted sources is
the twisted convolution. -/
theorem twisted_dirichletConv (x : GaugeTorus) (a b : ℕ → ℂ) {N : ℕ} (hN : N ≠ 0) :
    ∑ p ∈ N.divisorsAntidiagonal, twisted x a p.1 * twisted x b p.2 =
      twisted x (fun M => ∑ p ∈ M.divisorsAntidiagonal, a p.1 * b p.2) N := by
  simp only [twisted]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Nat.mem_divisorsAntidiagonal.mp hp
  have hpN : p.1 * p.2 ≠ 0 := by rw [hp'.1]; exact hN
  have h1 : p.1 ≠ 0 := left_ne_zero_of_mul hpN
  have h2 : p.2 ≠ 0 := right_ne_zero_of_mul hpN
  rw [← hp'.1, twist_mul x h1 h2]
  ring

end GaloisForLFunctions.ArithmeticCorrelationGeometry
