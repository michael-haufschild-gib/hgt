import GaloisForLFunctions.RHTower.ParitySectorJointRigidity
import GaloisForLFunctions.RHTower.WeilOddConeHalfPoleRigidity
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity

/-!
# Polar Weil positivity: the only fakes are negative double poles

`WeilPositive lam` is Weil positivity on every pole-free test (`f̂(±i/2) = 0`), all parities.  Its
cone is `{Λ}` under RH unless the weights carry a NEGATIVE DOUBLE POLE at `s = 1`.

**Theorem** (`riemannHypothesis_of_weilPositive_of_abel`).  If `lam` is polar Weil-positive and
`F(s) = Σ_{n ≥ 2} lam(n) n^{−1−s}` has no negative double pole (`s² F(s) ≥ −ε` for small `s > 0`),
then RH holds and `lam = Λ` on `n ≥ 2`.

**Corollary** (`riemannHypothesis_iff_exists_bddBelow_weilPositive`).  RH holds iff some weight
system bounded below is polar Weil-positive, and then it is `Λ`.

Proof.  Polar positivity already gives absolute convergence on `Re s > 1`
(`summable_abs_div_rpow_of_weilPositive`) and the log-density ceiling (`weil_log_density_le`).  It
contains even pole-free positivity (`weilPositiveEvenPolar_of_weilPositive`, through the symbol form
`∫ |f̂|² S_lam = 2π Re W(f)` of a pole-free test).  The Abel pinning (`realWeil_nonneg_of_polar`)
then gives even positivity at pole weight one, which is RH with `lam = Λ`.

A negative double pole (`Σ_{n ≤ x} lam(n) ≈ −c x log x`) is not excluded here.  Heuristically, on
pole-free combinations of two far bumps the window density is approximately midpoint-concave for
even tests and midpoint-convex for odd tests, and a density linear in the log-scale satisfies both;
only tests with a pole term see its slope.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector ResonatorProfile WeilOneSided WeilPoleWeight

/-- **Symbol form of a pole-free test:** `∫ |f̂|² S_lam = 2π Re W_lam(f)`. -/
theorem integral_weilAtomSymbol_eq_two_pi_mul_re {lam : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hp : paperFT f (I / 2) = 0) (hm : paperFT f (-(I / 2)) = 0) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * (weilFullFunctional lam (EF.weilTest f f)).re := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  obtain ⟨-, -, hks, -, -⟩ := weilTest_self_data hf hfs
  have hkc := EF.weilTest_hasCompactSupport hfc hfc
  set k := EF.weilTest f f with hk
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  rw [integral_weilAtomSymbol_eq_sub hf hfs lam]
  have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  rw [← hN] at hWf
  have hre : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N (τ / (2 * π))) =
      2 * π * (zetaZeroConfig.W f f).re := by
    rw [hWf, Complex.ofReal_re]; field_simp
  rw [hre, weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt,
    ← zeta_W_eq_weilFullFunctional hf hfc, Complex.sub_re]
  have hvan : ∀ n : ℕ, N < n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * a) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * a))
      have h2 : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn'
    have hlog : 2 * a < Real.log n := by rw [Real.lt_log_iff_exp_lt hnpos]; exact hn'
    have hout : ∀ y : ℝ, 2 * a < |y| → k y = 0 := by
      intro y hy
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hks hmem
      rw [mem_Icc] at this
      rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0] at hy; linarith [this.2]
      · rw [abs_of_neg h0] at hy; linarith [this.1]
    have hl0 : 0 < Real.log n := by linarith
    exact ⟨hout _ (by rw [abs_of_pos hl0]; exact hlog),
      hout _ (by rw [abs_neg, abs_of_pos hl0]; exact hlog)⟩
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n
      else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re =
      ∑ n ∈ Finset.Icc 2 N, (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
        (k (Real.log n) + k (-Real.log n)).re := by
    rw [tsum_eq_sum (s := Finset.Icc 2 N) (fun n hn => ?_), Complex.re_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_Icc.mp hn).1, Complex.re_ofReal_mul]
    · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · rw [if_neg (by omega), Complex.ofReal_zero, zero_mul]
      · rw [(hvan n h).1, (hvan n h).2, add_zero, mul_zero]
  rw [hsum]
  ring

/-- Polar Weil positivity contains even pole-free positivity. -/
theorem weilPositiveEvenPolar_of_weilPositive {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    WeilPositiveEvenPolar lam := by
  intro f hf hfc hfe h0
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hfs : tsupport f ⊆ Icc (-|R|) |R| := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    rw [mem_Icc]
    constructor <;> [have := neg_abs_le x; have := le_abs_self x] <;>
      linarith [le_abs_self R]
  have hm : paperFT f (-(I / 2)) = 0 := by rw [paperFT_neg_of_even hfe]; exact h0
  have h := hW |R| (abs_nonneg R) f hf hfs h0 hm
  rw [integral_weilAtomSymbol_eq_two_pi_mul_re (abs_nonneg R) hf hfs h0 hm] at h
  have hπ : 0 < 2 * π := by positivity
  exact nonneg_of_mul_nonneg_right (by linarith) hπ

/-- **Polar rigidity without negative double pole.** -/
theorem riemannHypothesis_of_weilPositive_of_abel {lam : ℕ → ℝ} (hW : WeilPositive lam)
    (hdp : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s)) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hsl := fun σ (hσ : 1 < σ) => WeilMeanSquare.summable_abs_div_rpow_of_weilPositive hW hσ
  have hup := eventually_le_one_add_of_log_density_le hsl fun _ hε => weil_log_density_le hW hε
  exact weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_one_of_real fun _ hg hgc hge =>
    realWeil_nonneg_of_polar (weilPositiveEvenPolar_of_weilPositive hW) hsl hup hdp hg hgc hge)

/-- **Polar rigidity for weights bounded below.** -/
theorem riemannHypothesis_of_weilPositive_of_ge {lam : ℕ → ℝ} (hW : WeilPositive lam) {C : ℝ}
    (hlb : ∀ n, 2 ≤ n → -C ≤ lam n) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hlb' : ∀ n, 2 ≤ n → -max C 0 ≤ lam n := fun n hn =>
    (neg_le_neg (le_max_left C 0)).trans (hlb n hn)
  have hsl := fun σ (hσ : 1 < σ) => WeilMeanSquare.summable_abs_div_rpow_of_weilPositive hW hσ
  exact riemannHypothesis_of_weilPositive_of_abel hW (eventually_neg_le_of_ge hsl hC hlb')

/-- **RH is polar Weil positivity of a weight system bounded below.** -/
theorem riemannHypothesis_iff_exists_bddBelow_weilPositive :
    RiemannHypothesis ↔ ∃ (C : ℝ) (lam : ℕ → ℝ), (∀ n, 2 ≤ n → -C ≤ lam n) ∧ WeilPositive lam := by
  constructor
  · intro hRH
    exact ⟨0, fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      fun n _ => by simp [ArithmeticFunction.vonMangoldt_nonneg],
      riemannHypothesis_iff_weilPositive_vonMangoldt.mp hRH⟩
  · rintro ⟨C, lam, hlb, hW⟩
    exact (riemannHypothesis_of_weilPositive_of_ge hW hlb).1

end RHTower.EvenSector

end
