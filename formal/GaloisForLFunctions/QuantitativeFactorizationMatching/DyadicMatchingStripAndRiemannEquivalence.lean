import GaloisForLFunctions.QuantitativeFactorizationMatching.OreDeficiencyAndCascadeConservation
import GaloisForLFunctions.QuantitativeFactorizationMatching.GlobalDyadicGraphAndCofactorFibres
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.RHTower.MobiusEvenIndexPositiveRecurrence
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanEmptyLegReadsTheZeroAbscissa
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EverySparseConfigurationIsRealized
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheNormCountOfAnEditIsAConvolution

/-!
# Positivity-Free Strip Transfer, Riemann Equivalence, and Beurling Prime-Edit Selectivity

Complete analytic consequences and equivalences of quantitative squarefree matchings across all
factor counts on dyadic blocks `(X, 2X]`, proved **without positivity or spectral methods**:

1. **Positivity-free & spectral-free strip transfer (`dyadic_matching_holomorphic_inv_zeta_and_zero_free`)**:
   If `0 < θ < 1` and every sufficiently large dyadic block `(X, 2X]` admits an opposite-parity
   matching `M_X` (along any allowed relation `R X`, in particular `GlobalDyadicOneTwoRel`) with
   `#M_X.unmatchedSet ≤ C X^θ`, then:
   - `|M(x)| = |∑_{1 ≤ n ≤ x} μ(n)| ≤ K x^θ` for all `x ≥ 1` (elementary dyadic binary splitting);
   - the partial sums `∑_{n < N} μ(n) n^{-s}` converge on `{Re s > θ}` to a holomorphic function
     `F(s)` (`growthCont moebiusCoeffC θ s`) via finite summation by parts;
   - `F(s) · (s - 1) ζ(s) = s - 1` propagates across the convex half-plane `{Re s > θ}` by analytic
     continuation, forcing `ζ(s) ≠ 0` and `F(s) = 1 / ζ(s)` for all `Re s > θ`, `s ≠ 1`;
   - `zetaZeroAbscissa ≤ max (1 / 2) θ`, strictly breaking the `20999 / 24000 = 7/8 - 1/24000`
     zero-free barrier whenever `θ < 20999 / 24000`.
2. **Unconditional `O(X^β)` (`β > 20999 / 24000`), exact `O(X^{7/8})`, and exact `RiemannHypothesis`
   equivalence (`dyadic_matching_half_iff_riemannHypothesis`)**:
   - Every finite set `S` admits an `OppositeParityMatching FullOppositeParityRel S` leaving
     `|∑_{n ∈ S} μ(n)|` unmatched squarefree integers;
   - Unconditionally, every dyadic block `(X, 2X]` (`X ≥ 1`) admits an opposite-parity matching
     leaving `≤ C_β X^β` unmatched integers for every `β > 20999 / 24000`, and `≤ C X^{7/8}` exact;
   - `RiemannHypothesis` holds if and only if for every `ε > 0` there exists `C > 0` such that
     every dyadic block `(X, 2X]` (`X ≥ 1`) admits an opposite-parity matching leaving at most
     `C X^{1/2 + ε}` unmatched squarefree integers.
3. **Integer-norm Beurling prime-edit selectivity barrier (`exists_primeEdit_matching_barrier`)**:
   For every `σ ∈ (20999 / 24000, 14 / 15)` (including `σ = 7 / 8`) and every `σ' ∈ (1 / 2, σ)`,
   there exists a two-sided edit `e` of the rational primes such that `editSystem e` has integer
   norms, linear norm counting `A' x + O(x^{14/15})`, and `O(R^{14/15})` prime-generator edit budget
   (hence asymptotically identical prime counts to `ℙ` on every log-power cell `(u, v] ⊆ [R, 2R]`),
   yet its dyadic generalized-integer norm blocks admit **no** opposite-parity matching with
   `O(X^{σ'})` unmatched elements. Any global `O(X^{σ'})` matching below `14 / 15` must therefore
   use arithmetic structure of `ℤ` invisible to prime-edited Euler products (specifically unique
   factorization / absence of deleted and doubled prime norms).
-/

open Complex Finset Filter Topology
open _root_.RHTower.BeurlingDeletion
open GaloisForLFunctions.HeckeLFunctions
open GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.WorldsOfTheZeroConfiguration
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.ThinAdditions
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.NormCount
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-! ### 1. Elementary dyadic binary-splitting transfer from `(X, 2X]` to `Icc 1 N` -/

/-- Elementary binary-splitting transfer: if `0 < θ`, `|b(n)| ≤ B₀ n^θ` for `n ≥ 1`, and
`|∑_{X < n ≤ 2X} b(n)| ≤ C₁ X^θ` for all `X ≥ 1`, then `|∑_{1 ≤ n ≤ N} b(n)| ≤ K N^θ` for all
`N ≥ 1` with an explicit constant `K ≥ 0`. Uses no positivity, Mellin, or spectral input. -/
theorem abs_sum_Icc_le_of_dyadic_Ioc {b : ℕ → ℝ} {θ B₀ C₁ : ℝ}
    (hθ : 0 < θ) (hB₀ : 0 ≤ B₀) (hC₁ : 0 ≤ C₁)
    (hb : ∀ n : ℕ, 1 ≤ n → |b n| ≤ B₀ * (n : ℝ) ^ θ)
    (hdyad : ∀ X : ℕ, 1 ≤ X → |∑ n ∈ Ioc X (2 * X), b n| ≤ C₁ * (X : ℝ) ^ θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Icc 1 N, b n| ≤ K * (N : ℝ) ^ θ := by
  set r : ℝ := (2 : ℝ) ^ (-θ)
  have hr_pos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr_lt1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1mr : 0 < 1 - r := sub_pos.mpr hr_lt1
  set K : ℝ := max B₀ ((C₁ * r + B₀) / (1 - r))
  have hK_ge_B : B₀ ≤ K := le_max_left _ _
  have hK_nn : 0 ≤ K := hB₀.trans hK_ge_B
  have hK_step : (K + C₁) * r + B₀ ≤ K := by
    have h1 : (C₁ * r + B₀) / (1 - r) ≤ K := le_max_right _ _
    have h2 : C₁ * r + B₀ ≤ K * (1 - r) := (div_le_iff₀ h1mr).mp h1
    linarith
  refine ⟨K, hK_nn, fun N => ?_⟩
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    rcases eq_or_lt_of_le hN with rfl | hN2
    · rw [Icc_self, sum_singleton]
      calc |b 1| ≤ B₀ * ((1 : ℕ) : ℝ) ^ θ := hb 1 le_rfl
        _ = B₀ := by simp
        _ ≤ K := hK_ge_B
        _ = K * ((1 : ℕ) : ℝ) ^ θ := by simp
    · set m : ℕ := N / 2
      have hm1 : 1 ≤ m := by omega
      have hm_lt : m < N := by omega
      have hm_le_half : (m : ℝ) ≤ (N : ℝ) / 2 := by
        have h2m : 2 * m ≤ N := Nat.mul_div_le N 2
        have h2m_r : (2 : ℝ) * m ≤ N := by exact_mod_cast h2m
        linarith
      have hN_pos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hm_rpow : (m : ℝ) ^ θ ≤ r * (N : ℝ) ^ θ := by
        calc (m : ℝ) ^ θ ≤ ((N : ℝ) / 2) ^ θ :=
              Real.rpow_le_rpow (Nat.cast_nonneg m) hm_le_half hθ.le
          _ = (N : ℝ) ^ θ * (2 : ℝ) ^ (-θ) := by
              rw [div_eq_mul_inv, Real.mul_rpow hN_pos.le (by norm_num),
                Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
          _ = r * (N : ℝ) ^ θ := mul_comm _ _
      have hsplit : Icc 1 N = Icc 1 m ∪ Ioc m N := by
        ext k
        simp only [mem_union, mem_Icc, mem_Ioc]
        omega
      have hdisj : Disjoint (Icc 1 m) (Ioc m N) := by
        rw [disjoint_left]
        intro k hk1 hk2
        have := (mem_Icc.mp hk1).2
        have := (mem_Ioc.mp hk2).1
        omega
      have htail : |∑ n ∈ Ioc m N, b n| ≤ C₁ * (m : ℝ) ^ θ + B₀ * (N : ℝ) ^ θ := by
        have hN_cases : N = 2 * m ∨ N = 2 * m + 1 := by omega
        rcases hN_cases with hNeq | hNeq
        · have hBN : 0 ≤ B₀ * (N : ℝ) ^ θ := by positivity
          calc |∑ n ∈ Ioc m N, b n| = |∑ n ∈ Ioc m (2 * m), b n| := by rw [hNeq]
            _ ≤ C₁ * (m : ℝ) ^ θ := hdyad m hm1
            _ ≤ C₁ * (m : ℝ) ^ θ + B₀ * (N : ℝ) ^ θ := le_add_of_nonneg_right hBN
        · have hnotMem : N ∉ Ioc m (2 * m) := by
            simp only [mem_Ioc]; omega
          have hins : Ioc m N = insert N (Ioc m (2 * m)) := by
            ext k; simp only [mem_Ioc, mem_insert]; omega
          rw [hins, sum_insert hnotMem]
          calc |b N + ∑ n ∈ Ioc m (2 * m), b n|
              ≤ |b N| + |∑ n ∈ Ioc m (2 * m), b n| := abs_add_le _ _
            _ ≤ B₀ * (N : ℝ) ^ θ + C₁ * (m : ℝ) ^ θ :=
                add_le_add (hb N hN) (hdyad m hm1)
            _ = C₁ * (m : ℝ) ^ θ + B₀ * (N : ℝ) ^ θ := add_comm _ _
      rw [hsplit, sum_union hdisj]
      calc |(∑ n ∈ Icc 1 m, b n) + ∑ n ∈ Ioc m N, b n|
          ≤ |∑ n ∈ Icc 1 m, b n| + |∑ n ∈ Ioc m N, b n| := abs_add_le _ _
        _ ≤ K * (m : ℝ) ^ θ + (C₁ * (m : ℝ) ^ θ + B₀ * (N : ℝ) ^ θ) :=
            add_le_add (ih m hm_lt hm1) htail
        _ = (K + C₁) * (m : ℝ) ^ θ + B₀ * (N : ℝ) ^ θ := by ring
        _ ≤ (K + C₁) * (r * (N : ℝ) ^ θ) + B₀ * (N : ℝ) ^ θ := by
            gcongr
        _ = ((K + C₁) * r + B₀) * (N : ℝ) ^ θ := by ring
        _ ≤ K * (N : ℝ) ^ θ :=
            mul_le_mul_of_nonneg_right hK_step (Real.rpow_nonneg hN_pos.le _)

/-- Upgrading an eventual dyadic bound `X ≥ X₀` to all `X ≥ 1` given `|b(n)| ≤ B₀ n^θ`. -/
theorem abs_sum_Icc_le_of_eventually_dyadic_Ioc {b : ℕ → ℝ} {θ B₀ C : ℝ} {X₀ : ℕ}
    (hθ : 0 < θ) (hB₀ : 0 ≤ B₀)
    (hb : ∀ n : ℕ, 1 ≤ n → |b n| ≤ B₀ * (n : ℝ) ^ θ)
    (hdyad : ∀ X : ℕ, X₀ ≤ X → |∑ n ∈ Ioc X (2 * X), b n| ≤ C * (X : ℝ) ^ θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Icc 1 N, b n| ≤ K * (N : ℝ) ^ θ := by
  set C₁ : ℝ := max (max C 0) (B₀ * (2 : ℝ) ^ θ * (X₀ : ℝ))
  have hC₁ : 0 ≤ C₁ := le_trans (le_max_right C 0) (le_max_left _ _)
  refine abs_sum_Icc_le_of_dyadic_Ioc hθ hB₀ hC₁ hb fun X hX1 => ?_
  rcases le_or_gt X₀ X with hXX₀ | hlt
  · exact (hdyad X hXX₀).trans
      (mul_le_mul_of_nonneg_right ((le_max_left C 0).trans (le_max_left _ _)) (by positivity))
  · have hterm : ∀ n ∈ Ioc X (2 * X), |b n| ≤ B₀ * (2 : ℝ) ^ θ * (X : ℝ) ^ θ := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
      calc |b n| ≤ B₀ * (n : ℝ) ^ θ := hb n (by omega)
        _ ≤ B₀ * ((2 * X : ℕ) : ℝ) ^ θ :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn2) hθ.le) hB₀
        _ = B₀ * (2 : ℝ) ^ θ * (X : ℝ) ^ θ := by
            rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg X),
              mul_assoc]
    have hcard : ((Ioc X (2 * X)).card : ℝ) ≤ X₀ := by
      rw [Nat.card_Ioc]
      exact_mod_cast (show 2 * X - X ≤ X₀ by omega)
    calc |∑ n ∈ Ioc X (2 * X), b n|
        ≤ ∑ n ∈ Ioc X (2 * X), |b n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Ioc X (2 * X), (B₀ * (2 : ℝ) ^ θ * (X : ℝ) ^ θ) := sum_le_sum hterm
      _ = ((Ioc X (2 * X)).card : ℝ) * (B₀ * (2 : ℝ) ^ θ * (X : ℝ) ^ θ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (X₀ : ℝ) * (B₀ * (2 : ℝ) ^ θ * (X : ℝ) ^ θ) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (B₀ * (2 : ℝ) ^ θ * (X₀ : ℝ)) * (X : ℝ) ^ θ := by ring
      _ ≤ C₁ * (X : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ### 2. Positivity-free & spectral-free strip transfer from dyadic matchings -/

/-- Convexity of the open right half-plane `{s : ℂ | θ < s.re}`. -/
private theorem convex_halfPlane_gt (θ : ℝ) : Convex ℝ {s : ℂ | θ < s.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at *
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; linarith
  · have h1 : a * θ < a * x.re := mul_lt_mul_of_pos_left hx ha'
    have h2 : b * θ ≤ b * y.re := mul_le_mul_of_nonneg_left hy.le hb
    calc θ = (a + b) * θ := by rw [hab, one_mul]
      _ = a * θ + b * θ := add_mul a b θ
      _ < a * x.re + b * y.re := add_lt_add_of_lt_of_le h1 h2

/-- **Positivity-free & spectral-free strip transfer**: If `0 < θ < 1` and every sufficiently large
dyadic block `(X, 2X]` (`X ≥ X₀`) admits an opposite-parity matching `M_X` (for any family of edge
relations `R X`) with `#M_X.unmatchedSet ≤ C X^θ`, then:
1. `|M(x)| ≤ K x^θ` for all `x ≥ 1`;
2. `∑_{n < N} μ(n) n^{-s}` converges on `{Re s > θ}` to a holomorphic function `F(s)` satisfying
   `F(s) * riemannZeta s = 1` and `riemannZeta s ≠ 0` for all `Re s > θ`, `s ≠ 1` (and `F(1) = 0`);
3. `zetaZeroAbscissa ≤ max (1 / 2) θ`. -/
theorem dyadic_matching_holomorphic_inv_zeta_and_zero_free
    {θ C : ℝ} {X₀ : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hmatch : ∀ X : ℕ, X₀ ≤ X →
      ∃ (R : ℕ → ℕ → Prop) (M : OppositeParityMatching R (Ioc X (2 * X))),
        (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ θ) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ)| ≤ K * x ^ θ) ∧
    (∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | θ < s.re} ∧
      (∀ s : ℂ, θ < s.re →
        Tendsto (fun N => ∑ n ∈ range N, LSeries.term _root_.RHTower.moebiusCoeffC s n)
          atTop (𝓝 (F s))) ∧
      F 1 = 0 ∧
      ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 ∧ F s * riemannZeta s = 1) ∧
    _root_.RHTower.zetaZeroAbscissa ≤ max (1 / 2) θ := by
  have hb : ∀ n : ℕ, 1 ≤ n → |(μ n : ℝ)| ≤ 1 * (n : ℝ) ^ θ := by
    intro n hn
    have h1 : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast hn) hθ0.le
    linarith
  have hdyad : ∀ X : ℕ, X₀ ≤ X → |∑ n ∈ Ioc X (2 * X), (μ n : ℝ)| ≤ C * (X : ℝ) ^ θ := by
    intro X hX
    obtain ⟨R, M, hM⟩ := hmatch X hX
    have hle_int : |∑ n ∈ Ioc X (2 * X), μ n| ≤ (M.unmatchedSet.card : ℤ) :=
      M.abs_sum_moebius_le_unmatched
    have hle_real : |∑ n ∈ Ioc X (2 * X), (μ n : ℝ)| ≤ (M.unmatchedSet.card : ℝ) := by
      have : (∑ n ∈ Ioc X (2 * X), (μ n : ℝ)) = ((∑ n ∈ Ioc X (2 * X), μ n : ℤ) : ℝ) := by
        push_cast; rfl
      rw [this, ← Int.cast_abs]
      exact_mod_cast hle_int
    exact hle_real.trans hM
  obtain ⟨K, hK0, hK_nat⟩ := abs_sum_Icc_le_of_eventually_dyadic_Ioc hθ0 zero_le_one hb hdyad
  have hK_real : ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ)| ≤ K * x ^ θ := by
    intro x hx
    have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    exact (hK_nat ⌊x⌋₊ hfl1).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hfl_le hθ0.le) hK0)
  have hK_complex : ∀ x : ℝ, 1 ≤ x →
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, _root_.RHTower.moebiusCoeffC n‖ ≤ K * x ^ θ := by
    intro x hx
    have heq : (∑ n ∈ Icc 1 ⌊x⌋₊, _root_.RHTower.moebiusCoeffC n) =
        ((∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) : ℝ) : ℂ) := by
      simp only [_root_.RHTower.moebiusCoeffC]; push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact hK_real x hx
  -- Holomorphic continuation `F = growthCont moebiusCoeffC θ` via finite summation by parts
  let F : ℂ → ℂ := growthCont _root_.RHTower.moebiusCoeffC θ
  have hc0 : _root_.RHTower.moebiusCoeffC 0 = 0 := _root_.RHTower.moebiusCoeff_zero
  have hF_diff : DifferentiableOn ℂ F {s : ℂ | θ < s.re} :=
    differentiableOn_growthCont hc0 hθ0.le hK_complex
  have hF_tendsto : ∀ s : ℂ, θ < s.re →
      Tendsto (fun N => ∑ n ∈ range N, LSeries.term _root_.RHTower.moebiusCoeffC s n)
        atTop (𝓝 (F s)) :=
    fun s hs => tendsto_sum_term_growthCont hc0 hθ0.le hK_complex hs
  -- Propagate `F(z) * zetaEntire(z) = z - 1` across the convex half-plane `{Re z > θ}`
  let U : Set ℂ := {z : ℂ | θ < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfPlane_gt θ).isPreconnected
  have h_lhs_an : AnalyticOnNhd ℂ (fun z : ℂ => F z * _root_.RHTower.zetaEntire z) U :=
    (hF_diff.mul _root_.RHTower.differentiable_zetaEntire.differentiableOn).analyticOnNhd hU_open
  have h_rhs_an : AnalyticOnNhd ℂ (fun z : ℂ => z - 1) U :=
    ((differentiable_id.sub_const (1 : ℂ)).differentiableOn).analyticOnNhd hU_open
  have h2U : (2 : ℂ) ∈ U := by
    show θ < (2 : ℂ).re
    simp only [Complex.re_ofNat]; linarith
  have hev_eq : (fun z : ℂ => F z * _root_.RHTower.zetaEntire z) =ᶠ[𝓝 (2 : ℂ)]
      fun z : ℂ => z - 1 := by
    have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2V : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
    filter_upwards [hV.mem_nhds h2V] with z hz
    have hz1 : 1 < z.re := hz
    have hzne : z ≠ 1 := fun h => by rw [h] at hz1; simp at hz1
    have hsum : LSeriesSummable _root_.RHTower.moebiusCoeffC z :=
      LSeriesSummable_of_bounded_of_one_lt_re
        (m := 1) (fun n _ => _root_.RHTower.norm_moebiusCoeff_le_one n) hz1
    have hFL : F z = LSeries _root_.RHTower.moebiusCoeffC z :=
      growthCont_eq_LSeries hc0 hθ0.le hK_complex (by linarith) hsum
    rw [hFL, _root_.RHTower.zetaEntire_eq hzne]
    have hinv := _root_.RHTower.LSeries_moebiusCoeff_mul_riemannZeta hz1
    linear_combination (z - 1) * hinv
  have hident := h_lhs_an.eqOn_of_preconnected_of_eventuallyEq h_rhs_an hU_conn h2U hev_eq
  -- Evaluate at `s = 1` and at `s ≠ 1` in `U`
  have h1U : (1 : ℂ) ∈ U := by show θ < (1 : ℂ).re; simp [hθ1]
  have hF1_zero : F 1 = 0 := by
    have hval1 := hident h1U
    simp only [sub_self] at hval1
    have hze1 : _root_.RHTower.zetaEntire 1 ≠ 0 := by
      -- Since `zetaEntire 1 = (Gammaℝ 1)⁻¹ = √π ≠ 0`
      unfold _root_.RHTower.zetaEntire
      rw [sub_self, zero_mul, zero_add]
      exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by simp))
    exact (mul_eq_zero.mp hval1).resolve_right hze1
  have hF_inv : ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 ∧ F s * riemannZeta s = 1 := by
    intro s hs hs1
    have hval := hident hs
    simp only at hval
    rw [_root_.RHTower.zetaEntire_eq hs1] at hval
    have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hprod : F s * riemannZeta s = 1 := by
      apply mul_left_cancel₀ hs_sub
      linear_combination hval
    refine ⟨fun hζ => ?_, hprod⟩
    rw [hζ, mul_zero] at hprod
    exact zero_ne_one hprod
  -- Deduce `zetaZeroAbscissa ≤ max (1 / 2) θ` without positivity or spectral methods
  have habs : _root_.RHTower.zetaZeroAbscissa ≤ max (1 / 2) θ := by
    have hα : 0 ≤ max (1 / 2) θ - 1 / 2 := sub_nonneg.mpr (le_max_left _ _)
    have hbound := _root_.RHTower.zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound hα fun ρ hρ => ?_
    · linarith
    · obtain ⟨hζ, _⟩ := _root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρ
      have hρ1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hζ)
      by_contra hgt
      push Not at hgt
      have hθ_lt : θ < ρ.re := lt_of_le_of_lt (le_max_right (1 / 2) θ) (by linarith)
      exact (hF_inv ρ hθ_lt hρ1).1 hζ
  exact ⟨⟨K, hK0, hK_real⟩, ⟨F, hF_diff, hF_tendsto, hF1_zero, hF_inv⟩, habs⟩

/-- Specialization to `GlobalDyadicOneTwoRel` and breaking the `20999 / 24000` barrier: any
`O(X^θ)` unmatched bound on `GlobalDyadicOneTwoRel` with `θ < 20999 / 24000` forces
`zetaZeroAbscissa ≤ max (1 / 2) θ < 20999 / 24000`. -/
theorem globalDyadicOneTwo_sub_barrier_forces_abscissa_lt
    {θ C : ℝ} {X₀ : ℕ} (hθ0 : 0 < θ) (hθ_sub : θ < 20999 / 24000)
    (hmatch : ∀ X : ℕ, X₀ ≤ X →
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2 * X)),
        (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ θ) :
    _root_.RHTower.zetaZeroAbscissa ≤ max (1 / 2) θ ∧
      _root_.RHTower.zetaZeroAbscissa < 20999 / 24000 := by
  have hθ1 : θ < 1 := by linarith
  have h := (dyadic_matching_holomorphic_inv_zeta_and_zero_free hθ0 hθ1
    (fun X hX => let ⟨M, hM⟩ := hmatch X hX; ⟨GlobalDyadicOneTwoRel, M, hM⟩)).2.2
  refine ⟨h, lt_of_le_of_lt h (max_lt (by norm_num) hθ_sub)⟩

/-! ### 3. Unconditional `O(X^β)` / `O(X^{7/8})` attainment and exact `RiemannHypothesis` equivalence -/

/-- The unconstrained opposite-parity relation on squarefree integers. -/
def FullOppositeParityRel (a b : ℕ) : Prop :=
  μ a = 1 ∧ μ b = -1

/-- Every finite set `S ⊆ ℕ` admits an `OppositeParityMatching FullOppositeParityRel S` whose
unmatched set has cardinality equal to `|∑_{n ∈ S} μ(n)|` (zero Hall excess). -/
theorem exists_fullOppositeParityMatching_unmatched_eq_abs_sum (S : Finset ℕ) :
    ∃ M : OppositeParityMatching FullOppositeParityRel S,
      (M.unmatchedSet.card : ℤ) = |∑ n ∈ S, μ n| := by
  classical
  obtain ⟨P, hP_def⟩ : ∃ P : Finset ℕ, P = posParity S := ⟨_, rfl⟩
  obtain ⟨N, hN_def⟩ : ∃ N : Finset ℕ, N = negParity S := ⟨_, rfl⟩
  have hsum := sum_moebius_eq_card_pos_sub_neg S
  have hsq_card := card_squarefreeOf S
  rw [← hP_def, ← hN_def] at hsum hsq_card
  rcases le_or_gt P.card N.card with hle | hgt
  · obtain ⟨T, hTN, hT_card⟩ := exists_subset_card_eq hle
    have hfin_eq : Fintype.card P = Fintype.card T := by
      rw [Fintype.card_coe, Fintype.card_coe, hT_card]
    let e : P ≃ T := Fintype.equivOfCardEq hfin_eq
    let partner : ℕ → ℕ := fun a => if ha : a ∈ P then (e ⟨a, ha⟩).1 else 0
    have hinj : Set.InjOn partner ↑P := by
      intro a₁ ha₁ a₂ ha₂ heq
      have h1 : a₁ ∈ P := ha₁
      have h2 : a₂ ∈ P := ha₂
      simp only [partner, dif_pos h1, dif_pos h2] at heq
      exact congrArg Subtype.val (e.injective (Subtype.ext heq))
    let M : OppositeParityMatching FullOppositeParityRel S :=
      { sources := P
        partner := partner
        sources_subset := by rw [hP_def]
        injOn := hinj
        partner_mem := fun a ha => by
          simp only [partner, dif_pos ha]
          exact hN_def ▸ hTN (e ⟨a, ha⟩).2
        adj := fun a ha => by
          simp only [FullOppositeParityRel, partner, dif_pos ha]
          have ha_pos : a ∈ posParity S := hP_def ▸ ha
          have hb_neg : (e ⟨a, ha⟩).1 ∈ negParity S := hN_def ▸ hTN (e ⟨a, ha⟩).2
          exact ⟨(mem_filter.mp ha_pos).2, (mem_filter.mp hb_neg).2⟩ }
    refine ⟨M, ?_⟩
    have hm_card : M.matchedSet.card = 2 * P.card := by
      rw [OppositeParityMatching.matchedSet,
        card_union_of_disjoint M.disjoint_sources_targets, M.card_targets]
      change P.card + P.card = 2 * P.card
      omega
    have hunm : M.unmatchedSet.card + M.matchedSet.card = (squarefreeOf S).card := by
      rw [OppositeParityMatching.unmatchedSet]
      exact card_sdiff_add_card_eq_card M.matchedSet_subset
    rw [hsq_card, hm_card] at hunm
    rw [hsum, abs_of_nonpos (by omega)]
    omega
  · obtain ⟨U, hUP, hU_card⟩ := exists_subset_card_eq hgt.le
    have hfin_eq : Fintype.card U = Fintype.card N := by
      rw [Fintype.card_coe, Fintype.card_coe, hU_card]
    let e : U ≃ N := Fintype.equivOfCardEq hfin_eq
    let partner : ℕ → ℕ := fun a => if ha : a ∈ U then (e ⟨a, ha⟩).1 else 0
    have hinj : Set.InjOn partner ↑U := by
      intro a₁ ha₁ a₂ ha₂ heq
      have h1 : a₁ ∈ U := ha₁
      have h2 : a₂ ∈ U := ha₂
      simp only [partner, dif_pos h1, dif_pos h2] at heq
      exact congrArg Subtype.val (e.injective (Subtype.ext heq))
    let M : OppositeParityMatching FullOppositeParityRel S :=
      { sources := U
        partner := partner
        sources_subset := hP_def ▸ hUP
        injOn := hinj
        partner_mem := fun a ha => by
          simp only [partner, dif_pos ha]
          exact hN_def ▸ (e ⟨a, ha⟩).2
        adj := fun a ha => by
          simp only [FullOppositeParityRel, partner, dif_pos ha]
          have ha_pos : a ∈ posParity S := hP_def ▸ hUP ha
          have hb_neg : (e ⟨a, ha⟩).1 ∈ negParity S := hN_def ▸ (e ⟨a, ha⟩).2
          exact ⟨(mem_filter.mp ha_pos).2, (mem_filter.mp hb_neg).2⟩ }
    refine ⟨M, ?_⟩
    have hm_card : M.matchedSet.card = 2 * N.card := by
      rw [OppositeParityMatching.matchedSet,
        card_union_of_disjoint M.disjoint_sources_targets, M.card_targets]
      change U.card + U.card = 2 * N.card
      omega
    have hunm : M.unmatchedSet.card + M.matchedSet.card = (squarefreeOf S).card := by
      rw [OppositeParityMatching.unmatchedSet]
      exact card_sdiff_add_card_eq_card M.matchedSet_subset
    rw [hsq_card, hm_card] at hunm
    rw [hsum, abs_of_nonneg (by omega)]
    omega

/-- Converse strip-to-matching theorem: for every `β > zetaZeroAbscissa`, there exists `C > 0` such
that every dyadic block `(X, 2X]` (`X ≥ 1`) admits an `OppositeParityMatching FullOppositeParityRel`
leaving at most `C X^β` unmatched squarefree integers. -/
theorem exists_dyadic_matching_of_abscissa_lt {β : ℝ}
    (hβ : _root_.RHTower.zetaZeroAbscissa < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
        (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ β := by
  have hβ_pos : 0 < β := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (_root_.RHTower.half_le_zetaZeroAbscissa.trans hβ.le)
  obtain ⟨K, hK0, hM_bound⟩ := BezoutValuationIncidence.exists_moebius_power_bound_of_abscissa_lt hβ
  refine ⟨(K + 1) * ((2 : ℝ) ^ β + 1), by positivity, fun X hX => ?_⟩
  obtain ⟨M, hM_eq⟩ := exists_fullOppositeParityMatching_unmatched_eq_abs_sum (Ioc X (2 * X))
  refine ⟨M, ?_⟩
  have hsplit : Icc 1 (2 * X) = Icc 1 X ∪ Ioc X (2 * X) := by
    ext k; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 X) (Ioc X (2 * X)) := by
    rw [disjoint_left]; intro k hk1 hk2
    have := (mem_Icc.mp hk1).2; have := (mem_Ioc.mp hk2).1; omega
  have hdiff : (∑ n ∈ Ioc X (2 * X), BezoutValuationIncidence.moebiusReal n) =
      (∑ n ∈ Icc 1 (2 * X), BezoutValuationIncidence.moebiusReal n) -
        (∑ n ∈ Icc 1 X, BezoutValuationIncidence.moebiusReal n) := by
    rw [hsplit, sum_union hdisj]; ring
  have hm_real : (M.unmatchedSet.card : ℝ) =
      |∑ n ∈ Ioc X (2 * X), BezoutValuationIncidence.moebiusReal n| := by
    have hcast : ((M.unmatchedSet.card : ℤ) : ℝ) =
        |((∑ n ∈ Ioc X (2 * X), μ n : ℤ) : ℝ)| := by
      rw [hM_eq, Int.cast_abs]
    simpa [BezoutValuationIncidence.moebiusReal] using hcast
  rw [hm_real, hdiff]
  calc |(∑ n ∈ Icc 1 (2 * X), BezoutValuationIncidence.moebiusReal n) -
          (∑ n ∈ Icc 1 X, BezoutValuationIncidence.moebiusReal n)|
      ≤ |∑ n ∈ Icc 1 (2 * X), BezoutValuationIncidence.moebiusReal n| +
          |∑ n ∈ Icc 1 X, BezoutValuationIncidence.moebiusReal n| := abs_sub _ _
    _ ≤ K * ((2 * X : ℕ) : ℝ) ^ β + K * (X : ℝ) ^ β :=
        add_le_add (hM_bound (2 * X) (by omega)) (hM_bound X hX)
    _ = K * ((2 : ℝ) ^ β + 1) * (X : ℝ) ^ β := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg X)]
        ring
    _ ≤ (K + 1) * ((2 : ℝ) ^ β + 1) * (X : ℝ) ^ β := by gcongr; linarith

/-- **Unconditional sub-`7/8` (`20999 / 24000`) and exact `7/8` dyadic matching bounds**:
1. For every `β > 20999 / 24000`, every dyadic block `(X, 2X]` admits an opposite-parity matching
   with `≤ C X^β` unmatched squarefree integers;
2. With no `+ ε` loss, every dyadic block `(X, 2X]` (`X ≥ 1`) admits an opposite-parity matching
   with `≤ C X^{7/8}` unmatched squarefree integers. -/
theorem unconditional_dyadic_matching_sub_seven_eighths :
    (∀ {β : ℝ}, 20999 / 24000 < β →
      ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ β) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
        (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (7 / 8 : ℝ)) := by
  have hsub : ∀ {β : ℝ}, 20999 / 24000 < β → _ := fun {β} hβ =>
    exists_dyadic_matching_of_abscissa_lt
      (lt_of_le_of_lt ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths hβ)
  exact ⟨hsub, hsub (by norm_num)⟩

/-- **Exact `RiemannHypothesis` equivalence for dyadic squarefree matchings**:
`RiemannHypothesis` holds if and only if for every `ε > 0` there exists `C > 0` such that every
dyadic block `(X, 2X]` (`X ≥ 1`) admits an opposite-parity matching with at most `C X^{1/2 + ε}`
unmatched squarefree integers (both for `FullOppositeParityRel` and quantified over arbitrary
allowed edge relations `R`). -/
theorem dyadic_matching_half_iff_riemannHypothesis :
    ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) ↔ RiemannHypothesis) ∧
    ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ (R : ℕ → ℕ → Prop) (M : OppositeParityMatching R (Ioc X (2 * X))),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) ↔ RiemannHypothesis) := by
  have h1_to_2 :
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) →
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ (R : ℕ → ℕ → Prop) (M : OppositeParityMatching R (Ioc X (2 * X))),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) :=
    fun H ε hε =>
      let ⟨C, hC, hX⟩ := H ε hε
      ⟨C, hC, fun X hX1 => let ⟨M, hM⟩ := hX X hX1; ⟨FullOppositeParityRel, M, hM⟩⟩
  have h2_to_rh :
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ (R : ℕ → ℕ → Prop) (M : OppositeParityMatching R (Ioc X (2 * X))),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) → RiemannHypothesis := by
    intro H
    rw [← _root_.RHTower.zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
    apply le_antisymm _ _root_.RHTower.half_le_zetaZeroAbscissa
    by_contra hgt
    push Not at hgt
    set δ : ℝ := min ((_root_.RHTower.zetaZeroAbscissa - 1 / 2) / 2) (1 / 4)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ_lt : 1 / 2 + δ < 1 := by
      have : δ ≤ 1 / 4 := min_le_right _ _
      linarith
    obtain ⟨C, _, hX⟩ := H δ hδ_pos
    have habs := (dyadic_matching_holomorphic_inv_zeta_and_zero_free
      (θ := 1 / 2 + δ) (C := C) (X₀ := 1) (by linarith) hδ_lt hX).2.2
    have hmax : max (1 / 2) (1 / 2 + δ) = 1 / 2 + δ := max_eq_right (by linarith)
    rw [hmax] at habs
    have hδ_le : δ ≤ (_root_.RHTower.zetaZeroAbscissa - 1 / 2) / 2 := min_le_left _ _
    linarith
  have hrh_to_1 : RiemannHypothesis →
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) := by
    intro hRH ε hε
    have hΘ : _root_.RHTower.zetaZeroAbscissa = 1 / 2 :=
      _root_.RHTower.zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH
    exact exists_dyadic_matching_of_abscissa_lt (by rw [hΘ]; linarith)
  exact ⟨⟨fun H => h2_to_rh (h1_to_2 H), hrh_to_1⟩,
    ⟨h2_to_rh, fun hRH => h1_to_2 (hrh_to_1 hRH)⟩⟩

/-! ### 4. Integer-norm Beurling prime-edit selectivity barrier across `(20999 / 24000, 14 / 15)` -/

/-- Dyadic norm block `{g : B.Integer | X < natIntNorm g ≤ 2X}` of a discrete integer-norm
Beurling system. -/
def beurlingDyadicBlock (B : _root_.RHTower.BeurlingSystem) (hInt : HasIntegerNorms B)
    (hDisc : B.IsDiscrete) (X : ℕ) : Finset B.Integer := by
  classical exact (hDisc (2 * (X : ℝ))).toFinset.filter fun g => X < natIntNorm hInt g

theorem mem_beurlingDyadicBlock {B : _root_.RHTower.BeurlingSystem} {hInt : HasIntegerNorms B}
    {hDisc : B.IsDiscrete} {X : ℕ} {g : B.Integer} :
    g ∈ beurlingDyadicBlock B hInt hDisc X ↔ X < natIntNorm hInt g ∧ natIntNorm hInt g ≤ 2 * X := by
  classical
  simp only [beurlingDyadicBlock, mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    ← natIntNorm_spec hInt g]
  constructor
  · rintro ⟨hle, hgt⟩
    exact ⟨hgt, by exact_mod_cast (show (natIntNorm hInt g : ℝ) ≤ ((2 * X : ℕ) : ℝ) by
      push_cast; exact hle)⟩
  · rintro ⟨hgt, hle⟩
    exact ⟨by exact_mod_cast (show ((natIntNorm hInt g : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) by
      exact_mod_cast hle), hgt⟩

/-- An opposite-parity matching of squarefree generalized integers on `S : Finset B.Integer`. -/
structure BeurlingOppositeParityMatching (B : _root_.RHTower.BeurlingSystem)
    (S : Finset B.Integer) where
  sources : Finset B.Integer
  partner : B.Integer → B.Integer
  sources_subset : sources ⊆ S.filter (fun g => B.moebius g = 1)
  injOn : Set.InjOn partner ↑sources
  partner_mem : ∀ a ∈ sources, partner a ∈ S.filter (fun g => B.moebius g = -1)

/-- Unmatched squarefree generalized integers of `S` under `M`. -/
def BeurlingOppositeParityMatching.unmatchedSet {B : _root_.RHTower.BeurlingSystem}
    {S : Finset B.Integer} (M : BeurlingOppositeParityMatching B S) : Finset B.Integer := by
  classical exact (S.filter fun g => g.Nodup) \ (M.sources ∪ M.sources.image M.partner)

theorem BeurlingOppositeParityMatching.abs_sum_moebius_le_unmatched
    {B : _root_.RHTower.BeurlingSystem} {S : Finset B.Integer}
    (M : BeurlingOppositeParityMatching B S) :
    |∑ g ∈ S, B.moebius g| ≤ (M.unmatchedSet.card : ℤ) := by
  classical
  let Sq := S.filter fun g => g.Nodup
  let Mat := M.sources ∪ M.sources.image M.partner
  have hdisj_st : Disjoint M.sources (M.sources.image M.partner) := by
    rw [disjoint_left]
    intro g hg1 hg2
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hg2
    have h1 := (mem_filter.mp (M.sources_subset hg1)).2
    have h2 := (mem_filter.mp (M.partner_mem a ha)).2
    omega
  have hMat_sub : Mat ⊆ Sq := by
    intro g hg
    rcases mem_union.mp hg with hs | ht
    · obtain ⟨hgS, hμ⟩ := mem_filter.mp (M.sources_subset hs)
      refine mem_filter.mpr ⟨hgS, ?_⟩
      by_contra hnd
      rw [_root_.RHTower.BeurlingSystem.moebius, if_neg hnd] at hμ
      omega
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp ht
      obtain ⟨hgS, hμ⟩ := mem_filter.mp (M.partner_mem a ha)
      refine mem_filter.mpr ⟨hgS, ?_⟩
      by_contra hnd
      rw [_root_.RHTower.BeurlingSystem.moebius, if_neg hnd] at hμ
      omega
  have hsum_Sq : ∑ g ∈ S, B.moebius g = ∑ g ∈ Sq, B.moebius g := by
    refine (sum_subset (filter_subset _ S) fun g _ hnot => ?_).symm
    have hnd : ¬ g.Nodup := fun h => hnot (mem_filter.mpr ⟨‹_›, h⟩)
    simp [_root_.RHTower.BeurlingSystem.moebius, hnd]
  have hsum_Mat : ∑ g ∈ Mat, B.moebius g = 0 := by
    rw [sum_union hdisj_st, sum_image M.injOn]
    have h1 : ∑ a ∈ M.sources, B.moebius a = (M.sources.card : ℤ) := by
      calc ∑ a ∈ M.sources, B.moebius a = ∑ _a ∈ M.sources, (1 : ℤ) :=
            sum_congr rfl fun a ha => (mem_filter.mp (M.sources_subset ha)).2
        _ = (M.sources.card : ℤ) := by simp
    have h2 : ∑ a ∈ M.sources, B.moebius (M.partner a) = -(M.sources.card : ℤ) := by
      calc ∑ a ∈ M.sources, B.moebius (M.partner a) = ∑ _a ∈ M.sources, (-1 : ℤ) :=
            sum_congr rfl fun a ha => (mem_filter.mp (M.partner_mem a ha)).2
        _ = -(M.sources.card : ℤ) := by simp
    omega
  have hsplit : ∑ g ∈ Sq, B.moebius g =
      ∑ g ∈ M.unmatchedSet, B.moebius g + ∑ g ∈ Mat, B.moebius g := by
    rw [BeurlingOppositeParityMatching.unmatchedSet]
    exact (sum_sdiff hMat_sub).symm
  rw [hsum_Sq, hsplit, hsum_Mat, add_zero]
  calc |∑ g ∈ M.unmatchedSet, B.moebius g|
      ≤ ∑ g ∈ M.unmatchedSet, |B.moebius g| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g ∈ M.unmatchedSet, (1 : ℤ) := by
        refine sum_le_sum fun g _ => ?_
        exact_mod_cast B.abs_moebius_le_one g
    _ = (M.unmatchedSet.card : ℤ) := by simp

/-- Norm-grouped Möbius coefficient `b_n = ∑_{natIntNorm g = n} μ_B(g)` of a discrete integer-norm
Beurling system. -/
def beurlingIntMoebius (B : _root_.RHTower.BeurlingSystem) (hInt : HasIntegerNorms B)
    (hDisc : B.IsDiscrete) (n : ℕ) : ℤ := by
  classical exact ∑ g ∈ (finite_fiber_natIntNorm hInt hDisc n).toFinset, B.moebius g

private theorem beurlingIntMoebius_zero (B : _root_.RHTower.BeurlingSystem)
    (hInt : HasIntegerNorms B) (hDisc : B.IsDiscrete) :
    beurlingIntMoebius B hInt hDisc 0 = 0 := by
  classical
  unfold beurlingIntMoebius
  refine sum_eq_zero fun g hg => ?_
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
  have := one_le_natIntNorm hInt g
  omega

private theorem abs_beurlingIntMoebius_le_intCount (B : _root_.RHTower.BeurlingSystem)
    (hInt : HasIntegerNorms B) (hDisc : B.IsDiscrete) (n : ℕ) :
    |(beurlingIntMoebius B hInt hDisc n : ℝ)| ≤
      (SumProductArithmeticOfTheLogarithm.intCount B hInt n : ℝ) := by
  classical
  unfold beurlingIntMoebius
  rw [Int.cast_sum]
  calc |∑ g ∈ (finite_fiber_natIntNorm hInt hDisc n).toFinset, (B.moebius g : ℝ)|
      ≤ ∑ g ∈ (finite_fiber_natIntNorm hInt hDisc n).toFinset, |(B.moebius g : ℝ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g ∈ (finite_fiber_natIntNorm hInt hDisc n).toFinset, (1 : ℝ) :=
        sum_le_sum fun g _ => B.abs_moebius_le_one g
    _ = ((finite_fiber_natIntNorm hInt hDisc n).toFinset.card : ℝ) := by simp
    _ = (SumProductArithmeticOfTheLogarithm.intCount B hInt n : ℝ) := by
        rw [SumProductArithmeticOfTheLogarithm.intCount,
          Set.ncard_eq_toFinset_card _ (finite_fiber_natIntNorm hInt hDisc n)]

private theorem sum_beurlingIntMoebius_Ioc_eq (B : _root_.RHTower.BeurlingSystem)
    (hInt : HasIntegerNorms B) (hDisc : B.IsDiscrete) (X : ℕ) :
    ∑ n ∈ Ioc X (2 * X), beurlingIntMoebius B hInt hDisc n =
      ∑ g ∈ beurlingDyadicBlock B hInt hDisc X, B.moebius g := by
  classical
  have hmaps : ∀ g ∈ beurlingDyadicBlock B hInt hDisc X, natIntNorm hInt g ∈ Ioc X (2 * X) :=
    fun g hg => mem_Ioc.mpr (mem_beurlingDyadicBlock.mp hg)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun n hn => ?_
  unfold beurlingIntMoebius
  congr 1
  ext g
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_filter, mem_beurlingDyadicBlock]
  constructor
  · intro hgn
    exact ⟨hgn ▸ mem_Ioc.mp hn, hgn⟩
  · exact fun h => h.2

/-- Elementary divisor bound `#(n.divisors) ≤ 2 n^{1/2}` for all `n ≥ 1`. -/
private theorem card_divisors_le_two_mul_rpow_half {n : ℕ} (hn : 1 ≤ n) :
    (n.divisors.card : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  classical
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  set m : ℕ := ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊
  have hm_le : (m : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Nat.floor_le (by positivity)
  have hm_gt : (n : ℝ) ^ (1 / 2 : ℝ) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn_lt_sq : n < (m + 1) * (m + 1) := by
    have hsq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 < ((m : ℝ) + 1) ^ 2 :=
      pow_lt_pow_left₀ hm_gt (by positivity) two_ne_zero
    rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn_pos.le] at hsq
    norm_num at hsq
    exact_mod_cast (show (n : ℝ) < ((m + 1) * (m + 1) : ℕ) by push_cast; nlinarith)
  obtain ⟨S₁, hS₁_def⟩ : ∃ S₁ : Finset ℕ, S₁ = n.divisors.filter (· ≤ m) := ⟨_, rfl⟩
  obtain ⟨S₂, hS₂_def⟩ : ∃ S₂ : Finset ℕ, S₂ = n.divisors.filter (m < ·) := ⟨_, rfl⟩
  have hunion : n.divisors = S₁ ∪ S₂ := by
    ext d; rw [hS₁_def, hS₂_def]; simp only [mem_union, mem_filter]
    exact ⟨fun hd => (le_or_gt d m).imp (fun h => ⟨hd, h⟩) (fun h => ⟨hd, h⟩),
      fun h => h.elim And.left And.left⟩
  have hS₁_sub : S₁ ⊆ Icc 1 m := by
    intro d hd
    obtain ⟨hd_div, hd_le⟩ := mem_filter.mp (hS₁_def ▸ hd)
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd_div) hn, hd_le⟩
  have hS₁_card : S₁.card ≤ m := (card_le_card hS₁_sub).trans (by simp)
  have hS₂_img : S₂.image (n / ·) ⊆ Icc 1 m := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hq
    obtain ⟨hd_div, hd_gt⟩ := mem_filter.mp (hS₂_def ▸ hd)
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd_div
    have hd_le_n : d ≤ n := Nat.le_of_dvd hn hdvd
    have hq_pos : 1 ≤ n / d := Nat.div_pos hd_le_n (by omega)
    have hq_le_m : n / d ≤ m := by
      by_contra hgt_m
      have hm1_d : m + 1 ≤ d := hd_gt
      have hm1_q : m + 1 ≤ n / d := by omega
      have hprod : (m + 1) * (m + 1) ≤ n := by
        calc (m + 1) * (m + 1) ≤ d * (n / d) := Nat.mul_le_mul hm1_d hm1_q
          _ = n := Nat.mul_div_cancel' hdvd
      omega
    exact mem_Icc.mpr ⟨hq_pos, hq_le_m⟩
  have hS₂_inj : Set.InjOn (n / ·) ↑S₂ := by
    intro d₁ hd₁ d₂ hd₂ heq
    dsimp only at heq
    have hdvd₁ := Nat.dvd_of_mem_divisors (mem_filter.mp (hS₂_def ▸ (mem_coe.mp hd₁))).1
    have hdvd₂ := Nat.dvd_of_mem_divisors (mem_filter.mp (hS₂_def ▸ (mem_coe.mp hd₂))).1
    have hmul : d₁ * (n / d₁) = d₂ * (n / d₁) := by
      rw [Nat.mul_div_cancel' hdvd₁, heq, Nat.mul_div_cancel' hdvd₂]
    have hq_pos : 0 < n / d₁ :=
      Nat.div_pos (Nat.le_of_dvd hn hdvd₁) (Nat.pos_of_dvd_of_pos hdvd₁ hn)
    exact Nat.eq_of_mul_eq_mul_right hq_pos hmul
  have hS₂_card : S₂.card ≤ m := by
    rw [← card_image_of_injOn hS₂_inj]
    exact (card_le_card hS₂_img).trans (by simp)
  have htot : n.divisors.card ≤ 2 * m := by
    rw [hunion]
    exact (card_union_le S₁ S₂).trans (by omega)
  calc (n.divisors.card : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast htot
    _ = 2 * (m : ℝ) := by push_cast; rfl
    _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hm_le (by norm_num)

/-- For any two-sided prime edit `e`, `intCount (editSystem e) _ n ≤ 2 n^{1/2}` for all `n ≥ 1`. -/
private theorem intCount_editSystem_le_two_mul_rpow_half (e : ℕ → ℤ) {n : ℕ} (hn : 1 ≤ n) :
    (SumProductArithmeticOfTheLogarithm.intCount (editSystem e)
      (hasIntegerNorms_editSystem e) n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have heq := intCount_eq (minusSet e) (plusSet e) n
  change (SumProductArithmeticOfTheLogarithm.intCount (editSystem e)
    (hasIntegerNorms_editSystem e) n : ℝ) = _ at heq
  rw [heq, ArithmeticFunction.mul_apply]
  have hsFree_le : ∀ (S : Set ℕ) (m : ℕ), sFreeR S m ≤ 1 := by
    intro S m
    unfold sFreeR
    split_ifs <;> norm_num
  have hle_antidiag : ∑ x ∈ n.divisorsAntidiagonal,
      freeFn (minusSet e) x.1 * freeFn (plusSet e)ᶜ x.2 ≤ (n.divisorsAntidiagonal.card : ℝ) := by
    calc ∑ x ∈ n.divisorsAntidiagonal, freeFn (minusSet e) x.1 * freeFn (plusSet e)ᶜ x.2
        ≤ ∑ _x ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
          refine sum_le_sum fun x _ => ?_
          rw [freeFn_apply, freeFn_apply]
          calc sFreeR (minusSet e) x.1 * sFreeR (plusSet e)ᶜ x.2
              ≤ 1 * 1 := mul_le_mul (hsFree_le _ _) (hsFree_le _ _)
                  (sFreeR_nonneg _ _) zero_le_one
            _ = 1 := mul_one 1
      _ = (n.divisorsAntidiagonal.card : ℝ) := by simp
  have hcard_eq : n.divisorsAntidiagonal.card = n.divisors.card := by
    have hinj : Set.InjOn Prod.fst (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
      intro x hx y hy hfst
      obtain ⟨hx_mul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      obtain ⟨hy_mul, _⟩ := Nat.mem_divisorsAntidiagonal.mp hy
      have hx1_pos : 0 < x.1 := Nat.pos_of_ne_zero fun h0 => hn0 (by rw [← hx_mul, h0, zero_mul])
      have hsnd : x.2 = y.2 :=
        Nat.eq_of_mul_eq_mul_left hx1_pos (hx_mul.trans (hy_mul.symm.trans (by rw [hfst])))
      exact Prod.ext hfst hsnd
    have himg : n.divisorsAntidiagonal.image Prod.fst = n.divisors := by
      ext d
      simp only [mem_image, Nat.mem_divisorsAntidiagonal, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨hab, hn0⟩, rfl⟩
        exact ⟨⟨b, hab.symm⟩, hn0⟩
      · rintro ⟨⟨b, rfl⟩, hn0⟩
        exact ⟨(d, b), ⟨rfl, hn0⟩, rfl⟩
    rw [← card_image_of_injOn hinj, himg]
  calc ∑ x ∈ n.divisorsAntidiagonal, freeFn (minusSet e) x.1 * freeFn (plusSet e)ᶜ x.2
      ≤ (n.divisorsAntidiagonal.card : ℝ) := hle_antidiag
    _ = (n.divisors.card : ℝ) := by rw [hcard_eq]
    _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := card_divisors_le_two_mul_rpow_half hn

/-- Fiber regrouping of `B.moebiusSeriesC s` into `LSeries (beurlingIntMoebius B hInt hDisc) s`
whenever `∑_g |g|^{-Re s} < ∞`. -/
private theorem moebiusSeriesC_eq_LSeries_of_summable {B : _root_.RHTower.BeurlingSystem}
    (hInt : HasIntegerNorms B) (hDisc : B.IsDiscrete) {s : ℂ}
    (hZr : Summable fun g : Multiset B.Label => (B.intNorm g) ^ (-s.re)) :
    LSeriesSummable (fun n => (beurlingIntMoebius B hInt hDisc n : ℂ)) s ∧
      B.moebiusSeriesC s = LSeries (fun n => (beurlingIntMoebius B hInt hDisc n : ℂ)) s := by
  classical
  have hLS_cnt := (zetaSeriesC_eq_LSeries_of_summable hInt hDisc hZr).1
  have hLS_mob : LSeriesSummable (fun n => (beurlingIntMoebius B hInt hDisc n : ℂ)) s := by
    refine Summable.of_norm_bounded hLS_cnt.norm fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      rw [Complex.norm_intCast, Complex.norm_natCast]
      exact abs_beurlingIntMoebius_le_intCount B hInt hDisc n
  have hM : Summable fun g : Multiset B.Label =>
      (B.moebius g : ℂ) * ((B.intNorm g : ℝ) : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded hZr fun g => ?_
    rw [norm_mul, B.norm_intNorm_cpow]
    have hnorm : ‖(B.moebius g : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast B.abs_moebius_le_one g
    exact mul_le_of_le_one_left (Real.rpow_nonneg (B.intNorm_pos g).le _) hnorm
  set eqv := Equiv.sigmaFiberEquiv (natIntNorm hInt)
  have hsigma : Summable ((fun g : Multiset B.Label =>
      (B.moebius g : ℂ) * ((B.intNorm g : ℝ) : ℂ) ^ (-s)) ∘ eqv) :=
    eqv.summable_iff.mpr hM
  refine ⟨hLS_mob, ?_⟩
  rw [_root_.RHTower.BeurlingSystem.moebiusSeriesC, (eqv.tsum_eq _).symm]
  change ∑' c, ((fun g : Multiset B.Label =>
    (B.moebius g : ℂ) * ((B.intNorm g : ℝ) : ℂ) ^ (-s)) ∘ eqv) c = _
  rw [hsigma.tsum_sigma]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    haveI : IsEmpty {g : B.Integer // natIntNorm hInt g = 0} :=
      ⟨fun c => by have := one_le_natIntNorm hInt c.1; omega⟩
    simp
  · letI : Fintype {g : B.Integer // natIntNorm hInt g = n} :=
      (finite_fiber_natIntNorm hInt hDisc n).fintype
    rw [tsum_fintype, LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
    have hval : ∀ c : {g : B.Integer // natIntNorm hInt g = n},
        ((fun g : Multiset B.Label =>
          (B.moebius g : ℂ) * ((B.intNorm g : ℝ) : ℂ) ^ (-s)) ∘ eqv) ⟨n, c⟩ =
          (B.moebius c.1 : ℂ) * (n : ℂ) ^ (-s) := fun c => by
      change (B.moebius c.1 : ℂ) * ((B.intNorm c.1 : ℝ) : ℂ) ^ (-s) = _
      rw [← natIntNorm_spec hInt c.1, c.2]; push_cast; rfl
    simp_rw [hval, ← sum_mul]
    congr 1
    unfold beurlingIntMoebius
    rw [Int.cast_sum]
    let f_bij : {g : B.Integer // natIntNorm hInt g = n} ≃
        (finite_fiber_natIntNorm hInt hDisc n).toFinset :=
      { toFun := fun c => ⟨c.1, (finite_fiber_natIntNorm hInt hDisc n).mem_toFinset.mpr c.2⟩
        invFun := fun c => ⟨c.1, (finite_fiber_natIntNorm hInt hDisc n).mem_toFinset.mp c.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Finset.sum_coe_sort (finite_fiber_natIntNorm hInt hDisc n).toFinset]
    exact Fintype.sum_equiv f_bij _ _ fun _ => rfl

/-- **Integer-norm Beurling prime-edit selectivity barrier across `(20999 / 24000, 14 / 15)`**:
For every `σ ∈ (20999 / 24000, 14 / 15)` (including `σ = 7 / 8`) and every `σ' ∈ (1 / 2, σ)`,
there exists a two-sided edit `e` of the rational primes such that:
1. `editSystem e` has integer norms, is discrete, and is **not** norm-equivalent to the rational primes;
2. `|(editSystem e).countBall x - A' x| ≤ C x^{14/15}` (`A' ≥ 0`) for all `x ≥ 1`;
3. `∑_{1 ≤ k ≤ n} |e(k)| ≤ C_edit n^{14/15}` for all `n ≥ 1` (so the prime-generator count on
   every log-power cell `(u, v] ⊆ [R, 2R]` agrees with `ℙ` up to `O(R^{14/15})`);
4. Yet there do **not** exist `C_m : ℝ` and `X₀ : ℕ` such that every dyadic norm block
   `beurlingDyadicBlock (editSystem e) _ _ X` (`X ≥ X₀`) admits a `BeurlingOppositeParityMatching`
   leaving at most `C_m X^{σ'}` unmatched squarefree generalized integers. -/
theorem exists_primeEdit_matching_barrier {σ σ' : ℝ}
    (hσ_lo : 20999 / 24000 < σ) (hσ_hi : σ < 14 / 15)
    (hσ'_lo : 1 / 2 < σ') (hσ'_hi : σ' < σ) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      NotNormEquivPrimes (editSystem e) ∧
      (∃ A' C : ℝ, 0 ≤ A' ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A' * x| ≤ C * x ^ (14 / 15 : ℝ)) ∧
      (∃ C_edit : ℝ, 0 ≤ C_edit ∧ ∀ n : ℕ, 1 ≤ n →
        ∑ k ∈ Icc 1 n, |(e k : ℝ)| ≤ C_edit * (n : ℝ) ^ (14 / 15 : ℝ)) ∧
      ¬ (∃ (C_m : ℝ) (X₀ : ℕ), ∀ X : ℕ, X₀ ≤ X →
          ∃ M : BeurlingOppositeParityMatching (editSystem e)
              (beurlingDyadicBlock (editSystem e) (hasIntegerNorms_editSystem e)
                (isDiscrete_editSystem e) X),
            (M.unmatchedSet.card : ℝ) ≤ C_m * (X : ℝ) ^ σ') := by
  have hd : 0 < 14 / 15 - σ := by linarith
  set A_cfg : ℝ := 1 / (14 / 15 - σ)
  have hA_pos : 0 < A_cfg := one_div_pos.mpr hd
  have hroom : σ + 1 / (2 * A_cfg) < 14 / 15 := by
    have : 1 / (2 * A_cfg) = (14 / 15 - σ) / 2 := by simp only [A_cfg]; field_simp
    linarith
  have hcfg := isSparseConfig_linePoints (σ := σ) (A := A_cfg) (by linarith) hA_pos hroom
  have hζ₀ : riemannZeta (linePoints σ A_cfg 0) ≠ 0 :=
    MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
      (by show 20999 / 24000 < σ; exact hσ_lo)
  set e : ℕ → ℤ := gedit (sparseTarget (linePoints σ A_cfg))
  have he : IsEdit e := isEdit_gedit _
  have htwin := hcfg.isFactorTwin_sparse
  have hset : {z : ℂ | sparseFactor (linePoints σ A_cfg) z = 0} =
      {z : ℂ | ∃ j, z = linePoints σ A_cfg j ∨ z = (starRingEnd ℂ) (linePoints σ A_cfg j)} := by
    ext z; exact hcfg.sparseFactor_eq_zero_iff z
  have hfake := htwin.hasFakeZeroSet hcfg.differentiable_sparseFactor.differentiableOn
  rw [hset] at hfake
  obtain ⟨G, hG_diff, hG_eq, hzero⟩ := hfake
  set z₀ : ℂ := linePoints σ A_cfg 0
  have hz₀_re : z₀.re = σ := rfl
  have hz₀_ne1 : z₀ ≠ 1 := fun h1 => by
    have := congrArg Complex.re h1; rw [hz₀_re, Complex.one_re] at this; linarith
  have hGz₀ : G z₀ = 0 :=
    (hzero z₀ (by rw [hz₀_re]; linarith) hz₀_ne1 hζ₀).mpr ⟨0, Or.inl rfl⟩
  obtain ⟨p_ed, hp_ed⟩ := exists_ne_zero_of_fake_zero he hG_diff hG_eq
    (by rw [hz₀_re]; linarith) hz₀_ne1 hζ₀ hGz₀
  have hnot_equiv : NotNormEquivPrimes (editSystem e) := notNormEquivPrimes_editSystem he hp_ed
  set η : ℝ := 1 - (σ + 1 / (2 * A_cfg))
  have h2A_pos : 0 < 1 / (2 * A_cfg) := by positivity
  have hη_pos : 0 < η := by simp only [η]; linarith
  have h1mη_lt : 1 - η < 14 / 15 := by simp only [η]; linarith
  have hcount := editSystem_gedit_count (m := sparseTarget (linePoints σ A_cfg))
    (A := 2) (η := η) (by norm_num) (by simp only [η]; linarith)
    (fun k hk => hcfg.abs_sparseTarget_le hk) h1mη_lt (by norm_num)
  -- Edited-prime budget bound `∑_{1 ≤ k ≤ n} |e(k)| ≤ C_edit n^{14/15}`
  have hedit_bound : ∃ C_edit : ℝ, 0 ≤ C_edit ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Icc 1 n, |(e k : ℝ)| ≤ C_edit * (n : ℝ) ^ (14 / 15 : ℝ) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1mη_pos : 0 < 1 - η := by simp only [η]; linarith
    refine ⟨(2 / (1 - η)) / Real.log 2, by positivity, fun n hn => ?_⟩
    have hI : Icc 1 n = Ioc 0 n := by
      ext k; simp only [mem_Icc, mem_Ioc]; omega
    rw [hI]
    have htarget_sum : ∑ k ∈ Ioc 0 n, |sparseTarget (linePoints σ A_cfg) k| ≤
        (2 / (1 - η)) * (n : ℝ) ^ (1 - η) := by
      rw [← hI]
      calc ∑ k ∈ Icc 1 n, |sparseTarget (linePoints σ A_cfg) k|
          ≤ ∑ k ∈ Icc 1 n, 2 * (k : ℝ) ^ ((1 - η) - 1) := by
            refine sum_le_sum fun k hk => ?_
            rw [show (1 - η) - 1 = -η by ring]
            exact hcfg.abs_sparseTarget_le (mem_Icc.mp hk).1
        _ = 2 * ∑ k ∈ Icc 1 n, (k : ℝ) ^ ((1 - η) - 1) := by rw [mul_sum]
        _ ≤ 2 * ((n : ℝ) ^ (1 - η) / (1 - η)) :=
            mul_le_mul_of_nonneg_left
              (DeletionData.sum_rpow_le h1mη_pos (by linarith) n) (by norm_num)
        _ = (2 / (1 - η)) * (n : ℝ) ^ (1 - η) := by ring
    calc ∑ k ∈ Ioc 0 n, |(e k : ℝ)|
        ≤ (∑ k ∈ Ioc 0 n, |sparseTarget (linePoints σ A_cfg) k|) / Real.log 2 :=
          sum_abs_gedit_le _ n
      _ ≤ ((2 / (1 - η)) * (n : ℝ) ^ (1 - η)) / Real.log 2 :=
          div_le_div_of_nonneg_right htarget_sum hlog2.le
      _ = ((2 / (1 - η)) / Real.log 2) * (n : ℝ) ^ (1 - η) := by ring
      _ ≤ ((2 / (1 - η)) / Real.log 2) * (n : ℝ) ^ (14 / 15 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h1mη_lt.le) (by positivity)
  -- Obstruction to any `O(X^{σ'})` opposite-parity matching on `beurlingDyadicBlock`
  refine ⟨e, he, hnot_equiv, hcount, hedit_bound, ?_⟩
  rintro ⟨C_m, X₀, hmatch⟩
  let B := editSystem e
  let hInt := hasIntegerNorms_editSystem e
  let hDisc := isDiscrete_editSystem e
  let b : ℕ → ℝ := fun n => (beurlingIntMoebius B hInt hDisc n : ℝ)
  have hσ'_pos : 0 < σ' := by linarith
  have hb_single : ∀ n : ℕ, 1 ≤ n → |b n| ≤ 2 * (n : ℝ) ^ σ' := by
    intro n hn
    calc |b n| ≤ (SumProductArithmeticOfTheLogarithm.intCount B hInt n : ℝ) :=
          abs_beurlingIntMoebius_le_intCount B hInt hDisc n
      _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := intCount_editSystem_le_two_mul_rpow_half e hn
      _ ≤ 2 * (n : ℝ) ^ σ' :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hσ'_lo.le) (by norm_num)
  have hdyad_b : ∀ X : ℕ, X₀ ≤ X → |∑ n ∈ Ioc X (2 * X), b n| ≤ C_m * (X : ℝ) ^ σ' := by
    intro X hX
    obtain ⟨M, hM⟩ := hmatch X hX
    have heq_sum : ∑ n ∈ Ioc X (2 * X), b n =
        ((∑ g ∈ beurlingDyadicBlock B hInt hDisc X, B.moebius g : ℤ) : ℝ) := by
      simp only [b]
      rw [← Int.cast_sum, sum_beurlingIntMoebius_Ioc_eq B hInt hDisc X]
    rw [heq_sum, ← Int.cast_abs]
    have hle_real : ((|∑ g ∈ beurlingDyadicBlock B hInt hDisc X, B.moebius g| : ℤ) : ℝ) ≤
        (M.unmatchedSet.card : ℝ) := by
      exact_mod_cast M.abs_sum_moebius_le_unmatched
    exact hle_real.trans hM
  obtain ⟨K, hK0, hK_nat⟩ :=
    abs_sum_Icc_le_of_eventually_dyadic_Ioc hσ'_pos (by norm_num) hb_single hdyad_b
  let bc : ℕ → ℂ := fun n => (beurlingIntMoebius B hInt hDisc n : ℂ)
  have hbc0 : bc 0 = 0 := by simp [bc, beurlingIntMoebius_zero]
  have hK_c : ∀ x : ℝ, 1 ≤ x → ‖∑ n ∈ Icc 1 ⌊x⌋₊, bc n‖ ≤ K * x ^ σ' := by
    intro x hx
    have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have heq : (∑ n ∈ Icc 1 ⌊x⌋₊, bc n) = ((∑ n ∈ Icc 1 ⌊x⌋₊, b n : ℝ) : ℂ) := by
      simp only [bc, b]; push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact (hK_nat ⌊x⌋₊ hfl1).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hfl_le hσ'_pos.le) hK0)
  -- Analytic continuation of `growthCont bc σ' * G = z - 1` onto `{Re z > σ'}`
  let F_B : ℂ → ℂ := growthCont bc σ'
  let U : Set ℂ := {z : ℂ | σ' < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfPlane_gt σ').isPreconnected
  have hFB_diff : DifferentiableOn ℂ F_B U := differentiableOn_growthCont hbc0 hσ'_pos.le hK_c
  have hG_diff_U : DifferentiableOn ℂ G U :=
    hG_diff.mono fun z hz => lt_trans hσ'_lo hz
  have h_lhs_an : AnalyticOnNhd ℂ (fun z : ℂ => F_B z * G z) U :=
    (hFB_diff.mul hG_diff_U).analyticOnNhd hU_open
  have h_rhs_an : AnalyticOnNhd ℂ (fun z : ℂ => z - 1) U :=
    ((differentiable_id.sub_const (1 : ℂ)).differentiableOn).analyticOnNhd hU_open
  have h2U : (2 : ℂ) ∈ U := by show σ' < (2 : ℂ).re; simp only [Complex.re_ofNat]; linarith
  obtain ⟨A', C_cnt, _, hcnt_bound⟩ := hcount
  have hLin := hasLinearCounting_of_count_sub_le (by norm_num : (14 / 15 : ℝ) ≤ 1) hcnt_bound
  have hev_eq : (fun z : ℂ => F_B z * G z) =ᶠ[𝓝 (2 : ℂ)] fun z : ℂ => z - 1 := by
    have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2V : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
    filter_upwards [hV.mem_nhds h2V] with z hz
    have hz1 : 1 < z.re := hz
    have hZr := _root_.RHTower.BeurlingSystem.summable_intNorm_rpow hDisc hLin hz1
    obtain ⟨hLS_bc, hmob_eq⟩ := moebiusSeriesC_eq_LSeries_of_summable hInt hDisc hZr
    have hFB_eq : F_B z = B.moebiusSeriesC z :=
      (growthCont_eq_LSeries hbc0 hσ'_pos.le hK_c (by linarith) hLS_bc).trans hmob_eq.symm
    have hinv := _root_.RHTower.BeurlingSystem.moebiusSeriesC_mul_zetaSeriesC hDisc hLin hz1
    change F_B z * G z = z - 1
    rw [hFB_eq, hG_eq z hz1]
    linear_combination (z - 1) * hinv
  have hident := h_lhs_an.eqOn_of_preconnected_of_eventuallyEq h_rhs_an hU_conn h2U hev_eq
  have hz₀_U : z₀ ∈ U := by show σ' < z₀.re; rw [hz₀_re]; exact hσ'_hi
  have hval := hident hz₀_U
  simp only [hGz₀, mul_zero] at hval
  exact hz₀_ne1 (by linear_combination -hval)

end GaloisForLFunctions.QuantitativeFactorizationMatching
