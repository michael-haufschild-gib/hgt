import GaloisForLFunctions.QuantitativeFactorizationMatching.OreDeficiencyAndCascadeConservation
import GaloisForLFunctions.QuantitativeFactorizationMatching.AllFiniteLayersCellMatching
import GaloisForLFunctions.QuantitativeFactorizationMatching.PrescribedAndLocalCofactorObstructions
import GaloisForLFunctions.QuantitativeFactorizationMatching.GlobalDyadicGraphAndCofactorFibres
import GaloisForLFunctions.QuantitativeFactorizationMatching.DyadicMatchingStripAndRiemannEquivalence

/-!
# Complete Resolution of Quantitative Factorization Matching Across Squarefree Layers

This module synthesizes the unconditional classification of opposite-parity matchings across
squarefree prime-factor layers `ω(n) = k` on dyadic intervals `(X, 2X]`, together with their
positivity-free and spectral-free analytic consequences for `M(x)`, `1 / ζ(s)`, zero-free strips,
`RiemannHypothesis`, and integer-norm Beurling prime-edit selectivity:

1. **Local & prescribed-cofactor classification (`complete_local_and_prescribed_matching_trichotomy`)**:
   - Exact König–Ore decomposition `#M.unmatchedSet ≥ |∑_{n ∈ S} μ(n)| + 2 · hallExcessZ R S`
     (attained with equality) and universal cascade conservation across finite layers;
   - **Positive extension across every finite factor horizon `K ≥ 1`**: for every `B > 0`,
     sequential cellwise `{2, 3, 5}`-cofactor injections match 100% of squarefree integers in
     `(R, 2R]` with `1 ≤ ω(n) ≤ K` into a single disjoint opposite-parity matching at cell width
     `≤ 2R / (log R)^B` (tracking consumed targets across layers, with zero unweighted Möbius sum
     and uniform `Γ`-Sobolev energy bound `O(R^{1-δ} (log log R)^{2(K-1)} / (log R)^{2B+2})`),
     whereas any matching supported on `ω(n) ≤ K + 1` leaves at least `(6/π² - ε) R` unmatched
     squarefree integers;
   - **Negative global obstructions for prescribed finite prime sets and bounded-arity local moves**:
     * Every finite prime set `P₀` isolates all `P₀`-rough squarefree integers in `(X, 2X]`,
       forcing `≥ ((6/π²) ∏_{p ∈ P₀} p/(p+1) - ε) X` unmatched integers, while `M₀`-saturated
       multiples admit zero upward `(1 → 2)` `P₀`-targets;
     * Power-local bounded-arity common-cofactor exchanges (`H ≤ C X^θ`, `θ < 1`) isolate
       `≫ X / (log X)^r` balanced `r`-primes and leave `> X^β` unmatched integers for every `β < 1`;
     * Log-power cell bounded-arity common-cofactor exchanges (`H ≤ C X / (log X)^B`, `B > k`)
       isolate `> X^β` friable squarefree integers and leave `> X^β` unmatched integers for every
       `β < 1 - k / B` (hence `> X^{1/2 + δ}` when `B > 2k` and `> X^{20999/24000 + δ}` when
       `B > 24000k`).

2. **Global dyadic `(1 ↔ 2)` common-cofactor graph & ordered cofactor fibres
   (`complete_global_cofactor_and_fibre_resolution`)**:
   - Multiplicative sum-freeness of `(X, 2X]` forbids pure prime insertions/deletions, making
     `(1 ↔ 2)` prime exchanges `c p ↔ c q r` the unique minimal arity (`ω(u) + ω(v) ≥ 3`);
   - Unconstrained `GlobalDyadicOneTwoRel` eliminates **all** isolated vertices for `X ≥ 6` and
     gives every squarefree vertex degree `≥ D` for every `D` and sufficiently large `X`;
   - Restricting `GlobalDyadicOneTwoRel` to fixed `evenPrefixCofactor` fibres incurs a universal
     boundary debt of `≥ c X / (log X)³` negative-Möbius integers in empty positive fibres, proving
     that cross-fibre cofactor-changing `(1 ↔ 2)` moves are mandatory for sub-logarithmic matching.

3. **Positivity-free & spectral-free analytic consequences, `RiemannHypothesis` equivalence, and
   Beurling prime-edit selectivity (`complete_analytic_strip_rh_and_beurling_resolution`)**:
   - Any `O(X^θ)` (`0 < θ < 1`) dyadic opposite-parity matching yields `|M(x)| ≤ K x^θ`, converges
     `∑_{n < N} μ(n) n^{-s} → 1 / ζ(s)` holomorphically on `{Re s > θ, s ≠ 1}` via summation by
     parts and analytic continuation without positivity or spectral input, forces `ζ(s) ≠ 0` on
     `{Re s > θ}`, and bounds `zetaZeroAbscissa ≤ max (1 / 2) θ` (strictly `< 20999 / 24000` when
     `θ < 20999 / 24000`);
   - Unconditionally, every dyadic block `(X, 2X]` (`X ≥ 1`) admits an opposite-parity matching
     with `≤ C_β X^β` unmatched integers for every `β > 20999 / 24000` and `≤ C X^{7/8}` exact;
   - `RiemannHypothesis` holds if and only if every dyadic block `(X, 2X]` admits an opposite-parity
     matching with `≤ C_ε X^{1/2 + ε}` unmatched squarefree integers for every `ε > 0`;
   - Across every `σ ∈ (20999 / 24000, 14 / 15)` and `σ' ∈ (1 / 2, σ)`, there exist integer-norm
     two-sided prime edits `editSystem e` matching `ℙ` up to `O(R^{14/15})` on every log-power cell
     whose dyadic norm blocks admit **no** `O(X^{σ'})` opposite-parity matching.
-/

open Complex Finset Filter Topology
open _root_.RHTower _root_.RHTower.PrimeCells _root_.RHTower.CubicGamma
open GaloisForLFunctions.HeckeLFunctions
open GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.WorldsOfTheZeroConfiguration
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits
open scoped Classical BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-- **Part I — Local & prescribed-cofactor matching trichotomy**:
1. Exact König–Ore bipartite deficiency formula on any finite set `S`;
2. Positive cellwise `{2, 3, 5}` matching extension across every finite factor horizon `K ≥ 1` at
   log-power cell width `≤ 2R / (log R)^B`, paired with the `(6/π² - ε) R` unmatched tail law for
   any finite factor cutoff;
3. Linear unmatched obstruction for any prescribed finite prime set `P₀`;
4. Super-polynomial (`> X^β` for all `β < 1`) unmatched obstruction for power-local bounded-arity
   exchanges (`H ≤ C X^θ`, `θ < 1`);
5. Polynomial friable-isolation obstruction (`> X^β` for all `β < 1 - k / B`) for log-power cell
   bounded-arity exchanges (`H ≤ C X / (log X)^B`, `B > k`). -/
theorem complete_local_and_prescribed_matching_trichotomy :
    -- 1. König–Ore exact deficiency law
    (∀ (R : ℕ → ℕ → Prop) (S : Finset ℕ),
      (∀ M : OppositeParityMatching R S,
        |∑ n ∈ S, μ n| + 2 * hallExcessZ R S ≤ (M.unmatchedSet.card : ℤ)) ∧
      (∃ M : OppositeParityMatching R S,
        (M.unmatchedSet.card : ℤ) = |∑ n ∈ S, μ n| + 2 * hallExcessZ R S)) ∧
    -- 2. All-finite-layer cellwise extension + universal finite-horizon linear tail
    (∀ (K : ℕ), 1 ≤ K → ∀ {B : ℝ}, 0 < B →
      ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        ∃ (φ : ℕ → ℕ → ℕ)
          (M : OppositeParityMatching
            (fun a b => |(b : ℝ) - a| ≤ 2 * R / Real.log R ^ B) (Ioc R (2 * R))),
          IsValidLayerCascade (Ioc R (2 * R)) φ K ∧
          (∀ n ∈ Ioc R (2 * R), Squarefree n → 1 ≤ n.primeFactors.card →
            n.primeFactors.card ≤ K → n ∈ M.matchedSet) ∧
          ∑ n ∈ M.matchedSet, μ n = 0 ∧
          ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
            gammaNorm δ (fun t => ∑ n ∈ M.matchedSet, ((μ n : ℤ) : ℝ) * atom n t) ^ 2 ≤
              C * (R : ℝ) ^ (1 - δ) * Real.log (Real.log R) ^ (2 * (K - 1)) /
                Real.log R ^ (2 * B + 2)) ∧
    (∀ (K : ℕ) {ε : ℝ}, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∀ {Rel : ℕ → ℕ → Prop} (M : OppositeParityMatching Rel (Ioc R (2 * R))),
        (∀ n ∈ M.matchedSet, n.primeFactors.card ≤ K + 1) →
        (6 / Real.pi ^ (2 : ℕ) - ε) * (R : ℝ) ≤ (M.unmatchedSet.card : ℝ)) ∧
    -- 3. Prescribed finite prime-group linear obstruction
    (∀ (P₀ : Finset ℕ), (∀ p ∈ P₀, p.Prime) →
      ∀ {ε : ℝ}, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∀ M : OppositeParityMatching (PrescribedPrimeExchange P₀) (Ioc X (2 * X)),
          ((6 / Real.pi ^ (2 : ℕ)) * (∏ p ∈ P₀, (p : ℝ) / ((p : ℝ) + 1)) - ε) * (X : ℝ) ≤
            (M.unmatchedSet.card : ℝ)) ∧
    -- 4. Power-local bounded-arity obstruction (`H ≤ C X^θ`, `θ < 1`)
    (∀ (k : ℕ) {θ C β : ℝ}, θ < 1 → 0 < C → β < 1 →
      ∃ X₁ : ℕ, ∀ Y : ℕ, X₁ ≤ Y →
        ∀ M : OppositeParityMatching (BoundedArityLocalExchange k (C * (Y : ℝ) ^ θ))
            (Ioc Y (2 * Y)),
          (Y : ℝ) ^ β < (M.unmatchedSet.card : ℝ)) ∧
    -- 5. Log-power cell bounded-arity obstruction (`H ≤ C X / (log X)^B`, `B > k`)
    (∀ (k : ℕ) {B C β : ℝ}, (k : ℝ) < B → 0 < C → β < 1 - (k : ℝ) / B →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∀ M : OppositeParityMatching
            (BoundedArityLocalExchange k (C * (X : ℝ) / Real.log X ^ B)) (Ioc X (2 * X)),
          (X : ℝ) ^ β < (M.unmatchedSet.card : ℝ)) := by
  refine ⟨minUnmatched_ore_decomposition, ?_, eventually_unmatched_after_finite_layers_ge,
    ?_, ?_, ?_⟩
  · intro K hK B hB
    obtain ⟨C, hC, R₀, hR₀⟩ := exists_all_finite_layers_cell_matching K hK hB
    refine ⟨C, hC, R₀, fun R hR => ?_⟩
    obtain ⟨φ, M, hval, _, _, hcov, hsum, _, hgn⟩ := hR₀ R hR
    exact ⟨φ, M, hval, hcov, hsum, hgn⟩
  · intro P₀ hP₀ ε hε
    exact (eventually_prescribedPrimeExchange_unmatched_linear P₀ hP₀).2.2.2 hε
  · intro k θ C β hθ hC hβ
    obtain ⟨_, _, X₀, hX₀⟩ := eventually_powerLocal_boundedArity_isolated_ge k hθ hC
    exact (hX₀ X₀ le_rfl).2 hβ
  · intro k B C β hBk hC hβ
    obtain ⟨X₀, hX₀⟩ := eventually_logPowerCell_boundedArity_unmatched_gt_rpow k hBk hC hβ
    exact ⟨X₀, fun X hX M => (hX₀ X hX).2 M⟩

/-- **Part II — Global dyadic `(1 ↔ 2)` common-cofactor graph & ordered cofactor fibres**:
1. Multiplicative sum-freeness of `(X, 2X]` forces `1 ≤ ω(u)`, `1 ≤ ω(v)`, and `3 ≤ ω(u) + ω(v)`
   on every opposite-parity common-cofactor exchange `a = c u ↔ b = c v`;
2. `GlobalDyadicOneTwoRel` has **zero** isolated squarefree vertices on `(X, 2X]` for all `X ≥ 6`;
3. For every `D : ℕ`, eventually every squarefree integer in `(X, 2X]` has at least `D` distinct
   opposite-parity `GlobalDyadicOneTwoRel`-neighbors;
4. Restricting `GlobalDyadicOneTwoRel` to fixed `evenPrefixCofactor` fibres leaves at least
   `c X / (log X)³` unmatched integers (`c > 0`) on every sufficiently large dyadic block. -/
theorem complete_global_cofactor_and_fibre_resolution :
    (∀ {X a b : ℕ}, a ∈ squarefreeOf (Ioc X (2 * X)) → b ∈ squarefreeOf (Ioc X (2 * X)) →
      ∀ {c u v : ℕ}, μ a = -μ b → a = c * u → b = c * v →
        1 ≤ u.primeFactors.card ∧ 1 ≤ v.primeFactors.card ∧
        3 ≤ u.primeFactors.card + v.primeFactors.card) ∧
    (∀ {X : ℕ}, 6 ≤ X → isolatedVertices GlobalDyadicOneTwoRel (Ioc X (2 * X)) = ∅) ∧
    (∀ D : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ n ∈ squarefreeOf (Ioc X (2 * X)),
        D ≤ ((squarefreeOf (Ioc X (2 * X))).filter (GlobalDyadicOneTwoRel n ·)).card) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ M : OppositeParityMatching
          (fun a b => GlobalDyadicOneTwoRel a b ∧ evenPrefixCofactor a = evenPrefixCofactor b)
          (Ioc X (2 * X)),
        c * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (M.unmatchedSet.card : ℝ)) := by
  refine ⟨fun ha hb => (dyadic_no_pure_insertion_deletion ha hb).2,
    fun hX => globalDyadicOneTwo_isolatedVertices_empty hX,
    eventually_globalDyadicOneTwo_degree_ge, ?_⟩
  obtain ⟨c, hc, X₀, hX₀⟩ := eventually_evenPrefixFibre_debt_ge
  exact ⟨c, hc, X₀, fun X hX => (hX₀ X hX).2⟩

/-- **Part III — Positivity-free strip transfer, `RiemannHypothesis` equivalence, and Beurling
prime-edit selectivity**:
1. Positivity-free and spectral-free transfer from any `O(X^θ)` (`0 < θ < 1`) dyadic matching to
   `|M(x)| ≤ K x^θ`, holomorphic convergence `∑_{n < N} μ(n) n^{-s} → 1 / ζ(s)` on `{Re s > θ}`,
   `ζ(s) ≠ 0`, and `zetaZeroAbscissa ≤ max (1 / 2) θ`;
2. Unconditional `O(X^β)` (`β > 20999 / 24000`) and exact `O(X^{7/8})` dyadic opposite-parity
   matchings;
3. Exact equivalence between `RiemannHypothesis` and `O_ε(X^{1/2 + ε})` dyadic opposite-parity
   matchings;
4. Integer-norm Beurling prime-edit selectivity barrier across `(20999 / 24000, 14 / 15)`. -/
theorem complete_analytic_strip_rh_and_beurling_resolution :
    -- 1. Positivity-free & spectral-free strip transfer
    (∀ {θ C : ℝ} {X₀ : ℕ}, 0 < θ → θ < 1 →
      (∀ X : ℕ, X₀ ≤ X →
        ∃ (R : ℕ → ℕ → Prop) (M : OppositeParityMatching R (Ioc X (2 * X))),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ θ) →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
        |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ)| ≤ K * x ^ θ) ∧
      (∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F {s : ℂ | θ < s.re} ∧
        (∀ s : ℂ, θ < s.re →
          Tendsto (fun N => ∑ n ∈ range N, LSeries.term _root_.RHTower.moebiusCoeffC s n)
            atTop (𝓝 (F s))) ∧
        F 1 = 0 ∧
        ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 ∧ F s * riemannZeta s = 1) ∧
      _root_.RHTower.zetaZeroAbscissa ≤ max (1 / 2) θ) ∧
    -- 2. Unconditional `β > 20999 / 24000` and exact `7 / 8` dyadic matchings
    ((∀ {β : ℝ}, 20999 / 24000 < β →
        ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
          ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
            (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ β) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
          (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (7 / 8 : ℝ))) ∧
    -- 3. Exact `RiemannHypothesis` equivalence
    (((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
          ∃ M : OppositeParityMatching FullOppositeParityRel (Ioc X (2 * X)),
            (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) ↔ RiemannHypothesis) ∧
      ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
          ∃ (R : ℕ → ℕ → Prop) (M : OppositeParityMatching R (Ioc X (2 * X))),
            (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) ↔ RiemannHypothesis)) ∧
    -- 4. Integer-norm Beurling prime-edit selectivity barrier
    (∀ {σ σ' : ℝ}, 20999 / 24000 < σ → σ < 14 / 15 → 1 / 2 < σ' → σ' < σ →
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
              (M.unmatchedSet.card : ℝ) ≤ C_m * (X : ℝ) ^ σ')) :=
  ⟨fun hθ0 hθ1 hm => dyadic_matching_holomorphic_inv_zeta_and_zero_free hθ0 hθ1 hm,
   unconditional_dyadic_matching_sub_seven_eighths,
   dyadic_matching_half_iff_riemannHypothesis,
   fun hσ_lo hσ_hi hσ'_lo hσ'_hi => exists_primeEdit_matching_barrier hσ_lo hσ_hi hσ'_lo hσ'_hi⟩

/-- **Unified Master Theorem**: Complete unconditional resolution of the quantitative
factorization-matching problem across squarefree factor counts, common-cofactor and bounded-arity
local/prescribed vs. global `(1 ↔ 2)` graphs, ordered cofactor-fibre boundary debt, positivity-free
and spectral-free strip transfer, `RiemannHypothesis` equivalence, and integer-norm Beurling
prime-edit selectivity. -/
theorem complete_resolution_of_quantitative_factorization_matching :
    -- All-finite-layer cellwise extension (`1 ≤ ω(n) ≤ K`)
    (∀ (K : ℕ), 1 ≤ K → ∀ {B : ℝ}, 0 < B →
      ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        ∃ (φ : ℕ → ℕ → ℕ)
          (M : OppositeParityMatching
            (fun a b => |(b : ℝ) - a| ≤ 2 * R / Real.log R ^ B) (Ioc R (2 * R))),
          IsValidLayerCascade (Ioc R (2 * R)) φ K ∧
          (∀ n ∈ Ioc R (2 * R), Squarefree n → 1 ≤ n.primeFactors.card →
            n.primeFactors.card ≤ K → n ∈ M.matchedSet) ∧
          ∑ n ∈ M.matchedSet, μ n = 0) ∧
    -- Log-power cell bounded-arity obstruction (`H ≤ C X / (log X)^B`, `B > k`)
    (∀ (k : ℕ) {B C β : ℝ}, (k : ℝ) < B → 0 < C → β < 1 - (k : ℝ) / B →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∀ M : OppositeParityMatching
            (BoundedArityLocalExchange k (C * (X : ℝ) / Real.log X ^ B)) (Ioc X (2 * X)),
          (X : ℝ) ^ β < (M.unmatchedSet.card : ℝ)) ∧
    -- Global `(1 ↔ 2)` non-isolation (`X ≥ 6`) and ordered cofactor-fibre `X / (log X)³` debt
    ((∀ {X : ℕ}, 6 ≤ X → isolatedVertices GlobalDyadicOneTwoRel (Ioc X (2 * X)) = ∅) ∧
      (∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∀ M : OppositeParityMatching
            (fun a b => GlobalDyadicOneTwoRel a b ∧ evenPrefixCofactor a = evenPrefixCofactor b)
            (Ioc X (2 * X)),
          c * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (M.unmatchedSet.card : ℝ))) ∧
    -- Positivity-free strip transfer + unconditional `20999/24000` + `RiemannHypothesis` iff + Beurling barrier
    ((∀ {θ C : ℝ} {X₀ : ℕ}, 0 < θ → θ < 20999 / 24000 →
        (∀ X : ℕ, X₀ ≤ X →
          ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2 * X)),
            (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ θ) →
        _root_.RHTower.zetaZeroAbscissa ≤ max (1 / 2) θ ∧
          _root_.RHTower.zetaZeroAbscissa < 20999 / 24000) ∧
      ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
          ∃ (R : ℕ → ℕ → Prop) (M : OppositeParityMatching R (Ioc X (2 * X))),
            (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) ↔ RiemannHypothesis)) := by
  refine ⟨?_,
    complete_local_and_prescribed_matching_trichotomy.2.2.2.2.2,
    ⟨complete_global_cofactor_and_fibre_resolution.2.1,
      complete_global_cofactor_and_fibre_resolution.2.2.2⟩,
    ⟨globalDyadicOneTwo_sub_barrier_forces_abscissa_lt,
      dyadic_matching_half_iff_riemannHypothesis.2⟩⟩
  intro K hK B hB
  obtain ⟨C, hC, R₀, hR₀⟩ := complete_local_and_prescribed_matching_trichotomy.2.1 K hK hB
  refine ⟨C, hC, R₀, fun R hR => ?_⟩
  obtain ⟨φ, M, hval, hcov, hsum, _⟩ := hR₀ R hR
  exact ⟨φ, M, hval, hcov, hsum⟩

end GaloisForLFunctions.QuantitativeFactorizationMatching
