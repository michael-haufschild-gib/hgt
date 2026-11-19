import GaloisForLFunctions.QuantitativeFactorizationMatching.SelfContainedFibreClassPowerSaving

/-!
# Complete Unconditional Resolution of the Cross-Fibre Factorization Involution Question

This module synthesizes the complete mathematical answer, implications, and corollaries for
cross-fibre `(1 ↔ 2)` factorization involutions `c p ↔ c q r` on `(X, 2X]` without positivity or
spectral machinery:

1. **Explicit involution algebra & double-use bookkeeping
   (`FactorizationInvolution`, `sum_moebius_eq_jointUnmatched_sub_doubleUsed`,
   `resolveDoubleUse`, `involutionWalk_omega_descent`)**:
   - Sign-reversing involutions on squarefree vertices are in canonical bijection with
     `OppositeParityMatching`s and glue across pairwise-disjoint blocks;
   - Combining two involutions `τ₀, τ₁` obeys the exact signed remainder identity
     `∑_{n ∈ S} μ n = ∑_{n ∈ jointUnmatchedSet τ₀ τ₁} μ n - ∑_{n ∈ doubleUsedSet τ₀ τ₁} μ n`;
   - Alternating-walk resolution (`resolveDoubleUse`) eliminates all double-used endpoints into a
     single involution retaining `τ₀.movedPos` and `τ₁.movedNeg`, with strict factor-count descent
     `ω(x) + 2k = ω(a)` between ordered-fibre drops and `(1 → 2)` upward steps.
2. **Unique integer factorization selectivity
   (`unique_factorization_decoding_and_norm_selectivity`, `exists_primeEdit_matching_barrier`)**:
   - `maxPrimeStem` and `maxPrimeStem ∘ maxPrimeStem` uniquely decode `(c, p)` and `(c, q, r)`
     across all cofactors simultaneously, whereas norm collisions in generalized integer systems and
     two-sided prime edits (`editSystem e` matching `ℙ` up to `O(R^{14/15})` on log-power cells)
     destroy sub-`σ` dyadic matchings across `(20999 / 24000, 14 / 15)`.
3. **100% empty-fibre evacuation, `Θ(X / (log X)³)` pilot drop, and `O(X^{113/180})` power saving
   (`eventually_emptyFibres_evacuated_by_involution`,
   `eventually_pilotFibreClass_debt_and_strict_drop`,
   `eventually_balancedFibreClass_power_saving`)**:
   - `rankedCrossFibreInvolution X` evacuates 100% of all empty-positive ordered cofactor fibres;
   - `pilotVertices X` has `Θ(X / (log X)³)` unmatched debt under every ordered-cofactor involution,
     and `{2, 3, 5}` root-clearing + cross-fibre pairing strictly lowers global `#unmatchedSet` by
     at least `2 * #(pilotVertices X)` below **any** ordered-cofactor involution;
   - On the growing self-contained fibre class `balancedFibreClass X`
     (`# ≥ c_fib X^{1/3} / (log X)²`), ordered-cofactor debt is `Θ(X / (log X)³)`, while an
     explicit closed `GlobalDyadicOneTwoRel` involution leaves `≤ 4 * X^{113/180} ≤ 4 * X^{2/3}`
     unmatched vertices and signed remainder (`> X^{1/3}` power saving).
4. **Sharp persistence invariants (`fibreUnion_ordered_and_global_bounds`,
   `eventually_roughFibreClass_debt_persists`, `pilotVertices_isolated_on_large_cofactor_class`)**:
   - Cube-root rough subtree surplus (`10 * #fibrePos ≤ 9 * #fibreNeg`) forces `≥ c_pers X / (log X)³`
     unmatched vertices under **every** involution confined to `roughFibreCofactors X`, even though
     both positive and negative populations have order `≥ c X / (log X)³`;
   - Every `GlobalDyadicOneTwoRel` neighbor `m` of `pilotVertices X` satisfies
     `(evenPrefixCofactor m)² < X`, isolating 100% of `pilotVertices X` on any fibre class with
     `a² ≥ X`.
5. **Positivity-free analytic ending, functional-equation reflection, and `RiemannHypothesis`
   equivalence (`involution_analytic_ending_and_reflection`,
   `factorizationInvolution_half_iff_riemannHypothesis`)**:
   - `O(X^θ)` (`1 / 2 ≤ θ < 1`) dyadic involutions yield `|M(x)| ≤ K x^θ` by dyadic summation,
     holomorphic continuation `∑_{n < N} μ(n) n^{-s} → F(s)` on `{Re s > θ}` by Abel summation,
     `F(s) * riemannZeta s = 1` (`s ≠ 1`) by analytic continuation, and two-sided zero confinement
     `1 - θ ≤ Re ρ ≤ θ` for **every** nontrivial zero `ρ` of `riemannZeta` by functional-equation
     reflection (`riemannZeta_one_sub_eq_zero_of_mem_openStrip`), making `O_ε(X^{1/2 + ε})` dyadic
     involutions unconditionally equivalent to `RiemannHypothesis`.
-/

open Complex Finset Topology
open Filter (Tendsto atTop)
open _root_.RHTower _root_.RHTower.BeurlingDeletion
open GaloisForLFunctions.HeckeLFunctions
open GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.WorldsOfTheZeroConfiguration
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits
open scoped Classical BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-! ### 1. Positivity-free analytic ending and two-sided functional-equation reflection -/

/-- **Positivity-free analytic ending & functional-equation reflection**:
if `1 / 2 ≤ θ < 1` and every sufficiently large dyadic block `(X, 2X]` (`X ≥ X₀`) admits a
`FactorizationInvolution` `τ_X` (along any allowed edge relation `R X`, in particular
`GlobalDyadicOneTwoRel`) with `#τ_X.unmatchedSet ≤ C X^θ`, then using only signed finite pairing,
dyadic block summation, Abel summation, analytic continuation, and functional-equation reflection:
1. **Mertens bound**: `|M(x)| = |∑_{1 ≤ n ≤ ⌊x⌋₊} μ(n)| ≤ K x^θ` for all `x ≥ 1`;
2. **Dirichlet-series continuation & zeta inversion**: `∑_{n < N} μ(n) n^{-s}` converges on
   `{Re s > θ}` to a holomorphic function `F(s)` satisfying `F(1) = 0` and
   `F(s) * riemannZeta s = 1` (`riemannZeta s ≠ 0`) for all `Re s > θ`, `s ≠ 1`;
3. **Reflected two-sided zero-free strip**: every nontrivial zero `ρ` of `riemannZeta`
   (`¬ ∃ n : ℕ, ρ = -2 * (n + 1)`) satisfies `1 - θ ≤ ρ.re ∧ ρ.re ≤ θ`, and
   `zetaZeroAbscissa ≤ θ`. -/
theorem involution_analytic_ending_and_reflection
    {θ C : ℝ} {X₀ : ℕ} (hθ_half : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hinv : ∀ X : ℕ, X₀ ≤ X →
      ∃ (R : ℕ → ℕ → Prop) (τ : FactorizationInvolution R (Ioc X (2 * X))),
        (τ.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ θ) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ)| ≤ K * x ^ θ) ∧
    (∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | θ < s.re} ∧
      (∀ s : ℂ, θ < s.re →
        Tendsto (fun N => ∑ n ∈ range N, LSeries.term _root_.RHTower.moebiusCoeffC s n)
          atTop (𝓝 (F s))) ∧
      F 1 = 0 ∧
      ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 ∧ F s * riemannZeta s = 1) ∧
    (∀ ρ : ℂ, riemannZeta ρ = 0 → (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) →
      1 - θ ≤ ρ.re ∧ ρ.re ≤ θ) ∧
    _root_.RHTower.zetaZeroAbscissa ≤ θ := by
  have hθ0 : 0 < θ := by linarith only [hθ_half]
  have hmatch : ∀ X : ℕ, X₀ ≤ X →
      ∃ (R : ℕ → ℕ → Prop) (M : OppositeParityMatching R (Ioc X (2 * X))),
        (M.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ θ := by
    intro X hX
    obtain ⟨R, τ, hτ⟩ := hinv X hX
    exact ⟨R, τ.toMatching, τ.toMatching_unmatchedSet.symm ▸ hτ⟩
  obtain ⟨hMert, ⟨F, hF_diff, hF_tend, hF1, hF_inv⟩, habs_max⟩ :=
    dyadic_matching_holomorphic_inv_zeta_and_zero_free hθ0 hθ1 hmatch
  have habs : _root_.RHTower.zetaZeroAbscissa ≤ θ := by
    rwa [max_eq_right hθ_half] at habs_max
  refine ⟨hMert, ⟨F, hF_diff, hF_tend, hF1, hF_inv⟩, fun ρ hζ htriv => ?_, habs⟩
  have hnot_triv : ∀ n : ℕ, ρ ≠ -(2 * ((n : ℂ) + 1)) := fun n hn =>
    htriv ⟨n, by linear_combination hn⟩
  obtain ⟨h0, h1⟩ := _root_.RHTower.riemannZeta_zero_re_mem_Ioo hζ hnot_triv
  have hρ_ne1 : ρ ≠ 1 := fun heq => by rw [heq, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hre_le : ρ.re ≤ θ := by
    by_contra hgt
    exact (hF_inv ρ (not_le.mp hgt) hρ_ne1).1 hζ
  have hrefl : riemannZeta (1 - ρ) = 0 :=
    _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ h0 h1
  have h1mρ_ne1 : (1 : ℂ) - ρ ≠ 1 := fun heq => by
    have hρ0 : ρ = 0 := by linear_combination -heq
    rw [hρ0, Complex.zero_re] at h0
    exact lt_irrefl 0 h0
  have h1m_le : ((1 : ℂ) - ρ).re ≤ θ := by
    by_contra hgt
    exact (hF_inv (1 - ρ) (not_le.mp hgt) h1mρ_ne1).1 hrefl
  rw [Complex.sub_re, Complex.one_re] at h1m_le
  exact ⟨by linarith, hre_le⟩

/-- **Unconditional `O(X^β)` / `O(X^{7/8})` involutions and exact `RiemannHypothesis` equivalence**:
1. Unconditionally, for every `β > 20999 / 24000` (and at exact `β = 7 / 8`), every dyadic block
   `(X, 2X]` (`X ≥ 1`) admits a `FactorizationInvolution` with `≤ C X^β` unmatched vertices;
2. `RiemannHypothesis` holds if and only if for every `ε > 0` there exists `C > 0` such that every
   dyadic block `(X, 2X]` (`X ≥ 1`) admits a `FactorizationInvolution` leaving at most
   `C X^{1/2 + ε}` unmatched squarefree integers. -/
theorem factorizationInvolution_half_iff_riemannHypothesis :
    ((∀ {β : ℝ}, 20999 / 24000 < β →
        ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
          ∃ τ : FactorizationInvolution FullOppositeParityRel (Ioc X (2 * X)),
            (τ.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ β) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
        ∃ τ : FactorizationInvolution FullOppositeParityRel (Ioc X (2 * X)),
          (τ.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (7 / 8 : ℝ))) ∧
    (((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
          ∃ τ : FactorizationInvolution FullOppositeParityRel (Ioc X (2 * X)),
            (τ.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) ↔ RiemannHypothesis) ∧
      ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
          ∃ (R : ℕ → ℕ → Prop) (τ : FactorizationInvolution R (Ioc X (2 * X))),
            (τ.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) ↔ RiemannHypothesis)) := by
  obtain ⟨hsub, ⟨C78, hC78, h78⟩⟩ := unconditional_dyadic_matching_sub_seven_eighths
  obtain ⟨hiff_full, hiff_any⟩ := dyadic_matching_half_iff_riemannHypothesis
  refine ⟨⟨fun {β} hβ => ?_, ⟨C78, hC78, fun X hX => ?_⟩⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨C, hC, hX⟩ := hsub hβ
    refine ⟨C, hC, fun X hX1 => ?_⟩
    obtain ⟨M, hM⟩ := hX X hX1
    exact ⟨FactorizationInvolution.ofMatching M,
      (FactorizationInvolution.ofMatching_unmatchedSet M).symm ▸ hM⟩
  · obtain ⟨M, hM⟩ := h78 X hX
    exact ⟨FactorizationInvolution.ofMatching M,
      (FactorizationInvolution.ofMatching_unmatchedSet M).symm ▸ hM⟩
  · refine Iff.trans ?_ hiff_full
    constructor
    · intro H ε hε
      obtain ⟨C, hC, hX⟩ := H ε hε
      exact ⟨C, hC, fun X hX1 =>
        let ⟨τ, hτ⟩ := hX X hX1; ⟨τ.toMatching, τ.toMatching_unmatchedSet.symm ▸ hτ⟩⟩
    · intro H ε hε
      obtain ⟨C, hC, hX⟩ := H ε hε
      exact ⟨C, hC, fun X hX1 =>
        let ⟨M, hM⟩ := hX X hX1
        ⟨FactorizationInvolution.ofMatching M,
          (FactorizationInvolution.ofMatching_unmatchedSet M).symm ▸ hM⟩⟩
  · refine Iff.trans ?_ hiff_any
    constructor
    · intro H ε hε
      obtain ⟨C, hC, hX⟩ := H ε hε
      exact ⟨C, hC, fun X hX1 =>
        let ⟨R, τ, hτ⟩ := hX X hX1; ⟨R, τ.toMatching, τ.toMatching_unmatchedSet.symm ▸ hτ⟩⟩
    · intro H ε hε
      obtain ⟨C, hC, hX⟩ := H ε hε
      exact ⟨C, hC, fun X hX1 =>
        let ⟨R, M, hM⟩ := hX X hX1
        ⟨R, FactorizationInvolution.ofMatching M,
          (FactorizationInvolution.ofMatching_unmatchedSet M).symm ▸ hM⟩⟩

/-! ### 2. Unified Master Resolution Theorem -/

/-- **Complete Unconditional Resolution of Cross-Fibre Factorization Involutions, Power-Saving
Pilot Classes, Persistence Invariants, and the Positivity-Free Analytic Ending**:
1. **Double-use signed remainder & alternating-walk resolution**: exact identity
   `∑_{n ∈ S} μ n = ∑_{n ∈ jointUnmatchedSet τ₀ τ₁} μ n - ∑_{n ∈ doubleUsedSet τ₀ τ₁} μ n` and
   double-use elimination `resolveDoubleUse τ₀ τ₁` retaining `τ₀.movedPos` and `τ₁.movedNeg`;
2. **Unique factorization selectivity**: injective `maxPrimeStem` decoding on `ℕ` versus norm
   collisions on generalized integers;
3. **100% empty-fibre evacuation & `Θ(X / (log X)³)` pilot global reduction**:
   `rankedCrossFibreInvolution X` evacuates every empty-positive ordered cofactor fibre, while
   `pilotVertices X` (`Θ(X / (log X)³)`) is 100% unmatched under every ordered involution `τ₀` and
   resolves into `τ_*` with `τ_*.unmatchedSet.card + 2 * #(pilotVertices X) ≤ τ₀.unmatchedSet.card`;
4. **Provable `O(X^{113/180}) ⊆ O(X^{2/3})` power saving on a self-contained growing fibre class**:
   `balancedFibreClass X` (`# ≥ c_fib X^{1/3} / (log X)²`) carries `Θ(X / (log X)³)` ordered-cofactor
   debt yet admits a closed `GlobalDyadicOneTwoRel` involution with `≤ 4 * X^{113/180}` unmatched
   vertices and signed remainder;
5. **Larger invariants forcing debt persistence**: both the cube-root rough surplus invariant on
   `roughFibreCofactors X` (`≥ c_pers X / (log X)³` persistent debt despite `Θ(X / (log X)³)`
   positive and negative populations) and the `(evenPrefixCofactor m)² < X` cofactor-scale jump
   barrier isolating 100% of `pilotVertices X` on `{a | X ≤ a²}`;
6. **Positivity-free analytic ending, two-sided reflection, & `RiemannHypothesis` equivalence**:
   `O(X^θ)` (`1 / 2 ≤ θ < 1`) dyadic involutions confine all nontrivial zeros of `riemannZeta` to
   `1 - θ ≤ Re ρ ≤ θ` via signed finite pairing, Dirichlet-series continuation, and reflection, and
   `O_ε(X^{1/2 + ε})` dyadic involutions are unconditionally equivalent to `RiemannHypothesis`. -/
theorem complete_section_two_six_breakthrough_resolution :
    -- 1. Double-use signed remainder law & alternating-walk double-use resolution
    (∀ {R₁ R₂ : ℕ → ℕ → Prop} {S : Finset ℕ}
        (τ₁ : FactorizationInvolution R₁ S) (τ₂ : FactorizationInvolution R₂ S),
      ∑ n ∈ S, μ n =
        (∑ n ∈ jointUnmatchedSet τ₁ τ₂, μ n) - (∑ n ∈ doubleUsedSet τ₁ τ₂, μ n)) ∧
    (∀ {R : ℕ → ℕ → Prop} {S : Finset ℕ}
        (τ₀ τ₁ : FactorizationInvolution R S),
      τ₀.movedPos ⊆ (resolveDoubleUse τ₀ τ₁).movedPos ∧
      τ₁.movedNeg ⊆ (resolveDoubleUse τ₀ τ₁).movedNeg) ∧
    -- 2. Unique prime factorization decoding vs. generalized-integer norm collision
    ((∀ {c₁ c₂ q₁ r₁ q₂ r₂ : ℕ}, c₁ ≠ 0 → c₂ ≠ 0 →
        q₁.Prime → r₁.Prime → q₂.Prime → r₂.Prime → q₁ < r₁ → q₂ < r₂ →
        (∀ d ∈ c₁.primeFactors, d < q₁) → (∀ d ∈ c₂.primeFactors, d < q₂) →
        c₁ * (q₁ * r₁) = c₂ * (q₂ * r₂) → c₁ = c₂ ∧ q₁ = q₂ ∧ r₁ = r₂) ∧
      (∀ (B : _root_.RHTower.BeurlingSystem) (hInt : HasIntegerNorms B)
        {g₁ g₂ : B.Integer}, g₁ ≠ g₂ → natIntNorm hInt g₁ = natIntNorm hInt g₂ →
        ¬ ∃ decode : ℕ → B.Integer,
          decode (natIntNorm hInt g₁) = g₁ ∧ decode (natIntNorm hInt g₂) = g₂)) ∧
    -- 3. 100% empty-fibre evacuation & `Θ(X / (log X)³)` pilot strict global drop
    ((∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        (negParity (Ioc X (2 * X))).filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅) ⊆
          (rankedCrossFibreInvolution X).movedNeg) ∧
      (∃ (c_fib c₁ c₂ : ℝ), 0 < c_fib ∧ 0 < c₁ ∧ c₁ < c₂ ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c_fib * (X : ℝ) ^ (2 / 3 : ℝ) / Real.log X ^ (2 : ℕ) ≤ ((pilotCofactors X).card : ℝ) ∧
        c₁ * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ ((pilotVertices X).card : ℝ) ∧
        ((pilotVertices X).card : ℝ) ≤ c₂ * (X : ℝ) / Real.log X ^ (3 : ℕ) ∧
        ∀ τ₀ : FactorizationInvolution OrderedFibreRel (Ioc X (2 * X)),
          pilotVertices X ⊆ τ₀.unmatchedSet ∧
          ∃ τ_star : FactorizationInvolution GlobalDyadicOneTwoRel (Ioc X (2 * X)),
            τ₀.movedSet ∪ pilotVertices X ⊆ τ_star.movedSet ∧
            τ_star.unmatchedSet.card + 2 * (pilotVertices X).card ≤ τ₀.unmatchedSet.card)) ∧
    -- 4. Unconditional `O(X^{113/180}) ⊆ O(X^{2/3})` power saving on `balancedFibreClass X`
    (∃ (c_fib c₁ c₂ : ℝ), 0 < c_fib ∧ 0 < c₁ ∧ c₁ < c₂ ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c_fib * (X : ℝ) ^ (1 / 3 : ℝ) / Real.log X ^ (2 : ℕ) ≤
        ((balancedFibreClass X).card : ℝ) ∧
      (∀ τ₀ : FactorizationInvolution OrderedFibreRel (fibreUnion X (balancedFibreClass X)),
        c₁ * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (τ₀.unmatchedSet.card : ℝ)) ∧
      (∃ τ_ord : FactorizationInvolution OrderedFibreRel (fibreUnion X (balancedFibreClass X)),
        (τ_ord.unmatchedSet.card : ℝ) ≤ c₂ * (X : ℝ) / Real.log X ^ (3 : ℕ)) ∧
      (∃ τ : FactorizationInvolution GlobalDyadicOneTwoRel (fibreUnion X (balancedFibreClass X)),
        (τ.unmatchedSet.card : ℝ) ≤ 4 * (X : ℝ) ^ (113 / 180 : ℝ) ∧
        (τ.unmatchedSet.card : ℝ) ≤ 4 * (X : ℝ) ^ (2 / 3 : ℝ) ∧
        |(∑ n ∈ fibreUnion X (balancedFibreClass X), μ n : ℝ)| ≤
          4 * (X : ℝ) ^ (113 / 180 : ℝ))) ∧
    -- 5. Larger invariants forcing persistence (`roughFibreCofactors` & `a² ≥ X` jump barrier)
    ((∃ (c_pos c_neg c_pers : ℝ), 0 < c_pos ∧ 0 < c_neg ∧ 0 < c_pers ∧
        ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
          c_pos * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
            ((posParity (fibreUnion X (roughFibreCofactors X))).card : ℝ) ∧
          c_neg * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
            ((negParity (fibreUnion X (roughFibreCofactors X))).card : ℝ) ∧
          ∀ {R : ℕ → ℕ → Prop}
              (τ : FactorizationInvolution R (fibreUnion X (roughFibreCofactors X))),
            c_pers * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (τ.unmatchedSet.card : ℝ)) ∧
      (∀ {X : ℕ} {A : Finset ℕ},
        (∀ a ∈ A, X ≤ a ^ 2) → pilotCofactors X ⊆ A →
        ∀ τ : FactorizationInvolution GlobalDyadicOneTwoRel (fibreUnion X A),
          pilotVertices X ⊆ τ.unmatchedSet)) ∧
    -- 6. Positivity-free analytic ending, reflection, & `RiemannHypothesis` equivalence
    ((∀ {θ C : ℝ} {X₀ : ℕ}, 1 / 2 ≤ θ → θ < 1 →
        (∀ X : ℕ, X₀ ≤ X →
          ∃ (R : ℕ → ℕ → Prop) (τ : FactorizationInvolution R (Ioc X (2 * X))),
            (τ.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ θ) →
        (∀ ρ : ℂ, riemannZeta ρ = 0 → (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) →
          1 - θ ≤ ρ.re ∧ ρ.re ≤ θ) ∧
        _root_.RHTower.zetaZeroAbscissa ≤ θ) ∧
      ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
          ∃ (R : ℕ → ℕ → Prop) (τ : FactorizationInvolution R (Ioc X (2 * X))),
            (τ.unmatchedSet.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 2 + ε)) ↔ RiemannHypothesis)) := by
  refine ⟨fun τ₁ τ₂ => sum_moebius_eq_jointUnmatched_sub_doubleUsed τ₁ τ₂,
    fun τ₀ τ₁ => ⟨(resolveDoubleUse_spec τ₀ τ₁).1, (resolveDoubleUse_spec τ₀ τ₁).2.1⟩,
    ⟨unique_factorization_decoding_and_norm_selectivity.2.1,
      unique_factorization_decoding_and_norm_selectivity.2.2⟩,
    ⟨?_, ?_⟩,
    eventually_balancedFibreClass_power_saving,
    ⟨eventually_roughFibreClass_debt_persists,
      fun hA hpil τ => (pilotVertices_isolated_on_large_cofactor_class hA hpil τ).1⟩,
    ⟨fun hθ_half hθ1 hinv =>
      let h := involution_analytic_ending_and_reflection hθ_half hθ1 hinv
      ⟨h.2.2.1, h.2.2.2⟩,
      factorizationInvolution_half_iff_riemannHypothesis.2.2⟩⟩
  · obtain ⟨X₀, hX₀⟩ := eventually_emptyFibres_evacuated_by_involution
    exact ⟨X₀, fun X hX => (hX₀ X hX).1⟩
  · obtain ⟨c_fib, c₁, c₂, hcf, hc1, hc12, X₀, hX₀⟩ :=
      eventually_pilotFibreClass_debt_and_strict_drop
    refine ⟨c_fib, c₁, c₂, hcf, hc1, hc12, X₀, fun X hX => ?_⟩
    obtain ⟨hfib, _, hlo, hhi, hτ⟩ := hX₀ X hX
    refine ⟨hfib, hlo, hhi, fun τ₀ => ?_⟩
    obtain ⟨hunm, τ_star, hcov, _, hred⟩ := hτ τ₀
    exact ⟨hunm, τ_star, hcov, hred⟩

end GaloisForLFunctions.QuantitativeFactorizationMatching
