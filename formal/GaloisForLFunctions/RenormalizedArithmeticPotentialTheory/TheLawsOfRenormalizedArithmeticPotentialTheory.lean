import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheArithmeticPoint
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsHeckeCovariant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PolarMatchingReadsTheDensityOfTheGauge
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsTheTowerForm
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTorsionCountertermIsAtMostTwoLogarithms
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSignOfTheTowerFinitePart
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheStabilityLawReachesTheSpacingUpToALogarithm
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonSeesOnlyTheMeanOfAClassFunction
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PolarMatchingNeedsOnlyTheLeadingOrder
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonLawsHoldForProfilesOfBoundedVariation
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTowerDeficitChangesSignBetweenFortyThreeAndFortySeven
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCharacterMertensLimitIsTheLogarithmicDerivative
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartSeparatesZetaFromItsLiouvilleTwin
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheResidueFinitePartIsDiagonalizedByCharacters
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTwistedPoleReadsTheLogarithmicDerivative
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartSeesEveryFlippedPrime

/-!
# The laws of renormalized arithmetic potential theory

One statement collecting the laws of the programme, each in its sharp form.

1. **Rank one pays one matched direction**: a positive coupling of the prime block to a rank-one
   partner has prime survival `ℝ b` if `|b| = 1` and `0` otherwise (`primeSurvival_rankOne`).
2. **Covariance forces a scalar**: a diagonal renormalization of Weil's prime form is Hecke covariant
   iff it is constant on the orders (`heckeCovariant_iff_const`).
3. **The covariant counterterm is `log N + O(1)`** (`covariantCounterterm_sandwich`).
4. **The anomaly costs half a logarithm**: every torsion counterterm is at least
   `(3/2) log N − C` (`torsionCounterterm_ge`).
5. **The horizon divergence has unbounded rank** on the `p`-adic classes
   (`horizonCounterterm_rank_unbounded`).
6. **No anomaly at the horizon**: the tensor counterterm is invariant under `[p]`
   (`tensorCounterterm_heckeShift`).
7. **Both ends of the spectrum**: `|P_N| ≤ log N + O(1)`, reached at the top by the pole vector and
   at the bottom by the Liouville pole vector (`atomicWeilForm_spectrum_ends`).
8. **Finitely many flips are invisible to polar matching** (`finiteFlip_matching`).
9. **The finite part is `−2γ`** on uniform step profiles
   (`exists_abs_atomicWeilForm_stepProfile_finitePart_le`).
10. **Across `p`-adic classes the Gram is one prime power** (`primeBilinear_classPole_cross_eq`): the
    off-diagonal of the tower form.
11. **The anomaly costs at most one logarithm**: `2 log N + C` renormalizes the torsion pairing
    (`renormalizesAt_two_log`).
12. **The sign law of the tower finite part**: it is nonnegative on all classes of `p` iff
    `√p log p ≤ γ(p − 1)` (`towerFinitePart_nonneg_iff`).
13. **The stability law reaches the spacing up to a logarithm**: the Markov form of every atomic test
    of width `≤ e^{−C₁}/(N(1 + log N))` is nonnegative (`markovEnergy_atomicTest_nonneg_logSpacing`).
14. **The horizon is blind to residue classes**: on the unit classes mod `q` the counterterm is the
    rank-one `(q/φ(q)) ℓ²` (`exists_abs_atomicWeilForm_unitClassProfile_sub_le`).
15. **Characters of every modulus are invisible**: `Re χ` twists of uniform profiles carry no polar
    divergence for `χ ≠ 1` (`exists_abs_atomicWeilForm_charRe_le`).
16. **Polar matching needs only the leading order**: `A_ε(y)/log y → κ` gives
    `P_N(εx) = κ ℓ² + (η log N + C_η) · mass` (`gaugeForm_stepProfile_of_tendsto`).
17. **The finite part `−2γ` holds for profiles of bounded variation** up to `η log N + C_η`
    (`exists_abs_atomicWeilForm_bv_finitePart_le`).
18. **The sign table of the tower finite part**: for a prime `p` it is nonnegative on every depth
    iff `p ≥ 47` (`towerFinitePart_nonneg_iff_fortySeven_le`).
19. **The finite part is twice the Mertens limit**: `A_ε(y) − κ log y → α` gives
    `P_N(εx) = κ ℓ² + 2α|x|² + o(mass)` (`exists_abs_gaugeForm_stepProfile_finitePart_le`).
20. **The character Mertens limit is the logarithmic derivative**: `A_χ(y) → −L′/L(1, χ)` for
    `χ ≠ 1` (`tendsto_charMertensSum`, `charMertensLimit_eq_neg_logDeriv`).
21. **The finite part separates ζ from its Liouville twin**: on the polar hyperplane
    `P_N(λx) − P_N(x) = 2(2γ + τ)|x|² + o(mass)` with `2γ + τ > 0`
    (`exists_abs_liouvilleForm_sub_zetaForm_sub_le`).
22. **Mertens' theorem in residue classes with its constant**: `A(y; r) − log y/φ(q) → c_r`
    (`tendsto_classMertensSum_sub`).
23. **The residue finite part is diagonalized by characters**: on the unit classes the finite part
    is `c_{a⁻¹b} S_a + c_{b⁻¹a} S_b`, and every character is an eigenvector with eigenvalue
    `2 Re β_χ` (`exists_abs_residueGram_finitePart_le`, `sum_residueFinitePart_mul_char`).
24. **The twisted pole reads `−L′/L(1, χ)`**: `P_N(Re χ · u^{(M)}) = 2 Re β_χ |x|² + o(mass)` for
    `χ ≠ 1` (`exists_abs_atomicWeilForm_charPole_sub_le`).
25. **`ζ` maximizes the finite part**: among sign gauges with `κ = 1` and a convergent Mertens error,
    the limit satisfies `α ≤ −γ`, with equality only for `ε = 1` (`finitePartLimit_le_and_eq_iff`).
-/

noncomputable section

open Finset Matrix Filter Topology

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-- **The laws of renormalized arithmetic potential theory.** -/
theorem renormalized_arithmetic_potential_theory_laws :
    -- rank one pays one matched direction
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] (b : α → ℝ) (v : β → ℝ), v ≠ 0 →
      primeSurvival 1 (vecMulVec b v) (vecMulVec v v) =
        if b ⬝ᵥ b = 1 then Submodule.span ℝ {b} else ⊥) ∧
    -- covariance forces a scalar
    (∀ h : ℕ → ℝ, (∀ t n : ℕ, 0 < t → h (t * n) = h n) ↔ ∀ n : ℕ, 0 < n → h n = h 1) ∧
    -- the covariant counterterm is `log N + O(1)`
    (∀ N : ℕ, 1 ≤ N →
      (∀ x : ℕ → ℝ, atomicWeilForm N x ≤
          (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
      ∀ κ : ℝ, (∀ x : ℕ → ℝ, atomicWeilForm N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2) →
        Real.log N - (Real.log 8 + 4) ≤ κ) ∧
    -- the anomaly costs half a logarithm
    (∀ N : ℕ, 1 ≤ N → ∀ κ : ℝ, RenormalizesAt N κ →
      3 / 2 * Real.log N - (Real.log 8 + 4 + tameConstant + 3 / 2) ≤ κ) ∧
    -- the horizon divergence has unbounded rank
    (∀ p : ℕ, p.Prime → ∀ (J : ℕ) (K : ℝ), ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ∀ ℓ : Fin J → ((ℕ → ℝ) →ₗ[ℝ] ℝ), ∃ x : ℕ → ℝ,
        (∀ i, ℓ i x = 0) ∧ 0 < ∑ n ∈ Icc 1 M, x n ^ 2 ∧
          K * ∑ n ∈ Icc 1 M, x n ^ 2 < atomicWeilForm M x) ∧
    -- no anomaly at the horizon
    (∀ p : ℕ, p.Prime → ∀ (J N : ℕ) (x : ℕ → ℝ),
      tensorCounterterm p (J + 1) (p * N) (heckeShift p x) = tensorCounterterm p J N x) ∧
    -- both ends of the spectrum
    (∀ N : ℕ, 1 ≤ N →
      (∀ x : ℕ → ℝ, |atomicWeilForm N x| ≤
          (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
      (Real.log N - (Real.log 8 + 4)) * ∑ n ∈ Icc 1 N, poleVector n ^ 2 ≤
        atomicWeilForm N poleVector ∧
      atomicWeilForm N (liouvilleTrunc N) ≤
        -(Real.log N - flipConstant) * ∑ n ∈ Icc 1 N, liouvilleTrunc N n ^ 2) ∧
    -- finitely many flips are invisible to polar matching
    (∀ F : Finset ℕ, (∀ p ∈ F, p.Prime) →
      IsSignGauge (finiteFlip F) ∧ ∀ y : ℕ, 1 ≤ y →
        |gaugeMertensSum (finiteFlip F) y - 1 * Real.log y| ≤
          Real.log 4 + 4 + 2 * ∑ p ∈ F, Real.log p / ((p : ℝ) - 1)) ∧
    -- the finite part is `−2γ`
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) →
      (∀ i, M i ≤ N) →
      |atomicWeilForm N (stepProfile c M) - polarFunctional N (stepProfile c M) ^ 2 +
          2 * Real.eulerMascheroniConstant * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C)) ∧
    -- across `p`-adic classes the Gram is one prime power
    (∀ p : ℕ, p.Prime → ∀ {j j' : ℕ}, j < j' → ∀ M : ℕ,
      primeBilinear M (classPole p j' M) (classPole p j M) = Real.log p * classMass p j' M) ∧
    -- the anomaly costs at most one logarithm
    (∀ N : ℕ, RenormalizesAt N (2 * Real.log N + (Real.log 4 + 4 + 2 * excessConstant))) ∧
    -- the sign law of the tower finite part
    (∀ p : ℕ, p.Prime →
      ((∀ (N : ℕ) (b : ℕ → ℝ), 0 ≤ towerFinitePart p N b) ↔ towerDeficit p ≤ 0)) ∧
    -- the stability law reaches the spacing up to a logarithm
    (∀ {g : ℝ → ℝ} {w : ℝ}, ContDiff ℝ 2 g → HasCompactSupport g →
      (∀ u, u ∉ Set.Icc 0 w → g u = 0) → ∀ {N : ℕ}, 1 ≤ N → 0 < w → w ≤ logSpacingWidth N →
        ∀ x : ℕ → ℝ, 0 ≤ RHTower.markovEnergy (fun u => (atomicTest N x g u : ℂ))) ∧
    -- the horizon is blind to residue classes
    (∀ (q : ℕ) [NeZero q], ∃ K : ℝ, ∀ {k N : ℕ} (c : (ZMod q)ˣ × Fin k → ℝ) (M : Fin k → ℕ),
      (∀ i, M i ≤ N) → (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (unitClassProfile q c M) -
          (q : ℝ) / q.totient * polarFunctional N (unitClassProfile q c M) ^ 2| ≤
        K * ∑ α, ∑ β, |c α| * |c β| * harmonicSum (min (M α.2) (M β.2))) ∧
    -- characters of every modulus are invisible
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∃ K : ℝ,
      ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) → (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (fun n : ℕ => (χ (n : ZMod q)).re * stepProfile c M n)| ≤
        K * (1 + Real.log N) * (∑ i, |c i|) ^ 2) ∧
    -- polar matching needs only the leading order
    (∀ ε : ℕ → ℝ, IsSignGauge ε → ∀ κ : ℝ, |κ| ≤ 1 →
      Tendsto (fun y : ℕ => gaugeMertensSum ε y / Real.log y) atTop (𝓝 κ) →
      ∀ η > 0, ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) →
        (∀ i, 1 ≤ M i) →
        |atomicWeilForm N (fun n => ε n * stepProfile c M n) -
            κ * polarFunctional N (stepProfile c M) ^ 2| ≤
          (η * Real.log N + C) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j))) ∧
    -- the finite part holds for profiles of bounded variation
    (∀ {g : ℝ → ℝ}, BoundedVariationOn g (Set.Icc 0 1) → ∀ η > 0, ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |atomicWeilForm N (fun n => g (Real.log n / Real.log N) * poleVector n) -
          polarFunctional N (fun n => g (Real.log n / Real.log N) * poleVector n) ^ 2 +
          2 * Real.eulerMascheroniConstant *
            ∑ n ∈ Icc 1 N, (g (Real.log n / Real.log N) * poleVector n) ^ 2| ≤
        η * Real.log N + C) ∧
    -- the sign table of the tower finite part
    (∀ p : ℕ, p.Prime → ((∀ (N : ℕ) (b : ℕ → ℝ), 0 ≤ towerFinitePart p N b) ↔ 47 ≤ p)) ∧
    -- the finite part is twice the Mertens limit
    (∀ ε : ℕ → ℝ, IsSignGauge ε → ∀ κ α : ℝ, |κ| ≤ 1 →
      Tendsto (gaugeMertensError ε κ) atTop (𝓝 α) → ∀ η > 0, ∃ C : ℝ,
        ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
        |atomicWeilForm N (fun n => ε n * stepProfile c M n) -
            κ * polarFunctional N (stepProfile c M) ^ 2 -
            2 * α * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
          ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C)) ∧
    -- the character Mertens limit is the logarithmic derivative
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      Tendsto (charMertensSum χ) atTop
        (𝓝 (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))) ∧
    -- the finite part separates ζ from its Liouville twin
    (∀ η > 0, 0 < 2 * Real.eulerMascheroniConstant + liouvilleEvenLimit ∧
      ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) →
        (∀ i, M i ≤ N) → polarFunctional N (stepProfile c M) = 0 →
        |atomicWeilForm N (fun n => liouvilleSign n * stepProfile c M n) -
            atomicWeilForm N (stepProfile c M) -
            2 * (2 * Real.eulerMascheroniConstant + liouvilleEvenLimit) *
              ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
          2 * ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C)) ∧
    -- Mertens' theorem in residue classes with its constant
    (∀ (q : ℕ) [NeZero q] (r : ZMod q), IsUnit r →
      Tendsto (fun y : ℕ => classMertensSum q r y - Real.log y / q.totient) atTop
        (𝓝 (classMertensConstant q r))) ∧
    -- the residue finite part is diagonalized by characters
    (∀ (q : ℕ) [NeZero q] (a b : ZMod q), IsUnit a → IsUnit b → ∀ η > 0, ∃ C : ℝ,
      ∀ M M' N : ℕ, 1 ≤ M → M ≤ M' → M' ≤ N →
        |primeBilinear N (residuePole q a M) (residuePole q b M') -
            (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M' -
            classMertensConstant q (a⁻¹ * b) * classHarmonic q a M -
            classMertensConstant q (b⁻¹ * a) * classHarmonic q b M| ≤
          η * harmonicSum M + C) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ),
      ∑ b : (ZMod q)ˣ, ((classMertensConstant q ↑(a⁻¹ * b) +
          classMertensConstant q ↑(b⁻¹ * a) : ℝ) : ℂ) * χ b =
        ((2 * (residueSpectralValue χ).re : ℝ) : ℂ) * χ a) ∧
    -- the twisted pole reads the logarithmic derivative
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ η > 0, ∃ C : ℝ,
      ∀ M N : ℕ, 1 ≤ M → M ≤ N →
        |atomicWeilForm N (charPole χ M) -
            2 * (residueSpectralValue χ).re * ∑ n ∈ Icc 1 N, charPole χ M n ^ 2| ≤
          η * harmonicSum M + C) ∧
    -- ζ maximizes the finite part among matched gauges
    (∀ ε : ℕ → ℝ, IsSignGauge ε → ∀ α : ℝ, Tendsto (gaugeMertensError ε 1) atTop (𝓝 α) →
      α ≤ -Real.eulerMascheroniConstant ∧
        (α = -Real.eulerMascheroniConstant ↔ ∀ n : ℕ, 1 ≤ n → ε n = 1)) :=
  ⟨fun _ _ hv => primeSurvival_rankOne hv,
    heckeCovariant_iff_const,
    fun _ hN => covariantCounterterm_sandwich hN,
    fun _ hN _ hκ => torsionCounterterm_ge hN hκ,
    fun _ hp J K => horizonCounterterm_rank_unbounded hp J K,
    fun _ hp J N x => tensorCounterterm_heckeShift hp J N x,
    fun _ hN => atomicWeilForm_spectrum_ends hN,
    fun _ hF => finiteFlip_matching hF,
    fun _ hη => exists_abs_atomicWeilForm_stepProfile_finitePart_le hη,
    fun _ hp _ _ hjj M => primeBilinear_classPole_cross_eq hp hjj M,
    renormalizesAt_two_log,
    fun _ hp => towerFinitePart_nonneg_iff hp,
    fun hg hgc hgsupp _ hN hw0 hw x =>
      markovEnergy_atomicTest_nonneg_logSpacing hg hgc hgsupp hN hw0 hw x,
    fun _ _ => exists_abs_atomicWeilForm_unitClassProfile_sub_le,
    fun _ _ χ hχ => exists_abs_atomicWeilForm_charRe_le χ hχ,
    fun _ hε _ hκ h => gaugeForm_stepProfile_of_tendsto hε hκ h,
    fun hg _ hη => exists_abs_atomicWeilForm_bv_finitePart_le hg hη,
    fun _ hp => towerFinitePart_nonneg_iff_fortySeven_le hp,
    fun _ hε _ _ hκ hE _ hη => exists_abs_gaugeForm_stepProfile_finitePart_le hε hκ hE hη,
    fun _ _ χ hχ => by
      rw [← charMertensLimit_eq_neg_logDeriv χ hχ]
      exact tendsto_charMertensSum χ hχ,
    fun _ hη => exists_abs_liouvilleForm_sub_zetaForm_sub_le hη,
    fun _ _ _ hr => tendsto_classMertensSum_sub hr,
    fun _ _ _ _ ha hb _ hη => exists_abs_residueGram_finitePart_le ha hb hη,
    fun _ _ χ a => sum_residueFinitePart_mul_char χ a,
    fun _ _ χ hχ _ hη => exists_abs_atomicWeilForm_charPole_sub_le χ hχ hη,
    fun _ hε _ hE => finitePartLimit_le_and_eq_iff hε hE⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
