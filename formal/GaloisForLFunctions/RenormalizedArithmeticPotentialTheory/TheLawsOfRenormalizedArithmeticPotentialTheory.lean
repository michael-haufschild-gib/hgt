import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheArithmeticPoint
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsHeckeCovariant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PolarMatchingReadsTheDensityOfTheGauge
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsTheTowerForm

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
-/

noncomputable section

open Finset Matrix

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
      primeBilinear M (classPole p j' M) (classPole p j M) = Real.log p * classMass p j' M) :=
  ⟨fun _ _ hv => primeSurvival_rankOne hv,
    heckeCovariant_iff_const,
    fun _ hN => covariantCounterterm_sandwich hN,
    fun _ hN _ hκ => torsionCounterterm_ge hN hκ,
    fun _ hp J K => horizonCounterterm_rank_unbounded hp J K,
    fun _ hp J N x => tensorCounterterm_heckeShift hp J N x,
    fun _ hN => atomicWeilForm_spectrum_ends hN,
    fun _ hF => finiteFlip_matching hF,
    fun _ hη => exists_abs_atomicWeilForm_stepProfile_finitePart_le hη,
    fun _ hp _ _ hjj M => primeBilinear_classPole_cross_eq hp hjj M⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
