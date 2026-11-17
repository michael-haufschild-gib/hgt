import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.FiniteLayerKreinStructureAndRigidity
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheBoundedIndexStratumIsLindelofDeep
import GaloisForLFunctions.RHTower.JointAncestryRealAmplitudeCapstone
import GaloisForLFunctions.RHTower.FiniteOffLineConverse
import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.RHTower.RobinLcmCriterion

/-!
# Stage 2 with hypothesis and conclusion on the prime side

Stage 2 of the route (B13) asks that a finite layer of off-line zeros be empty:
`FiniteOffLine → RiemannHypothesis`. Both sides have prime-side forms.

* **Hypothesis** (`confinedIndexBounded_iff_exists_finiteWaveLaw`). The confined index is bounded iff
  `|ψ(x) − x + Re Σ_{q ∈ S} x^q/q| ≤ K √x log²x` on `x ≥ 16` for some finite set `S` of zero
  copies and some `K`.
* **Conclusion** (`no_criticalState_iff_jasRealPositiveAbove_of_finiteOffLine`). Under a finite
  layer there is no critical state iff the zero measure is nonnegative against every real-amplitude
  kernel on the primes above some `X`.
* **Rows** (`stageTwo_primeSide_tfae`). B13 is equivalent to each of: a finite layer gives
  real-amplitude positivity above some `X`; a bounded confined index excludes the critical state;
  a finite wave law for `ψ` holds with the empty wave; a finite wave law gives real-amplitude
  positivity above some `X`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations _root_.RHTower _root_.RHTower.BacklundConverse

/-- The finite-wave law for `ψ`: `|ψ(x) − x + Re Σ_{q ∈ S} x^q/q| ≤ K √x log²x` for `x ≥ 16`. -/
def FiniteWaveLaw (S : Finset XiZeroCopy) (K : ℝ) : Prop :=
  ∀ x : ℝ, 16 ≤ x →
    |Chebyshev.psi x - x + (offLineWave S x).re| ≤ K * Real.sqrt x * Real.log x ^ 2

/-- The two definitions of a finite layer agree: the spectral point of a copy `ρ` has imaginary
part `½ − Re ρ`. -/
theorem finiteOffLine_iff_finite_re_ne_half :
    FiniteOffLine ↔ {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite := by
  have heq : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0} =
      {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2} := by
    ext q
    have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
      simp [xiSpectralPoint, Complex.mul_im]
    simp only [Set.mem_setOf_eq, him]
    constructor <;> intro h h0 <;> apply h <;> linarith
  unfold FiniteOffLine
  rw [heq]

/-- A finite layer is a finite wave law for `ψ`. -/
theorem finiteOffLine_iff_exists_finiteWaveLaw :
    FiniteOffLine ↔ ∃ (S : Finset XiZeroCopy) (K : ℝ), FiniteWaveLaw S K :=
  finiteOffLine_iff_finite_re_ne_half.trans finite_offLine_iff_exists_offLineWave

/-- **The hypothesis of stage 2 on the prime side.** The confined index is bounded iff `ψ(x) − x`
is a finite wave up to `O(√x log²x)`. -/
theorem confinedIndexBounded_iff_exists_finiteWaveLaw :
    ConfinedIndexBounded ↔ ∃ (S : Finset XiZeroCopy) (K : ℝ), FiniteWaveLaw S K :=
  (confinedIndexBounded_tfae.out 0 2).trans finiteOffLine_iff_exists_finiteWaveLaw

/-- The wave law with the empty wave is the Riemann hypothesis (von Koch, both directions). -/
theorem riemannHypothesis_iff_exists_finiteWaveLaw_empty :
    RiemannHypothesis ↔ ∃ K : ℝ, FiniteWaveLaw ∅ K := by
  constructor
  · intro hRH
    obtain ⟨K, _, hK⟩ := exists_abs_psi_sub_le_of_riemannHypothesis hRH
    exact ⟨K, fun x hx => by simpa [offLineWave] using hK x hx⟩
  · rintro ⟨K, hK⟩
    refine riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq (abs_nonneg K) ?_
    filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
    have h := hK x hx
    simp only [offLineWave, Finset.sum_empty, Complex.zero_re, add_zero] at h
    calc Chebyshev.psi x - x ≤ |Chebyshev.psi x - x| := le_abs_self _
      _ ≤ K * Real.sqrt x * Real.log x ^ 2 := h
      _ ≤ |K| * Real.sqrt x * Real.log x ^ 2 := by
          gcongr
          exact le_abs_self K

/-- **The conclusion of stage 2 on the prime side.** Under a finite layer, there is no critical
state iff the zero measure is nonnegative against every real-amplitude kernel on the primes above
some `X`. -/
theorem no_criticalState_iff_jasRealPositiveAbove_of_finiteOffLine (hfin : FiniteOffLine) :
    (¬ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F) ↔
      ∃ X : ℕ, JasRealPositiveAbove X 1 := by
  rw [← zetaBeyondTheWallPrimeContinuation_iff_no_criticalState,
    zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis]
  exact ⟨exists_jasRealPositiveAbove_one_of_riemannHypothesis, fun hX =>
    riemannHypothesis_iff_finiteOffLine_and_jasRealPositiveAbove.mpr ⟨hfin, hX⟩⟩

/-- **The prime-side rows of stage 2.** Each of the following is equivalent to B13:
1. `FiniteOffLine → RiemannHypothesis` (**B13**);
2. a finite layer gives real-amplitude positivity above some `X`;
3. a bounded confined index excludes the critical state;
4. if `ψ(x) − x` is a finite wave up to `O(√x log²x)`, the wave is empty;
5. a finite wave law for `ψ` gives real-amplitude positivity above some `X`. -/
theorem stageTwo_primeSide_tfae :
    [FiniteOffLine → RiemannHypothesis,
      FiniteOffLine → ∃ X : ℕ, JasRealPositiveAbove X 1,
      ConfinedIndexBounded →
        ¬ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
          (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
          IsCriticalHalfLineGroundState W₀ F,
      (∃ (S : Finset XiZeroCopy) (K : ℝ), FiniteWaveLaw S K) → ∃ K : ℝ, FiniteWaveLaw ∅ K,
      (∃ (S : Finset XiZeroCopy) (K : ℝ), FiniteWaveLaw S K) →
        ∃ X : ℕ, JasRealPositiveAbove X 1].TFAE := by
  have hno : ZetaBeyondTheWallPrimeContinuation ↔ _ :=
    zetaBeyondTheWallPrimeContinuation_iff_no_criticalState
  tfae_have 1 → 2 := fun h hfin => exists_jasRealPositiveAbove_one_of_riemannHypothesis (h hfin)
  tfae_have 2 → 1 := fun h hfin =>
    riemannHypothesis_iff_finiteOffLine_and_jasRealPositiveAbove.mpr ⟨hfin, h hfin⟩
  tfae_have 1 → 3 := fun h hb => hno.mp
    (zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis.mpr
      (h ((confinedIndexBounded_tfae.out 0 2).mp hb)))
  tfae_have 3 → 1 := fun h hfin => zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis.mp
    (hno.mpr (h ((confinedIndexBounded_tfae.out 0 2).mpr hfin)))
  tfae_have 1 → 4 := fun h hw => riemannHypothesis_iff_exists_finiteWaveLaw_empty.mp
    (h (finiteOffLine_iff_exists_finiteWaveLaw.mpr hw))
  tfae_have 4 → 1 := fun h hfin => riemannHypothesis_iff_exists_finiteWaveLaw_empty.mpr
    (h (finiteOffLine_iff_exists_finiteWaveLaw.mp hfin))
  tfae_have 2 → 5 := fun h hw => h (finiteOffLine_iff_exists_finiteWaveLaw.mpr hw)
  tfae_have 5 → 2 := fun h hfin => h (finiteOffLine_iff_exists_finiteWaveLaw.mp hfin)
  tfae_finish

#print axioms stageTwo_primeSide_tfae
#print axioms confinedIndexBounded_iff_exists_finiteWaveLaw
#print axioms no_criticalState_iff_jasRealPositiveAbove_of_finiteOffLine

end GaloisForLFunctions.ExclusionOfTheCriticalState
