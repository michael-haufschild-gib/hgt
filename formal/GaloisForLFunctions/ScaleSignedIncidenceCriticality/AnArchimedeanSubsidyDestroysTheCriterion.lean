import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimeWindowLadderConverges
import GaloisForLFunctions.RHTower.TrivialWeightBoostedWeilCone

/-!
# An archimedean subsidy destroys the criterion

The one reading of the field that is faithful is the unboosted Weil cone: membership pins the weight
to `Λ` at every index, so its defect scale is `0`
(`ThePrimeConeIsAPointAndTheGateIsIndexwise`, `ThePrimeWindowLadderConverges`). The corpus's
criteria list demands a "complete expression with no archimedean subsidy". This module measures what
a subsidy costs, and the answer is everything.

Boost the cone by an archimedean term of exponent `θ > ¼`: ask only for

`Re W_lam(f,f) + (1/2π) ∫ ‖f̂(r)‖² · C (1 + |r|)^θ ≥ 0`

at every compactly supported `C²` test. By `RHTower.TrivialWeightCone.trivialWeights_boostedWeilCone_of_quarter_lt`
the **all-ones weight** satisfies this for a suitable `C`, at every aperture
(`boostedCone_trivialWeight`). And the all-ones weight has the maximal defect scale `½`
(`weightDefectScale_trivialWeight`), since it already differs from `Λ` at the index `2`.

Hence `anArchimedeanSubsidyDestroysTheCriterion`: the boosted cone admits a weight of maximal
defect, so it pins nothing, while the unboosted cone pins the weight exactly. The subsidy does not
weaken the criterion by a margin — it removes it.

The lesson is the exact opposite of the usual reading of such boosts. A boosted inequality is easier
to prove precisely because it is satisfied by weights arbitrarily far from the arithmetic one; the
difficulty of the unboosted cone is not a technical obstacle but the entire content, and any
mechanism that buys positivity with an archimedean term has bought a statement with no arithmetic
consequence.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The boosted cone -/

/-- Weil positivity bought with an archimedean term of exponent `θ` and constant `C`. -/
def BoostedCone (θ C : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    MeasureTheory.Integrable (fun r : ℝ => ‖paperFT f r‖ ^ 2 * (1 + |r|) ^ θ) →
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re +
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (C * (1 + |r|) ^ θ)

/-- **The all-ones weight is in the boosted cone**, at every aperture. -/
theorem boostedCone_trivialWeight {θ : ℝ} (hθ : 1 / 4 < θ) :
    ∃ C : ℝ, 0 < C ∧ BoostedCone θ C (fun _ => 1) := by
  obtain ⟨C, hC, hmain⟩ := TrivialWeightCone.trivialWeights_boostedWeilCone_of_quarter_lt hθ
  exact ⟨C, hC, fun f hf hfc hint => hmain f hf hfc hint⟩

/-! ### 2. The all-ones weight has maximal defect -/

/-- **The all-ones weight is as far from the arithmetic weight as the unit allows.** -/
theorem weightDefectScale_trivialWeight : weightDefectScale (fun _ => 1) = 1 / 2 := by
  have hlog : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hne : (1 : ℝ) ≠ (ArithmeticFunction.vonMangoldt 2 : ℝ) := by
    rw [hlog]
    have := Real.log_two_lt_d9
    intro h
    rw [← h] at this
    norm_num at this
  have hmem : (2 : ℕ) ∈ defectIndices (fun _ => 1) := ⟨le_rfl, hne⟩
  refine le_antisymm (weightDefectScale_le_half _) ?_
  have hbdd : BddAbove ((fun m : ℕ => ((m : ℝ))⁻¹) '' defectIndices (fun _ => 1)) := by
    refine ⟨1 / 2, ?_⟩
    rintro x ⟨k, ⟨hk, -⟩, rfl⟩
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (by linarith) (by norm_num)).mpr hk2
  have hle : (((2 : ℕ) : ℝ))⁻¹ ≤ weightDefectScale (fun _ => 1) :=
    le_csSup hbdd ⟨2, hmem, rfl⟩
  simpa using hle

/-! ### 3. The subsidy removes the criterion -/

/-- **An archimedean subsidy destroys the criterion.** The boosted cone admits a weight of maximal
defect scale, so it constrains the weight not at all; the unboosted cone pins it to `Λ` at every
index. -/
theorem anArchimedeanSubsidyDestroysTheCriterion {θ : ℝ} (hθ : 1 / 4 < θ) :
    (∃ C : ℝ, 0 < C ∧ BoostedCone θ C (fun _ => 1) ∧
        weightDefectScale (fun _ => 1) = 1 / 2) ∧
      ∀ lam : ℕ → ℝ, WeilPositiveFull lam → weightDefectScale lam = 0 := by
  obtain ⟨C, hC, hcone⟩ := boostedCone_trivialWeight hθ
  refine ⟨⟨C, hC, hcone, weightDefectScale_trivialWeight⟩, fun lam hW => ?_⟩
  exact (weightDefectScale_eq_zero_iff lam).mpr (eq_vonMangoldt_of_weilPositiveFull hW)

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
