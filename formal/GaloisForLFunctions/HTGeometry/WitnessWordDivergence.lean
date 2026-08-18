import GaloisForLFunctions.HTGeometry.EncoderSelectionInformation

/-!
# The witness word

A codebook of one word carries no selection information at all, and its synthesis divergence
against a strictly positive reference is exactly the surprisal of that word.  Against the local
gate prior this is the affine word cost: the killing constant plus the length times the gate
rarity.
-/

open scoped BigOperators Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section PointLaw

variable {alpha : Type*}

/-- The deterministic law concentrated on one word. -/
def pointLaw (w0 : alpha) : alpha → ℝ := fun w => if w = w0 then 1 else 0

theorem pointLaw_nonneg (w0 : alpha) (w : alpha) : 0 ≤ pointLaw w0 w := by
  unfold pointLaw
  split_ifs <;> norm_num

theorem hasSum_pointLaw (w0 : alpha) : HasSum (pointLaw w0) 1 := by
  classical
  have hbase := hasSum_ite_eq w0 (1 : ℝ)
  exact hbase.congr_fun fun b => rfl

/-- A one-word codebook carries no selection information. -/
theorem entropy_pointLaw (w0 : alpha) : entropy (pointLaw w0) = 0 := by
  classical
  unfold entropy
  have hterm : ∀ w : alpha, -(pointLaw w0 w * Real.log (pointLaw w0 w)) = 0 := by
    intro w
    unfold pointLaw
    by_cases hw : w = w0
    · rw [if_pos hw]; simp
    · rw [if_neg hw]; simp
  rw [tsum_congr hterm, tsum_zero]

/-- **The synthesis divergence of a single witness word is its own surprisal.** -/
theorem relEntropy_pointLaw {p : alpha → ℝ} (_hp : ∀ w, 0 < p w) (w0 : alpha) :
    relEntropy (pointLaw w0) p = -Real.log (p w0) := by
  classical
  unfold relEntropy
  have hterm : ∀ w : alpha, pointLaw w0 w * Real.log (pointLaw w0 w / p w) =
      pointLaw w0 w * (-Real.log (p w0)) := by
    intro w
    unfold pointLaw
    by_cases hw : w = w0
    · subst hw
      rw [if_pos rfl, one_div, Real.log_inv]
    · rw [if_neg hw]; ring
  rw [tsum_congr hterm, tsum_mul_right, (hasSum_pointLaw w0).tsum_eq, one_mul]

end PointLaw

section WitnessWord

variable {Γ : Type*} [Fintype Γ]

/-- **`(25)`.**  One witness word preparing the state pays exactly its affine word cost, with no
selection information at all. -/
theorem relEntropy_pointLaw_wordPrior {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hM : 0 < Fintype.card Γ) (w0 : List Γ) :
    relEntropy (pointLaw w0) (wordPrior a) =
      -Real.log (1 - a) + (w0.length : ℝ) * Real.log ((Fintype.card Γ : ℝ) / a) := by
  rw [relEntropy_pointLaw (fun w => wordPrior_pos ha ha1 hM w) w0]
  exact neg_log_wordPrior ha ha1 hM w0

end WitnessWord

end

end GaloisForLFunctions.HTGeometry
