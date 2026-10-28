import GaloisForLFunctions.ArithmeticIndexDescent.TheEntirePrimeTwoEulerMixedSourceIsGammaSmall
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# Uniform finite index for the entire mixed Euler factor at two

One finite set of detail readings controls the negative dimension of Gamma
minus the full mixed Euler source. The bound is independent of the complete
cell horizon and includes every power of two. The pure coarse prime source,
the other Euler factors and the polar terms remain separate contributions.
-/

noncomputable section

open MeasureTheory
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Original Gamma energy minus the entire signed mixed Euler contribution at two. -/
def primeTwoEulerGammaProfileForm {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  levyEnergy (completePairProfile (fun a => ∑ i, x i * q i a)
    (fun a => ∑ i, x i * d i a) X) -
      primeTwoEulerMixedSource (fun a => ∑ i, x i * d i a)
        (fun a => ∑ i, x i * q i a) X

private def eulerLowDetailReadout {n : ℕ} (d : Fin n → ℕ → ℝ) (A : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin A → ℝ) where
  toFun x a := ∑ i, x i * d i a
  map_add' x y := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
    rfl

/-- A single finite detail head bounds every negative subspace of the actual Euler mixed form. -/
theorem exists_uniform_primeTwoEulerGamma_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → primeTwoEulerGammaProfileForm q d X x < 0) →
        Module.finrank ℝ W ≤ A := by
  obtain ⟨A, hA, hpay⟩ := exists_primeTwoEuler_gamma_small_tail (by norm_num : (0 : ℝ) < 1)
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := eulerLowDetailReadout d A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) :
      0 ≤ primeTwoEulerGammaProfileForm q d X x := by
    have hz (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 := by
      have h := congrFun hx (⟨a, ha⟩ : Fin A)
      exact h
    have htail : (fun a => if A ≤ a then ∑ i, x i * d i a else 0) =
        (fun a => ∑ i, x i * d i a) := by
      funext a
      by_cases ha : A ≤ a
      · exact if_pos ha
      · rw [if_neg ha, hz a (by omega)]
    have hp := hpay (fun a => ∑ i, x i * d i a) (fun a => ∑ i, x i * q i a) X
    rw [htail, one_mul] at hp
    have hsign := le_abs_self (primeTwoEulerMixedSource (fun a => ∑ i, x i * d i a)
      (fun a => ∑ i, x i * q i a) X)
    exact sub_nonneg.mpr (hsign.trans hp)
  have hker : LinearMap.ker (T.domRestrict W) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    by_contra hx0
    have hv : (x : Fin n → ℝ) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
    have hn := hW x x.property hv
    exact (not_lt_of_ge (hnonneg x hx)) hn
  have hinj : Function.Injective (T.domRestrict W) := LinearMap.ker_eq_bot.mp hker
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hd

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_uniform_primeTwoEulerGamma_negative_dimension
