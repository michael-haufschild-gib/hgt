import GaloisForLFunctions.ArithmeticIndexDescent.ThePrimeTwoMixedTailIsGammaSmall
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# A uniform finite index for Gamma minus the prime-two mixed term

The original Gamma form pays the prime-two mixed source once finitely many
low detail coordinates vanish. Every negative subspace therefore injects
into those coordinates. The resulting bound is independent of the complete
cell horizon and of the chosen finite family of coarse and detail profiles.
The pure coarse prime form, other primes and poles are not part of this form.
-/

noncomputable section

open MeasureTheory
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Actual complete-cell Gamma energy minus its signed prime-two mixed contribution. -/
def primeTwoGammaProfileForm {n : ℕ} (q d : Fin n → ℕ → ℝ) (Y : ℕ) (x : Fin n → ℝ) : ℝ :=
  levyEnergy (completePairProfile (fun a => ∑ i, x i * q i a)
    (fun a => ∑ i, x i * d i a) (2 * Y + 1)) -
      primeTwoMixedSource (fun a => ∑ i, x i * d i a)
        (fun a => ∑ i, x i * q i a) (2 * Y + 1) (2 * Y + 1)

private def lowDetailReadout {n : ℕ} (d : Fin n → ℕ → ℝ) (A : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin A → ℝ) where
  toFun x a := ∑ i, x i * d i a
  map_add' x y := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- A fixed number of actual low detail readings bounds every negative subspace. -/
theorem exists_uniform_primeTwoGamma_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (Y : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → primeTwoGammaProfileForm q d Y x < 0) →
        Module.finrank ℝ W ≤ A := by
  obtain ⟨A, hA, hpay⟩ := exists_primeTwo_gamma_small_tail (by norm_num : (0 : ℝ) < 1)
  refine ⟨A, hA, ?_⟩
  intro n q d Y W hW
  let T := lowDetailReadout d A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) : 0 ≤ primeTwoGammaProfileForm q d Y x := by
    have hz (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 := by
      have h := congrFun hx (⟨a, ha⟩ : Fin A)
      exact h
    have htail : (fun a => if A ≤ a then ∑ i, x i * d i a else 0) =
        (fun a => ∑ i, x i * d i a) := by
      funext a
      by_cases ha : A ≤ a
      · exact if_pos ha
      · rw [if_neg ha, hz a (by omega)]
    have hp := hpay (fun a => ∑ i, x i * d i a) (fun a => ∑ i, x i * q i a) Y
    rw [htail, one_mul] at hp
    have hsign := le_abs_self (primeTwoMixedSource (fun a => ∑ i, x i * d i a)
      (fun a => ∑ i, x i * q i a) (2 * Y + 1) (2 * Y + 1))
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

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_uniform_primeTwoGamma_negative_dimension
