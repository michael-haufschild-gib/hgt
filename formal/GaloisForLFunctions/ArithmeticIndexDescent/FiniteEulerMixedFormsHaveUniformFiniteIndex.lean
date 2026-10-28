import GaloisForLFunctions.ArithmeticIndexDescent.EveryFixedEulerMixedSourceIsGammaSmall
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# Finite index for a finite set of complete mixed Euler factors

The prime set is fixed, but all its prime powers and all complete cell horizons
are retained. The proved common Gamma-tail budget makes the form nonnegative
when a fixed finite detail head vanishes. Each negative subspace injects into
that head. The result concerns the mixed source and has no all-prime conclusion.
-/

noncomputable section

open MeasureTheory
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Gamma minus the entire mixed Euler source of a fixed finite prime set. -/
def finiteEulerGammaProfileForm {n : ℕ} (P : Finset Nat.Primes)
    (q d : Fin n → ℕ → ℝ) (X : ℕ) (x : Fin n → ℝ) : ℝ :=
  levyEnergy (completePairProfile (fun a => ∑ i, x i * q i a)
    (fun a => ∑ i, x i * d i a) X) -
      finiteEulerMixedSource P (fun a => ∑ i, x i * d i a)
        (fun a => ∑ i, x i * q i a) X

private def finiteEulerDetailReadout {n : ℕ} (d : Fin n → ℕ → ℝ) (A : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin A → ℝ) where
  toFun x a := ∑ i, x i * d i a
  map_add' x y := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
    rfl

/-- A fixed finite prime set has one upper negative-dimension bound at every complete horizon. -/
theorem exists_uniform_finiteEulerGamma_negative_dimension (P : Finset Nat.Primes) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → finiteEulerGammaProfileForm P q d X x < 0) →
        Module.finrank ℝ W ≤ A := by
  obtain ⟨A, hA, hpay⟩ := exists_finiteEuler_gamma_small_tail P (by norm_num : (0 : ℝ) < 1)
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := finiteEulerDetailReadout d A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) :
      0 ≤ finiteEulerGammaProfileForm P q d X x := by
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
    have hsign := le_abs_self (finiteEulerMixedSource P (fun a => ∑ i, x i * d i a)
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

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_uniform_finiteEulerGamma_negative_dimension
