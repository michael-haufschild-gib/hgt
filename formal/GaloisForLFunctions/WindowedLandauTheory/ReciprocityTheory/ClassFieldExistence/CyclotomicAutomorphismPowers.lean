import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Factorial.Basic

/-! Cyclotomic automorphisms contain the powers determined by the factorial of the base field degree. -/

noncomputable section

open NumberField

namespace GlobalTheory.Reciprocity

theorem exists_cyclotomic_automorphism_factorial_power {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {g : ℕ}
    (hg : g.Coprime M) :
    ∃ τ : K ≃ₐ[E] K, τ ζ = ζ ^ (g ^ (Module.finrank ℚ E).factorial) := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  haveI : NumberField K := NumberField.of_module_finite E K
  set H := (hζ.autToPow E).range with hH
  have hcard : Nat.card H = Module.finrank E K := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (MonoidHom.ofInjective (hζ.autToPow_injective E)).toEquiv).symm
  have htot : M.totient ≤ Module.finrank ℚ E * Module.finrank E K := by
    rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic M ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos M)]
    exact minpoly.natDegree_le ζ
  have hidx : H.index * Nat.card H = M.totient := by
    rw [Subgroup.index_mul_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hle : H.index ≤ Module.finrank ℚ E := by
    rw [← hidx, hcard] at htot
    exact Nat.le_of_mul_le_mul_right htot Module.finrank_pos
  have hdvd : H.index ∣ (Module.finrank ℚ E).factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero H.index_ne_zero_of_finite) hle
  have hmem : ZMod.unitOfCoprime g hg ^ (Module.finrank ℚ E).factorial ∈ H := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul]
    exact H.pow_mem (H.pow_index_mem _) c
  obtain ⟨τ, hτ⟩ := hmem
  refine ⟨τ, ?_⟩
  rw [← hζ.autToPow_spec E τ, hτ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    ← Nat.cast_pow, ZMod.val_natCast]
  exact (pow_eq_pow_mod _ hζ.pow_eq_one).symm

end GlobalTheory.Reciprocity
