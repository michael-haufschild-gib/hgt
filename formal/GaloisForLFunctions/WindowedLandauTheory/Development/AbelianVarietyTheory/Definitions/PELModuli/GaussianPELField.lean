import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.CMField

/-! The Gaussian number field and its integral power basis supply the
rank-two lattice for the one-dimensional PEL datum. -/

noncomputable section

open NumberField
open scoped ComplexConjugate

namespace GlobalTheory.UPel.HT.GaussOne

abbrev Qi := IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ)

def ii : Qi := ⟨Complex.I, IntermediateField.mem_adjoin_simple_self ℚ Complex.I⟩

def τ₀ : Qi →+* ℂ := Qi.toSubfield.subtype

@[simp] theorem τ₀_ii : τ₀ ii = Complex.I := rfl

private theorem primitive_I : IsPrimitiveRoot Complex.I 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₂ : Complex.I ^ (2 ^ 1) ≠ 1 := by
    simp only [pow_one, Complex.I_sq]
    exact fun h => one_ne_zero (CharZero.neg_eq_self_iff.mp h)
  have h₄ : Complex.I ^ (2 ^ (1 + 1)) = 1 := Complex.I_pow_four
  exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime_pow h₂ h₄)

instance qiCyclotomic : IsCyclotomicExtension {4} ℚ Qi := by
  change IsCyclotomicExtension {4} ℚ (IntermediateField.adjoin ℚ {Complex.I}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (IsIntegral.tower_top (A := ℚ) (primitive_I.isIntegral (Nat.zero_lt_succ 3))).isAlgebraic]
  exact primitive_I.adjoin_isCyclotomicExtension ℚ

instance qiNumberField : NumberField Qi := IsCyclotomicExtension.numberField {4} ℚ Qi

instance qiCM : IsCMField Qi :=
  IsCyclotomicExtension.Rat.isCMField Qi (S := {4}) ⟨4, Set.mem_singleton _, by omega⟩

theorem ii_primitive : IsPrimitiveRoot ii 4 :=
  (show IsPrimitiveRoot (τ₀ ii) 4 from primitive_I).of_map_of_injective τ₀.injective

private theorem totient_four : Nat.totient 4 = 2 :=
  Nat.totient_prime_pow_succ Nat.prime_two 1

theorem finrankQi : Module.finrank ℚ Qi = 2 :=
  (IsCyclotomicExtension.Rat.finrank 4 Qi).trans totient_four

def bQ : Module.Basis (Fin 2) ℚ Qi :=
  (ii_primitive.powerBasis ℚ).basis.reindex
    (finCongr ((ii_primitive.powerBasis ℚ).finrank.symm.trans finrankQi))

theorem bQ_apply (i : Fin 2) : bQ i = ii ^ (i : ℕ) := by
  rw [bQ, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, IsPrimitiveRoot.powerBasis_gen]
  rfl

theorem exists_coord (x : Qi) : ∃ a b : ℚ, x = (a : Qi) + b * ii := by
  refine ⟨bQ.repr x 0, bQ.repr x 1, ?_⟩
  simpa [Fin.sum_univ_two, bQ_apply, Algebra.smul_def] using (bQ.sum_repr x).symm

theorem emb_ext (τ σ : Qi →+* ℂ) (h : τ ii = σ ii) : τ = σ :=
  RingHom.ext fun x => by
    obtain ⟨a, b, rfl⟩ := exists_coord x
    simp only [map_add, map_mul, map_ratCast, h]

def ζO : 𝓞 Qi := ii_primitive.toInteger

@[simp] theorem coe_ζO : (ζO : Qi) = ii := rfl

theorem ii_sq : ii ^ 2 = -1 :=
  τ₀.injective (by simpa only [map_pow, τ₀_ii, map_neg, map_one] using Complex.I_sq)

theorem ζO_sq : ζO ^ 2 = -1 := by
  apply RingOfIntegers.ext
  exact ii_sq

def bO : Module.Basis (Fin 2) ℤ (𝓞 Qi) :=
  ii_primitive.integralPowerBasis.basis.reindex
    (finCongr (ii_primitive.integralPowerBasis_dim.trans totient_four))

theorem bO_apply (i : Fin 2) : bO i = ζO ^ (i : ℕ) := by
  rw [bO, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, IsPrimitiveRoot.integralPowerBasis_gen]
  rfl

theorem bO_zero : bO 0 = 1 := by rw [bO_apply]; exact pow_zero _

theorem bO_one : bO 1 = ζO := by rw [bO_apply]; exact pow_one _

theorem coordO (x : 𝓞 Qi) : ∃ a b : ℤ, x = (a : 𝓞 Qi) + b * ζO := by
  refine ⟨bO.repr x 0, bO.repr x 1, ?_⟩
  simpa only [Fin.sum_univ_two, bO_zero, bO_one, zsmul_eq_mul, mul_one] using (bO.sum_repr x).symm

def barO : 𝓞 Qi ≃+* 𝓞 Qi := (IsCMField.ringOfIntegersComplexConj Qi).toRingEquiv

theorem barO_eq (x : 𝓞 Qi) : ((barO x : 𝓞 Qi) : Qi) = IsCMField.complexConj Qi (x : Qi) :=
  IsCMField.coe_ringOfIntegersComplexConj Qi x

theorem barO_barO (x : 𝓞 Qi) : barO (barO x) = x := by
  apply RingOfIntegers.ext
  rw [barO_eq, barO_eq, IsCMField.complexConj_apply_apply]

theorem barO_ζO : barO ζO = -ζO := by
  apply RingOfIntegers.ext
  apply τ₀.injective
  change τ₀ ((barO ζO : 𝓞 Qi) : Qi) = τ₀ (-(ζO : Qi))
  rw [barO_eq, IsCMField.complexEmbedding_complexConj, map_neg, coe_ζO, τ₀_ii]
  exact Complex.conj_I

end GlobalTheory.UPel.HT.GaussOne
