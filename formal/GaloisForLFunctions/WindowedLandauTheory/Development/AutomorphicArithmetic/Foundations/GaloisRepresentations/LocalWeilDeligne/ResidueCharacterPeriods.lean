import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldArithmeticFrobenius
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.FiniteResidueAdditiveCharacter
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters

/-! A character that separates the powers of arithmetic Frobenius has
integer period equal to the residue degree. This applies to regular
multiplicative characters and to additive characters with trivial
automorphism stabilizer. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.ABHN Multiplicative

namespace GlobalTheory.WeilDeligne

theorem character_period_of_distinct_powers {U : Type*} [Group U] (f : MulAut U)
    (χ : U →* ℂˣ) (n : ℕ) (hn : 0 < n) (ho : orderOf f = n)
    (hs : ∀ i j : ℕ, i < n → j < n →
      χ.comp (f ^ i).toMonoidHom = χ.comp (f ^ j).toMonoidHom → i = j)
    (i j : ℤ) :
    χ.comp (f ^ i).toMonoidHom = χ.comp (f ^ j).toMonoidHom ↔ (n : ℤ) ∣ i - j := by
  rw [← ho, orderOf_dvd_sub_iff_zpow_eq_zpow]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hmod (k : ℤ) : f ^ (k % (n : ℤ)).toNat = f ^ k := by
    have hk : 0 ≤ k % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    rw [← zpow_natCast, Int.toNat_of_nonneg hk, ← ho, zpow_mod_orderOf]
  have hlt (k : ℤ) : (k % (n : ℤ)).toNat < n := by
    have hm := Int.emod_lt_of_pos k (show 0 < (n : ℤ) by exact_mod_cast hn)
    omega
  have h' := hs _ _ (hlt i) (hlt j) (by simpa only [hmod] using h)
  rw [← hmod i, ← hmod j, h']

section FiniteField

variable (F K : Type) [Field F] [Field K] [Algebra F K] [Finite K]

/-- Arithmetic Frobenius acting on the multiplicative group of the extension. -/
def residueUnitsFrobenius : MulAut Kˣ :=
  Units.mapEquiv (finiteFieldArithmeticFrobenius F K).toRingEquiv.toMulEquiv

/-- Arithmetic Frobenius acting on the additive group of the extension. -/
def residueAdditiveFrobenius : MulAut (Multiplicative K) :=
  (finiteFieldArithmeticFrobenius F K).toRingEquiv.toAddEquiv.toMultiplicative

theorem residueUnitsFrobenius_apply (z : Kˣ) :
    residueUnitsFrobenius F K z = z ^ Nat.card F := by
  apply Units.ext
  exact (finiteFieldArithmeticFrobenius_apply F K (z : K)).trans
    (Units.val_pow_eq_pow_val z _).symm

theorem residueAdditiveFrobenius_apply (z : Multiplicative K) :
    residueAdditiveFrobenius F K z = ofAdd (toAdd z ^ Nat.card F) :=
  congrArg ofAdd (finiteFieldArithmeticFrobenius_apply F K (toAdd z))

theorem orderOf_residueUnitsFrobenius :
    orderOf (residueUnitsFrobenius F K) = Module.finrank F K := by
  let m : Gal(K/F) →* MulAut Kˣ :=
    { toFun := fun d => Units.mapEquiv d.toRingEquiv.toMulEquiv
      map_one' := by ext x; rfl
      map_mul' := fun a b => by ext x; rfl }
  have hm : Function.Injective m := by
    intro a b h
    ext x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [map_zero, map_zero]
    exact congrArg Units.val (DFunLike.congr_fun h (Units.mk0 x hx))
  exact (orderOf_injective m hm _).trans (orderOf_finiteFieldArithmeticFrobenius F K)

private def residueAdditiveAction : Gal(K/F) →* MulAut (Multiplicative K) where
  toFun d := d.toRingEquiv.toAddEquiv.toMultiplicative
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

theorem orderOf_residueAdditiveFrobenius :
    orderOf (residueAdditiveFrobenius F K) = Module.finrank F K := by
  have hm : Function.Injective (residueAdditiveAction F K) := by
    intro a b h
    ext x
    exact congrArg toAdd (DFunLike.congr_fun h (ofAdd x))
  exact (orderOf_injective (residueAdditiveAction F K) hm _).trans
    (orderOf_finiteFieldArithmeticFrobenius F K)

theorem exists_fullPeriod_additiveCharacter (n : ℕ) (hn : 0 < n) (hd : Module.finrank F K = n) :
    ∃ χ : Multiplicative K →* ℂˣ, ∀ i j : ℤ,
      χ.comp ((residueAdditiveFrobenius F K) ^ i).toMonoidHom =
        χ.comp ((residueAdditiveFrobenius F K) ^ j).toMonoidHom ↔ (n : ℤ) ∣ i - j := by
  let f := residueAdditiveFrobenius F K
  let a := finiteFieldArithmeticFrobenius F K
  obtain ⟨χ, hχ⟩ := exists_additiveCharacter_aut_stabilizer_trivial K
  refine ⟨χ, character_period_of_distinct_powers f χ n hn
    ((orderOf_residueAdditiveFrobenius F K).trans hd) ?_⟩
  intro i j hi hj h
  have hp (k : ℕ) (x : K) : (f ^ k) (ofAdd x) = ofAdd ((a ^ k) x) := by
    have := DFunLike.congr_fun (map_pow (residueAdditiveAction F K) a k) (ofAdd x)
    exact this.symm
  have ha (x : K) : χ (ofAdd ((a ^ i) x)) = χ (ofAdd ((a ^ j) x)) := by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hp] using DFunLike.congr_fun h (ofAdd x)
  have hst := (hχ (a ^ i * (a ^ j)⁻¹).toRingEquiv).mp fun x => by
    have he := ha ((a ^ j).symm x)
    change χ (ofAdd ((a ^ i) ((a ^ j).symm x))) = _ at he
    rw [AlgEquiv.apply_symm_apply] at he
    exact he
  have he : a ^ i * (a ^ j)⁻¹ = 1 := by
    ext x
    exact DFunLike.congr_fun hst x
  have hdvd := (pow_eq_pow_iff_modEq (x := a)).mp (mul_inv_eq_one.mp he)
  rw [show orderOf a = n from (orderOf_finiteFieldArithmeticFrobenius F K).trans hd] at hdvd
  change i % n = j % n at hdvd
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hdvd

end FiniteField

theorem regularCharacter_has_fullPeriod (g : ℕ) [Fact g.Prime] (K : Type)
    [Field K] [Algebra (ZMod g) K] [Finite K] (n : ℕ) (hn : 0 < n)
    (hd : Module.finrank (ZMod g) K = n)
    (χ : Kˣ →* ℂˣ) (hχ : GlobalTheory.Published.IsRegularChar g n χ) (i j : ℤ) :
    χ.comp ((residueUnitsFrobenius (ZMod g) K) ^ i).toMonoidHom =
      χ.comp ((residueUnitsFrobenius (ZMod g) K) ^ j).toMonoidHom ↔ (n : ℤ) ∣ i - j := by
  let f := residueUnitsFrobenius (ZMod g) K
  refine character_period_of_distinct_powers f χ n hn
    ((orderOf_residueUnitsFrobenius (ZMod g) K).trans hd) ?_ i j
  have hq : Nat.card (ZMod g) = g := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hp (k : ℕ) (x : Kˣ) : (f ^ k) x = x ^ g ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, residueUnitsFrobenius_apply, hq, ← pow_mul, ← pow_succ]
  have he (k : ℕ) : χ.comp (f ^ k).toMonoidHom = χ ^ g ^ k := by
    apply MonoidHom.ext
    intro x
    change χ ((f ^ k) x) = (χ ^ g ^ k) x
    rw [hp, map_pow, MonoidHom.pow_apply]
  intro a b ha hb h
  rw [he, he] at h
  exact hχ a b ha hb h

end GlobalTheory.WeilDeligne
