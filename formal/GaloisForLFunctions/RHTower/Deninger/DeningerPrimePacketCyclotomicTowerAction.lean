import GaloisForLFunctions.RHTower.Deninger.DeningerPacketFrobeniusQuotientNontrivial
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeArithmeticCyclotomicComparison
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Faithful packet action on the arithmetic cyclotomic tower

This module constructs the missing forward half of the prime-packet inverse-limit comparison on
the actual algebraic closure of `ZMod p`.  A packet unit `u = (u_ℓ)_{ℓ ≠ p}` acts at level
`ℓ^k` by raising roots of unity to the finite reduction of `u_ℓ`.  The construction is:

* a group homomorphism at every finite stage;
* faithful after taking all stages;
* compatible with the inclusions `μ_{ℓ^k} → μ_{ℓ^(k+1)}`;
* valued in the genuine subgroup of compatible tower automorphisms; and
* equal to the literal `p`-power action on diagonal packet Frobenius.

No arbitrary choice of cyclic generator enters the action.  This matters for compatibility across
levels: independently chosen finite cyclic identifications would only give a product of unrelated
automorphism groups.  Surjectivity onto every compatible tower automorphism, and assembly across
the primary components into all automorphisms of `(F̄_p)ˣ`, remain separate inverse-limit and
primary-decomposition theorems.
-/

namespace RHTower

noncomputable section

/-- The `ℓ^k`-th roots of unity inside the chosen arithmetic closure of `𝔽_p`. -/
abbrev DeningerPrimeArithmeticRoots
    (p : Nat.Primes) (l : Nat.Primes) (k : ℕ) :=
  rootsOfUnity ((l : ℕ) ^ k) (DeningerPrimeArithmeticClosure p)

/-- Away from the characteristic, the arithmetic `ℓ^k`-root stage has exactly `ℓ^k`
elements. -/
theorem deningerPrimeArithmeticRoots_card (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    Nat.card (DeningerPrimeArithmeticRoots p l.1 k) = (l.1 : ℕ) ^ k := by
  letI : NeZero ((l.1 : ℕ) ^ k) := ⟨pow_ne_zero k l.1.2.ne_zero⟩
  letI : NeZero ((l.1 : ℕ) : ZMod (p : ℕ)) :=
    deningerAwayPrime_neZero_in_primeField p l
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity
    (DeningerPrimeArithmeticClosure p) ((l.1 : ℕ) ^ k)

/-- Canonical exponent action of units modulo `n` on a finite commutative group of cardinality
`n`.  It is defined by powers, rather than through a chosen cyclic generator. -/
def deningerFiniteCyclicUnitActionOfCardEq
    (G : Type*) [CommGroup G] [Finite G]
    (n : ℕ) (hcard : Nat.card G = n) :
    (ZMod n)ˣ →* MulAut G where
  toFun u := deningerCoprimePowerMulAut G u.val.val (by
    rw [hcard]
    exact (ZMod.val_coe_unit_coprime u).symm)
  map_one' := by
    letI : NeZero n :=
      ⟨hcard ▸ Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
    apply MulEquiv.ext
    intro x
    simp only [deningerCoprimePowerMulAut_apply]
    change x ^ ((1 : (ZMod n)ˣ).val.val) = x
    have hmod : Nat.ModEq (orderOf x) ((1 : (ZMod n)ˣ).val.val) 1 := by
      apply Nat.ModEq.of_dvd (hcard ▸ orderOf_dvd_natCard x)
      simpa [ZMod.val_one_eq_one_mod] using Nat.mod_modEq 1 n
    simpa only [pow_one] using (pow_eq_pow_iff_modEq.mpr hmod :
      x ^ ((1 : (ZMod n)ˣ).val.val) = x ^ 1)
  map_mul' u v := by
    letI : NeZero n :=
      ⟨hcard ▸ Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
    apply MulEquiv.ext
    intro x
    simp only [deningerCoprimePowerMulAut_apply]
    change x ^ ((u * v).val.val) = (x ^ v.val.val) ^ u.val.val
    rw [← pow_mul, Nat.mul_comm, pow_eq_pow_iff_modEq]
    apply Nat.ModEq.of_dvd (hcard ▸ orderOf_dvd_natCard x)
    change (u.val * v.val).val ≡ u.val.val * v.val.val [MOD n]
    rw [ZMod.val_mul]
    exact Nat.mod_modEq _ _

@[simp] theorem deningerFiniteCyclicUnitActionOfCardEq_apply
    (G : Type*) [CommGroup G] [Finite G]
    (n : ℕ) (hcard : Nat.card G = n)
    (u : (ZMod n)ˣ) (x : G) :
    deningerFiniteCyclicUnitActionOfCardEq G n hcard u x = x ^ u.val.val :=
  rfl

/-- On a cyclic group of cardinality `n`, the exponent action of `(ZMod n)ˣ` is faithful. -/
theorem deningerFiniteCyclicUnitActionOfCardEq_injective
    (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    (n : ℕ) (hcard : Nat.card G = n) :
    Function.Injective (deningerFiniteCyclicUnitActionOfCardEq G n hcard) := by
  letI : NeZero n :=
    ⟨hcard ▸ Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  intro u v huv
  obtain ⟨g, hg⟩ :=
    isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic G)
  have happ := DFunLike.congr_fun huv g
  change g ^ u.val.val = g ^ v.val.val at happ
  rw [pow_eq_pow_iff_modEq, hg, hcard, ← ZMod.natCast_eq_natCast_iff] at happ
  apply Units.ext
  exact (ZMod.natCast_zmod_val u.val).symm.trans
    (happ.trans (ZMod.natCast_zmod_val v.val))

/-- Action of the full packet on one actual arithmetic cyclotomic stage. -/
noncomputable def deningerPrimePacketCyclotomicStageAction
    (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    DeningerPacketUnits p →*
      MulAut (DeningerPrimeArithmeticRoots p l.1 k) :=
  (deningerFiniteCyclicUnitActionOfCardEq _ ((l.1 : ℕ) ^ k)
    (deningerPrimeArithmeticRoots_card p l k)).comp
      (deningerPacketCoordinateReduction p l k)

/-- Product of all away-prime, prime-power cyclotomic-stage automorphism groups. -/
abbrev DeningerPrimeCyclotomicTowerAut (p : Nat.Primes) :=
  ∀ l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}, ∀ k : ℕ,
    MulAut (DeningerPrimeArithmeticRoots p l.1 k)

/-- Simultaneous action of packet units on every arithmetic prime-power cyclotomic stage. -/
noncomputable def deningerPrimePacketCyclotomicTowerAction
    (p : Nat.Primes) :
    DeningerPacketUnits p →* DeningerPrimeCyclotomicTowerAut p where
  toFun u l k := deningerPrimePacketCyclotomicStageAction p l k u
  map_one' := by
    funext l k
    exact map_one _
  map_mul' u v := by
    funext l k
    exact map_mul _ _ _

/-- Finite reductions at all levels recover every packet coordinate. -/
theorem deningerPrimePacketCyclotomicTowerAction_injective (p : Nat.Primes) :
    Function.Injective (deningerPrimePacketCyclotomicTowerAction p) := by
  intro u v huv
  apply funext
  intro l
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  have hstage := congrFun (congrFun huv l) k
  have hred := (deningerFiniteCyclicUnitActionOfCardEq_injective
    (DeningerPrimeArithmeticRoots p l.1 k) ((l.1 : ℕ) ^ k)
    (deningerPrimeArithmeticRoots_card p l k)) hstage
  exact congrArg Units.val hred

/-- Natural inclusion `μ_{ℓ^k} → μ_{ℓ^(k+1)}` in the arithmetic closure. -/
def deningerPrimeArithmeticRootsInclusion
    (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    DeningerPrimeArithmeticRoots p l.1 k →*
      DeningerPrimeArithmeticRoots p l.1 (k + 1) :=
  Subgroup.inclusion (by
    intro z hz
    rw [mem_rootsOfUnity] at hz ⊢
    rw [pow_succ, pow_mul, hz, one_pow])

/-- **Inverse-system compatibility.**  Packet exponent actions commute with every consecutive
inclusion in the actual arithmetic root tower. -/
theorem deningerPrimePacketCyclotomicStageAction_compatible
    (p : Nat.Primes) (u : DeningerPacketUnits p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ)
    (z : DeningerPrimeArithmeticRoots p l.1 k) :
    deningerPrimeArithmeticRootsInclusion p l k
        (deningerPrimePacketCyclotomicStageAction p l k u z) =
      deningerPrimePacketCyclotomicStageAction p l (k + 1) u
        (deningerPrimeArithmeticRootsInclusion p l k z) := by
  apply Subtype.ext
  simp only [deningerPrimePacketCyclotomicStageAction, MonoidHom.coe_comp,
    Function.comp_apply, deningerFiniteCyclicUnitActionOfCardEq_apply,
    deningerPrimeArithmeticRootsInclusion, Subgroup.coe_inclusion]
  change (z.val ^ ((deningerPacketCoordinateReduction p l k u).val.val)) =
    z.val ^ ((deningerPacketCoordinateReduction p l (k + 1) u).val.val)
  rw [pow_eq_pow_iff_modEq]
  apply Nat.ModEq.of_dvd
    (orderOf_dvd_iff_pow_eq_one.mpr z.property)
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [deningerPacketCoordinateReduction, MonoidHom.comp_apply,
    deningerPadicUnitReduction, Units.coe_map]
  calc
    ((PadicInt.toZModPow k (u l : ℤ_[l.1])).val :
        ZMod ((l.1 : ℕ) ^ k)) =
      PadicInt.toZModPow k (u l : ℤ_[l.1]) := ZMod.natCast_zmod_val _
    _ = ZMod.cast (PadicInt.toZModPow (k + 1) (u l : ℤ_[l.1])) :=
      (PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k)
        (u l : ℤ_[l.1])).symm
    _ = ((PadicInt.toZModPow (k + 1) (u l : ℤ_[l.1])).val :
        ZMod ((l.1 : ℕ) ^ k)) := by
      let a := PadicInt.toZModPow (k + 1) (u l : ℤ_[l.1])
      calc
        ZMod.cast a = ZMod.cast (a.val : ZMod ((l.1 : ℕ) ^ (k + 1))) :=
          congrArg ZMod.cast (ZMod.natCast_zmod_val a).symm
        _ = (a.val : ZMod ((l.1 : ℕ) ^ k)) :=
          ZMod.cast_natCast (pow_dvd_pow (l.1 : ℕ) (Nat.le_succ k)) a.val

/-- **Arithmetic Frobenius compatibility.**  The diagonal packet unit acts by literal `p`-power
on every actual arithmetic cyclotomic stage. -/
theorem deningerPrimePacketCyclotomicStageAction_frobenius
    (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ)
    (z : DeningerPrimeArithmeticRoots p l.1 k) :
    deningerPrimePacketCyclotomicStageAction p l k
        (deningerPacketFrobeniusUnit p) z = z ^ (p : ℕ) := by
  simp only [deningerPrimePacketCyclotomicStageAction, MonoidHom.coe_comp,
    Function.comp_apply, deningerFiniteCyclicUnitActionOfCardEq_apply]
  rw [pow_eq_pow_iff_modEq]
  have hzpow : z ^ ((l.1 : ℕ) ^ k) = 1 := Subtype.ext z.property
  apply Nat.ModEq.of_dvd (orderOf_dvd_iff_pow_eq_one.mpr hzpow)
  rw [← ZMod.natCast_eq_natCast_iff]
  have h := congrArg Units.val
    (deningerPacketFrobeniusUnit_toZModPow p l k)
  simpa [deningerPacketCoordinateReduction, deningerPadicUnitReduction,
    ZMod.unitOfCoprime] using h

/-- Subgroup of tower automorphisms commuting with every consecutive stage inclusion. -/
def deningerPrimeCompatibleCyclotomicTowerAutSubgroup (p : Nat.Primes) :
    Subgroup (DeningerPrimeCyclotomicTowerAut p) where
  carrier A := ∀ l k (z : DeningerPrimeArithmeticRoots p l.1 k),
    deningerPrimeArithmeticRootsInclusion p l k (A l k z) =
      A l (k + 1) (deningerPrimeArithmeticRootsInclusion p l k z)
  one_mem' := by
    intro l k z
    rfl
  mul_mem' := by
    intro A B hA hB l k z
    change deningerPrimeArithmeticRootsInclusion p l k (A l k (B l k z)) =
      A l (k + 1)
        (B l (k + 1) (deningerPrimeArithmeticRootsInclusion p l k z))
    calc
      deningerPrimeArithmeticRootsInclusion p l k (A l k (B l k z)) =
          A l (k + 1)
            (deningerPrimeArithmeticRootsInclusion p l k (B l k z)) :=
        hA l k (B l k z)
      _ = A l (k + 1)
          (B l (k + 1) (deningerPrimeArithmeticRootsInclusion p l k z)) :=
        congrArg (A l (k + 1)) (hB l k z)
  inv_mem' := by
    intro A hA l k z
    change deningerPrimeArithmeticRootsInclusion p l k ((A l k).symm z) =
      (A l (k + 1)).symm (deningerPrimeArithmeticRootsInclusion p l k z)
    apply (A l (k + 1)).injective
    calc
      A l (k + 1)
          (deningerPrimeArithmeticRootsInclusion p l k ((A l k).symm z)) =
        deningerPrimeArithmeticRootsInclusion p l k
          (A l k ((A l k).symm z)) :=
        (hA l k ((A l k).symm z)).symm
      _ = deningerPrimeArithmeticRootsInclusion p l k z := by simp
      _ = A l (k + 1) ((A l (k + 1)).symm
          (deningerPrimeArithmeticRootsInclusion p l k z)) := by simp

/-- Genuine group of compatible prime-power cyclotomic-tower automorphisms. -/
abbrev DeningerPrimeCompatibleCyclotomicTowerAut (p : Nat.Primes) :=
  deningerPrimeCompatibleCyclotomicTowerAutSubgroup p

/-- Packet units act in the genuine compatible inverse-system subgroup. -/
noncomputable def deningerPrimePacketCompatibleCyclotomicTowerAction
    (p : Nat.Primes) :
    DeningerPacketUnits p →* DeningerPrimeCompatibleCyclotomicTowerAut p :=
  (deningerPrimePacketCyclotomicTowerAction p).codRestrict
    (deningerPrimeCompatibleCyclotomicTowerAutSubgroup p)
    (fun u => deningerPrimePacketCyclotomicStageAction_compatible p u)

/-- The compatible arithmetic tower action still loses no packet unit. -/
theorem deningerPrimePacketCompatibleCyclotomicTowerAction_injective
    (p : Nat.Primes) :
    Function.Injective (deningerPrimePacketCompatibleCyclotomicTowerAction p) := by
  intro u v huv
  apply deningerPrimePacketCyclotomicTowerAction_injective p
  exact congrArg Subtype.val huv

/-- Diagonal packet Frobenius acts by `p`-power inside the compatible tower subgroup. -/
theorem deningerPrimePacketCompatibleCyclotomicTowerAction_frobenius
    (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ)
    (z : DeningerPrimeArithmeticRoots p l.1 k) :
    (deningerPrimePacketCompatibleCyclotomicTowerAction p
        (deningerPacketFrobeniusUnit p) : DeningerPrimeCyclotomicTowerAut p) l k z =
      z ^ (p : ℕ) :=
  deningerPrimePacketCyclotomicStageAction_frobenius p l k z

/-- The canonical exponent action realizes every automorphism of a finite cyclic group. -/
theorem deningerFiniteCyclicUnitActionOfCardEq_surjective
    (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    (n : ℕ) (hcard : Nat.card G = n) :
    Function.Surjective (deningerFiniteCyclicUnitActionOfCardEq G n hcard) := by
  letI : NeZero n :=
    ⟨hcard ▸ Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  have hcards : Nat.card (ZMod n)ˣ = Nat.card (MulAut G) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      IsCyclic.card_mulAut, hcard]
  exact ((Nat.bijective_iff_injective_and_card
    (deningerFiniteCyclicUnitActionOfCardEq G n hcard)).2
      ⟨deningerFiniteCyclicUnitActionOfCardEq_injective G n hcard, hcards⟩).2

/-- Finite exponent attached to a compatible tower automorphism at one stage. -/
noncomputable def deningerCompatibleTowerExponentUnit
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    (ZMod ((l.1 : ℕ) ^ k))ˣ :=
  Classical.choose (deningerFiniteCyclicUnitActionOfCardEq_surjective
    (DeningerPrimeArithmeticRoots p l.1 k) ((l.1 : ℕ) ^ k)
    (deningerPrimeArithmeticRoots_card p l k) (A.val l k))

/-- The chosen finite exponent realizes the prescribed stage automorphism. -/
theorem deningerCompatibleTowerExponentUnit_spec
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    deningerFiniteCyclicUnitActionOfCardEq
        (DeningerPrimeArithmeticRoots p l.1 k) ((l.1 : ℕ) ^ k)
        (deningerPrimeArithmeticRoots_card p l k)
        (deningerCompatibleTowerExponentUnit p A l k) = A.val l k :=
  Classical.choose_spec (deningerFiniteCyclicUnitActionOfCardEq_surjective
    (DeningerPrimeArithmeticRoots p l.1 k) ((l.1 : ℕ) ^ k)
    (deningerPrimeArithmeticRoots_card p l k) (A.val l k))

/-- Consecutive finite exponent units are compatible under reduction. -/
theorem deningerCompatibleTowerExponentUnit_cast_succ
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    Units.map (ZMod.castHom
        (pow_dvd_pow (l.1 : ℕ) (Nat.le_succ k))
        (ZMod ((l.1 : ℕ) ^ k)))
      (deningerCompatibleTowerExponentUnit p A l (k + 1)) =
        deningerCompatibleTowerExponentUnit p A l k := by
  apply deningerFiniteCyclicUnitActionOfCardEq_injective
    (DeningerPrimeArithmeticRoots p l.1 k) ((l.1 : ℕ) ^ k)
    (deningerPrimeArithmeticRoots_card p l k)
  apply MulEquiv.ext
  intro z
  simp only [deningerFiniteCyclicUnitActionOfCardEq_apply]
  have hA := A.property l k z
  rw [← deningerCompatibleTowerExponentUnit_spec p A l k] at hA
  rw [← deningerCompatibleTowerExponentUnit_spec p A l (k + 1)] at hA
  simp only [deningerFiniteCyclicUnitActionOfCardEq_apply] at hA
  apply Subtype.ext
  let a := deningerCompatibleTowerExponentUnit p A l (k + 1)
  change z.val ^
      (Units.map (ZMod.castHom
        (pow_dvd_pow (l.1 : ℕ) (Nat.le_succ k))
        (ZMod ((l.1 : ℕ) ^ k))).toMonoidHom a).val.val =
    z.val ^ (deningerCompatibleTowerExponentUnit p A l k).val.val
  calc
    z.val ^
        (Units.map (ZMod.castHom
          (pow_dvd_pow (l.1 : ℕ) (Nat.le_succ k))
          (ZMod ((l.1 : ℕ) ^ k))).toMonoidHom a).val.val = z.val ^ a.val.val := by
      rw [pow_eq_pow_iff_modEq]
      apply Nat.ModEq.of_dvd (orderOf_dvd_iff_pow_eq_one.mpr z.property)
      rw [← ZMod.natCast_eq_natCast_iff]
      simp only [Units.coe_map]
      calc
        (((ZMod.cast a.val : ZMod ((l.1 : ℕ) ^ k))).val :
            ZMod ((l.1 : ℕ) ^ k)) = ZMod.cast a.val := ZMod.natCast_zmod_val _
        _ = ((a.val.val : ℕ) : ZMod ((l.1 : ℕ) ^ k)) := by
          calc
            ZMod.cast a.val =
                ZMod.cast (a.val.val : ZMod ((l.1 : ℕ) ^ (k + 1))) :=
              congrArg ZMod.cast (ZMod.natCast_zmod_val a.val).symm
            _ = _ := ZMod.cast_natCast
              (pow_dvd_pow (l.1 : ℕ) (Nat.le_succ k)) a.val.val
    _ = z.val ^ (deningerCompatibleTowerExponentUnit p A l k).val.val := by
      exact congrArg Subtype.val hA |>.symm

/-- Arbitrary finite exponent levels are compatible under reduction. -/
theorem deningerCompatibleTowerExponentUnit_cast
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)})
    {k1 k2 : ℕ} (hk : k1 ≤ k2) :
    ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) hk)
        (deningerCompatibleTowerExponentUnit p A l k2) =
      deningerCompatibleTowerExponentUnit p A l k1 := by
  induction k2, hk using Nat.le_induction with
  | base => simp
  | succ k2 hk ih =>
      calc
        ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) (Nat.le_succ_of_le hk))
            (deningerCompatibleTowerExponentUnit p A l (k2 + 1)) =
          ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) hk)
            (ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) (Nat.le_succ k2))
              (deningerCompatibleTowerExponentUnit p A l (k2 + 1))) := by
            have hcomp := congrArg
              (fun f => f (deningerCompatibleTowerExponentUnit p A l (k2 + 1)))
              (ZMod.unitsMap_comp
                (pow_dvd_pow (l.1 : ℕ) hk)
                (pow_dvd_pow (l.1 : ℕ) (Nat.le_succ k2)))
            exact hcomp.symm
        _ = ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) hk)
            (deningerCompatibleTowerExponentUnit p A l k2) := by
          exact congrArg (ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) hk))
            (by simpa [ZMod.unitsMap] using
              deningerCompatibleTowerExponentUnit_cast_succ p A l k2)
        _ = deningerCompatibleTowerExponentUnit p A l k1 := ih

/-- Polynomial evaluation at the finite exponent; the indeterminate is a universal compatible
element used to invoke the projective-limit property of `ℤ_ℓ`. -/
noncomputable def deningerCompatibleTowerExponentEval
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    Polynomial ℤ →+* ZMod ((l.1 : ℕ) ^ k) :=
  Polynomial.eval₂RingHom (Int.castRingHom _)
    (deningerCompatibleTowerExponentUnit p A l k).val

/-- The polynomial evaluation homomorphisms form a compatible projective system. -/
theorem deningerCompatibleTowerExponentEval_compatible
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)})
    (k1 k2 : ℕ) (hk : k1 ≤ k2) :
    (ZMod.castHom (pow_dvd_pow (l.1 : ℕ) hk)
      (ZMod ((l.1 : ℕ) ^ k1))).comp
        (deningerCompatibleTowerExponentEval p A l k2) =
      deningerCompatibleTowerExponentEval p A l k1 := by
  apply Polynomial.ringHom_ext
  · intro z
    simp [deningerCompatibleTowerExponentEval]
  · simp only [RingHom.comp_apply, deningerCompatibleTowerExponentEval,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    exact congrArg Units.val
      (deningerCompatibleTowerExponentUnit_cast p A l hk)

/-- Projective-limit lift of all finite exponents to one `ℓ`-adic integer. -/
noncomputable def deningerCompatibleTowerExponentPadicInt
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) : ℤ_[l.1] :=
  PadicInt.lift (deningerCompatibleTowerExponentEval_compatible p A l)
    Polynomial.X

/-- Every finite reduction of the lifted `ℓ`-adic integer is the prescribed exponent. -/
theorem deningerCompatibleTowerExponentPadicInt_toZModPow
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    PadicInt.toZModPow k (deningerCompatibleTowerExponentPadicInt p A l) =
      (deningerCompatibleTowerExponentUnit p A l k).val := by
  have h := DFunLike.congr_fun
    (PadicInt.lift_spec
      (deningerCompatibleTowerExponentEval_compatible p A l) k)
    Polynomial.X
  simpa [deningerCompatibleTowerExponentPadicInt,
    deningerCompatibleTowerExponentEval] using h

/-- The projective-limit exponent is a unit: its level-one reduction is a unit and hence nonzero. -/
theorem deningerCompatibleTowerExponentPadicInt_isUnit
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) :
    IsUnit (deningerCompatibleTowerExponentPadicInt p A l) := by
  letI : Fact (1 < (l.1 : ℕ) ^ 1) := ⟨by simpa using l.1.2.one_lt⟩
  by_contra hnot
  have hmax : deningerCompatibleTowerExponentPadicInt p A l ∈
      IsLocalRing.maximalIdeal ℤ_[l.1] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnot
  have hker : deningerCompatibleTowerExponentPadicInt p A l ∈
      RingHom.ker
        (PadicInt.toZModPow 1 : ℤ_[l.1] →+* ZMod ((l.1 : ℕ) ^ 1)) := by
    rw [PadicInt.ker_toZModPow, pow_one]
    simpa only [PadicInt.maximalIdeal_eq_span_p] using hmax
  rw [RingHom.mem_ker,
    deningerCompatibleTowerExponentPadicInt_toZModPow] at hker
  exact Units.ne_zero (deningerCompatibleTowerExponentUnit p A l 1) hker

/-- Reconstructed `ℓ`-adic unit attached to a compatible tower automorphism. -/
noncomputable def deningerCompatibleTowerExponentPadicUnit
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) : ℤ_[l.1]ˣ :=
  (deningerCompatibleTowerExponentPadicInt_isUnit p A l).unit

/-- Reduction of the reconstructed unit recovers every chosen finite exponent. -/
theorem deningerCompatibleTowerExponentPadicUnit_reduction
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    deningerPadicUnitReduction (l.1 : ℕ) k
        (deningerCompatibleTowerExponentPadicUnit p A l) =
      deningerCompatibleTowerExponentUnit p A l k := by
  apply Units.ext
  simp only [deningerPadicUnitReduction, Units.coe_map,
    deningerCompatibleTowerExponentPadicUnit]
  rw [IsUnit.unit_spec]
  exact deningerCompatibleTowerExponentPadicInt_toZModPow p A l k

/-- Reconstruct the full packet unit from a compatible arithmetic tower automorphism. -/
noncomputable def deningerCompatibleCyclotomicTowerToPacket
    (p : Nat.Primes) :
    DeningerPrimeCompatibleCyclotomicTowerAut p → DeningerPacketUnits p :=
  fun A l => deningerCompatibleTowerExponentPadicUnit p A l

/-- Reconstructing a packet and acting again returns the original compatible tower. -/
theorem deningerPrimePacketCompatibleCyclotomicTowerAction_rightInverse
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p) :
    deningerPrimePacketCompatibleCyclotomicTowerAction p
        (deningerCompatibleCyclotomicTowerToPacket p A) = A := by
  apply Subtype.ext
  funext l k
  change deningerPrimePacketCyclotomicStageAction p l k
      (deningerCompatibleCyclotomicTowerToPacket p A) = A.val l k
  rw [deningerPrimePacketCyclotomicStageAction]
  change deningerFiniteCyclicUnitActionOfCardEq
      (DeningerPrimeArithmeticRoots p l.1 k) ((l.1 : ℕ) ^ k)
      (deningerPrimeArithmeticRoots_card p l k)
      (deningerPadicUnitReduction (l.1 : ℕ) k
        (deningerCompatibleTowerExponentPadicUnit p A l)) = A.val l k
  rw [deningerCompatibleTowerExponentPadicUnit_reduction]
  exact deningerCompatibleTowerExponentUnit_spec p A l k

/-- Every compatible arithmetic prime-power cyclotomic-tower automorphism comes from a unique
packet unit. -/
theorem deningerPrimePacketCompatibleCyclotomicTowerAction_surjective
    (p : Nat.Primes) :
    Function.Surjective (deningerPrimePacketCompatibleCyclotomicTowerAction p) := by
  intro A
  exact ⟨deningerCompatibleCyclotomicTowerToPacket p A,
    deningerPrimePacketCompatibleCyclotomicTowerAction_rightInverse p A⟩

/-- **Prime-power inverse-limit comparison.**  Packet units are exactly the compatible
automorphisms of all actual away-prime cyclotomic towers. -/
noncomputable def deningerPrimePacketCompatibleCyclotomicTowerMulEquiv
    (p : Nat.Primes) :
    DeningerPacketUnits p ≃*
      DeningerPrimeCompatibleCyclotomicTowerAut p :=
  MulEquiv.ofBijective (deningerPrimePacketCompatibleCyclotomicTowerAction p)
    ⟨deningerPrimePacketCompatibleCyclotomicTowerAction_injective p,
      deningerPrimePacketCompatibleCyclotomicTowerAction_surjective p⟩

end

end RHTower
