import GaloisForLFunctions.RHTower.DeningerBaumslagAbelian

/-!
# An abelian group with unique roots is a rational vector space

In an abelian group with unique roots the root operations are homomorphisms and compose: the `m`-th
root of the `n`-th root is the `mn`-th root.  Together with the rational power operation this makes
the group a `ℚ`-vector space, written additively.

mathlib knows that a `ℚ`-module structure on an additive group is unique when it exists, but has no
existence statement of this kind.

* `deningerRoot_mul`, `deningerRoot_zpow`, `deningerRoot_root` : the root operations.
* `deningerRatModule` : the rational vector space structure.
* `deningerRatLinearMap` : every homomorphism between such groups is automatically rational linear.
* `deningerBauRatModule` : the rationalization of an abelian group is a rational vector space.
-/

namespace RHTower

section AbelianRoots

variable {H : Type*} [CommGroup H] (hH : DeningerUniquelyDivisible H)

/-- **Roots are multiplicative** in an abelian group with unique roots. -/
theorem deningerRoot_mul (x y : H) (n : ℕ) :
    deningerRoot hH n (x * y) = deningerRoot hH n x * deningerRoot hH n y := by
  refine (deningerRoot_unique hH n ?_).symm
  rw [mul_pow, deningerRoot_pow, deningerRoot_pow]

/-- **Roots commute with powers.** -/
theorem deningerRoot_zpow (x : H) (n : ℕ) (k : ℤ) :
    deningerRoot hH n (x ^ k) = deningerRoot hH n x ^ k := by
  refine (deningerRoot_unique hH n ?_).symm
  rw [← zpow_natCast (deningerRoot hH n x ^ k) (n + 1), ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, deningerRoot_pow]

/-- **Roots compose.** -/
theorem deningerRoot_root (x : H) (m n : ℕ) :
    deningerRoot hH m (deningerRoot hH n x) = deningerRoot hH (m * n + m + n) x := by
  have h := deningerRoot_pow_root hH x n m
  rw [show n * m + n + m = m * n + m + n by ring] at h
  exact (deningerRoot_unique hH m h).symm

/-- **Rational scalar multiplication** on an abelian group with unique roots. -/
@[reducible] noncomputable def deningerRatSMul : SMul ℚ (Additive H) :=
  ⟨fun q x => Additive.ofMul (deningerRatPow hH (Additive.toMul x) (Multiplicative.ofAdd q))⟩

theorem deningerRatSMul_def (q : ℚ) (x : Additive H) :
    (deningerRatSMul hH).smul q x =
      Additive.ofMul (deningerRoot hH (q.den - 1) (Additive.toMul x) ^ q.num) := rfl

/-- **An abelian group with unique roots is a rational vector space.** -/
@[reducible] noncomputable def deningerRatModule : Module ℚ (Additive H) :=
  letI := deningerRatSMul hH
  { one_smul := fun x => by
      show Additive.ofMul (deningerRatPow hH (Additive.toMul x) (Multiplicative.ofAdd (1 : ℚ))) = x
      rw [deningerRatPow_ofAdd_one]
      rfl
    mul_smul := fun q₁ q₂ x => by
      have h1 : 0 < q₁.den := q₁.pos
      have h2 : 0 < q₂.den := q₂.pos
      have hidx : (q₁.den - 1) * (q₂.den - 1) + (q₁.den - 1) + (q₂.den - 1) =
          q₁.den * q₂.den - 1 := by
        obtain ⟨a, ha⟩ : ∃ a, q₁.den = a + 1 := ⟨q₁.den - 1, by omega⟩
        obtain ⟨b, hb⟩ : ∃ b, q₂.den = b + 1 := ⟨q₂.den - 1, by omega⟩
        rw [ha, hb]
        simp only [Nat.add_sub_cancel]
        rw [show (a + 1) * (b + 1) = a * b + a + b + 1 by ring, Nat.add_sub_cancel]
      have hstep : deningerRoot hH (q₁.den - 1)
          (deningerRoot hH (q₂.den - 1) (Additive.toMul x)) =
          deningerRoot hH (q₁.den * q₂.den - 1) (Additive.toMul x) := by
        rw [deningerRoot_root, hidx]
      show Additive.ofMul (deningerRoot hH ((q₁ * q₂).den - 1) (Additive.toMul x) ^
          (q₁ * q₂).num) =
        Additive.ofMul (deningerRoot hH (q₁.den - 1)
          (deningerRoot hH (q₂.den - 1) (Additive.toMul x) ^ q₂.num) ^ q₁.num)
      rw [deningerRoot_zpow, hstep, ← zpow_mul]
      refine congrArg Additive.ofMul ?_
      refine deningerRootPow_congr hH (Additive.toMul x) ?_
      have hden : ((q₁.den * q₂.den - 1 : ℕ) : ℤ) + 1 = (q₁.den : ℤ) * (q₂.den : ℤ) := by
        have : 1 ≤ q₁.den * q₂.den := Nat.one_le_iff_ne_zero.2 (by positivity)
        push_cast [Nat.cast_sub this]
        ring
      have hden' : (((q₁ * q₂).den - 1 : ℕ) : ℤ) + 1 = ((q₁ * q₂).den : ℤ) := by
        have := (q₁ * q₂).pos
        omega
      rw [hden, hden']
      have hq : ((q₁ * q₂).num : ℚ) * ((q₁.den : ℚ) * (q₂.den : ℚ)) =
          ((q₂.num * q₁.num : ℤ) : ℚ) * ((q₁ * q₂).den : ℚ) := by
        have hA : (q₁.num : ℚ) = q₁ * q₁.den := by
          have hnd := Rat.num_div_den q₁
          have hdne : ((q₁.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 q₁.den_nz
          field_simp at hnd
          exact hnd.trans (mul_comm _ _)
        have hB : (q₂.num : ℚ) = q₂ * q₂.den := by
          have hnd := Rat.num_div_den q₂
          have hdne : ((q₂.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 q₂.den_nz
          field_simp at hnd
          exact hnd.trans (mul_comm _ _)
        have hC : ((q₁ * q₂).num : ℚ) = (q₁ * q₂) * (q₁ * q₂).den := by
          have hnd := Rat.num_div_den (q₁ * q₂)
          have hdne : (((q₁ * q₂).den : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (q₁ * q₂).den_nz
          field_simp at hnd
          exact hnd
        push_cast
        rw [hA, hB, hC]
        ring
      exact_mod_cast hq
    smul_zero := fun q => by
      show Additive.ofMul (deningerRoot hH (q.den - 1) (1 : H) ^ q.num) = 0
      rw [show deningerRoot hH (q.den - 1) (1 : H) = 1 from
        (deningerRoot_unique hH (q.den - 1) (one_pow _)).symm, one_zpow]
      rfl
    smul_add := fun q x y => by
      show Additive.ofMul (deningerRoot hH (q.den - 1) (Additive.toMul x * Additive.toMul y) ^
          q.num) = _
      rw [deningerRoot_mul, mul_zpow]
      rfl
    add_smul := fun q₁ q₂ x => by
      show Additive.ofMul (deningerRatPow hH (Additive.toMul x)
          (Multiplicative.ofAdd (q₁ + q₂))) = _
      rw [show (Multiplicative.ofAdd (q₁ + q₂)) =
        Multiplicative.ofAdd q₁ * Multiplicative.ofAdd q₂ from rfl, map_mul]
      rfl
    zero_smul := fun x => by
      show Additive.ofMul (deningerRoot hH ((0 : ℚ).den - 1) (Additive.toMul x) ^
        (0 : ℚ).num) = 0
      norm_num }

end AbelianRoots

section Linearity

variable {H K : Type*} [CommGroup H] [CommGroup K]
    (hH : DeningerUniquelyDivisible H) (hK : DeningerUniquelyDivisible K)

/-- **Every homomorphism between abelian groups with unique roots is rational linear**, because
homomorphisms preserve roots. -/
noncomputable def deningerRatLinearMap (f : H →* K) :
    letI := deningerRatModule hH
    letI := deningerRatModule hK
    Additive H →ₗ[ℚ] Additive K :=
  letI := deningerRatModule hH
  letI := deningerRatModule hK
  { toFun := fun x => Additive.ofMul (f (Additive.toMul x))
    map_add' := fun x y => by
      show Additive.ofMul (f (Additive.toMul x * Additive.toMul y)) = _
      rw [map_mul]
      rfl
    map_smul' := fun q x => by
      show Additive.ofMul (f (deningerRoot hH (q.den - 1) (Additive.toMul x) ^ q.num)) =
        Additive.ofMul (deningerRoot hK (q.den - 1) (f (Additive.toMul x)) ^ q.num)
      rw [map_zpow, deningerMap_root] }

theorem deningerRatLinearMap_apply (f : H →* K) (x : Additive H) :
    deningerRatLinearMap hH hK f x = Additive.ofMul (f (Additive.toMul x)) := rfl

/-- The rational vector space structure on a group with unique roots is the only one, so
`deningerRatModule` is canonical. -/
theorem deningerRatModule_unique (inst : Module ℚ (Additive H)) : inst = deningerRatModule hH :=
  Subsingleton.elim _ _

end Linearity

section Rationalization

variable {α : Type*} [CommGroup α]

/-- **The rationalization of an abelian group is a rational vector space.** -/
@[reducible] noncomputable def deningerBauRatModule : Module ℚ (Additive (DeningerBau α)) :=
  deningerRatModule DeningerBau.uniquelyDivisible

/-- The unit of the rationalization, as a map into the underlying rational vector space. -/
noncomputable def deningerBauRatUnit : Additive α →+ Additive (DeningerBau α) :=
  AddMonoidHom.mk' (fun x => Additive.ofMul (DeningerBau.of (Additive.toMul x)))
    (fun x y => by
      show Additive.ofMul (DeningerBau.of (Additive.toMul x * Additive.toMul y)) = _
      rw [map_mul]
      rfl)

/-- The lift of the universal property is rational linear. -/
noncomputable def deningerBauRatLift {H : Type*} [CommGroup H]
    (hH : DeningerUniquelyDivisible H) (f : α →* H) :
    letI := deningerBauRatModule (α := α)
    letI := deningerRatModule hH
    Additive (DeningerBau α) →ₗ[ℚ] Additive H :=
  deningerRatLinearMap DeningerBau.uniquelyDivisible hH (deningerBauLift hH f)

end Rationalization

end RHTower
