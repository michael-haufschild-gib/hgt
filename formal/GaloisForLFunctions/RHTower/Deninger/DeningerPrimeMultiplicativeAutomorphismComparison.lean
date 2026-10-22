import GaloisForLFunctions.RHTower.Deninger.DeningerPrimePacketCyclotomicTowerAction
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Multiplicative automorphisms of a Deninger prime fibre

For a rational prime `p`, this module closes the algebraic numerator missing from
`DeningerPrimeArithmeticCyclotomicComparison`: restriction to all actual prime-power roots of
unity gives

`MulAut (AlgebraicClosure (ZMod p))ˣ ≃*
  DeningerPrimeCompatibleCyclotomicTowerAut p`.

The proof is not a cardinality comparison.  It decomposes the torsion group
`(AlgebraicClosure (ZMod p))ˣ` into its height-one primary components, proves that the
characteristic-`p` component is trivial, extends every compatible away-prime tower action
componentwise, and proves restriction injective on the full group.

Composing with the packet/tower equivalence identifies the packet unit group with the literal
multiplicative automorphism group.  Under this comparison the diagonal packet Frobenius is the
restriction of arithmetic Frobenius and acts by literal `p`-power on every unit, not merely at
each finite cyclotomic stage.
-/

namespace RHTower

noncomputable section

open IsDedekindDomain

theorem deningerPrimeMulAut_heightOne_asIdeal_eq_span (P : HeightOneSpectrum ℤ) :
    P.asIdeal = Ideal.span
      {((Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 : ℤ)} := by
  have hIntEquiv :
      Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext n
    exact eq_intCast _ n
  have hspan := Rat.HeightOneSpectrum.span_natGenerator P
  rw [hIntEquiv] at hspan
  have hmap : Ideal.map (RingEquiv.refl ℤ) P.asIdeal = P.asIdeal := by
    change Ideal.map (RingHom.id ℤ) P.asIdeal = P.asIdeal
    exact Ideal.map_id _
  rw [hmap] at hspan
  exact hspan.symm

theorem deningerPrimeMulAut_prime_arithmetic_units_isTorsion (p : Nat.Primes) :
    Monoid.IsTorsion (DeningerPrimeArithmeticClosure p)ˣ := by
  intro x
  let E : IntermediateField (ZMod (p : ℕ)) (DeningerPrimeArithmeticClosure p) :=
    IntermediateField.adjoin (ZMod (p : ℕ)) {x.val}
  letI : FiniteDimensional (ZMod (p : ℕ)) E :=
    IntermediateField.finiteDimensional_adjoin (fun y hy => by
      have hyx : y = x.val := Set.mem_singleton_iff.mp hy
      subst y
      exact (Algebra.IsAlgebraic.isAlgebraic
        (R := ZMod (p : ℕ)) x.val).isIntegral)
  letI : Finite E := Module.finite_of_finite (ZMod (p : ℕ))
  let y : Eˣ :=
    Units.mk0
      (⟨x.val, IntermediateField.subset_adjoin
        (ZMod (p : ℕ)) {x.val} (Set.mem_singleton x.val)⟩ : E)
      (by
        intro h
        exact x.ne_zero (congrArg Subtype.val h))
  have hy : IsOfFinOrder y := isOfFinOrder_of_finite y
  let incl : E →+* DeningerPrimeArithmeticClosure p :=
    E.val
  let inclUnits : Eˣ →* (DeningerPrimeArithmeticClosure p)ˣ :=
    Units.map incl
  have hmap : inclUnits y = x := by
    apply Units.ext
    rfl
  rw [← hmap]
  exact inclUnits.isOfFinOrder hy

theorem deningerPrimeMulAut_prime_arithmetic_additive_isTorsion (p : Nat.Primes) :
    Module.IsTorsion ℤ (Additive (DeningerPrimeArithmeticClosure p)ˣ) := by
  rw [← AddMonoid.isTorsion_iff_isTorsion_int]
  exact deningerPrimeMulAut_prime_arithmetic_units_isTorsion p

noncomputable def deningerPrimeMulAut_primaryDecomposition (p : Nat.Primes) :
    (Π₀ P : HeightOneSpectrum ℤ,
      Ideal.primaryComponent
        (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal) ≃ₗ[ℤ]
      Additive (DeningerPrimeArithmeticClosure p)ˣ :=
  by
  classical
  exact
  (Ideal.iSupIndep_primaryComponent ℤ
    (Additive (DeningerPrimeArithmeticClosure p)ˣ)).linearEquiv
      (Ideal.iSup_primaryComponent_eq_top
        (deningerPrimeMulAut_prime_arithmetic_additive_isTorsion p))

theorem deningerPrimeMulAut_primary_exists_primePowerOrder
    (p : Nat.Primes) (P : HeightOneSpectrum ℤ)
    (x : Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal) :
    ∃ k : ℕ,
      x.val.toMul ^
          ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ^ k) = 1 := by
  let l : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P
  obtain ⟨k, hk⟩ :=
    (Ideal.primaryComponent_mem
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal x.val).mp x.prop
  have hlmem : (l.1 : ℤ) ∈ P.asIdeal := by
    rw [deningerPrimeMulAut_heightOne_asIdeal_eq_span P]
    exact Ideal.mem_span_singleton_self _
  have hlpow : (l.1 : ℤ) ^ k ∈ P.asIdeal ^ k :=
    Ideal.pow_mem_pow hlmem k
  have hsmul := (Submodule.mem_torsionBySet_iff
    (s := (↑(P.asIdeal ^ k) : Set ℤ)) x.val).mp hk
      ⟨(l.1 : ℤ) ^ k, hlpow⟩
  refine ⟨k, ?_⟩
  change ((l.1 ^ k : ℕ) : ℤ) • x.val = 0 at hsmul
  rw [natCast_zsmul] at hsmul
  simpa [l] using congrArg Additive.toMul hsmul

theorem deningerPrimeMulAut_primePowerOrder_mem_primary
    (p : Nat.Primes) (P : HeightOneSpectrum ℤ)
    (x : Additive (DeningerPrimeArithmeticClosure p)ˣ) (k : ℕ)
    (hx : x.toMul ^
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ^ k) = 1) :
    x ∈ Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal := by
  let l : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P
  rw [Ideal.primaryComponent_mem]
  refine ⟨k, ?_⟩
  rw [deningerPrimeMulAut_heightOne_asIdeal_eq_span P, Ideal.span_singleton_pow]
  rw [Submodule.torsionBySet_ideal_span_singleton_eq]
  change ((l.1 ^ k : ℕ) : ℤ) • x = 0
  rw [natCast_zsmul]
  apply_fun Additive.toMul
  simpa [l] using hx

def deningerPrimeMulAut_rootsInclusionLE
    (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)})
    {k m : ℕ} (hkm : k ≤ m) :
    DeningerPrimeArithmeticRoots p l.1 k →*
      DeningerPrimeArithmeticRoots p l.1 m :=
  Subgroup.inclusion (by
    intro z hz
    rw [mem_rootsOfUnity] at hz ⊢
    rw [← orderOf_dvd_iff_pow_eq_one] at hz ⊢
    exact hz.trans (pow_dvd_pow (l.1 : ℕ) hkm))

@[simp] theorem deningerPrimeMulAut_rootsInclusionLE_coe
    (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)})
    {k m : ℕ} (hkm : k ≤ m)
    (z : DeningerPrimeArithmeticRoots p l.1 k) :
    ((deningerPrimeMulAut_rootsInclusionLE p l hkm z :
        DeningerPrimeArithmeticRoots p l.1 m) :
      (DeningerPrimeArithmeticClosure p)ˣ) = z :=
  rfl

theorem deningerPrimeMulAut_compatibleTowerAction_compatible_le
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)})
    {k m : ℕ} (hkm : k ≤ m)
    (z : DeningerPrimeArithmeticRoots p l.1 k) :
    deningerPrimeMulAut_rootsInclusionLE p l hkm (A.val l k z) =
      A.val l m (deningerPrimeMulAut_rootsInclusionLE p l hkm z) := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
      apply Subtype.ext
      have hstep := A.property l m (deningerPrimeMulAut_rootsInclusionLE p l hkm z)
      exact (congrArg Subtype.val ih).trans (congrArg Subtype.val hstep)

noncomputable def deningerPrimeMulAut_primaryLevel
    (p : Nat.Primes) (P : HeightOneSpectrum ℤ)
    (x : Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal) : ℕ :=
  Classical.choose (deningerPrimeMulAut_primary_exists_primePowerOrder p P x)

theorem deningerPrimeMulAut_primaryLevel_spec
    (p : Nat.Primes) (P : HeightOneSpectrum ℤ)
    (x : Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal) :
    x.val.toMul ^
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ^
          deningerPrimeMulAut_primaryLevel p P x) = 1 :=
  Classical.choose_spec (deningerPrimeMulAut_primary_exists_primePowerOrder p P x)

noncomputable def deningerPrimeMulAut_compatibleTowerPrimaryApply
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (P : HeightOneSpectrum ℤ)
    (haway :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ))
    (x : Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal) :
    Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal := by
  let l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
    ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩
  let k := deningerPrimeMulAut_primaryLevel p P x
  let z : DeningerPrimeArithmeticRoots p l.1 k :=
    ⟨x.val.toMul, deningerPrimeMulAut_primaryLevel_spec p P x⟩
  let y := A.val l k z
  exact ⟨Additive.ofMul (y :
      (DeningerPrimeArithmeticClosure p)ˣ),
    deningerPrimeMulAut_primePowerOrder_mem_primary p P _ k (by
      change ((y : DeningerPrimeArithmeticRoots p l.1 k) :
        (DeningerPrimeArithmeticClosure p)ˣ) ^ (l.1 : ℕ) ^ k = 1
      exact y.property)⟩

theorem deningerPrimeMulAut_compatibleTowerPrimaryApply_spec
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (P : HeightOneSpectrum ℤ)
    (haway :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ))
    (x : Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal)
    (k : ℕ)
    (hx : x.val.toMul ^
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ^ k) = 1) :
    (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x).val.toMul =
      ((A.val
        ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩ k
        ⟨x.val.toMul, hx⟩ :
          DeningerPrimeArithmeticRoots p
            (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P) k) :
        (DeningerPrimeArithmeticClosure p)ˣ) := by
  let l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
    ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩
  let kc := deningerPrimeMulAut_primaryLevel p P x
  let zc : DeningerPrimeArithmeticRoots p l.1 kc :=
    ⟨x.val.toMul, deningerPrimeMulAut_primaryLevel_spec p P x⟩
  let z : DeningerPrimeArithmeticRoots p l.1 k := ⟨x.val.toMul, hx⟩
  let m := max kc k
  have hc := deningerPrimeMulAut_compatibleTowerAction_compatible_le p A l
    (show kc ≤ m from le_max_left _ _) zc
  have hk := deningerPrimeMulAut_compatibleTowerAction_compatible_le p A l
    (show k ≤ m from le_max_right _ _) z
  change ((A.val l kc zc :
      DeningerPrimeArithmeticRoots p l.1 kc) :
        (DeningerPrimeArithmeticClosure p)ˣ) =
    ((A.val l k z : DeningerPrimeArithmeticRoots p l.1 k) :
      (DeningerPrimeArithmeticClosure p)ˣ)
  calc
    ((A.val l kc zc : DeningerPrimeArithmeticRoots p l.1 kc) :
        (DeningerPrimeArithmeticClosure p)ˣ) =
        ((A.val l m (deningerPrimeMulAut_rootsInclusionLE p l
          (show kc ≤ m from le_max_left _ _) zc) :
            DeningerPrimeArithmeticRoots p l.1 m) :
          (DeningerPrimeArithmeticClosure p)ˣ) :=
      congrArg Subtype.val hc
    _ = ((A.val l m (deningerPrimeMulAut_rootsInclusionLE p l
          (show k ≤ m from le_max_right _ _) z) :
            DeningerPrimeArithmeticRoots p l.1 m) :
          (DeningerPrimeArithmeticClosure p)ˣ) := by
      congr 2
    _ = ((A.val l k z : DeningerPrimeArithmeticRoots p l.1 k) :
          (DeningerPrimeArithmeticClosure p)ˣ) :=
      (congrArg Subtype.val hk).symm

theorem deningerPrimeMulAut_primePowerOrder_mono
    {G : Type*} [Group G] (l : ℕ) {k m : ℕ} (hkm : k ≤ m) (x : G)
    (hx : x ^ l ^ k = 1) :
    x ^ l ^ m = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one] at hx ⊢
  exact hx.trans (pow_dvd_pow l hkm)

noncomputable def deningerPrimeMulAut_compatibleTowerPrimaryAddHom
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (P : HeightOneSpectrum ℤ)
    (haway :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ)) :
    Ideal.primaryComponent
        (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal →+
      Ideal.primaryComponent
        (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal where
  toFun := deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway
  map_zero' := by
    apply Subtype.ext
    apply_fun Additive.toMul
    rw [deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A P haway 0 0]
    · simp
    · simp
  map_add' x y := by
    let l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
      ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩
    obtain ⟨kx, hx⟩ := deningerPrimeMulAut_primary_exists_primePowerOrder p P x
    obtain ⟨ky, hy⟩ := deningerPrimeMulAut_primary_exists_primePowerOrder p P y
    let m := max kx ky
    have hxm : x.val.toMul ^ (l.1 : ℕ) ^ m = 1 :=
      deningerPrimeMulAut_primePowerOrder_mono (l.1 : ℕ) (le_max_left _ _) x.val.toMul hx
    have hym : y.val.toMul ^ (l.1 : ℕ) ^ m = 1 :=
      deningerPrimeMulAut_primePowerOrder_mono (l.1 : ℕ) (le_max_right _ _) y.val.toMul hy
    have hxym : (x + y).val.toMul ^ (l.1 : ℕ) ^ m = 1 := by
      change (x.val.toMul * y.val.toMul) ^ (l.1 : ℕ) ^ m = 1
      rw [mul_pow, hxm, hym, mul_one]
    apply Subtype.ext
    apply_fun Additive.toMul
    change
      (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway (x + y)).val.toMul =
        (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x).val.toMul *
          (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway y).val.toMul
    rw [deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A P haway (x + y) m hxym,
      deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A P haway x m hxm,
      deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A P haway y m hym]
    exact congrArg Subtype.val
      (map_mul (A.val l m)
        (⟨x.val.toMul, hxm⟩ :
          DeningerPrimeArithmeticRoots p l.1 m)
        (⟨y.val.toMul, hym⟩ :
          DeningerPrimeArithmeticRoots p l.1 m))

noncomputable def deningerPrimeMulAut_compatibleTowerPrimaryAddEquiv
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (P : HeightOneSpectrum ℤ)
    (haway :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ)) :
    Ideal.primaryComponent
        (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal ≃+
      Ideal.primaryComponent
        (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal where
  __ := deningerPrimeMulAut_compatibleTowerPrimaryAddHom p A P haway
  invFun := deningerPrimeMulAut_compatibleTowerPrimaryApply p A⁻¹ P haway
  left_inv x := by
    let l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
      ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩
    obtain ⟨k, hx⟩ := deningerPrimeMulAut_primary_exists_primePowerOrder p P x
    let z : DeningerPrimeArithmeticRoots p l.1 k := ⟨x.val.toMul, hx⟩
    have hAx :
        (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x).val.toMul =
          ((A.val l k z : DeningerPrimeArithmeticRoots p l.1 k) :
            (DeningerPrimeArithmeticClosure p)ˣ) :=
      deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A P haway x k hx
    have hroot :
        (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x).val.toMul ^
          (l.1 : ℕ) ^ k = 1 := by
      rw [hAx]
      exact (A.val l k z).property
    have hzin :
        (⟨(deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x).val.toMul,
            hroot⟩ :
          DeningerPrimeArithmeticRoots p l.1 k) = A.val l k z := by
      apply Subtype.ext
      exact hAx
    apply Subtype.ext
    apply_fun Additive.toMul
    change
      (deningerPrimeMulAut_compatibleTowerPrimaryApply p A⁻¹ P haway
        (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x)).val.toMul =
          x.val.toMul
    rw [deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A⁻¹ P haway
      (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x) k hroot]
    change (((A⁻¹).val l k
      (⟨(deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x).val.toMul,
        hroot⟩ : DeningerPrimeArithmeticRoots p l.1 k) :
          DeningerPrimeArithmeticRoots p l.1 k) :
        (DeningerPrimeArithmeticClosure p)ˣ) = x.val.toMul
    rw [hzin]
    simp [l, z]

  right_inv x := by
    let l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
      ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩
    obtain ⟨k, hx⟩ := deningerPrimeMulAut_primary_exists_primePowerOrder p P x
    let z : DeningerPrimeArithmeticRoots p l.1 k := ⟨x.val.toMul, hx⟩
    have hAx :
        (deningerPrimeMulAut_compatibleTowerPrimaryApply p A⁻¹ P haway x).val.toMul =
          (((A⁻¹).val l k z : DeningerPrimeArithmeticRoots p l.1 k) :
            (DeningerPrimeArithmeticClosure p)ˣ) :=
      deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A⁻¹ P haway x k hx
    have hroot :
        (deningerPrimeMulAut_compatibleTowerPrimaryApply p A⁻¹ P haway x).val.toMul ^
          (l.1 : ℕ) ^ k = 1 := by
      rw [hAx]
      exact ((A⁻¹).val l k z).property
    have hzin :
        (⟨(deningerPrimeMulAut_compatibleTowerPrimaryApply p A⁻¹ P haway x).val.toMul,
            hroot⟩ :
          DeningerPrimeArithmeticRoots p l.1 k) = (A⁻¹).val l k z := by
      apply Subtype.ext
      exact hAx
    apply Subtype.ext
    apply_fun Additive.toMul
    change
      (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway
        (deningerPrimeMulAut_compatibleTowerPrimaryApply p A⁻¹ P haway x)).val.toMul =
          x.val.toMul
    rw [deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A P haway
      (deningerPrimeMulAut_compatibleTowerPrimaryApply p A⁻¹ P haway x) k hroot]
    change ((A.val l k
      (⟨(deningerPrimeMulAut_compatibleTowerPrimaryApply p A⁻¹ P haway x).val.toMul,
        hroot⟩ : DeningerPrimeArithmeticRoots p l.1 k) :
          DeningerPrimeArithmeticRoots p l.1 k) :
        (DeningerPrimeArithmeticClosure p)ˣ) = x.val.toMul
    rw [hzin]
    simp [l, z]

theorem deningerPrimeMulAut_characteristic_primaryComponent_eq_bot
    (p : Nat.Primes) (P : HeightOneSpectrum ℤ)
    (hp :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 = (p : ℕ)) :
    Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  let xp : Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal := ⟨x, hx⟩
  obtain ⟨k, hk⟩ := deningerPrimeMulAut_primary_exists_primePowerOrder p P xp
  have hk' : x.toMul ^ (p : ℕ) ^ k = 1 := by
    simpa [hp] using hk
  have hxone : x.toMul = 1 := by
    have hmem :
        x.toMul ∈ rootsOfUnity 1 (DeningerPrimeArithmeticClosure p) := by
      exact (mem_rootsOfUnity_prime_pow_mul_iff'
        (R := DeningerPrimeArithmeticClosure p) (p : ℕ) k 1).mp (by
          simpa using hk')
    simpa [mem_rootsOfUnity] using hmem
  apply_fun Additive.toMul
  simpa using hxone

noncomputable def deningerPrimeMulAut_compatibleTowerPrimaryLinearEquiv
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (P : HeightOneSpectrum ℤ) :
    Ideal.primaryComponent
        (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal ≃ₗ[ℤ]
      Ideal.primaryComponent
        (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal :=
  if haway :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ) then
    (deningerPrimeMulAut_compatibleTowerPrimaryAddEquiv p A P haway).toIntLinearEquiv
  else
    LinearEquiv.refl ℤ _

noncomputable def deningerPrimeMulAut_compatibleTowerAdditiveLinearEquiv
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p) :
    Additive (DeningerPrimeArithmeticClosure p)ˣ ≃ₗ[ℤ]
      Additive (DeningerPrimeArithmeticClosure p)ˣ :=
  (deningerPrimeMulAut_primaryDecomposition p).symm |>.trans <|
    (DFinsupp.mapRange.linearEquiv
      (deningerPrimeMulAut_compatibleTowerPrimaryLinearEquiv p A)).trans
        (deningerPrimeMulAut_primaryDecomposition p)

noncomputable def deningerPrimeMulAut_compatibleTowerMulAut
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p) :
    MulAut (DeningerPrimeArithmeticClosure p)ˣ :=
  MulEquiv.toAdditive.symm
    (deningerPrimeMulAut_compatibleTowerAdditiveLinearEquiv p A).toAddEquiv

theorem deningerPrimeMulAut_compatibleTowerAdditiveLinearEquiv_apply_primary
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (P : HeightOneSpectrum ℤ)
    (haway :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ))
    (x : Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal) :
    deningerPrimeMulAut_compatibleTowerAdditiveLinearEquiv p A x.val =
      (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x).val := by
  classical
  let E := deningerPrimeMulAut_primaryDecomposition p
  have hsymm : E.symm x.val = DFinsupp.single P x := by
    exact Ideal.iSupIndep_primaryComponent
      ℤ (Additive (DeningerPrimeArithmeticClosure p)ˣ)
      |>.linearEquiv_symm_apply
        (Ideal.iSup_primaryComponent_eq_top
          (deningerPrimeMulAut_prime_arithmetic_additive_isTorsion p)) x.prop
  change E
      (DFinsupp.mapRange.linearEquiv
        (deningerPrimeMulAut_compatibleTowerPrimaryLinearEquiv p A) (E.symm x.val)) =
    (deningerPrimeMulAut_compatibleTowerPrimaryApply p A P haway x).val
  rw [hsymm]
  simp [E, deningerPrimeMulAut_primaryDecomposition,
    deningerPrimeMulAut_compatibleTowerPrimaryLinearEquiv, haway]
  rfl

abbrev DeningerPrimeArithmeticMulAut (p : Nat.Primes) :=
  MulAut (DeningerPrimeArithmeticClosure p)ˣ

def deningerPrimeArithmeticMulAutRestrictRoots
    (p : Nat.Primes) (f : DeningerPrimeArithmeticMulAut p)
    (l : Nat.Primes) (k : ℕ) :
    MulAut (DeningerPrimeArithmeticRoots p l k) where
  toFun z := ⟨f z.val, by
    rw [mem_rootsOfUnity, ← map_pow, z.property, map_one]⟩
  invFun z := ⟨f.symm z.val, by
    rw [mem_rootsOfUnity, ← map_pow, z.property, map_one]⟩
  left_inv z := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul f x.val y.val

noncomputable def deningerPrimeArithmeticMulAutTowerRestriction
    (p : Nat.Primes) :
    DeningerPrimeArithmeticMulAut p →*
      DeningerPrimeCompatibleCyclotomicTowerAut p where
  toFun f := ⟨fun l k =>
    deningerPrimeArithmeticMulAutRestrictRoots p f l.1 k, by
      intro l k z
      apply Subtype.ext
      rfl⟩
  map_one' := by
    apply Subtype.ext
    funext l k
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    rfl
  map_mul' f g := by
    apply Subtype.ext
    funext l k
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    rfl

theorem deningerPrimeArithmeticMulAutTowerRestriction_compatibleTowerMulAut_stage
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p)
    (P : HeightOneSpectrum ℤ)
    (haway :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ))
    (k : ℕ)
    (z : DeningerPrimeArithmeticRoots p
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P) k) :
    (deningerPrimeArithmeticMulAutTowerRestriction p
        (deningerPrimeMulAut_compatibleTowerMulAut p A)).val
          ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩ k z =
      A.val ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩ k z := by
  apply Subtype.ext
  let lAway :
      {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
    ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩
  let xa : Additive (DeningerPrimeArithmeticClosure p)ˣ :=
    Additive.ofMul z.val
  have hxpow :
      xa.toMul ^
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ^ k) = 1 := by
    exact z.property
  let x : Ideal.primaryComponent
      (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal :=
    ⟨xa, deningerPrimeMulAut_primePowerOrder_mem_primary p P xa k hxpow⟩
  have hglobal :=
    deningerPrimeMulAut_compatibleTowerAdditiveLinearEquiv_apply_primary p A P haway x
  have hstage :=
    deningerPrimeMulAut_compatibleTowerPrimaryApply_spec p A P haway x k hxpow
  change Additive.toMul
      (deningerPrimeMulAut_compatibleTowerAdditiveLinearEquiv p A xa) =
    ((A.val lAway k z :
        DeningerPrimeArithmeticRoots p lAway.1 k) :
      (DeningerPrimeArithmeticClosure p)ˣ)
  rw [show xa = x.val by rfl, hglobal]
  have hz :
      (⟨x.val.toMul, hxpow⟩ :
        DeningerPrimeArithmeticRoots p lAway.1 k) = z := by
    apply Subtype.ext
    rfl
  rw [hz] at hstage
  exact hstage

theorem deningerPrimeArithmeticMulAutTowerRestriction_rightInverse
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p) :
    deningerPrimeArithmeticMulAutTowerRestriction p
        (deningerPrimeMulAut_compatibleTowerMulAut p A) = A := by
  apply Subtype.ext
  funext l
  let P : HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm l.1
  have haway :
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ) := by
    simpa [P] using l.2
  let lP : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
    ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩
  have hat :
      (deningerPrimeArithmeticMulAutTowerRestriction p
          (deningerPrimeMulAut_compatibleTowerMulAut p A)).val lP =
        A.val lP := by
    funext k
    apply MulEquiv.ext
    intro z
    exact
      deningerPrimeArithmeticMulAutTowerRestriction_compatibleTowerMulAut_stage
        p A P haway k z
  have hP :
      Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P = l.1 := by
    simp [P]
  have hl : lP = l := by
    apply Subtype.ext
    exact hP
  exact hl ▸ hat

theorem deningerPrimeArithmeticMulAutTowerRestriction_injective
    (p : Nat.Primes) :
    Function.Injective (deningerPrimeArithmeticMulAutTowerRestriction p) := by
  intro f g hfg
  apply MulEquiv.ext
  intro x
  let F :
      Additive (DeningerPrimeArithmeticClosure p)ˣ ≃ₗ[ℤ]
        Additive (DeningerPrimeArithmeticClosure p)ˣ :=
    (MulEquiv.toAdditive f).toIntLinearEquiv
  let G :
      Additive (DeningerPrimeArithmeticClosure p)ˣ ≃ₗ[ℤ]
        Additive (DeningerPrimeArithmeticClosure p)ˣ :=
    (MulEquiv.toAdditive g).toIntLinearEquiv
  have hprimary :
      ∀ P : HeightOneSpectrum ℤ,
        Ideal.primaryComponent
            (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal ≤
          LinearMap.ker (F.toLinearMap - G.toLinearMap) := by
    intro P y hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    by_cases haway :
        (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 ≠ (p : ℕ)
    · let yp : Ideal.primaryComponent
          (Additive (DeningerPrimeArithmeticClosure p)ˣ) P.asIdeal :=
        ⟨y, hy⟩
      obtain ⟨k, hk⟩ := deningerPrimeMulAut_primary_exists_primePowerOrder p P yp
      let l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
        ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P, haway⟩
      let z : DeningerPrimeArithmeticRoots p l.1 k :=
        ⟨yp.val.toMul, hk⟩
      have hval :
          (deningerPrimeArithmeticMulAutTowerRestriction p f).val =
            (deningerPrimeArithmeticMulAutTowerRestriction p g).val :=
        congrArg Subtype.val hfg
      have hstage :
          (deningerPrimeArithmeticMulAutTowerRestriction p f).val l k =
            (deningerPrimeArithmeticMulAutTowerRestriction p g).val l k :=
        congrArg (fun T => T l k) hval
      have hz :=
        DFunLike.congr_fun hstage z
      have hunder :
          f yp.val.toMul = g yp.val.toMul :=
        congrArg Subtype.val hz
      exact congrArg Additive.ofMul hunder
    · have hp :
          (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) P).1 = (p : ℕ) :=
        not_ne_iff.mp haway
      have hbot := deningerPrimeMulAut_characteristic_primaryComponent_eq_bot p P hp
      have hyzero : y = 0 := by
        have hybot :
            y ∈ (⊥ : Submodule ℤ
              (Additive (DeningerPrimeArithmeticClosure p)ˣ)) := by
          rw [← hbot]
          exact hy
        simpa using hybot
      rw [hyzero]
      simp
  have htop :
      (⊤ : Submodule ℤ
          (Additive (DeningerPrimeArithmeticClosure p)ˣ)) ≤
        LinearMap.ker (F.toLinearMap - G.toLinearMap) := by
    rw [← Ideal.iSup_primaryComponent_eq_top
      (deningerPrimeMulAut_prime_arithmetic_additive_isTorsion p)]
    exact iSup_le hprimary
  have hxmem :
      Additive.ofMul x ∈
        LinearMap.ker (F.toLinearMap - G.toLinearMap) :=
    htop trivial
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hxmem
  exact congrArg Additive.toMul hxmem

theorem deningerPrimeArithmeticMulAutTowerRestriction_surjective
    (p : Nat.Primes) :
    Function.Surjective (deningerPrimeArithmeticMulAutTowerRestriction p) := by
  intro A
  exact ⟨deningerPrimeMulAut_compatibleTowerMulAut p A,
    deningerPrimeArithmeticMulAutTowerRestriction_rightInverse p A⟩

/-- Full multiplicative automorphisms of the algebraic closure units are exactly compatible
automorphisms of every away-prime-power cyclotomic tower. -/
noncomputable def deningerPrimeArithmeticMulAutCompatibleTowerMulEquiv
    (p : Nat.Primes) :
    DeningerPrimeArithmeticMulAut p ≃*
      DeningerPrimeCompatibleCyclotomicTowerAut p :=
  MulEquiv.ofBijective (deningerPrimeArithmeticMulAutTowerRestriction p)
    ⟨deningerPrimeArithmeticMulAutTowerRestriction_injective p,
      deningerPrimeArithmeticMulAutTowerRestriction_surjective p⟩

/-- Packet units are the full multiplicative automorphism group of the algebraic closure units. -/
noncomputable def deningerPrimePacketArithmeticMulAutMulEquiv
    (p : Nat.Primes) :
    DeningerPacketUnits p ≃* DeningerPrimeArithmeticMulAut p :=
  (deningerPrimePacketCompatibleCyclotomicTowerMulEquiv p).trans
    (deningerPrimeArithmeticMulAutCompatibleTowerMulEquiv p).symm

theorem deningerPrimePacketArithmeticMulAutMulEquiv_restriction
    (p : Nat.Primes) (u : DeningerPacketUnits p) :
    deningerPrimeArithmeticMulAutTowerRestriction p
        (deningerPrimePacketArithmeticMulAutMulEquiv p u) =
      deningerPrimePacketCompatibleCyclotomicTowerAction p u := by
  change deningerPrimeArithmeticMulAutCompatibleTowerMulEquiv p
      (deningerPrimePacketArithmeticMulAutMulEquiv p u) =
    deningerPrimePacketCompatibleCyclotomicTowerMulEquiv p u
  simp [deningerPrimePacketArithmeticMulAutMulEquiv]

/-- Arithmetic Frobenius restricted to the multiplicative group. -/
noncomputable def deningerPrimeArithmeticFrobeniusMulAut
    (p : Nat.Primes) :
    DeningerPrimeArithmeticMulAut p :=
  Units.mapEquiv
    (deningerPrimeArithmeticFrobenius p).toRingEquiv.toMulEquiv

theorem deningerPrimeArithmeticFrobeniusMulAut_apply
    (p : Nat.Primes) (x : (DeningerPrimeArithmeticClosure p)ˣ) :
    deningerPrimeArithmeticFrobeniusMulAut p x = x ^ (p : ℕ) := by
  apply Units.ext
  change deningerPrimeArithmeticFrobenius p
      (x : DeningerPrimeArithmeticClosure p) =
    (x : DeningerPrimeArithmeticClosure p) ^ (p : ℕ)
  change
    (x : DeningerPrimeArithmeticClosure p) ^
        Fintype.card (ZMod (p : ℕ)) =
      (x : DeningerPrimeArithmeticClosure p) ^ (p : ℕ)
  rw [ZMod.card]

theorem deningerPrimePacketArithmeticMulAutMulEquiv_frobenius
    (p : Nat.Primes) :
    deningerPrimePacketArithmeticMulAutMulEquiv p
        (deningerPacketFrobeniusUnit p) =
      deningerPrimeArithmeticFrobeniusMulAut p := by
  apply deningerPrimeArithmeticMulAutTowerRestriction_injective p
  apply Subtype.ext
  funext l k
  apply MulEquiv.ext
  intro z
  calc
    (deningerPrimeArithmeticMulAutTowerRestriction p
        (deningerPrimePacketArithmeticMulAutMulEquiv p
          (deningerPacketFrobeniusUnit p))).val l k z =
        (deningerPrimePacketCompatibleCyclotomicTowerAction p
          (deningerPacketFrobeniusUnit p)).val l k z := by
      have h := deningerPrimePacketArithmeticMulAutMulEquiv_restriction p
        (deningerPacketFrobeniusUnit p)
      exact DFunLike.congr_fun
        (congrArg (fun T => T l k) (congrArg Subtype.val h)) z
    _ = z ^ (p : ℕ) :=
      deningerPrimePacketCompatibleCyclotomicTowerAction_frobenius p l k z
    _ = (deningerPrimeArithmeticMulAutTowerRestriction p
        (deningerPrimeArithmeticFrobeniusMulAut p)).val l k z := by
      apply Subtype.ext
      exact (deningerPrimeArithmeticFrobeniusMulAut_apply p z.val).symm

theorem deningerPrimePacketArithmeticMulAutMulEquiv_frobenius_apply
    (p : Nat.Primes) (x : (DeningerPrimeArithmeticClosure p)ˣ) :
    deningerPrimePacketArithmeticMulAutMulEquiv p
        (deningerPacketFrobeniusUnit p) x =
      x ^ (p : ℕ) := by
  rw [deningerPrimePacketArithmeticMulAutMulEquiv_frobenius,
    deningerPrimeArithmeticFrobeniusMulAut_apply]

end

end RHTower
