import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticFiniteResidueEndpoint
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# The `S`-unit valuation isomorphism and the finite-prime endpoint page

For a finite set `S` of primes the positive `S`-units are the positive rationals whose `p`-adic
valuation vanishes at every prime outside `S`.  Unique factorization says exactly that the
valuation coordinates identify this group with the free abelian group on `S`: the coordinates of a
product of prime powers are its exponents, and a positive rational all of whose valuations vanish
is `1`.  After extension of scalars the valuation map becomes a linear isomorphism
`ℝ ⊗ U_S ≅ ℝ^S`, which is the residue coordinate map of the finite-prime endpoint page; its three
cohomology groups are then the constants, zero, and the orientation line.

The identification is natural for `S ⊆ S'`: on `S`-units the larger coordinate system is the
extension by zero of the smaller one.

* `deningerSUnits` : the group of positive `S`-units.
* `deningerSOrd_product`, `deningerSUnits_eq_of_ord_eq` : unique factorization in coordinates.
* `deningerSUnitsEquiv` : `U_S ≅ ⨁_{p ∈ S} ℤ`.
* `deningerSResidueEquiv` : the linear isomorphism `ℝ ⊗ U_S ≅ ℝ^S`.
* `deningerSEndpoint_H0`, `deningerSEndpoint_H1`, `deningerSEndpoint_H2` : the endpoint page.
* `deningerSOrd_extension` : naturality under `S ⊆ S'`.
-/

namespace RHTower

open scoped TensorProduct

section SUnits

/-- The rational unit attached to a prime. -/
noncomputable def deningerPrimeUnit (p : Nat.Primes) : ℚˣ :=
  Units.mk0 ((p : ℕ) : ℚ) (by
    have hp : 0 < (p : ℕ) := (p.2).pos
    exact_mod_cast hp.ne')

theorem deningerPrimeUnit_val (p : Nat.Primes) :
    ((deningerPrimeUnit p : ℚˣ) : ℚ) = ((p : ℕ) : ℚ) := rfl

/-- The valuation of one prime at another: `1` on the diagonal, `0` off it. -/
theorem deningerPadicValRat_primeUnit (q p : Nat.Primes) :
    padicValRat (q : ℕ) ((deningerPrimeUnit p : ℚˣ) : ℚ) = if p = q then 1 else 0 := by
  haveI : Fact ((q : ℕ)).Prime := ⟨q.2⟩
  rw [deningerPrimeUnit_val]
  by_cases h : p = q
  · subst h
    rw [if_pos rfl, padicValRat.self (p.2).one_lt]
  · rw [if_neg h, padicValRat.of_nat]
    have hnd : ¬ ((q : ℕ) ∣ (p : ℕ)) := by
      intro hdvd
      exact h (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hdvd).symm)
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    rfl

/-- The valuation of a finite product of rational units is the sum of the valuations. -/
theorem deningerPadicValRat_prod {q : ℕ} [Fact q.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚˣ) :
    padicValRat q ((∏ i ∈ s, f i : ℚˣ) : ℚ) = ∑ i ∈ s, padicValRat q ((f i : ℚˣ) : ℚ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Units.val_mul,
      padicValRat.mul (Units.ne_zero _) (Units.ne_zero _), ih]

/-- **A positive rational with trivial valuations is `1`.**  Its numerator and denominator are
coprime, so no prime divides either. -/
theorem deningerRat_eq_one_of_valuations {x : ℚ} (hx : 0 < x)
    (h : ∀ p : Nat.Primes, padicValRat (p : ℕ) x = 0) : x = 1 := by
  have hnum : 0 < x.num := Rat.num_pos.mpr hx
  have ha : x.num.natAbs ≠ 0 := by
    intro hcon
    rw [Int.natAbs_eq_zero] at hcon
    omega
  have hb : x.den ≠ 0 := x.den_nz
  have hcop : Nat.Coprime x.num.natAbs x.den := x.reduced
  have hval : ∀ p : Nat.Primes,
      (padicValNat (p : ℕ) x.num.natAbs : ℤ) - (padicValNat (p : ℕ) x.den : ℤ) = 0 := by
    intro p
    have := h p
    simpa [padicValRat, padicValInt] using this
  have hnodvd : ∀ p : Nat.Primes, ¬ ((p : ℕ) ∣ x.num.natAbs) ∧ ¬ ((p : ℕ) ∣ x.den) := by
    intro p
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    constructor
    · intro hdvd
      have h1 : 1 ≤ padicValNat (p : ℕ) x.num.natAbs := one_le_padicValNat_of_dvd ha hdvd
      have h2 : ¬ ((p : ℕ) ∣ x.den) := fun hdvd' =>
        Nat.Prime.one_lt p.2 |>.ne' (Nat.eq_one_of_dvd_coprimes hcop hdvd hdvd')
      have h3 : padicValNat (p : ℕ) x.den = 0 := padicValNat.eq_zero_of_not_dvd h2
      have := hval p
      rw [h3] at this
      omega
    · intro hdvd
      have h1 : 1 ≤ padicValNat (p : ℕ) x.den := one_le_padicValNat_of_dvd hb hdvd
      have h2 : ¬ ((p : ℕ) ∣ x.num.natAbs) := fun hdvd' =>
        Nat.Prime.one_lt p.2 |>.ne' (Nat.eq_one_of_dvd_coprimes hcop hdvd' hdvd)
      have h3 : padicValNat (p : ℕ) x.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd h2
      have := hval p
      rw [h3] at this
      omega
  have hnum1 : x.num.natAbs = 1 := by
    refine Nat.eq_one_iff_not_exists_prime_dvd.mpr ?_
    intro p hp hdvd
    exact (hnodvd ⟨p, hp⟩).1 hdvd
  have hden1 : x.den = 1 := by
    refine Nat.eq_one_iff_not_exists_prime_dvd.mpr ?_
    intro p hp hdvd
    exact (hnodvd ⟨p, hp⟩).2 hdvd
  have hnum' : x.num = 1 := by
    rcases Int.natAbs_eq x.num with h' | h'
    · rw [h', hnum1]
      rfl
    · omega
  refine Rat.ext ?_ ?_
  · rw [hnum']
    rfl
  · rw [hden1]
    rfl

/-- The group of positive `S`-units: positive rationals whose valuation vanishes outside `S`. -/
def deningerSUnits (S : Finset Nat.Primes) : Subgroup ℚˣ where
  carrier := {u : ℚˣ | 0 < (u : ℚ) ∧ ∀ p : Nat.Primes, p ∉ S → padicValRat (p : ℕ) (u : ℚ) = 0}
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨by rw [Units.val_mul]; exact mul_pos hu hv, fun p hp => ?_⟩
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_mul, padicValRat.mul (Units.ne_zero _) (Units.ne_zero _), hu' p hp, hv' p hp,
      add_zero]
  one_mem' := by
    refine ⟨by norm_num, fun p _ => ?_⟩
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    rw [Units.val_one, padicValRat.one]
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨?_, fun p hp => ?_⟩
    · rw [Units.val_inv_eq_inv_val]
      exact inv_pos.mpr hu
    · haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
      rw [Units.val_inv_eq_inv_val, padicValRat.inv, hu' p hp, neg_zero]

theorem deningerSUnits_pos {S : Finset Nat.Primes} {u : ℚˣ} (hu : u ∈ deningerSUnits S) :
    0 < (u : ℚ) := hu.1

theorem deningerSUnits_val_outside {S : Finset Nat.Primes} {u : ℚˣ} (hu : u ∈ deningerSUnits S)
    (p : Nat.Primes) (hp : p ∉ S) : padicValRat (p : ℕ) (u : ℚ) = 0 := hu.2 p hp

/-- The valuation coordinates of a rational unit along `S`. -/
def deningerSOrd (S : Finset Nat.Primes) (u : ℚˣ) (p : {x : Nat.Primes // x ∈ S}) : ℤ :=
  padicValRat ((p : Nat.Primes) : ℕ) (u : ℚ)

/-- The `S`-unit with prescribed exponents. -/
noncomputable def deningerSUnitProduct (S : Finset Nat.Primes)
    (n : {x : Nat.Primes // x ∈ S} → ℤ) : ℚˣ :=
  ∏ p : {x : Nat.Primes // x ∈ S}, deningerPrimeUnit (p : Nat.Primes) ^ n p

/-- **The valuation of a prescribed product** is its exponent inside `S` and zero outside. -/
theorem deningerSUnitProduct_val (S : Finset Nat.Primes) (n : {x : Nat.Primes // x ∈ S} → ℤ)
    (q : Nat.Primes) :
    padicValRat (q : ℕ) ((deningerSUnitProduct S n : ℚˣ) : ℚ)
      = if hq : q ∈ S then n ⟨q, hq⟩ else 0 := by
  classical
  haveI : Fact ((q : ℕ)).Prime := ⟨q.2⟩
  rw [deningerSUnitProduct, deningerPadicValRat_prod]
  have hterm : ∀ p : {x : Nat.Primes // x ∈ S},
      padicValRat (q : ℕ) (((deningerPrimeUnit (p : Nat.Primes) ^ n p : ℚˣ) : ℚ))
        = if (p : Nat.Primes) = q then n p else 0 := by
    intro p
    rw [Units.val_zpow_eq_zpow_val, padicValRat.zpow, deningerPadicValRat_primeUnit]
    by_cases h : (p : Nat.Primes) = q
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun p _ => hterm p]
  by_cases hq : q ∈ S
  · rw [dif_pos hq]
    rw [Finset.sum_eq_single (⟨q, hq⟩ : {x : Nat.Primes // x ∈ S})]
    · rw [if_pos rfl]
    · intro p _ hne
      refine if_neg fun h => hne ?_
      exact Subtype.ext h
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · rw [dif_neg hq]
    refine Finset.sum_eq_zero fun p _ => ?_
    refine if_neg fun h => hq ?_
    rw [← h]
    exact p.2

/-- The prescribed product is an `S`-unit. -/
theorem deningerSUnitProduct_mem (S : Finset Nat.Primes) (n : {x : Nat.Primes // x ∈ S} → ℤ) :
    deningerSUnitProduct S n ∈ deningerSUnits S := by
  refine ⟨?_, fun p hp => ?_⟩
  · classical
    have hpos : ∀ s : Finset {x : Nat.Primes // x ∈ S},
        0 < ((∏ p ∈ s, deningerPrimeUnit p.1 ^ n p : ℚˣ) : ℚ) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Units.val_mul]
        refine mul_pos ?_ ih
        rw [Units.val_zpow_eq_zpow_val, deningerPrimeUnit_val]
        exact zpow_pos (by exact_mod_cast a.1.2.pos) _
    exact hpos Finset.univ
  · rw [deningerSUnitProduct_val S n p, dif_neg hp]

/-- **Unique factorization in coordinates**: the exponents of a prescribed product are recovered by
its valuations. -/
theorem deningerSOrd_product (S : Finset Nat.Primes) (n : {x : Nat.Primes // x ∈ S} → ℤ) :
    deningerSOrd S (deningerSUnitProduct S n) = n := by
  funext p
  rw [deningerSOrd, deningerSUnitProduct_val S n (p : Nat.Primes), dif_pos p.2]

/-- **`S`-units are determined by their valuation coordinates.** -/
theorem deningerSUnits_eq_of_ord_eq {S : Finset Nat.Primes} {u v : ℚˣ}
    (hu : u ∈ deningerSUnits S) (hv : v ∈ deningerSUnits S)
    (h : deningerSOrd S u = deningerSOrd S v) : u = v := by
  have hw : ((u * v⁻¹ : ℚˣ) : ℚ) = 1 := by
    refine deningerRat_eq_one_of_valuations ?_ ?_
    · rw [Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos hu.1 (inv_pos.mpr hv.1)
    · intro p
      haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
      rw [Units.val_mul, Units.val_inv_eq_inv_val,
        padicValRat.mul (Units.ne_zero _) (by simp),
        padicValRat.inv]
      by_cases hp : p ∈ S
      · have := congrFun h ⟨p, hp⟩
        rw [deningerSOrd, deningerSOrd] at this
        rw [this, add_neg_cancel]
      · rw [hu.2 p hp, hv.2 p hp, neg_zero, add_zero]
  have hw' : (u * v⁻¹ : ℚˣ) = 1 := Units.ext hw
  calc u = u * v⁻¹ * v := by rw [inv_mul_cancel_right]
    _ = v := by rw [hw', one_mul]

/-- **The valuation isomorphism.**  The positive `S`-units are the free abelian group on `S`. -/
noncomputable def deningerSUnitsEquiv (S : Finset Nat.Primes) :
    Additive ↥(deningerSUnits S) ≃+ ({x : Nat.Primes // x ∈ S} → ℤ) :=
  AddEquiv.mk'
    { toFun := fun u => deningerSOrd S ((Additive.toMul u : ↥(deningerSUnits S)) : ℚˣ)
      invFun := fun n =>
        Additive.ofMul (⟨deningerSUnitProduct S n, deningerSUnitProduct_mem S n⟩ :
          ↥(deningerSUnits S))
      left_inv := by
        intro u
        refine Additive.toMul.injective ?_
        refine Subtype.ext ?_
        refine deningerSUnits_eq_of_ord_eq (deningerSUnitProduct_mem S _)
          (Additive.toMul u).2 ?_
        exact deningerSOrd_product S _
      right_inv := by
        intro n
        exact deningerSOrd_product S n }
    (by
      intro u v
      funext p
      haveI : Fact (((p : Nat.Primes) : ℕ)).Prime := ⟨(p : Nat.Primes).2⟩
      show padicValRat _ (((Additive.toMul (u + v) : ↥(deningerSUnits S)) : ℚˣ) : ℚ) = _
      show padicValRat _ ((((Additive.toMul u : ↥(deningerSUnits S)) *
        (Additive.toMul v : ↥(deningerSUnits S)) : ↥(deningerSUnits S)) : ℚˣ) : ℚ) = _
      rw [Subgroup.coe_mul, Units.val_mul,
        padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]
      rfl)

end SUnits

section EndpointPage

/-- The real `S`-unit space `U_S = ℝ ⊗ (ℤ[S^{-1}]^× / ±1)`. -/
noncomputable abbrev deningerSUnitSpace (S : Finset Nat.Primes) : Type :=
  ℝ ⊗[ℤ] Additive ↥(deningerSUnits S)

/-- **The residue coordinate isomorphism.**  Extension of scalars turns the valuation isomorphism
into a linear isomorphism onto the residue coordinates `ℝ^S`. -/
noncomputable def deningerSResidueEquiv (S : Finset Nat.Primes) :
    deningerSUnitSpace S ≃ₗ[ℝ] ({x : Nat.Primes // x ∈ S} → ℝ) :=
  (LinearEquiv.baseChange ℤ ℝ _ _ (deningerSUnitsEquiv S).toIntLinearEquiv).trans
    (TensorProduct.piScalarRight ℤ ℝ ℝ {x : Nat.Primes // x ∈ S})

variable (Orientation : Type) [AddCommGroup Orientation] [Module ℝ Orientation]

/-- The finite-prime endpoint page of `S`. -/
noncomputable def deningerSEndpointComplex (S : Finset Nat.Primes) :
    DeningerArithmeticThreeTermComplex ℝ ℝ (deningerSUnitSpace S)
      (({x : Nat.Primes // x ∈ S} → ℝ) × Orientation) :=
  deningerFiniteResidueEndpointComplex (Orientation := Orientation) (deningerSResidueEquiv S)

/-- **Degree zero of the endpoint page is the constant line.** -/
noncomputable def deningerSEndpoint_H0 (S : Finset Nat.Primes) :
    (deningerSEndpointComplex Orientation S).H0 ≃ₗ[ℝ] ℝ :=
  deningerFiniteResidueEndpointComplex.H0Equiv (Orientation := Orientation)
    (deningerSResidueEquiv S)

/-- **Degree one of the endpoint page vanishes.** -/
theorem deningerSEndpoint_H1 (S : Finset Nat.Primes)
    (x : (deningerSEndpointComplex Orientation S).H1) : x = 0 :=
  deningerFiniteResidueEndpointComplex.H1_eq_zero (Orientation := Orientation)
    (deningerSResidueEquiv S) x

/-- **Degree two of the endpoint page is the orientation line**, by projection. -/
noncomputable def deningerSEndpoint_H2 (S : Finset Nat.Primes) :
    (deningerSEndpointComplex Orientation S).H2 ≃ₗ[ℝ] Orientation :=
  deningerFiniteResidueEndpointComplex.H2Equiv (Orientation := Orientation)
    (deningerSResidueEquiv S)

end EndpointPage

section Naturality

/-- The `S`-units of a smaller set are `S'`-units. -/
theorem deningerSUnits_mono {S S' : Finset Nat.Primes} (h : S ⊆ S') :
    deningerSUnits S ≤ deningerSUnits S' := by
  rintro u ⟨hu, hu'⟩
  exact ⟨hu, fun p hp => hu' p fun hcon => hp (h hcon)⟩

/-- **Naturality of the valuation coordinates.**  On `S`-units the coordinates of the larger set
are the extension by zero of the coordinates of the smaller one. -/
theorem deningerSOrd_extension {S S' : Finset Nat.Primes} {u : ℚˣ} (hu : u ∈ deningerSUnits S)
    (p : {x : Nat.Primes // x ∈ S'}) :
    deningerSOrd S' u p
      = if hp : (p : Nat.Primes) ∈ S then deningerSOrd S u ⟨(p : Nat.Primes), hp⟩ else 0 := by
  by_cases hp : (p : Nat.Primes) ∈ S
  · rw [dif_pos hp]
    rfl
  · rw [dif_neg hp, deningerSOrd]
    exact hu.2 (p : Nat.Primes) hp

/-- The prescribed product is natural for extension by zero of exponents. -/
theorem deningerSUnitProduct_extension {S S' : Finset Nat.Primes} (h : S ⊆ S')
    (n : {x : Nat.Primes // x ∈ S} → ℤ) :
    deningerSUnitProduct S' (fun p => if hp : (p : Nat.Primes) ∈ S then n ⟨_, hp⟩ else 0)
      = deningerSUnitProduct S n := by
  refine deningerSUnits_eq_of_ord_eq (S := S') (deningerSUnitProduct_mem S' _)
    (deningerSUnits_mono h (deningerSUnitProduct_mem S n)) ?_
  funext p
  show padicValRat _ _ = padicValRat _ _
  rw [deningerSUnitProduct_val S' _ (p : Nat.Primes), deningerSUnitProduct_val S n
    (p : Nat.Primes), dif_pos p.2]

end Naturality

end RHTower
