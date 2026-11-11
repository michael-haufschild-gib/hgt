import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCubicCharacterOfTwoIsARayClassCharacterModuloSix
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheZerosOfAHeckeLFunctionSatisfyWeilsExplicitFormula
import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheThirdCyclotomicFieldContainsZeta

/-!
# The degree-two character of the cube roots of two has its Hodge index

The splitting field `L = ℚ(∛2, ω)` of `X³ − 2` has Galois group `S₃`. Its permutation
representation on the three roots is `1 ⊕ ρ` with `ρ` irreducible of degree two, and `Frob_p^m`
fixes exactly the roots lying in `𝔽_{p^m}`. So the contacts of `ρ` are point counts:

  `Λ_ρ(p^m) = (#{x ∈ 𝔽_{p^m} : x³ = 2} − 1) log p`  (`artinCubeContact`),

uniformly in `p`, the ramified primes `2`, `3` included (there both sides vanish).

* **Reciprocity** (`heckeMangoldt_cubicTwoHecke`). `Λ_ρ` is the von Mangoldt function of the
  cubic character `χ` of `2` over `ℚ(ω)`, a primitive ray class character modulo `6`
  (`cubicTwoHecke`). At an inert `p ≡ 2 (3)`, cubing is bijective on `𝔽_{p^m}` for odd `m` and
  `2` is a cube for even `m`. At a split `p = 𝔭𝔭̄`, `2` is a cube in `𝔽_{p^m}` iff `χ(𝔭)^m = 1`
  (Euler's criterion and cubic reciprocity), and `χ(𝔭)χ(𝔭̄) = χ((p)) = 1`.
* **Weil's explicit formula for `ρ`** (`W_artinZeros_eq`) with these contacts, and
* **the index law for `ρ`** (`exists_le_negIndex_artinGram_iff`,
  `forall_negIndex_artinGram_eq_zero_iff`): Weil's form of `ρ` has `n` negative squares on some
  family of `n` tests iff `L(s, ρ)` has at least `n` distinct zeros right of the critical line.

This is the index law for an Artin character of a non-abelian extension.
-/

noncomputable section

open NumberField Complex

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CubeRootsOfTwo

open MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein HeckeLFunctions

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### Cube roots in a finite field -/

section FiniteField

variable {F : Type*} [Field F] [Fintype F]

/-- If `3 ∤ q − 1`, the only cubic root of unity is `1`. -/
theorem cube_eq_one_of_not_dvd (h : ¬ 3 ∣ Fintype.card F - 1) {z : F} (hz : z ^ 3 = 1) :
    z = 1 := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hg := (pow_gcd_eq_one (a := z)).mpr ⟨hz, FiniteField.pow_card_sub_one_eq_one z hz0⟩
  rwa [(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h, pow_one] at hg

/-- If `3 ∤ q − 1`, every element has exactly one cube root. -/
theorem card_cube_roots_of_not_dvd (h : ¬ 3 ∣ Fintype.card F - 1) (a : F) :
    Nat.card {x : F // x ^ 3 = a} = 1 := by
  have hinj : Function.Injective (fun x : F => x ^ 3) := by
    intro x y hxy
    simp only at hxy
    by_cases hy : y = 0
    · subst hy
      simpa using hxy
    · have h1 : (x / y) ^ 3 = 1 := by rw [div_pow, hxy, div_self (pow_ne_zero 3 hy)]
      exact (div_eq_one_iff_eq hy).mp (cube_eq_one_of_not_dvd h h1)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) a
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun u v => Subtype.ext (hinj (u.2.trans v.2.symm))⟩, ⟨⟨x, hx⟩⟩⟩

variable [DecidableEq F]

/-- **Euler's criterion for cubes.** If `3 ∣ q − 1` and `a ≠ 0`, `x³ = a` has three solutions if
`a^{(q−1)/3} = 1` and none otherwise: cubing maps `Fˣ` onto the kernel of the `(q−1)/3`-th power,
with kernel of order three. -/
theorem card_cube_roots_of_dvd (h : 3 ∣ Fintype.card F - 1) {a : F} (ha : a ≠ 0) :
    Nat.card {x : F // x ^ 3 = a} = if a ^ ((Fintype.card F - 1) / 3) = 1 then 3 else 0 := by
  set q := Fintype.card F
  have hN : Nat.card Fˣ = q - 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_units]
  set m := (q - 1) / 3
  have hm3 : 3 * m = q - 1 := Nat.mul_div_cancel' h
  let a' : Fˣ := Units.mk0 a ha
  have e : {x : F // x ^ 3 = a} ≃ (powMonoidHom 3 : Fˣ →* Fˣ) ⁻¹' {a'} :=
    { toFun := fun x => ⟨Units.mk0 x.1 (fun h0 => ha (by rw [← x.2, h0]; ring)),
        by ext; simp [a', x.2]⟩
      invFun := fun u => ⟨(u.1 : F), by
        have := congrArg Units.val (Set.mem_singleton_iff.mp u.2)
        simpa [a'] using this⟩
      left_inv := fun x => by ext; simp
      right_inv := fun u => by ext; simp }
  rw [Nat.card_congr e]
  split_ifs with hpow
  · have hle : (powMonoidHom 3 : Fˣ →* Fˣ).range ≤ (powMonoidHom m : Fˣ →* Fˣ).ker := by
      rintro _ ⟨u, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul, hm3, ← hN,
        pow_card_eq_one']
    have hgcd3 : (q - 1).gcd 3 = 3 := Nat.gcd_eq_right h
    have hgcdm : (q - 1).gcd m = m := Nat.gcd_eq_right ⟨3, by rw [← hm3]; ring⟩
    have hcard : Nat.card (powMonoidHom m : Fˣ →* Fˣ).ker ≤
        Nat.card (powMonoidHom 3 : Fˣ →* Fˣ).range := by
      rw [IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_range, hN, hgcd3, hgcdm]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    have ha' : a' ∈ (powMonoidHom m : Fˣ →* Fˣ).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      ext
      simpa [a'] using hpow
    rw [← heq] at ha'
    obtain ⟨b, hb⟩ := ha'
    rw [← hb, Nat.card_congr ((powMonoidHom 3 : Fˣ →* Fˣ).fiberEquivKer b),
      IsCyclic.card_powMonoidHom_ker, hN, hgcd3]
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨u, hu⟩
    apply hpow
    have hu' : u ^ 3 = a' := hu
    have : (a' : F) ^ m = 1 := by
      rw [← hu', Units.val_pow_eq_pow_val, ← pow_mul, hm3]
      exact FiniteField.pow_card_sub_one_eq_one _ u.ne_zero
    simpa [a'] using this

end FiniteField

/-! ### The cube roots of two in `𝔽_{p^m}` -/

/-- The number of solutions of `x³ = 2` in the field with `p^m` elements (`0` unless `p` is
prime). -/
def cubeRootsOfTwoCount (p m : ℕ) : ℕ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    Nat.card {x : GaloisField p m // x ^ 3 = 2}
  else 0

theorem cubeRootsOfTwoCount_eq {p : ℕ} [hp : Fact p.Prime] (m : ℕ) :
    cubeRootsOfTwoCount p m = Nat.card {x : GaloisField p m // x ^ 3 = 2} := by
  rw [cubeRootsOfTwoCount, dif_pos hp.out]

theorem fintype_card_galoisField {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m ≠ 0) :
    @Fintype.card (GaloisField p m) (Fintype.ofFinite _) = p ^ m := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p m hm]

/-- In characteristic `2`, `x³ = 2 = 0` has the single root `0`. -/
theorem cubeRootsOfTwoCount_two (m : ℕ) : cubeRootsOfTwoCount 2 m = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [cubeRootsOfTwoCount_eq]
  have h2 : (2 : GaloisField 2 m) = 0 := by
    have := CharP.cast_eq_zero (GaloisField 2 m) 2
    exact_mod_cast this
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun u v => Subtype.ext ?_⟩, ⟨⟨0, by rw [h2]; ring⟩⟩⟩
  have hu := u.2
  have hv := v.2
  rw [h2] at hu hv
  rw [pow_eq_zero_iff (by norm_num)] at hu hv
  rw [hu, hv]

/-- If `3 ∤ p^m − 1`, the equation `x³ = 2` has one root in `𝔽_{p^m}`. -/
theorem cubeRootsOfTwoCount_of_not_dvd {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (h : ¬ 3 ∣ p ^ m - 1) : cubeRootsOfTwoCount p m = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI := Fintype.ofFinite (GaloisField p m)
  rw [cubeRootsOfTwoCount_eq]
  exact card_cube_roots_of_not_dvd (by rwa [fintype_card_galoisField hm]) _

/-- The power `t ↦ 2^t` along `t_j = (p^j − 1)/3` for `p ≡ 1 (3)`: `2^{t_j} = z^j` with
`z = 2^{(p−1)/3}` in the prime field. -/
theorem two_pow_eq_of_mod_three_eq_one {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (m j : ℕ) :
    (2 : GaloisField p m) ^ ((p ^ j - 1) / 3) =
      algebraMap (ZMod p) (GaloisField p m) (((2 : ZMod p) ^ ((p - 1) / 3)) ^ j) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hs : 3 * ((p - 1) / 3) = p - 1 := Nat.mul_div_cancel' (by omega)
  induction j with
  | zero => simp
  | succ j ih =>
    have hpj : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
    have h3 : 3 ∣ p ^ j - 1 := by
      have := Nat.sub_dvd_pow_sub_pow p 1 j
      rw [one_pow] at this
      exact (Nat.dvd_of_mod_eq_zero (by omega : (p - 1) % 3 = 0)).trans this
    have ht : 3 * ((p ^ j - 1) / 3) = p ^ j - 1 := Nat.mul_div_cancel' h3
    have hsplit : (p ^ (j + 1) - 1) / 3 = p * ((p ^ j - 1) / 3) + (p - 1) / 3 := by
      have : p ^ (j + 1) - 1 = 3 * (p * ((p ^ j - 1) / 3) + (p - 1) / 3) := by
        rw [Nat.mul_add, ← mul_assoc, mul_comm 3 p, mul_assoc, ht, hs, pow_succ,
          Nat.mul_sub, mul_one, mul_comm (p ^ j) p]
        have : p ≤ p * p ^ j := Nat.le_mul_of_pos_right p (by omega)
        omega
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hsplit, pow_add, pow_mul, ih, ← map_pow, ZMod.pow_card, pow_succ, map_mul]
    congr 1
    rw [map_pow, map_ofNat]

/-- **Split primes.** For `p ≡ 1 (3)`, `x³ = 2` has three roots in `𝔽_{p^m}` if
`(2^{(p−1)/3})^m = 1` in `𝔽_p`, and none otherwise. -/
theorem cubeRootsOfTwoCount_split {p m : ℕ} [hp : Fact p.Prime] (hp3 : p % 3 = 1) (hm : m ≠ 0) :
    cubeRootsOfTwoCount p m =
      if ((2 : ZMod p) ^ ((p - 1) / 3)) ^ m = 1 then 3 else 0 := by
  classical
  letI := Fintype.ofFinite (GaloisField p m)
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp3
  have h3 : 3 ∣ p ^ m - 1 := by
    have := Nat.sub_dvd_pow_sub_pow p 1 m
    rw [one_pow] at this
    exact (Nat.dvd_of_mod_eq_zero (by omega : (p - 1) % 3 = 0)).trans this
  have h20 : (2 : GaloisField p m) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField p m) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p m) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  rw [cubeRootsOfTwoCount_eq, card_cube_roots_of_dvd (by rwa [fintype_card_galoisField hm]) h20,
    fintype_card_galoisField hm, two_pow_eq_of_mod_three_eq_one hp3 m m,
    ← map_one (algebraMap (ZMod p) (GaloisField p m)),
    (algebraMap (ZMod p) (GaloisField p m)).injective.eq_iff]

/-- **Inert primes.** For `p ≡ 2 (3)`, `p ≠ 2`, and `m` even, `2 ∈ 𝔽_p` is a cube in
`𝔽_{p^m}` and has three cube roots. -/
theorem cubeRootsOfTwoCount_inert_even {p m : ℕ} [hp : Fact p.Prime] (hp3 : p % 3 = 2)
    (hp2 : p ≠ 2) (hm : m ≠ 0) (he : Even m) : cubeRootsOfTwoCount p m = 3 := by
  classical
  letI := Fintype.ofFinite (GaloisField p m)
  obtain ⟨j, rfl⟩ := he
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  -- `3 (p − 1) ∣ p^{2j} − 1`
  have hdvd : 3 * (p - 1) ∣ p ^ (j + j) - 1 := by
    have h1 := Nat.sub_dvd_pow_sub_pow (p ^ 2) 1 j
    rw [one_pow, ← pow_mul] at h1
    have h2 : 3 * (p - 1) ∣ p ^ 2 - 1 := by
      have e : p ^ 2 - 1 = (p - 1) * (p + 1) := by
        rw [sq, Nat.sub_one_mul, Nat.mul_add_one]; omega
      rw [e, mul_comm 3]
      exact Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero (by omega))
    rw [show j + j = 2 * j by ring]
    exact h2.trans h1
  obtain ⟨c, hc⟩ := hdvd
  have h3 : 3 ∣ p ^ (j + j) - 1 := ⟨(p - 1) * c, by rw [hc]; ring⟩
  have h20 : (2 : GaloisField p (j + j)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField p (j + j)) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p (j + j)) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  have hpow : (2 : GaloisField p (j + j)) ^ ((p ^ (j + j) - 1) / 3) = 1 := by
    have e : (p ^ (j + j) - 1) / 3 = (p - 1) * c := by
      rw [hc, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    have hz : (2 : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one (by
        intro h
        have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at h'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h'))
    rw [e, pow_mul, show (2 : GaloisField p (j + j)) = algebraMap (ZMod p) _ 2 from
      (map_ofNat _ 2).symm, ← map_pow, hz, map_one, one_pow]
  rw [cubeRootsOfTwoCount_eq, card_cube_roots_of_dvd (by rwa [fintype_card_galoisField hm]) h20,
    fintype_card_galoisField hm, if_pos hpow]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CubeRootsOfTwo
