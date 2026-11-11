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
open scoped ComplexConjugate

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CubeRootsOfTwo

open MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein HeckeLFunctions
open HTGeometry Zeta23 Zeta23.WeilEF RHTower.WeilLineIntegral GaloisForLFunctions.EntireZeroDivisor

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
  have hu : (u : GaloisField 2 m) ^ 3 = 0 := by rw [u.2, h2]
  have hv : (v : GaloisField 2 m) ^ 3 = 0 := by rw [v.2, h2]
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
    have hsplit : (p ^ (j + 1) - 1) / 3 = ((p ^ j - 1) / 3) * p + (p - 1) / 3 := by
      have : p ^ (j + 1) - 1 = 3 * (p * ((p ^ j - 1) / 3) + (p - 1) / 3) := by
        rw [Nat.mul_add, ← mul_assoc, mul_comm 3 p, mul_assoc, ht, hs, pow_succ,
          Nat.mul_sub, mul_one, mul_comm (p ^ j) p]
        have : p ≤ p * p ^ j := Nat.le_mul_of_pos_right p (by omega)
        omega
      rw [this, Nat.mul_div_cancel_left _ (by norm_num), mul_comm p]
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
  by_cases hc : ((2 : ZMod p) ^ ((p - 1) / 3)) ^ m = 1 <;> simp [hc]

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


/-! ### The primes of `ℤ[ω]` above `p` -/

theorem finrank_O : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank, IsCyclotomicExtension.finrank K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 3)), Nat.totient_prime Nat.prime_three]

/-- `N((n)) = n²`. -/
theorem absNorm_span_natCast (n : ℕ) : Ideal.absNorm (Ideal.span {(n : O)}) = n ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h : (n : O) = algebraMap ℤ O (n : ℤ) := by simp
  rw [h, Algebra.norm_algebraMap, finrank_O, Int.natAbs_pow, Int.natAbs_natCast]

/-- An ideal below a non-zero ideal of the same norm is that ideal. -/
theorem eq_of_le_of_absNorm_eq {I J : Ideal O} (h : I ≤ J) (hn : Ideal.absNorm I = Ideal.absNorm J)
    (hI : I ≠ ⊥) : I = J := by
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr h
  have hJ : Ideal.absNorm J ≠ 0 := by
    rw [← hn]; exact fun h0 => hI (Ideal.absNorm_eq_zero_iff.mp h0)
  have h1 : Ideal.absNorm Q = 1 := by
    have := congrArg Ideal.absNorm hQ
    rw [map_mul, hn] at this
    exact (Nat.mul_eq_left hJ).mp this.symm
  rw [hQ, Ideal.absNorm_eq_one_iff.mp h1, Ideal.mul_top]

section Above

variable {p : ℕ} (hp : p.Prime) {P : Ideal O} [hPm : P.IsMaximal] (hpP : (p : O) ∈ P)
include hp hpP

/-- A prime above `p` has norm `p` or `p²`. -/
theorem absNorm_eq_of_mem : Ideal.absNorm P = p ∨ Ideal.absNorm P = p ^ 2 := by
  have hdvd : Ideal.absNorm P ∣ p ^ 2 := by
    rw [← absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem P).mpr hpP)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · exact absurd (Ideal.absNorm_eq_one_iff.mp (by simpa using hk')) hPm.ne_top
  · exact Or.inl (by simpa using hk')
  · exact Or.inr hk'

omit hPm in
/-- A prime above `p` of norm `p²` is `(p)`. -/
theorem eq_span_of_absNorm_eq_sq (h : Ideal.absNorm P = p ^ 2) : Ideal.span {(p : O)} = P :=
  eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem P).mpr hpP)
    (by rw [absNorm_span_natCast, h])
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero)

/-- The residue characteristic is `p`. -/
theorem ringChar_eq : ringChar (O ⧸ P) = p :=
  CharP.ringChar_of_prime_eq_zero hp (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hpP)

/-- A prime above `p` contains no other rational prime `q`. -/
theorem natPrime_not_mem {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) : (q : O) ∉ P := by
  intro hqP
  have hcop : IsCoprime (q : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hp).mpr hqp)
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom O)
  apply hPm.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.add_mem (P.mul_mem_left _ hqP) (P.mul_mem_left _ hpP)

/-- Away from `3` a prime above `p` does not contain `λ`. -/
theorem lambda_not_mem (hp3 : p ≠ 3) : lambda ∉ P := by
  intro hl
  apply natPrime_not_mem hp hpP Nat.prime_three (Ne.symm hp3)
  obtain ⟨c, hc⟩ := (dvd_pow_self lambda two_ne_zero).trans lambda_sq_dvd_three
  have : ((3 : ℕ) : O) = 3 := by norm_num
  rw [this, hc]; exact P.mul_mem_right _ hl

/-- `3 ∣ N𝔭 − 1` away from `3`. -/
theorem three_dvd_absNorm_sub_one (hp3 : p ≠ 3) : 3 ∣ Ideal.absNorm P - 1 := by
  have h := card_sub_one_div_three P (lambda_not_mem hp hpP hp3)
  rwa [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at h

end Above

/-- A prime ideal power of norm `p^m` lies above `p`, with norm `p^f`, `f k = m`. -/
theorem exists_absNorm_of_pow_eq {p m k : ℕ} (hp : p.Prime) {P : Ideal O} (hP : P.IsPrime)
    (hk : 1 ≤ k) (h : Ideal.absNorm P ^ k = p ^ m) :
    (p : O) ∈ P ∧ ∃ f, 1 ≤ f ∧ Ideal.absNorm P = p ^ f ∧ f * k = m := by
  have hdvd : Ideal.absNorm P ∣ p ^ m := h ▸ dvd_pow_self _ (by omega)
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf'
    · exact absurd (Ideal.absNorm_eq_one_iff.mp (by simpa using hf)) hP.ne_top
    · exact hf'
  refine ⟨?_, f, hf1, hf, ?_⟩
  · have hmem := Ideal.absNorm_mem P
    rw [hf, Nat.cast_pow] at hmem
    exact hP.mem_of_pow_mem _ hmem
  · rw [hf, ← pow_mul] at h
    exact Nat.pow_right_injective hp.two_le h

/-! ### The contacts of `χ` -/

open ArtinMertens
open scoped Classical

/-- Membership in the index set of the contacts at `n`. -/
theorem mem_contactSet {n : ℕ} {P : Ideal O} {k : ℕ} :
    (P, k) ∈ (primePowersLe K n).filter (fun pk => Ideal.absNorm pk.1 ^ pk.2 = n) ↔
      P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ Ideal.absNorm P ^ k = n := by
  rw [Finset.mem_filter, mem_primePowersLe]
  constructor
  · rintro ⟨⟨h1, h2, h3, -⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3, h4.le⟩, h4⟩

theorem heckeValue_cubicTwoHecke_pow_mul_log (P : Ideal O) (k : ℕ) :
    heckeValue sixModulus cubicTwoHecke P ^ k * (Real.log (Ideal.absNorm P) : ℂ) =
      ringComplex (twoCubicValue P) ^ k * (Real.log (Ideal.absNorm P) : ℂ) := by
  rw [heckeValue_cubicTwoHecke]

/-- At a prime power of `2` or `3` every contact vanishes: those primes divide the modulus. -/
theorem heckeMangoldt_cubicTwoHecke_of_dvd_six {p m : ℕ} (hp : p.Prime) (h6 : p ∣ 6) :
    heckeMangoldt sixModulus cubicTwoHecke (p ^ m) = 0 := by
  rw [heckeMangoldt]
  refine Finset.sum_eq_zero fun ⟨P, k⟩ hPk => ?_
  obtain ⟨hP, -, hk, hn⟩ := mem_contactSet.mp hPk
  obtain ⟨hpP, -⟩ := exists_absNorm_of_pow_eq hp hP hk hn
  have h0 : twoCubicValue P = 0 := by
    by_contra hne
    have htop := (twoCubicValue_ne_zero_iff P).mp hne
    have h6P : Ideal.span {(6 : O)} ≤ P := by
      rw [Ideal.span_singleton_le_iff_mem]
      obtain ⟨c, hc⟩ := h6
      have : (6 : O) = (p : O) * (c : O) := by exact_mod_cast hc
      rw [this]; exact P.mul_mem_right _ hpP
    exact hP.ne_top (eq_top_iff.mpr (htop ▸ sup_le le_rfl h6P))
  simp only [heckeValue_cubicTwoHecke, h0, map_zero, zero_pow (by omega : k ≠ 0), zero_mul]


/-- The norm of a prime ideal power is a prime power. -/
theorem isPrimePow_of_mem_contactSet {n : ℕ} {P : Ideal O} {k : ℕ}
    (h : (P, k) ∈ (primePowersLe K n).filter (fun pk => Ideal.absNorm pk.1 ^ pk.2 = n)) :
    IsPrimePow n := by
  obtain ⟨hP, hP0, hk, hn⟩ := mem_contactSet.mp h
  haveI := hP.isMaximal hP0
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  obtain ⟨q, -, f, hq, hcard⟩ := FiniteField.card' (O ⧸ P)
  have hN : Ideal.absNorm P = q ^ (f : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  rw [← hn, hN, ← pow_mul]
  exact (isPrimePow_nat_iff _).mpr ⟨q, (f : ℕ) * k, hq, Nat.mul_pos f.pos (by omega), rfl⟩

/-! #### Inert primes -/

section Inert

variable {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
include hp hp3

/-- Above an inert `p` the only prime is `(p)`, of norm `p²`. -/
theorem eq_span_of_inert {P : Ideal O} [P.IsMaximal] (hpP : (p : O) ∈ P) :
    Ideal.span {(p : O)} = P ∧ Ideal.absNorm P = p ^ 2 := by
  have hp3' : p ≠ 3 := by rintro rfl; norm_num at hp3
  rcases absNorm_eq_of_mem hp hpP with h | h
  · have h3 := three_dvd_absNorm_sub_one hp hpP hp3'
    rw [h] at h3
    omega
  · exact ⟨eq_span_of_absNorm_eq_sq hp hpP h, h⟩

theorem span_isMaximal_of_inert : (Ideal.span {(p : O)}).IsMaximal := by
  have hne : Ideal.span {(p : O)} ≠ ⊤ := by
    intro h
    have h1 := absNorm_span_natCast p
    rw [h, Ideal.absNorm_top] at h1
    have := hp.two_le
    nlinarith
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  rw [(eq_span_of_inert hp hp3 (hle (Ideal.mem_span_singleton_self _))).1]
  exact hM

/-- **Contacts at an inert prime**: `2 log p` at even powers, `0` at odd powers. -/
theorem heckeMangoldt_cubicTwoHecke_inert (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m) :
    heckeMangoldt sixModulus cubicTwoHecke (p ^ m) =
      if Even m then 2 * (Real.log p : ℂ) else 0 := by
  haveI := span_isMaximal_of_inert hp hp3
  have hmem : ∀ P k, (P, k) ∈ (primePowersLe K (p ^ m)).filter
      (fun pk => Ideal.absNorm pk.1 ^ pk.2 = p ^ m) → P = Ideal.span {(p : O)} ∧ 2 * k = m := by
    intro P k h
    obtain ⟨hP, hP0, hk, hn⟩ := mem_contactSet.mp h
    haveI := hP.isMaximal hP0
    obtain ⟨hpP, f, -, hf, hfk⟩ := exists_absNorm_of_pow_eq hp hP hk hn
    obtain ⟨hspan, hN⟩ := eq_span_of_inert hp hp3 hpP
    rw [hN] at hf
    have : f = 2 := (Nat.pow_right_injective hp.two_le hf).symm
    exact ⟨hspan.symm, by rw [← hfk, this]⟩
  rw [heckeMangoldt]
  split_ifs with he
  · obtain ⟨j, rfl⟩ := he
    have hS : (primePowersLe K (p ^ (j + j))).filter
        (fun pk => Ideal.absNorm pk.1 ^ pk.2 = p ^ (j + j)) = {(Ideal.span {(p : O)}, j)} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨mem_contactSet.mpr ⟨inferInstance, ?_, by omega, ?_⟩, ?_⟩
      · rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
      · rw [absNorm_span_natCast, ← pow_mul, two_mul]
      · rintro ⟨P, k⟩ h
        obtain ⟨rfl, hk⟩ := hmem P k h
        simp only [Prod.mk.injEq, true_and]
        omega
    rw [hS, Finset.sum_singleton, heckeValue_cubicTwoHecke,
      twoCubicValue_natCast (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm)
        (fun h => by
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
          rw [← this] at hp3; norm_num at hp3),
      map_one, one_pow, one_mul, absNorm_span_natCast, Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  · refine Finset.sum_eq_zero fun ⟨P, k⟩ h => ?_
    obtain ⟨-, hk⟩ := hmem P k h
    exact absurd ⟨k, by omega⟩ he

end Inert

/-! #### Split primes -/

section Split

variable {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1)
include hp hp3

theorem ne_three_of_split : p ≠ 3 := by rintro rfl; norm_num at hp3

theorem ne_two_of_split : p ≠ 2 := by rintro rfl; norm_num at hp3

/-- There are two ideals of norm `p`. -/
theorem card_idealsOfNorm_split : (idealsOfNorm K p).card = 2 := by
  have h := FamilyContinuationTheory.card_ideals_thirdCyclotomic K hp.pos
  have hd : FamilyContinuationTheory.EisensteinNorm.divisorChar p = 2 := by
    rw [FamilyContinuationTheory.EisensteinNorm.divisorChar, Nat.Prime.divisors hp,
      Finset.sum_pair (Ne.symm hp.one_lt.ne')]
    simp [FamilyContinuationTheory.EisensteinNorm.chi3, hp3]
  rw [hd] at h
  have h' : Nat.card {I : Ideal O // Ideal.absNorm I = p} = 2 := by exact_mod_cast h
  rw [idealsOfNorm, ← h']
  exact (Nat.card_eq_card_finite_toFinset _).symm

omit hp3 in
/-- An ideal of norm `p` is maximal. -/
theorem isMaximal_of_absNorm_eq {I : Ideal O} (hI : Ideal.absNorm I = p) : I.IsMaximal := by
  have hI0 : I ≠ ⊥ := fun h => hp.ne_zero (by rw [← hI, h, Ideal.absNorm_bot])
  exact (Ideal.isPrime_of_irreducible_absNorm (hI ▸ hp)).isMaximal hI0

/-- Every prime above a split `p` has norm `p`. -/
theorem absNorm_eq_of_split {P : Ideal O} [P.IsMaximal] (hpP : (p : O) ∈ P) :
    Ideal.absNorm P = p := by
  rcases absNorm_eq_of_mem hp hpP with h | h
  · exact h
  · exfalso
    have hspan := eq_span_of_absNorm_eq_sq hp hpP h
    obtain ⟨I, hI⟩ : (idealsOfNorm K p).Nonempty := by
      rw [← Finset.card_pos, card_idealsOfNorm_split hp hp3]; norm_num
    rw [mem_idealsOfNorm] at hI
    have hpI : (p : O) ∈ I := by simpa [hI] using Ideal.absNorm_mem I
    haveI := isMaximal_of_absNorm_eq hp hI
    have hle : P ≤ I := hspan ▸ (Ideal.span_singleton_le_iff_mem I).mpr hpI
    have hPI : P = I := (inferInstance : P.IsMaximal).eq_of_le
      (inferInstance : I.IsMaximal).ne_top hle
    rw [hPI, hI] at h
    have := hp.two_le
    nlinarith

/-- **Contacts at a split prime** as a sum over the two primes of norm `p`. -/
theorem heckeMangoldt_cubicTwoHecke_split {m : ℕ} (hm : 1 ≤ m) :
    heckeMangoldt sixModulus cubicTwoHecke (p ^ m) =
      (∑ I ∈ idealsOfNorm K p, ringComplex (twoCubicValue I) ^ m) * (Real.log p : ℂ) := by
  have hS : (primePowersLe K (p ^ m)).filter (fun pk => Ideal.absNorm pk.1 ^ pk.2 = p ^ m) =
      (idealsOfNorm K p).image (fun I => (I, m)) := by
    ext ⟨P, k⟩
    rw [mem_contactSet, Finset.mem_image]
    constructor
    · rintro ⟨hP, hP0, hk, hn⟩
      haveI := hP.isMaximal hP0
      obtain ⟨hpP, f, -, hf, hfk⟩ := exists_absNorm_of_pow_eq hp hP hk hn
      have hN := absNorm_eq_of_split hp hp3 hpP
      rw [hN] at hf
      have hf1 : f = 1 := (Nat.pow_right_injective hp.two_le (by simpa using hf)).symm
      exact ⟨P, mem_idealsOfNorm.mpr hN, by rw [Prod.mk.injEq]; exact ⟨rfl, by rw [← hfk, hf1, one_mul]⟩⟩
    · rintro ⟨I, hI, hIP⟩
      rw [Prod.mk.injEq] at hIP
      obtain ⟨rfl, rfl⟩ := hIP
      rw [mem_idealsOfNorm] at hI
      haveI := isMaximal_of_absNorm_eq hp hI
      exact ⟨inferInstance, fun h => hp.ne_zero (by rw [← hI, h, Ideal.absNorm_bot]), hm,
        by rw [hI]⟩
  rw [heckeMangoldt, hS, Finset.sum_image (fun I _ J _ h => (Prod.mk.injEq _ _ _ _).mp h |>.1),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [mem_idealsOfNorm] at hI
  rw [heckeValue_cubicTwoHecke, hI]

/-- The two primes above a split `p` multiply to `(p)`, so their values are inverse. -/
theorem twoCubicValue_mul_of_split {P₁ P₂ : Ideal O} (h₁ : Ideal.absNorm P₁ = p)
    (h₂ : Ideal.absNorm P₂ = p) (hne : P₁ ≠ P₂) : twoCubicValue P₁ * twoCubicValue P₂ = 1 := by
  haveI := isMaximal_of_absNorm_eq hp h₁
  haveI := isMaximal_of_absNorm_eq hp h₂
  have hp₁ : (p : O) ∈ P₁ := by simpa [h₁] using Ideal.absNorm_mem P₁
  have hp₂ : (p : O) ∈ P₂ := by simpa [h₂] using Ideal.absNorm_mem P₂
  have hcop : P₁ ⊔ P₂ = ⊤ := Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance hne
  have hprod : Ideal.span {(p : O)} = P₁ * P₂ := by
    refine eq_of_le_of_absNorm_eq ?_ ?_ ?_
    · rw [Ideal.mul_eq_inf_of_coprime hcop, Ideal.span_singleton_le_iff_mem]
      exact ⟨hp₁, hp₂⟩
    · rw [absNorm_span_natCast, map_mul, h₁, h₂, sq]
    · rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  rw [← twoCubicValue_mul, ← hprod]
  exact twoCubicValue_natCast
    (fun h => ne_two_of_split hp hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm)
    (fun h => ne_three_of_split hp hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm)

/-- At a prime of norm `p`, `χ(𝔭)` is a cubic root of unity. -/
theorem twoCubicValue_pow_three_of_split {P : Ideal O} (hP : Ideal.absNorm P = p) :
    twoCubicValue P ^ 3 = 1 := by
  haveI := isMaximal_of_absNorm_eq hp hP
  have hpP : (p : O) ∈ P := by simpa [hP] using Ideal.absNorm_mem P
  have hg := lambda_not_mem hp hpP (ne_three_of_split hp hp3)
  have h2P : (2 : O) ∉ P := by
    have := natPrime_not_mem hp hpP Nat.prime_two (Ne.symm (ne_two_of_split hp hp3))
    simpa using this
  rw [twoCubicValue_prime P hg (by rw [ringChar_eq hp hpP]; exact ne_two_of_split hp hp3)]
  exact MetaplecticMobiusDescent.CubicJacobi.cubicValue_cube P hg 2 h2P

/-- **Euler's criterion through reciprocity.** At a prime `𝔭` of norm `p`, `2` is a cube in
`𝔽_{p^m}` iff `χ(𝔭)^m = 1`. -/
theorem cubeRootsOfTwoCount_eq_of_split {P : Ideal O} (hP : Ideal.absNorm P = p) {m : ℕ}
    (hm : m ≠ 0) : cubeRootsOfTwoCount p m = if twoCubicValue P ^ m = 1 then 3 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := isMaximal_of_absNorm_eq hp hP
  have hpP : (p : O) ∈ P := by simpa [hP] using Ideal.absNorm_mem P
  have hg := lambda_not_mem hp hpP (ne_three_of_split hp hp3)
  have hchar := ringChar_eq hp hpP
  haveI : CharP (O ⧸ P) p := ringChar.eq_iff.mp hchar
  have h2P : (2 : O) ∉ P := by
    have := natPrime_not_mem hp hpP Nat.prime_two (Ne.symm (ne_two_of_split hp hp3))
    simpa using this
  have h3P : (3 : O) ∉ P := by
    have := natPrime_not_mem hp hpP Nat.prime_three (Ne.symm (ne_three_of_split hp hp3))
    simpa using this
  set c := twoCubicValue P
  have hc : c = cubicChar P hg (Ideal.Quotient.mk P 2) :=
    twoCubicValue_prime P hg (by rw [hchar]; exact ne_two_of_split hp hp3)
  have hc3 : c ^ 3 = 1 := twoCubicValue_pow_three_of_split hp hp3 hP
  -- reduce `c` into the residue field `𝔽_p`
  let τ : ZMod p →+* O ⧸ P := ZMod.castHom (dvd_refl p) (O ⧸ P)
  have hcard : Nat.card (O ⧸ P) = p := by
    rw [← hP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hτ : τ ((2 : ZMod p) ^ ((p - 1) / 3)) = Ideal.Quotient.mk P c := by
    rw [hc, cubicChar_reduce, hcard, map_pow, map_ofNat, map_ofNat]
  rw [cubeRootsOfTwoCount_split hp3 hm]
  have hiff : ((2 : ZMod p) ^ ((p - 1) / 3)) ^ m = 1 ↔ c ^ m = 1 := by
    rw [← τ.injective.eq_iff, map_pow, hτ, map_one, ← map_pow]
    constructor
    · intro h
      by_contra hne
      have hu3 : (c ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
      have hq : (c ^ m) ^ 2 + c ^ m + 1 = 0 := by
        have : (c ^ m - 1) * ((c ^ m) ^ 2 + c ^ m + 1) = 0 := by
          linear_combination hu3
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
      apply h3P
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := congrArg (Ideal.Quotient.mk P) hq
      rw [map_add, map_add, map_pow, h, map_one, map_zero] at this
      rw [show (Ideal.Quotient.mk P) 3 = 1 ^ 2 + 1 + 1 by rw [map_ofNat]; norm_num]
      exact this
    · intro h
      rw [h, map_one]
  by_cases h : c ^ m = 1
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (mt hiff.mp h), if_neg h]

/-- **Contacts at a split prime.** With `χ(𝔭)χ(𝔭̄) = 1` and `2` a cube in `𝔽_{p^m}` iff
`χ(𝔭)^m = 1`: `χ(𝔭)^m + χ(𝔭̄)^m = #{x³ = 2} − 1`. -/
theorem heckeMangoldt_cubicTwoHecke_split_eq {m : ℕ} (hm : 1 ≤ m) :
    heckeMangoldt sixModulus cubicTwoHecke (p ^ m) =
      (((cubeRootsOfTwoCount p m : ℝ) - 1) * Real.log p : ℝ) := by
  obtain ⟨P₁, P₂, hne, hS⟩ := Finset.card_eq_two.mp (card_idealsOfNorm_split hp hp3)
  have h₁ : Ideal.absNorm P₁ = p := mem_idealsOfNorm.mp (hS ▸ Finset.mem_insert_self _ _)
  have h₂ : Ideal.absNorm P₂ = p :=
    mem_idealsOfNorm.mp (hS ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [heckeMangoldt_cubicTwoHecke_split hp hp3 hm, hS, Finset.sum_pair hne,
    cubeRootsOfTwoCount_eq_of_split hp hp3 h₁ (by omega)]
  set u := twoCubicValue P₁ ^ m
  set v := twoCubicValue P₂ ^ m
  have huv : u * v = 1 := by
    rw [← mul_pow, twoCubicValue_mul_of_split hp hp3 h₁ h₂ hne, one_pow]
  have hu3 : u ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, twoCubicValue_pow_three_of_split hp hp3 h₁, one_pow]
  have hsum : ringComplex (twoCubicValue P₁) ^ m + ringComplex (twoCubicValue P₂) ^ m =
      ringComplex (u + v) := by rw [map_add, map_pow, map_pow]
  rw [hsum]
  push_cast
  congr 1
  split_ifs with hu
  · have hv : v = 1 := by rw [hu, one_mul] at huv; exact huv
    rw [hu, hv, show (1 : O) + 1 = 2 by norm_num, map_ofNat]
    norm_num
  · have hv : v = u ^ 2 := by
      calc v = u ^ 3 * v := by rw [hu3, one_mul]
        _ = u ^ 2 * (u * v) := by ring
        _ = u ^ 2 := by rw [huv, mul_one]
    have hq : u ^ 2 + u + 1 = 0 := by
      have : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination hu3
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hu)
    have : u + v = -1 := by rw [hv]; linear_combination hq
    rw [this, map_neg, map_one]
    norm_num

end Split

/-! ### The Artin character -/

/-- **The contacts of the degree-two Artin character of `ℚ(∛2, ω)`**: at `n = p^m`,
`(#{x ∈ 𝔽_{p^m} : x³ = 2} − 1) log p`, the trace of `Frob_p^m` on the roots of `X³ − 2` minus
the trivial representation; zero off the prime powers. -/
def artinCubeContact (n : ℕ) : ℝ :=
  if IsPrimePow n then
    ((cubeRootsOfTwoCount n.minFac (n.factorization n.minFac) : ℝ) - 1) * Real.log n.minFac
  else 0

theorem artinCubeContact_prime_pow {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) :
    artinCubeContact (p ^ m) = ((cubeRootsOfTwoCount p m : ℝ) - 1) * Real.log p := by
  have hpp : IsPrimePow (p ^ m) := (isPrimePow_nat_iff _).mpr ⟨p, m, hp, hm, rfl⟩
  have hf : (p ^ m).factorization p = m := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one]
  rw [artinCubeContact, if_pos hpp, hp.pow_minFac (by omega), hf]

/-- `p^m ≡ 2 (mod 3)` for `p ≡ 2 (mod 3)` and odd `m`. -/
theorem not_three_dvd_pow_sub_one_of_odd {p m : ℕ} (hp3 : p % 3 = 2) (hm : ¬ Even m) :
    ¬ 3 ∣ p ^ m - 1 := by
  obtain ⟨j, rfl⟩ := Nat.not_even_iff_odd.mp hm
  have h : p ^ (2 * j + 1) % 3 = 2 := by
    rw [Nat.pow_mod, hp3, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  omega

/-- **Reciprocity for the degree-two character**: the von Mangoldt function of the cubic
character of `2` over `ℚ(ω)` is the Artin contact `(#{x³ = 2} − 1) log p` at every `n`. -/
theorem heckeMangoldt_cubicTwoHecke (n : ℕ) :
    heckeMangoldt sixModulus cubicTwoHecke n = (artinCubeContact n : ℂ) := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, m, hp, hm, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    rw [artinCubeContact_prime_pow hp hm]
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have h23 : p = 2 ∨ p = 3 := by
        interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; norm_num at hp)
      rcases h23 with rfl | rfl
      · rw [heckeMangoldt_cubicTwoHecke_of_dvd_six Nat.prime_two (by norm_num),
          cubeRootsOfTwoCount_two]
        simp
      · have h3 : ¬ 3 ∣ 3 ^ m - 1 := by
          have hd : 3 ∣ 3 ^ m := dvd_pow_self 3 (by omega)
          have hpos : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
          omega
        rw [heckeMangoldt_cubicTwoHecke_of_dvd_six Nat.prime_three (by norm_num),
          cubeRootsOfTwoCount_of_not_dvd Nat.prime_three (by omega) h3]
        simp
    · have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
        have h0 : p % 3 ≠ 0 := by
          intro h
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
          omega
        omega
      rcases hmod with h1 | h2
      · exact heckeMangoldt_cubicTwoHecke_split_eq hp h1 hm
      · haveI : Fact p.Prime := ⟨hp⟩
        rw [heckeMangoldt_cubicTwoHecke_inert hp h2 (by omega) hm]
        split_ifs with he
        · rw [cubeRootsOfTwoCount_inert_even h2 (by omega) (by omega) he]
          push_cast; ring
        · rw [cubeRootsOfTwoCount_of_not_dvd hp (by omega)
            (not_three_dvd_pow_sub_one_of_odd h2 he)]
          simp
  · rw [artinCubeContact, if_neg hn, Complex.ofReal_zero, heckeMangoldt]
    exact Finset.sum_eq_zero fun ⟨P, k⟩ h => absurd (isPrimePow_of_mem_contactSet h) hn

/-- `L(s, ρ)`: its logarithmic derivative is the Dirichlet series of the Artin contacts. -/
theorem logDeriv_heckeL_cubicTwoHecke {s : ℂ} (hs : 1 < s.re) :
    logDeriv (heckeL sixModulus cubicTwoHecke) s =
      -LSeries (fun n => (artinCubeContact n : ℂ)) s := by
  rw [logDeriv_heckeL _ _ hs]
  congr 2
  funext n
  exact heckeMangoldt_cubicTwoHecke n

/-! ### Weil's explicit formula and the index law for `ρ` -/

/-- `χ` is not trivial: `χ(1 + 3ω) ≠ 1`. -/
theorem cubicTwoHecke_ne_one : cubicTwoHecke ≠ 1 := by
  intro h
  have hgood := good_one_add_three_omega
  set I : Ideal O := Ideal.span {1 + 3 * omega}
  have hI0 : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h0
    exact hgood.2 (h0 ▸ dvd_zero _)
  have hm : idealUnit hI0 ∈ idealGroup sixModulus :=
    (idealUnit_mem_idealGroup_iff sixModulus hI0).mpr
      ((twoCubicValue_ne_zero_iff I).mp (isUnit_twoCubicOf hgood.1 hgood.2).ne_zero)
  have hv := heckeValue_cubicTwoHecke I
  rw [heckeValue_of_mem sixModulus _ hI0 hm, h, MonoidHom.one_apply, Units.val_one,
    ← map_one ringComplex] at hv
  exact twoCubicOf_one_add_three_omega_ne_one (ringComplex_injective hv).symm

theorem heckePole_cubicTwoHecke : heckePole sixModulus cubicTwoHecke = 0 := by
  rw [heckePole, if_neg cubicTwoHecke_ne_one]

/-- The zeros of `L(s, ρ) = L(s, χ)` in the critical strip, with their multiplicities. -/
abbrev artinZeros :=
  heckeZeros sixModulus cubicTwoHecke heckeFiniteConductor_cubicTwoHecke

/-- **Weil's explicit formula for `ρ`**, with the Artin contacts on the prime side. -/
theorem W_artinZeros_eq {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    artinZeros.W f g =
      (1 / (2 * Real.pi) : ℂ) *
          (∫ t : ℝ, paperFT (EF.weilTest f g) t *
            ((heckeSymbol sixModulus cubicTwoHecke t : ℝ) : ℂ)) -
        ∑' n : ℕ, (artinCubeContact n : ℂ) / Real.sqrt n * EF.weilTest f g (Real.log n) -
        ∑' n : ℕ, (artinCubeContact n : ℂ) / Real.sqrt n * EF.weilTest f g (-Real.log n) := by
  rw [W_heckeZeros_eq sixModulus cubicTwoHecke heckeFiniteConductor_cubicTwoHecke hf hfc hg hgc,
    heckePole_cubicTwoHecke, zero_mul, zero_add]
  simp only [heckeMangoldt_cubicTwoHecke, Complex.conj_ofReal]

/-- **The index law for the degree-two Artin character.** Weil's form of `ρ` has `n` negative
squares on some family of `n` tests iff `L(s, ρ)` has at least `n` distinct zeros to the right of
the critical line. -/
theorem exists_le_negIndex_artinGram_iff (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram artinZeros f)) ↔
      (n : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros artinZeros).encard :=
  exists_le_negIndex_heckeGram_iff sixModulus cubicTwoHecke heckeFiniteConductor_cubicTwoHecke n

/-- **Castelnuovo and Severi for `ρ`.** Weil's form of `ρ` has no negative square on any family
of tests iff all zeros of the completed `L(s, ρ)` lie on the critical line. -/
theorem forall_negIndex_artinGram_eq_zero_iff :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram artinZeros f) = 0) ↔
      ∀ ρ : ℂ, heckeXi sixModulus cubicTwoHecke ρ = 0 → ρ.re = 1 / 2 :=
  forall_negIndex_heckeGram_eq_zero_iff sixModulus cubicTwoHecke heckeFiniteConductor_cubicTwoHecke

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CubeRootsOfTwo
