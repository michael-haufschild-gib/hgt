import GaloisForLFunctions.RHTower.DeningerRationalWittCoherentCyclotomicDescent
import GaloisForLFunctions.RHTower.DeningerPrimeMultiplicativeAutomorphismComparison

/-!
# Cyclotomic exhaustion of the complexified rational-Witt presentation

Prior modules embedded each finite prime-to-`p` cyclotomic stage into
`ℂ[(AlgebraicClosure (ZMod p))ˣ]`, but did not prove that these stages exhaust the presentation.
This module proves that missing converse.

Every algebraic-closure unit has finite order prime to `p`, hence occurs in one chosen finite root
embedding. Monoid-algebra induction and directedness then put every finite-support presentation
element in a single cyclotomic stage. If the ambient element is arithmetic-Frobenius fixed,
injectivity and Frobenius naturality force its finite-stage preimage to be fixed as well.
-/

namespace RHTower

noncomputable section

theorem deningerPrimeArithmeticUnit_orderOf_coprime
    (p : Nat.Primes) (x : (DeningerPrimeArithmeticClosure p)ˣ) :
    (p : ℕ).Coprime (orderOf x) := by
  rw [p.2.coprime_iff_not_dvd]
  intro hdiv
  obtain ⟨k, hk⟩ := hdiv
  have hkeq : orderOf x = (p : ℕ) * k := hk
  have hfin : IsOfFinOrder x :=
    deningerPrimeMulAut_prime_arithmetic_units_isTorsion p x
  have hnpos : 0 < orderOf x := orderOf_pos_iff.mpr hfin
  have hpow : x ^ ((p : ℕ) ^ 1 * k) = 1 := by
    rw [pow_one, ← hk]
    exact pow_orderOf_eq_one x
  have hroot : x ∈ rootsOfUnity k (DeningerPrimeArithmeticClosure p) :=
    (mem_rootsOfUnity_prime_pow_mul_iff' (DeningerPrimeArithmeticClosure p)
      (p : ℕ) 1 k).mp hpow
  have hdvd : orderOf x ∣ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact (mem_rootsOfUnity k x).mp hroot
  have hprodpos : 0 < (p : ℕ) * k := by simpa [hkeq] using hnpos
  have hkpos : 0 < k := pos_of_mul_pos_right hprodpos (Nat.zero_le _)
  have hle : orderOf x ≤ k := Nat.le_of_dvd hkpos hdvd
  have hklt : k < (p : ℕ) * k :=
    lt_mul_of_one_lt_left hkpos p.2.one_lt
  exact (not_lt_of_ge hle) (hkeq ▸ hklt)

theorem deningerPrimeFiniteWittRootEmbedding_exists_stage
    (p : Nat.Primes) (x : (DeningerPrimeArithmeticClosure p)ˣ) :
    ∃ (s : DeningerFiniteFrobeniusStage (p : ℕ))
      (j : Multiplicative (ZMod s.modulus)),
      deningerPrimeFiniteWittRootEmbedding p s j = x := by
  have hfin : IsOfFinOrder x :=
    deningerPrimeMulAut_prime_arithmetic_units_isTorsion p x
  let s : DeningerFiniteFrobeniusStage (p : ℕ) :=
    ⟨orderOf x, orderOf_ne_zero_iff.mpr hfin,
      deningerPrimeArithmeticUnit_orderOf_coprime p x⟩
  letI : NeZero s.modulus := ⟨s.modulus_ne_zero⟩
  have hxpow :
      ((x : (DeningerPrimeArithmeticClosure p)ˣ) :
        DeningerPrimeArithmeticClosure p) ^ s.modulus = 1 := by
    exact congrArg Units.val (pow_orderOf_eq_one x)
  obtain ⟨i, _hi, heq⟩ :=
    (deningerPrimeFiniteWittPrimitiveRoot_spec p s).eq_pow_of_pow_eq_one hxpow
  refine ⟨s, Multiplicative.ofAdd (i : ZMod s.modulus), ?_⟩
  apply Units.ext
  rw [deningerPrimeFiniteWittRootEmbedding_nat]
  exact heq

theorem deningerPrimeComplexifiedRationalWitt_single_exists_stage
    (p : Nat.Primes) (x : (DeningerPrimeArithmeticClosure p)ˣ) (c : ℂ) :
    ∃ (s : DeningerFiniteFrobeniusStage (p : ℕ))
      (w : DeningerFiniteCyclotomicWittAlgebra s.modulus),
      deningerPrimeFiniteCyclotomicWittInclusion p s w =
        MonoidAlgebra.single x c := by
  obtain ⟨s, j, hj⟩ := deningerPrimeFiniteWittRootEmbedding_exists_stage p x
  refine ⟨s, AddMonoidAlgebra.single j.toAdd c, ?_⟩
  rw [deningerPrimeFiniteCyclotomicWittInclusion_single]
  simpa using congrArg (fun y => MonoidAlgebra.single y c) hj

/-- Every presentation element occurs at one finite cyclotomic stage. -/
theorem deningerPrimeComplexifiedRationalWitt_exists_finiteStage
    (p : Nat.Primes) (w : DeningerPrimeComplexifiedRationalWittPresentation p) :
    ∃ (s : DeningerFiniteFrobeniusStage (p : ℕ))
      (v : DeningerFiniteCyclotomicWittAlgebra s.modulus),
      deningerPrimeFiniteCyclotomicWittInclusion p s v = w := by
  induction w using MonoidAlgebra.induction with
  | zero =>
      let s : DeningerFiniteFrobeniusStage (p : ℕ) :=
        ⟨1, one_ne_zero, Nat.coprime_one_right (p : ℕ)⟩
      exact ⟨s, 0, map_zero _⟩
  | single_add x c w _hx _hc ih =>
      obtain ⟨s, v, hv⟩ := ih
      obtain ⟨t, u, hu⟩ :=
        deningerPrimeComplexifiedRationalWitt_single_exists_stage p x c
      obtain ⟨r, hsr, htr⟩ := exists_ge_ge s t
      refine ⟨r,
        deningerPrimeFiniteCyclotomicWittTransition p hsr v +
          deningerPrimeFiniteCyclotomicWittTransition p htr u, ?_⟩
      rw [map_add]
      have hs := DFunLike.congr_fun
        (deningerPrimeFiniteCyclotomicWittInclusion_transition p hsr) v
      have ht := DFunLike.congr_fun
        (deningerPrimeFiniteCyclotomicWittInclusion_transition p htr) u
      change
        deningerPrimeFiniteCyclotomicWittInclusion p r
            (deningerPrimeFiniteCyclotomicWittTransition p hsr v) +
          deningerPrimeFiniteCyclotomicWittInclusion p r
            (deningerPrimeFiniteCyclotomicWittTransition p htr u) = _
      change
        deningerPrimeFiniteCyclotomicWittInclusion p r
            (deningerPrimeFiniteCyclotomicWittTransition p hsr v) =
          deningerPrimeFiniteCyclotomicWittInclusion p s v at hs
      change
        deningerPrimeFiniteCyclotomicWittInclusion p r
            (deningerPrimeFiniteCyclotomicWittTransition p htr u) =
          deningerPrimeFiniteCyclotomicWittInclusion p t u at ht
      rw [hs, ht, hv, hu, add_comm]

/-- Every ambient Frobenius-fixed element has a Frobenius-fixed representative at one finite
cyclotomic stage. -/
theorem deningerPrimeComplexifiedRationalWitt_fixed_exists_finiteStage
    (p : Nat.Primes) (w : DeningerPrimeComplexifiedRationalWittPresentation p)
    (hw : deningerPrimeComplexifiedRationalWittFrobenius p w = w) :
    ∃ (s : DeningerFiniteFrobeniusStage (p : ℕ))
      (v : DeningerFiniteCyclotomicWittAlgebra s.modulus),
      deningerFiniteCyclotomicWittFrobenius
          (p : ℕ) s.modulus s.coprime v = v ∧
      deningerPrimeFiniteCyclotomicWittInclusion p s v = w := by
  obtain ⟨s, v, hv⟩ :=
    deningerPrimeComplexifiedRationalWitt_exists_finiteStage p w
  refine ⟨s, v, ?_, hv⟩
  apply deningerPrimeFiniteCyclotomicWittInclusion_injective p s
  calc
    deningerPrimeFiniteCyclotomicWittInclusion p s
        (deningerFiniteCyclotomicWittFrobenius
          (p : ℕ) s.modulus s.coprime v) =
        deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s v) :=
      (deningerPrimeFiniteCyclotomicWittInclusion_frobenius p s v).symm
    _ = deningerPrimeComplexifiedRationalWittFrobenius p w := congrArg _ hv
    _ = w := hw
    _ = deningerPrimeFiniteCyclotomicWittInclusion p s v := hv.symm

end

end RHTower
