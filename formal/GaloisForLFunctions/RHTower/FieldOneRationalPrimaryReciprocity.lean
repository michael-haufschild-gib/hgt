import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleDiagonalReciprocity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Rational primary decomposition and full diagonal reciprocity

Two additive homomorphisms out of `ℚ` agree once they agree on every
reciprocal prime power. The proof factors the reduced denominator into
pairwise-coprime prime powers, constructs Bézout coefficients, and decomposes
its reciprocal as a finite sum of prime-power fractions.

Applying this extension theorem to the prime-local finite-adele reciprocity
law proves

`ψ_f (Δ_f q) = q mod ℤ`

for every rational `q`. Hence the standard semilocal character with negative
archimedean sign vanishes on the full diagonal copy of `ℚ`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function

/-- Additive homomorphisms out of `ℚ` agree if they agree on all reciprocal
prime powers. -/
theorem Rat.addMonoidHom_ext_primePowers
    {A : Type*} [AddCommGroup A]
    (f g : ℚ →+ A)
    (hprime :
      ∀ (p : ℕ), p.Prime → ∀ n : ℕ,
        f ((1 : ℚ) / (p : ℚ) ^ n) =
          g ((1 : ℚ) / (p : ℚ) ^ n)) :
    f = g := by
  ext q
  let d := q.den
  have hd0 : d ≠ 0 := q.den_nz
  by_cases hd1 : d = 1
  · have hqint : q = q.num := by
      calc
        q = (q.num : ℚ) / (q.den : ℚ) :=
          q.num_div_den.symm
        _ = (q.num : ℚ) := by
          rw [show q.den = d by rfl, hd1]
          simp
    have hone :
        f (1 : ℚ) = g (1 : ℚ) := by
      simpa using hprime 2 Nat.prime_two 0
    rw [hqint,
      show (q.num : ℚ) = q.num • (1 : ℚ) by simp,
      map_zsmul, map_zsmul, hone]
  have hdgt : 1 < d := by
    omega
  let t : Finset ℕ := d.primeFactors
  let s : ℕ → ℤ := fun p => (p ^ d.factorization p : ℕ)
  have ht : t.Nonempty := Nat.nonempty_primeFactors.mpr hdgt
  have hpair :
      Pairwise (IsCoprime on fun i : t => s i) := by
    intro p r hpr
    exact Nat.Coprime.isCoprime
      (Nat.pairwise_coprime_pow_primeFactors_factorization
        (n := d) hpr)
  obtain ⟨μ, hμ⟩ :=
    (exists_sum_eq_one_iff_pairwise_coprime
      (R := ℤ) (s := s) ht).2 hpair
  have hdenprodNat :
      ∏ p ∈ t, p ^ d.factorization p = d := by
    simpa only [t] using
      (Nat.prod_factorization_pow_eq_self hd0)
  have hdenprod :
      ∏ p ∈ t, s p = (d : ℤ) := by
    change
      (∏ p ∈ t, (p ^ d.factorization p : ℕ) : ℤ) =
        (d : ℤ)
    exact_mod_cast hdenprodNat
  have hs_ne (p : ℕ) (hp : p ∈ t) : s p ≠ 0 := by
    dsimp [s]
    exact_mod_cast pow_ne_zero (d.factorization p)
      (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  have hdecomp :
      (1 : ℚ) / d =
        ∑ p ∈ t, (μ p : ℚ) / (s p : ℚ) := by
    calc
      (1 : ℚ) / d =
          ((∑ p ∈ t, μ p * ∏ r ∈ t \ {p}, s r : ℤ) : ℚ) /
            d := by rw [hμ]; simp
      _ = ∑ p ∈ t,
          ((μ p * ∏ r ∈ t \ {p}, s r : ℤ) : ℚ) / d := by
        push_cast
        rw [Finset.sum_div]
      _ = ∑ p ∈ t, (μ p : ℚ) / (s p : ℚ) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply (div_eq_div_iff
          (show (d : ℚ) ≠ 0 by exact_mod_cast hd0)
          (show (s p : ℚ) ≠ 0 by exact_mod_cast hs_ne p hp)).2
        norm_cast
        rw [← hdenprod,
          Finset.prod_eq_prod_diff_singleton_mul hp s]
        ring
  have hreciprocal :
      f ((1 : ℚ) / d) = g ((1 : ℚ) / d) := by
    rw [hdecomp, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpprime : p.Prime :=
      Nat.prime_of_mem_primeFactors hp
    have hs :
        (s p : ℚ) = (p : ℚ) ^ d.factorization p := by
      norm_cast
    rw [hs]
    have hscale :
        (μ p : ℚ) / (p : ℚ) ^ d.factorization p =
          μ p • ((1 : ℚ) / (p : ℚ) ^ d.factorization p) := by
      rw [zsmul_eq_mul]
      ring
    rw [hscale, map_zsmul, map_zsmul,
      hprime p hpprime (d.factorization p)]
  have hq :
      q = q.num • ((1 : ℚ) / d) := by
    calc
      q = (q.num : ℚ) / (q.den : ℚ) :=
        q.num_div_den.symm
      _ = q.num • ((1 : ℚ) / d) := by
        rw [zsmul_eq_mul]
        dsimp [d]
        ring
  rw [hq, map_zsmul, map_zsmul, hreciprocal]

/-- Restriction of the finite-adele standard character to diagonal rationals. -/
noncomputable def fieldOneFiniteAdeleDiagonalUnitAddCircleCharacter :
    ℚ →+ UnitAddCircle :=
  fieldOneFiniteAdeleStandardUnitAddCircleCharacter.comp
    (algebraMap ℚ FieldOneFiniteAdele).toAddMonoidHom

theorem fieldOneFiniteAdeleDiagonalUnitAddCircleCharacter_primePower
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    fieldOneFiniteAdeleDiagonalUnitAddCircleCharacter
        ((1 : ℚ) / (p : ℚ) ^ n) =
      fieldOneRationalUnitAddCircleCharacter
        ((1 : ℚ) / (p : ℚ) ^ n) := by
  let v : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
      ⟨p, hp⟩
  have h :=
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter_algebraMap_int_div_pow
      v 1 n
  change
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter
        (algebraMap ℚ FieldOneFiniteAdele
          ((1 : ℚ) / (p : ℚ) ^ n)) =
      fieldOneRationalUnitAddCircleCharacter
        ((1 : ℚ) / (p : ℚ) ^ n)
  simpa only [v,
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply,
    Nat.cast_one, Int.cast_one] using h

/-- Full rational diagonal reciprocity for the finite-adele standard
character. -/
theorem fieldOneFiniteAdeleStandardUnitAddCircleCharacter_algebraMap_rat
    (q : ℚ) :
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter
        (algebraMap ℚ FieldOneFiniteAdele q) =
      fieldOneRationalUnitAddCircleCharacter q := by
  have heq :
      fieldOneFiniteAdeleDiagonalUnitAddCircleCharacter =
        fieldOneRationalUnitAddCircleCharacter :=
    Rat.addMonoidHom_ext_primePowers
      fieldOneFiniteAdeleDiagonalUnitAddCircleCharacter
      fieldOneRationalUnitAddCircleCharacter
      fieldOneFiniteAdeleDiagonalUnitAddCircleCharacter_primePower
  exact DFunLike.congr_fun heq q

/-- The standard semilocal character is trivial on the full diagonal copy of
`ℚ`. -/
theorem fieldOneSemilocalStandardUnitAddCircleCharacter_diagonal_rat
    (q : ℚ) :
    fieldOneSemilocalStandardUnitAddCircleCharacter
      ((q : ℝ), algebraMap ℚ FieldOneFiniteAdele q) = 0 := by
  change
    -(((q : ℝ)) : UnitAddCircle) +
      fieldOneFiniteAdeleStandardUnitAddCircleCharacter
        (algebraMap ℚ FieldOneFiniteAdele q) = 0
  rw [fieldOneFiniteAdeleStandardUnitAddCircleCharacter_algebraMap_rat]
  exact neg_add_cancel _

end

end GaloisForLFunctions.RHTower
