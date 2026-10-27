import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit

/-!
# The archimedean intersection is a log-order

The torsion orbits `O_n` and `O_m` are the horizontal divisors `Φ_n = 0` and `Φ_m = 0` of `𝔾_m`
over `ℤ`. Their intersection scheme is `Spec ℤ[ζ_n]/(Φ_m(ζ_n))`, a finite ring. Its order is the
norm of `Φ_m(ζ_n)`, and the norm is the product over the complex embeddings, i.e. over the points of
`O_n`, of `Φ_m(η) = ∏_{ξ ∈ O_m} (η − ξ)`. Hence (`log_card_quotient_cyclotomicValue`), for `m ≠ n`,

    log #(𝓞_{ℚ(ζ_n)} / (Φ_m(ζ_n))) = Σ_{η ∈ O_n, ξ ∈ O_m} log |η − ξ| = I(n, m):

the archimedean intersection number of AET is the logarithm of the order of the finite
intersection. This is the product formula for torsion divisors, and it is where integers enter the
prime side: every entry of Weil's prime kernel is the log-order of a finite ring.

With the arithmetic point `O_1 = {1}` (`log_card_quotient_zeta_sub_one`):

    Λ(n) = log #(𝓞_{ℚ(ζ_n)} / (ζ_n − 1)),

the von Mangoldt function is the log-order of the residue ring of `1 − ζ_n`: `p` when `n` is a power
of `p`, and `1` (a unit) otherwise.

The diagonal is the discriminant (`orbitIntersection_self_eq_log_discr`): for a prime power,

    I(p^k, p^k) = log |d_{ℚ(ζ_{p^k})}|,

the arithmetic degree of the relative dualizing sheaf of `𝓞_{ℚ(ζ_{p^k})}` over `ℤ`. The self-intersection
of a torsion orbit is the canonical degree of its cyclotomic field: adjunction on the circle.
-/

noncomputable section

open Polynomial NumberField Finset

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

variable (n : ℕ) [NeZero n]

/-- `ℚ(ζ_n)` is the `n`-th cyclotomic extension of `ℚ` (stated explicitly for instance search). -/
private theorem isCyclotomicExtension_rat : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.isCyclotomicExtension n ℚ

attribute [local instance] isCyclotomicExtension_rat

/-- The primitive root `ζ_n` of `ℚ(ζ_n)`. -/
abbrev zetaN : CyclotomicField n ℚ := IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)

theorem zetaN_spec : IsPrimitiveRoot (zetaN n) n :=
  IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)

/-- `Φ_m(ζ_n)` as an algebraic integer of `ℚ(ζ_n)`: the equation of the intersection of `O_n`
with `O_m`. -/
def cyclotomicValue (m : ℕ) : 𝓞 (CyclotomicField n ℚ) :=
  aeval (zetaN_spec n).toInteger (cyclotomic m ℤ)

theorem coe_cyclotomicValue (m : ℕ) :
    (cyclotomicValue n m : CyclotomicField n ℚ) = aeval (zetaN n) (cyclotomic m ℚ) := by
  rw [← map_cyclotomic_int m ℚ, aeval_def, eval₂_map,
    show (algebraMap ℚ (CyclotomicField n ℚ)).comp (Int.castRingHom ℚ) =
      algebraMap ℤ (CyclotomicField n ℚ) from RingHom.ext_int _ _, ← aeval_def]
  have hz : zetaN n = (algebraMap (𝓞 (CyclotomicField n ℚ)) (CyclotomicField n ℚ)).toIntAlgHom
      (zetaN_spec n).toInteger := rfl
  rw [hz, aeval_algHom_apply]
  rfl

/-- Under a complex embedding `σ`, `σ(Φ_m(ζ_n)) = ∏_{ξ ∈ O_m} (σ ζ_n − ξ)`. -/
theorem embedding_cyclotomicValue {m : ℕ} (hm : 0 < m) (σ : CyclotomicField n ℚ →ₐ[ℚ] ℂ) :
    σ (cyclotomicValue n m : CyclotomicField n ℚ) =
      ∏ ξ ∈ primitiveRoots m ℂ, (σ (zetaN n) - ξ) := by
  rw [coe_cyclotomicValue, ← aeval_algHom_apply, aeval_def, eval₂_eq_eval_map, map_cyclotomic,
    cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp m hm.ne'), eval_prod]
  simp only [eval_sub, eval_X, eval_C]

/-- **The archimedean intersection is a log-order.** For `m ≠ n`,
`log #(𝓞_{ℚ(ζ_n)}/(Φ_m(ζ_n))) = Σ_{η ∈ O_n} Σ_{ξ ∈ O_m} log |η − ξ| = I(n, m)`. -/
theorem log_card_quotient_cyclotomicValue {m : ℕ} (hm : 0 < m) (hmn : m ≠ n) :
    Real.log (Nat.card (𝓞 (CyclotomicField n ℚ) ⧸ Ideal.span {cyclotomicValue n m})) =
      orbitIntersection n m := by
  set L := CyclotomicField n ℚ
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat hn
  -- the order of the quotient is the absolute norm
  have hcard : (Nat.card (𝓞 L ⧸ Ideal.span {cyclotomicValue n m}) : ℝ) =
      |((Algebra.norm ℚ (cyclotomicValue n m : L) : ℚ) : ℝ)| := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
      Nat.cast_natAbs, ← Algebra.coe_norm_int]
    push_cast
    rfl
  -- the norm is the product over the complex embeddings, i.e. over `O_n`
  have hprod : ((Algebra.norm ℚ (cyclotomicValue n m : L) : ℚ) : ℂ) =
      ∏ η ∈ primitiveRoots n ℂ, ∏ ξ ∈ primitiveRoots m ℂ, (η - ξ) := by
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ (cyclotomicValue n m : L)
    rw [eq_ratCast] at h
    rw [h]
    simp only [embedding_cyclotomicValue n hm]
    rw [← prod_coe_sort (primitiveRoots n ℂ)]
    exact Fintype.prod_equiv ((zetaN_spec n).embeddingsEquivPrimitiveRoots ℂ hirr)
      (fun σ => ∏ ξ ∈ primitiveRoots m ℂ, (σ (zetaN n) - ξ))
      (fun η => ∏ ξ ∈ primitiveRoots m ℂ, ((η : ℂ) - ξ))
      (fun σ => by rw [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe])
  have hne : ∀ η ∈ primitiveRoots n ℂ, ∀ ξ ∈ primitiveRoots m ℂ, ‖η - ξ‖ ≠ 0 := by
    intro η hη ξ hξ h0
    rw [norm_eq_zero, sub_eq_zero] at h0
    subst h0
    exact hmn (((mem_primitiveRoots hm).mp hξ).unique ((mem_primitiveRoots hn).mp hη))
  have habs : |((Algebra.norm ℚ (cyclotomicValue n m : L) : ℚ) : ℝ)| =
      ‖((Algebra.norm ℚ (cyclotomicValue n m : L) : ℚ) : ℂ)‖ := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [hcard, habs, hprod, norm_prod]
  simp_rw [norm_prod]
  rw [Real.log_prod fun η hη => (prod_pos fun ξ hξ => (norm_nonneg _).lt_of_ne
    (hne η hη ξ hξ).symm).ne', orbitIntersection]
  refine sum_congr rfl fun η hη => ?_
  rw [Real.log_prod fun ξ hξ => hne η hη ξ hξ]

/-- `Φ_1(ζ_n) = ζ_n − 1`. -/
theorem coe_cyclotomicValue_one :
    (cyclotomicValue n 1 : CyclotomicField n ℚ) = zetaN n - 1 := by
  rw [coe_cyclotomicValue, cyclotomic_one]
  simp

/-- **The von Mangoldt function is a log-order**: for `n ≥ 2`,
`Λ(n) = log #(𝓞_{ℚ(ζ_n)}/(Φ_1(ζ_n)))`, the order of the residue ring of `ζ_n − 1`. -/
theorem log_card_quotient_zeta_sub_one (hn : 2 ≤ n) :
    Real.log (Nat.card (𝓞 (CyclotomicField n ℚ) ⧸ Ideal.span {cyclotomicValue n 1})) =
      ArithmeticFunction.vonMangoldt n := by
  rw [log_card_quotient_cyclotomicValue n one_pos (by omega), orbitIntersection_comm]
  have h := orbitIntersection_hecke (m := 1) one_pos (show 1 < n by omega)
  simpa using h

/-! ### The diagonal is the discriminant -/

/-- **Adjunction on the circle**: the self-intersection of `O_{p^k}` is the logarithm of the absolute
discriminant of `ℚ(ζ_{p^k})`. -/
theorem orbitIntersection_self_eq_log_discr (p k : ℕ) [hp : Fact p.Prime] (hk : 0 < k) :
    orbitIntersection (p ^ k) (p ^ k) =
      Real.log |(NumberField.discr (CyclotomicField (p ^ k) ℚ) : ℝ)| := by
  have hpp := hp.out
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hpp.ne_zero⟩
  have hdisc := IsCyclotomicExtension.Rat.discr_prime_pow p k (CyclotomicField (p ^ k) ℚ)
  have hpk : 0 < p ^ k := pow_pos hpp.pos k
  have hφ : (0 : ℝ) < Nat.totient (p ^ k) := by exact_mod_cast Nat.totient_pos.mpr hpk
  -- the left side: `φ(p^k) · (k log p − log p/(p − 1))`
  have hL : orbitIntersection (p ^ k) (p ^ k) = Nat.totient (p ^ k) * selfIntersection (p ^ k) := by
    rw [selfIntersection]; field_simp
  rw [hL, selfIntersection_eq hpk, tameDifferent_prime_pow hpp hk.ne', Nat.cast_pow,
    Real.log_pow, Nat.totient_prime_pow hpp hk]
  -- the right side: `p^{k−1}((p − 1)k − 1) log p`
  rw [hdisc]
  push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, Nat.abs_cast, Real.log_pow]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hk1 : 1 ≤ (p - 1) * k := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := hpp.two_le; omega) hk.ne')
  have hcast : ((p ^ (k - 1) * ((p - 1) * k - 1) : ℕ) : ℝ) =
      (p : ℝ) ^ (k - 1) * (((p : ℝ) - 1) * k - 1) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk1, Nat.cast_mul, Nat.cast_sub hpp.one_le]
    push_cast; ring
  rw [hcast, Nat.cast_sub hpp.one_le, Nat.cast_one]
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

end GaloisForLFunctions.ArithmeticIntersectionTheory
