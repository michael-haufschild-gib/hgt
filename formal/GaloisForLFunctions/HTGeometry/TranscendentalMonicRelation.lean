import GaloisForLFunctions.HTGeometry.BivariateSeparableResultant
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Perfect

/-!
# Monic separable relations over a transcendental coordinate

Let `d` be transcendental over `ℂ` in a field `K`.  If `g ∈ K` is algebraic over `ℂ(d)`, then
after multiplication by a nonzero `y(d)` it satisfies a monic relation `P(d, y(d) g) = 0` with
`P ∈ ℂ[T][W]` whose fibre discriminant `Res_W(P, ∂_W P) ∈ ℂ[T]` is a nonzero polynomial.

Denominators of the coefficients of a relation over `ℂ(d)` are cleared, an integral multiple is
taken, and `P` is its minimal polynomial over `ℂ[T]`; by Gauss's lemma `P` stays irreducible over
`ℂ(T)`, hence separable in characteristic zero.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped IntermediateField

noncomputable section

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- Evaluation of a two-variable polynomial at `(d, w)`. -/
def evalAt₂ (d : K) (P : ℂ[X][X]) (w : K) : K := (P.map (aeval d).toRingHom).eval w

/-- **Clearing denominators.** -/
theorem exists_poly_relation_of_isAlgebraic {d g : K} (hg : IsAlgebraic ℂ⟮d⟯ g) :
    ∃ Q : ℂ[X][X], Q ≠ 0 ∧ evalAt₂ d Q g = 0 := by
  classical
  obtain ⟨μ, hμ0, hμ⟩ := hg
  set n := μ.natDegree
  have hrep : ∀ i, ∃ r s : ℂ[X], ((μ.coeff i : ℂ⟮d⟯) : K) = aeval d r / aeval d s ∧
      aeval d s ≠ 0 := by
    intro i
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ
      ((μ.coeff i : ℂ⟮d⟯) : K)).mp (μ.coeff i).2
    by_cases hs : aeval d s = 0
    · refine ⟨0, 1, ?_, by simp⟩
      rw [hrs, hs, div_zero, map_zero, zero_div]
    · exact ⟨r, s, hrs, hs⟩
  choose r s hrs hs0 using hrep
  set S : ℂ[X] := ∏ j ∈ Finset.range (n + 1), s j
  have hS0 : aeval d S ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hs0 j
  set Q : ℂ[X][X] := ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (r i * ∏ j ∈ (Finset.range (n + 1)).erase i, s j) * Polynomial.X ^ i
  have hcoeff : ∀ i ∈ Finset.range (n + 1),
      aeval d (r i * ∏ j ∈ (Finset.range (n + 1)).erase i, s j) =
        ((μ.coeff i : ℂ⟮d⟯) : K) * aeval d S := by
    intro i hi
    have hS : S = s i * ∏ j ∈ (Finset.range (n + 1)).erase i, s j :=
      (Finset.mul_prod_erase _ s hi).symm
    rw [map_mul, hrs i, hS, map_mul]
    field_simp [hs0 i]
  have hμsum : (aeval g μ : K) =
      ∑ i ∈ Finset.range (n + 1), ((μ.coeff i : ℂ⟮d⟯) : K) * g ^ i := by
    rw [aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
    rfl
  have hevalQ : evalAt₂ d Q g = aeval d S * (aeval g μ : K) := by
    rw [hμsum, Finset.mul_sum, evalAt₂, Polynomial.map_sum, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    change aeval d _ * g ^ i = _
    rw [hcoeff i hi]
    ring
  refine ⟨Q, ?_, by rw [hevalQ, hμ, mul_zero]⟩
  intro hQ
  have hn : Q.coeff n = r n * ∏ j ∈ (Finset.range (n + 1)).erase n, s j := by
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.self_mem_range_succ n) h
  have hlead := hcoeff n (Finset.self_mem_range_succ n)
  rw [← hn, hQ, Polynomial.coeff_zero, map_zero] at hlead
  have hμn : ((μ.coeff n : ℂ⟮d⟯) : K) ≠ 0 := by
    have : μ.coeff n ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hμ0
    exact_mod_cast this
  exact mul_ne_zero hμn hS0 hlead.symm

/-- **Monic separable relation.** -/
theorem exists_monic_separable_relation {d g : K} (hd : Transcendental ℂ d)
    (hg : IsAlgebraic ℂ⟮d⟯ g) :
    ∃ (y : ℂ[X]) (P : ℂ[X][X]), aeval d y ≠ 0 ∧ P.Monic ∧ 0 < P.natDegree ∧
      biResultant P ≠ 0 ∧ evalAt₂ d P (aeval d y * g) = 0 := by
  classical
  letI : Algebra ℂ[X] K := (aeval d).toRingHom.toAlgebra
  have hinj : Function.Injective (algebraMap ℂ[X] K) := transcendental_iff_injective.mp hd
  obtain ⟨Q, hQ0, hQ⟩ := exists_poly_relation_of_isAlgebraic hg
  have halg : IsAlgebraic ℂ[X] g := ⟨Q, hQ0, by
    rw [aeval_def, eval₂_eq_eval_map]; exact hQ⟩
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  set P := minpoly ℂ[X] (y • g)
  have hmonic : P.Monic := minpoly.monic hyint
  have hdeg : 0 < P.natDegree := minpoly.natDegree_pos hyint
  have hirr : Irreducible P := minpoly.irreducible hyint
  have hsmul : y • g = aeval d y * g := Algebra.smul_def y g
  refine ⟨y, P, fun h => hy0 (hinj (by rw [map_zero]; exact h)), hmonic, hdeg, ?_, ?_⟩
  · -- separability over the fraction field
    have hprim : P.IsPrimitive := hmonic.isPrimitive
    have hirrK : Irreducible (P.map (algebraMap ℂ[X] (RatFunc ℂ))) :=
      (hprim.irreducible_iff_irreducible_map_fraction_map).mp hirr
    have hsepK : (P.map (algebraMap ℂ[X] (RatFunc ℂ))).Separable :=
      PerfectField.separable_of_irreducible hirrK
    have hmonK : (P.map (algebraMap ℂ[X] (RatFunc ℂ))).Monic := hmonic.map _
    have hres := (separable_iff_resultant_ne_zero hmonK).mp hsepK
    intro h0
    apply hres
    rw [hmonic.natDegree_map, Polynomial.derivative_map, Polynomial.resultant_map_map]
    change algebraMap ℂ[X] (RatFunc ℂ) (biResultant P) = 0
    rw [h0, map_zero]
  · have h := minpoly.aeval ℂ[X] (y • g)
    rw [aeval_def, eval₂_eq_eval_map, hsmul] at h
    exact h

end

end GaloisForLFunctions.HTGeometry
