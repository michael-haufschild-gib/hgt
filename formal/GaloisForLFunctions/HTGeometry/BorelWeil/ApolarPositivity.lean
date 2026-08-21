/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.Apolarity
import GaloisForLFunctions.HTGeometry.BorelWeil.PolyRealization

/-!
# Positivity of the apolarity form on integral polynomials

The minor product `bwPoly` has integer coefficients: it is the image of the corresponding
polynomial over `ℤ`.  Over a field of characteristic zero the apolarity self-pairing of such a
polynomial is the image of `∑_a (coeff a)² · a!`, a strictly positive integer whenever the
polynomial is nonzero.  This supplies the one characteristic-zero input needed for complete
reducibility.

## Main results

* `bwPoly_map` — base change of the minor product from `ℤ`.
* `apolar_self_ne_zero_of_integral` — positivity of the self-pairing.
* `apolar_bwPoly_self_ne_zero`
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

theorem genericMatrix_map (f : ℤ →+* k) :
    (genericMatrix N ℤ).map (MvPolynomial.map f) = genericMatrix N k := by
  ext i j
  simp [genericMatrix, Matrix.map_apply]

theorem truncate_genericMatrix_map (j : ℕ) (f : ℤ →+* k) :
    (truncate j (genericMatrix N ℤ)).map (MvPolynomial.map f)
      = truncate j (genericMatrix N k) := by
  ext i i'
  by_cases h1 : (i : ℕ) < j
  · by_cases h2 : (i' : ℕ) < j
    · rw [Matrix.map_apply, truncate_apply_of_both h1 h2, truncate_apply_of_both h1 h2]
      simp [genericMatrix]
    · rw [Matrix.map_apply, truncate_apply_of_not_right h2, truncate_apply_of_not_right h2]
      by_cases h3 : i = i' <;> simp [h3]
  · rw [Matrix.map_apply, truncate_apply_of_not_left h1, truncate_apply_of_not_left h1]
    by_cases h3 : i = i' <;> simp [h3]

theorem minorPoly_map (j : ℕ) (f : ℤ →+* k) :
    MvPolynomial.map f (minorPoly j N ℤ) = minorPoly j N k := by
  rw [minorPoly, minorPoly, RingHom.map_det, ← truncate_genericMatrix_map j f]
  rfl

theorem bwPoly_map (m : Fin N → ℕ) (f : ℤ →+* k) :
    MvPolynomial.map f (bwPoly m ℤ) = bwPoly m k := by
  rw [bwPoly, bwPoly, map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [map_pow, minorPoly_map]

/-- The self-pairing of an integral polynomial is the image of a positive integer. -/
theorem apolar_self_ne_zero_of_integral [CharZero k] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : MvPolynomial σ ℤ) (hq : MvPolynomial.map (Int.castRingHom k) q ≠ 0) :
    apolar (MvPolynomial.map (Int.castRingHom k) q) (MvPolynomial.map (Int.castRingHom k) q)
      ≠ 0 := by
  classical
  have hinj : Function.Injective (Int.castRingHom k) := Int.cast_injective
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, map_zero] at hq
    exact hq rfl
  set S : ℤ := ∑ a ∈ q.support, (MvPolynomial.coeff a q) ^ 2 * (factD a : ℤ) with hS
  have hSpos : 0 < S := by
    obtain ⟨a₀, ha₀⟩ := MvPolynomial.support_nonempty.mpr hq0
    refine Finset.sum_pos' (fun a _ => ?_) ⟨a₀, ha₀, ?_⟩
    · exact mul_nonneg (sq_nonneg _) (Int.ofNat_nonneg _)
    · have : MvPolynomial.coeff a₀ q ≠ 0 := MvPolynomial.mem_support_iff.mp ha₀
      exact mul_pos (by positivity) (by exact_mod_cast factD_pos a₀)
  have hsupp : (MvPolynomial.map (Int.castRingHom k) q).support = q.support :=
    MvPolynomial.support_map_of_injective q hinj
  have hval : apolar (MvPolynomial.map (Int.castRingHom k) q)
      (MvPolynomial.map (Int.castRingHom k) q) = ((S : ℤ) : k) := by
    rw [apolar, hsupp, hS]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPolynomial.coeff_map, eq_intCast (Int.castRingHom k)]
    push_cast
    ring
  rw [hval]
  exact_mod_cast hSpos.ne'

theorem apolar_bwPoly_self_ne_zero [CharZero k] (m : Fin N → ℕ) :
    apolar (bwPoly m k) (bwPoly m k) ≠ 0 := by
  have hmap := bwPoly_map (k := k) m (Int.castRingHom k)
  have hne : MvPolynomial.map (Int.castRingHom k) (bwPoly m ℤ) ≠ 0 := by
    rw [hmap]
    intro h0
    have hval := congrArg (matEval (1 : Matrix (Fin N) (Fin N) k)) h0
    rw [matEval_one_bwPoly, matEval_zero] at hval
    exact one_ne_zero hval
  have := apolar_self_ne_zero_of_integral (k := k) (bwPoly m ℤ) hne
  rwa [hmap] at this

end GaloisForLFunctions.HTGeometry.BorelWeil
