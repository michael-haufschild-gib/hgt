import GaloisForLFunctions.HTGeometry.AlgebraicPrimitiveDescent
import GaloisForLFunctions.HTGeometry.MultiplicativeShiftIndependence

/-!
# Rigidity of first-order shift relations over an endomorphism base

Let `L` be a field carrying a ring endomorphism `σ` which restricts along `K → L` to a ring
endomorphism `ψ` of the base, and assume the `σ`-invariants of `L` all come from `K`.

Two rigidity statements govern the first-order relations `σ w = w + c` and `σ z = a · z`.

* **Additive rigidity.**  A solution of `σ w = w + c` with `c` in the base which is *algebraic*
  over the base already *lies* in the base.  Mapping the minimal polynomial by `ψ` and translating
  the variable by `c` produces a monic polynomial of the same degree annihilating `w`, hence the
  minimal polynomial itself; comparison of second-highest coefficients makes
  `w + nextCoeff/natDegree` invariant.  Unlike the corpus's automorphism version this needs no
  surjectivity of `ψ`: divisibility of the minimal polynomial replaces irreducibility of its image.

* **Multiplicative rigidity.**  Two solutions of `σ zᵢ = aᵢ · zᵢ` which are algebraically dependent
  over the base admit a nonzero integer vector `m` with `z₁ ^ m₁ · z₂ ^ m₂` in the base.  This is
  the contrapositive of the corpus's minimal-support descent, combined with invariance of the
  monomial divided by the coboundary witness.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Evaluating a `ψ`-mapped polynomial at `σ w` is `σ` of the evaluation at `w`. -/
theorem aeval_shift_map (σ : L →+* L) (ψ : K →+* K)
    (hcomp : ∀ a : K, σ (algebraMap K L a) = algebraMap K L (ψ a)) (w : L) (p : K[X]) :
    aeval (σ w) (p.map ψ) = σ (aeval w p) := by
  have hhom : (algebraMap K L).comp ψ = (σ : L →+* L).comp (algebraMap K L) := by
    ext a
    simpa using (hcomp a).symm
  rw [aeval_def, eval₂_map, aeval_def, hom_eval₂, hhom]

/-- **Additive rigidity of a first-order shift relation.**  An algebraic solution of
`σ w = w + c` with `c` in the base lies in the base. -/
theorem exists_algebraMap_eq_of_isIntegral_of_shift_add [CharZero K]
    (σ : L →+* L) (ψ : K →+* K)
    (hcomp : ∀ a : K, σ (algebraMap K L a) = algebraMap K L (ψ a))
    (hfix : ∀ y : L, σ y = y → ∃ a : K, algebraMap K L a = y)
    {w : L} {c : K} (hw : σ w = w + algebraMap K L c) (hint : IsIntegral K w) :
    ∃ a : K, algebraMap K L a = w := by
  classical
  set P : K[X] := minpoly K w with hP
  have hPm : P.Monic := minpoly.monic hint
  have hPpos : 0 < P.natDegree := (minpoly.irreducible hint).natDegree_pos
  have hψinj : Function.Injective ψ := ψ.injective
  have hmapm : (P.map ψ).Monic := hPm.map ψ
  have hmapdeg : (P.map ψ).natDegree = P.natDegree := natDegree_map_eq_of_injective hψinj P
  set Q : K[X] := Polynomial.taylor c (P.map ψ) with hQ
  have hQeq : Q = (P.map ψ).comp (X + C c) := by rw [hQ, taylor_apply]
  have hQm : Q.Monic := by rw [hQeq]; exact hmapm.comp_X_add_C c
  have hQdeg : Q.natDegree = P.natDegree := by
    rw [hQ, natDegree_taylor, hmapdeg]
  have hQroot : aeval w Q = 0 := by
    rw [hQeq, aeval_comp]
    have hval : aeval w (X + C c : K[X]) = σ w := by
      rw [hw]; simp
    rw [hval, aeval_shift_map σ ψ hcomp w P, minpoly.aeval K w, map_zero]
  have hdvd : P ∣ Q := minpoly.dvd _ _ hQroot
  have hQP : Q = P := eq_of_monic_of_dvd_of_natDegree_le hPm hQm hdvd (le_of_eq hQdeg)
  -- compare the second-highest coefficients
  have hnext : P.nextCoeff = ψ P.nextCoeff + (P.natDegree : K) * c := by
    have h1 : Q.nextCoeff = (P.map ψ).nextCoeff + ((P.map ψ).natDegree : K) * c := by
      rw [hQ]
      exact GaloisForLFunctions.nextCoeff_taylor_of_monic (P.map ψ) hmapm
        (by rw [hmapdeg]; exact hPpos) c
    rw [hQP, nextCoeff_map hψinj, hmapdeg] at h1
    exact h1
  set t : K := P.nextCoeff / (P.natDegree : K) with ht
  have hn0 : ((P.natDegree : K)) ≠ 0 := Nat.cast_ne_zero.mpr hPpos.ne'
  have hψt : ψ t = t - c := by
    have h : ψ P.nextCoeff = P.nextCoeff - (P.natDegree : K) * c := by
      linear_combination -hnext
    rw [ht, map_div₀, map_natCast, h]
    field_simp
  have hfixw : σ (w + algebraMap K L t) = w + algebraMap K L t := by
    rw [map_add, hw, hcomp, hψt, map_sub]
    ring
  obtain ⟨a, ha⟩ := hfix _ hfixw
  refine ⟨a - t, ?_⟩
  rw [map_sub, ha]
  ring

/-- **Multiplicative rigidity of first-order shift relations.**  Algebraically dependent
multiplicative shift coordinates admit a nonzero integer monomial lying in the base. -/
theorem exists_algebraMap_eq_zpow_prod_of_not_algebraicIndependent
    (σ : L →+* L) (ψ : K →+* K)
    (hcomp : ∀ a : K, σ (algebraMap K L a) = algebraMap K L (ψ a))
    (hfix : ∀ y : L, σ y = y → ∃ a : K, algebraMap K L a = y)
    {r : ℕ} (y : Fin r → L) (q : Fin r → K) (hy : ∀ i, y i ≠ 0) (hq : ∀ i, q i ≠ 0)
    (hshift : ∀ i, σ (y i) = algebraMap K L (q i) * y i)
    (hdep : ¬ AlgebraicIndependent K y) :
    ∃ m : Fin r → ℤ, m ≠ 0 ∧ ∃ a : K, algebraMap K L a = ∏ i, (y i) ^ (m i) := by
  classical
  have hcob : ¬ (∀ (u : K) (m : Fin r → ℤ), u ≠ 0 → m ≠ 0 →
      ψ u ≠ u * ∏ i : Fin r, q i ^ (m i)) := by
    intro h
    exact hdep (algebraicIndependent_of_multiplicativeShift σ ψ ψ.injective hcomp y q hy hq
      hshift h)
  rw [not_forall] at hcob
  push Not at hcob
  obtain ⟨u, m, hu, hm, hrel⟩ := hcob
  refine ⟨m, hm, ?_⟩
  set W : L := ∏ i, (y i) ^ (m i) with hW
  have hqprod : (∏ i : Fin r, q i ^ (m i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hq i)
  have hW0 : W ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hy i)
  have hσW : σ W = algebraMap K L (∏ i : Fin r, q i ^ (m i)) * W := by
    rw [hW, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀, hshift, mul_zpow, map_zpow₀]
  have huL : algebraMap K L u ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hu
  have hA : algebraMap K L (∏ i : Fin r, q i ^ (m i)) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hqprod
  have hfixed : σ (W / algebraMap K L u) = W / algebraMap K L u := by
    rw [map_div₀, hσW, hcomp, hrel, map_mul, mul_comm (algebraMap K L u)]
    exact mul_div_mul_left W (algebraMap K L u) hA
  obtain ⟨a, ha⟩ := hfix _ hfixed
  refine ⟨a * u, ?_⟩
  rw [map_mul, ha, div_mul_cancel₀ W huL]

end GaloisForLFunctions.HTGeometry
