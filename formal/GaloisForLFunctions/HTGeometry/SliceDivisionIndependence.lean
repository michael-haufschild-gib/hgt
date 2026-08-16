import GaloisForLFunctions.HTGeometry.WeierstrassDivisionUniqueness
import GaloisForLFunctions.HTGeometry.SliceWeierstrassFactorization
import GaloisForLFunctions.HTGeometry.DistinguishedRootShrink

/-!
# Independence of the low-degree part in a Weierstrass division

On a disc containing all the roots of the Weierstrass polynomial of a slice, a relation

`Q(z)·W(z) + ∑_{j<d} B_j z^j = 0`

with `Q` continuous forces every `B_j` to vanish, and then `Q` itself to vanish.  This is the
independence half of the free-module statement: the powers `1, z, …, z^{d-1}` are independent over
the parameter ring modulo the Weierstrass polynomial.

The first half is the low-degree vanishing theorem — a polynomial of degree below the number of
roots that is a continuous multiple of the monic polynomial of those roots is zero — and the second
is that a nonzero polynomial has finitely many zeros, so a continuous function killed by it off a
finite set is killed everywhere.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Metric Filter
open _root_.HTGeometry (multisetLinearProd)
open scoped Topology

/-- The low-degree polynomial assembled from a coefficient sequence. -/
noncomputable def lowDegreePoly {R : Type*} [CommRing R] (B : ℕ → R) (d : ℕ) : Polynomial R :=
  ∑ j ∈ Finset.range d, Polynomial.monomial j (B j)

theorem lowDegreePoly_coeff {R : Type*} [CommRing R] (B : ℕ → R) (d m : ℕ) :
    (lowDegreePoly B d).coeff m = if m < d then B m else 0 := by
  classical
  rw [lowDegreePoly, finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases hm : m < d
  · rw [if_pos hm, Finset.sum_eq_single m]
    · simp
    · intro j _ hj
      exact if_neg (fun h => hj h)
    · intro h
      exact absurd (Finset.mem_range.mpr hm) h
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun j hj => ?_
    refine if_neg ?_
    intro h
    subst h
    exact hm (Finset.mem_range.mp hj)

theorem degree_lowDegreePoly_lt {R : Type*} [CommRing R] (B : ℕ → R) (d : ℕ) :
    (lowDegreePoly B d).degree < (d : ℕ) := by
  refine degree_lt_iff_coeff_zero _ _ |>.mpr ?_
  intro m hm
  rw [lowDegreePoly_coeff]
  refine if_neg ?_
  intro h
  exact absurd (by exact_mod_cast hm : (d : ℕ) ≤ m) (by omega)

theorem eval_lowDegreePoly {R : Type*} [CommRing R] (B : ℕ → R) (d : ℕ) (z : R) :
    (lowDegreePoly B d).eval z = ∑ j ∈ Finset.range d, B j * z ^ j := by
  rw [lowDegreePoly, eval_finsetSum]
  exact Finset.sum_congr rfl fun j _ => by rw [eval_monomial]

theorem eval_multisetProd_eq_multisetLinearProd (M : Multiset ℂ) (z : ℂ) :
    ((M.map fun r => Polynomial.X - Polynomial.C r).prod).eval z = multisetLinearProd M z := by
  rw [eval_multiset_prod, Multiset.map_map, multisetLinearProd]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun r _ => ?_)
  simp

/-- **Independence of the low-degree part.**  On a disc containing every root of the monic
polynomial of a multiset, a continuous multiple of that polynomial plus a polynomial of degree below
the number of roots vanishes only trivially. -/
theorem lowDegree_and_quotient_eq_zero {ρs : Multiset ℂ} {t₁ : ℝ}
    (hsmall : ∀ ρ ∈ ρs, ‖ρ‖ < t₁) {Q : ℂ → ℂ} (hQ : ContinuousOn Q (ball (0 : ℂ) t₁))
    {B : ℕ → ℂ} {d : ℕ} (hd : d = Multiset.card ρs)
    (hrel : ∀ z ∈ ball (0 : ℂ) t₁,
      Q z * multisetLinearProd ρs z + ∑ j ∈ Finset.range d, B j * z ^ j = 0) :
    (∀ j, j < d → B j = 0) ∧ ∀ z ∈ ball (0 : ℂ) t₁, Q z = 0 := by
  classical
  set W : Polynomial ℂ := (ρs.map fun r => Polynomial.X - Polynomial.C r).prod with hW
  have hdeg : (lowDegreePoly B d).degree < (Multiset.card ρs : ℕ) := by
    rw [← hd]
    exact degree_lowDegreePoly_lt B d
  have hmul : ∀ z ∈ ball (0 : ℂ) t₁,
      (lowDegreePoly B d).eval z = (-Q z) * W.eval z := by
    intro z hz
    rw [eval_lowDegreePoly, hW, eval_multisetProd_eq_multisetLinearProd]
    have := hrel z hz
    linear_combination this
  have hP : lowDegreePoly B d = 0 :=
    eq_zero_of_degree_lt_of_continuous_multiple ρs hsmall (lowDegreePoly B d) hdeg
      (fun z => -Q z) (hQ.neg) hmul
  have hB : ∀ j, j < d → B j = 0 := by
    intro j hj
    have := congrArg (fun p : Polynomial ℂ => p.coeff j) hP
    simp only [lowDegreePoly_coeff, coeff_zero, if_pos hj] at this
    exact this
  refine ⟨hB, ?_⟩
  -- with the low-degree part gone, the quotient is killed off the finite root set
  have hWne : W ≠ 0 := by
    rw [hW]
    refine Multiset.prod_ne_zero ?_
    intro hmem
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp hmem
    exact Polynomial.X_sub_C_ne_zero r hr
  have hfin : {z : ℂ | W.eval z = 0}.Finite := by
    refine Set.Finite.subset (W.roots.toFinset.finite_toSet) ?_
    intro z hz
    simp only [Multiset.mem_toFinset, Finset.mem_coe]
    exact (mem_roots hWne).mpr hz
  intro z hz
  refine eqOn_of_continuousOn_of_finite_diff isOpen_ball hQ continuousOn_const hfin ?_ hz
  intro w hw hwF
  have hWw : W.eval w ≠ 0 := hwF
  have hrelw := hrel w hw
  have hzero : ∑ j ∈ Finset.range d, B j * w ^ j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hB j (Finset.mem_range.mp hj), zero_mul]
  rw [hzero, add_zero] at hrelw
  have hWeval : multisetLinearProd ρs w = W.eval w := by
    rw [hW, eval_multisetProd_eq_multisetLinearProd]
  rw [hWeval] at hrelw
  exact (mul_eq_zero.mp hrelw).resolve_right hWw

end GaloisForLFunctions.HTGeometry
