import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# The derivative gcd measures multiplicity

Over an algebraically closed field of characteristic zero the greatest common divisor of a nonzero
polynomial and its derivative has root multiplicity one less than the polynomial at every point.
Summing over the divisor gives

`deg gcd (W, W') + #{distinct roots of W} = deg W`,

so the complementary degree is exactly the distinct-root census.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]

omit [IsAlgClosed K] in
/-- Root multiplicity of the derivative gcd is one less than that of the polynomial. -/
theorem rootMultiplicity_gcd_derivative (W : K[X]) (hW : W ≠ 0) (a : K) :
    rootMultiplicity a (EuclideanDomain.gcd W (derivative W)) = rootMultiplicity a W - 1 := by
  classical
  set g := EuclideanDomain.gcd W (derivative W) with hg
  have hg0 : g ≠ 0 := by
    intro h
    rw [hg, EuclideanDomain.gcd_eq_zero_iff] at h
    exact hW h.1
  set m := rootMultiplicity a W with hm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have hzero : rootMultiplicity a g = 0 := by
      by_contra hne
      have hroot : g.IsRoot a := (rootMultiplicity_pos hg0).1 (Nat.pos_of_ne_zero hne)
      have hdvd : (X - C a) ∣ W :=
        ((dvd_iff_isRoot).2 hroot).trans (EuclideanDomain.gcd_dvd_left _ _)
      have : W.IsRoot a := (dvd_iff_isRoot).1 hdvd
      have := (rootMultiplicity_pos hW).2 this
      omega
    omega
  · have hroot : W.IsRoot a := (rootMultiplicity_pos hW).1 hmpos
    have hd : derivative W ≠ 0 := by
      intro hd0
      have hdeg : W.natDegree = 0 := Polynomial.derivative_eq_zero.mp hd0
      have hWC : W = C (W.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hcoeff : W.coeff 0 = 0 := by
        have := hroot
        rw [Polynomial.IsRoot, hWC] at this
        simpa using this
      rw [hWC, hcoeff] at hW
      simp at hW
    have hderiv : rootMultiplicity a (derivative W) = m - 1 :=
      derivative_rootMultiplicity_of_root hroot
    have hle : rootMultiplicity a g ≤ m - 1 := by
      rw [← hderiv]
      exact (le_rootMultiplicity_iff hd).2
        ((pow_rootMultiplicity_dvd g a).trans (EuclideanDomain.gcd_dvd_right W (derivative W)))
    have hge : m - 1 ≤ rootMultiplicity a g := by
      have hdvdW : (X - C a) ^ (m - 1) ∣ W :=
        dvd_trans (pow_dvd_pow _ (Nat.sub_le m 1)) (pow_rootMultiplicity_dvd W a)
      have hdvdD : (X - C a) ^ (m - 1) ∣ derivative W := by
        rw [← hderiv]; exact pow_rootMultiplicity_dvd _ _
      exact (le_rootMultiplicity_iff hg0).2 (EuclideanDomain.dvd_gcd hdvdW hdvdD)
    omega

omit [CharZero K] [IsAlgClosed K] in
/-- The distinct roots of the derivative gcd are among those of the polynomial. -/
theorem roots_toFinset_gcd_derivative_subset (W : K[X]) (hW : W ≠ 0) :
    (EuclideanDomain.gcd W (derivative W)).roots.toFinset ⊆ W.roots.toFinset := by
  classical
  intro a ha
  have hg0 : EuclideanDomain.gcd W (derivative W) ≠ 0 := by
    intro h
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    exact hW h.1
  rw [Multiset.mem_toFinset, mem_roots hg0] at ha
  rw [Multiset.mem_toFinset, mem_roots hW]
  exact (dvd_iff_isRoot).1 (((dvd_iff_isRoot).2 ha).trans (EuclideanDomain.gcd_dvd_left _ _))

omit [CharZero K] in
/-- Degree as the total multiplicity over the distinct root set. -/
theorem natDegree_eq_sum_rootMultiplicity (p : K[X]) (_hp : p ≠ 0) :
    p.natDegree = ∑ a ∈ p.roots.toFinset, rootMultiplicity a p := by
  classical
  have hsplit : p.Splits := IsAlgClosed.splits p
  rw [hsplit.natDegree_eq_card_roots, ← Multiset.toFinset_sum_count_eq p.roots]
  exact Finset.sum_congr rfl fun a _ => count_roots p

/-- **The derivative gcd degree is complementary to the distinct-root census.** -/
theorem natDegree_gcd_derivative_add_card_roots (W : K[X]) (hW : W ≠ 0) :
    (EuclideanDomain.gcd W (derivative W)).natDegree + W.roots.toFinset.card =
      W.natDegree := by
  classical
  set g := EuclideanDomain.gcd W (derivative W) with hg
  have hg0 : g ≠ 0 := by
    intro h
    rw [hg, EuclideanDomain.gcd_eq_zero_iff] at h
    exact hW h.1
  have hgsum : g.natDegree = ∑ a ∈ W.roots.toFinset, rootMultiplicity a g := by
    rw [natDegree_eq_sum_rootMultiplicity g hg0]
    refine Finset.sum_subset (roots_toFinset_gcd_derivative_subset W hW) ?_
    intro a _ hna
    by_contra hne
    exact hna (Multiset.mem_toFinset.2 ((mem_roots hg0).2
      ((rootMultiplicity_pos hg0).1 (Nat.pos_of_ne_zero hne))))
  have hstep : ∀ a ∈ W.roots.toFinset, rootMultiplicity a g + 1 = rootMultiplicity a W := by
    intro a ha
    have hpos : 0 < rootMultiplicity a W :=
      (rootMultiplicity_pos hW).2 ((mem_roots hW).1 (Multiset.mem_toFinset.1 ha))
    have hmult := rootMultiplicity_gcd_derivative W hW a
    rw [← hg] at hmult
    omega
  have hsum : ∑ a ∈ W.roots.toFinset, (rootMultiplicity a g + 1) =
      ∑ a ∈ W.roots.toFinset, rootMultiplicity a W :=
    Finset.sum_congr rfl hstep
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [hgsum, hsum, ← natDegree_eq_sum_rootMultiplicity W hW]

/-- The distinct-root census as a complementary degree. -/
theorem card_roots_toFinset_eq_natDegree_sub_gcd (W : K[X]) (hW : W ≠ 0) :
    W.roots.toFinset.card =
      W.natDegree - (EuclideanDomain.gcd W (derivative W)).natDegree := by
  have := natDegree_gcd_derivative_add_card_roots W hW
  omega

end GaloisForLFunctions.HTGeometry
