/-
# Periodic point avoidance for the hRigid finite-count route

Focused counting bricks for replacing the stale "fixed-period accumulating target set" interface by
finite bad-locus avoidance among the roots of `f_c^[p] - X`.
-/
import GaloisForLFunctions.Bottcher.IndexResonance

open Polynomial

namespace Bottcher

/-- If the fixed-point polynomial has more roots than a finite bad set, one fixed point avoids it. -/
theorem exists_fixedPointPoly_root_notMem_finset (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable) (B : Finset ℂ) (hBcard : B.card < 2 ^ p) :
    ∃ z, z ∈ (fixedPointPoly c p).roots.toFinset ∧ z ∉ B := by
  classical
  by_contra h
  have hsub : (fixedPointPoly c p).roots.toFinset ⊆ B := by
    intro z hz
    by_contra hzB
    exact h ⟨z, hz, hzB⟩
  have hcard_le : (fixedPointPoly c p).roots.toFinset.card ≤ B.card := Finset.card_le_card hsub
  rw [fixedPointPoly_roots_card c hp hsep] at hcard_le
  omega

/-- Fixed-point avoidance, stated dynamically rather than as root membership. -/
theorem exists_periodic_point_notMem_finset (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable) (B : Finset ℂ) (hBcard : B.card < 2 ^ p) :
    ∃ z, (quadratic c)^[p] z = z ∧ z ∉ B := by
  classical
  obtain ⟨z, hzroot, hzB⟩ := exists_fixedPointPoly_root_notMem_finset c hp hsep B hBcard
  refine ⟨z, ?_, hzB⟩
  rw [← fixedPointPoly_isRoot_iff]
  exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hzroot)

/-- The union of the zero sets of two polynomials has size at most the sum of their degrees. -/
theorem roots_union_card_le_natDegree_add (e q : Polynomial ℂ) :
    (e.roots.toFinset ∪ q.roots.toFinset).card ≤ e.natDegree + q.natDegree := by
  classical
  have hecard : e.roots.toFinset.card ≤ e.natDegree := by
    exact le_trans (Multiset.toFinset_card_le _) (card_roots' e)
  have hqcard : q.roots.toFinset.card ≤ q.natDegree := by
    exact le_trans (Multiset.toFinset_card_le _) (card_roots' q)
  exact le_trans (Finset.card_union_le e.roots.toFinset q.roots.toFinset)
    (Nat.add_le_add hecard hqcard)

/-- A large separable fixed-point set contains a point avoiding the zero loci of two polynomials. -/
theorem exists_periodic_point_avoiding_two_polys_of_natDegree_add_lt (c : ℂ) {p : ℕ}
    (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable) {e q : Polynomial ℂ}
    (he : e ≠ 0) (hq : q ≠ 0) (hdeg : e.natDegree + q.natDegree < 2 ^ p) :
    ∃ z, (quadratic c)^[p] z = z ∧ e.eval z ≠ 0 ∧ q.eval z ≠ 0 := by
  classical
  let B : Finset ℂ := e.roots.toFinset ∪ q.roots.toFinset
  have hBcard : B.card < 2 ^ p := lt_of_le_of_lt (roots_union_card_le_natDegree_add e q) hdeg
  obtain ⟨z, hFz, hzB⟩ := exists_periodic_point_notMem_finset c hp hsep B hBcard
  refine ⟨z, hFz, ?_, ?_⟩
  · intro hez
    have hzroots : z ∈ e.roots.toFinset := by
      exact Multiset.mem_toFinset.mpr ((mem_roots he).mpr hez)
    exact hzB (Finset.mem_union.mpr (Or.inl hzroots))
  · intro hqz
    have hzroots : z ∈ q.roots.toFinset := by
      exact Multiset.mem_toFinset.mpr ((mem_roots hq).mpr hqz)
    exact hzB (Finset.mem_union.mpr (Or.inr hzroots))

/-- The union of the zero sets of a finite polynomial family has size bounded by the sum of degrees. -/
theorem roots_biUnion_card_le_sum_natDegree (A : Finset (Polynomial ℂ)) :
    (A.biUnion fun q => q.roots.toFinset).card ≤ ∑ q ∈ A, q.natDegree := by
  classical
  refine le_trans (Finset.card_biUnion_le (s := A) (t := fun q => q.roots.toFinset)) ?_
  exact Finset.sum_le_sum fun q _hq =>
    le_trans (Multiset.toFinset_card_le _) (card_roots' q)

/-- If a point avoids the root union of a finite family, every nonzero polynomial in the family is
nonzero at that point. -/
theorem eval_ne_zero_of_notMem_roots_biUnion {A : Finset (Polynomial ℂ)} {q : Polynomial ℂ}
    (hqA : q ∈ A) (hq0 : q ≠ 0) {z : ℂ}
    (hz : z ∉ A.biUnion fun r => r.roots.toFinset) :
    q.eval z ≠ 0 := by
  intro hqz
  have hzroots : z ∈ q.roots.toFinset := by
    exact Multiset.mem_toFinset.mpr ((mem_roots hq0).mpr hqz)
  exact hz (Finset.mem_biUnion.mpr ⟨q, hqA, hzroots⟩)

/-- Any finite set of points larger than a polynomial zero-locus budget contains a point avoiding
all zero loci in the polynomial family. -/
theorem exists_mem_finset_avoiding_polys_of_sum_natDegree_lt (R : Finset ℂ)
    (A : Finset (Polynomial ℂ)) (hA0 : ∀ q ∈ A, q ≠ 0)
    (hdeg : (∑ q ∈ A, q.natDegree) < R.card) :
    ∃ z ∈ R, ∀ q ∈ A, q.eval z ≠ 0 := by
  classical
  let Z : Finset ℂ := A.biUnion fun q => q.roots.toFinset
  by_contra h
  have hsub : R ⊆ Z := by
    intro z hzR
    by_contra hzZ
    have havoid : ∀ q ∈ A, q.eval z ≠ 0 := by
      intro q hqA
      exact eval_ne_zero_of_notMem_roots_biUnion hqA (hA0 q hqA) hzZ
    exact h ⟨z, hzR, havoid⟩
  have hcard_le : R.card ≤ Z.card := Finset.card_le_card hsub
  have hZcard : Z.card ≤ ∑ q ∈ A, q.natDegree := roots_biUnion_card_le_sum_natDegree A
  have : R.card < R.card := lt_of_le_of_lt (le_trans hcard_le hZcard) hdeg
  exact (lt_irrefl R.card) this

/-- A large separable fixed-point set contains a root avoiding every zero locus in a finite polynomial
family. -/
theorem exists_fixedPointPoly_root_avoiding_polys_of_sum_natDegree_lt (c : ℂ) {p : ℕ}
    (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable) (A : Finset (Polynomial ℂ))
    (hA0 : ∀ q ∈ A, q ≠ 0) (hdeg : (∑ q ∈ A, q.natDegree) < 2 ^ p) :
    ∃ z, z ∈ (fixedPointPoly c p).roots.toFinset ∧ (quadratic c)^[p] z = z ∧
      ∀ q ∈ A, q.eval z ≠ 0 := by
  classical
  let B : Finset ℂ := A.biUnion fun q => q.roots.toFinset
  have hBcard : B.card < 2 ^ p := lt_of_le_of_lt (roots_biUnion_card_le_sum_natDegree A) hdeg
  obtain ⟨z, hzroot, hzB⟩ := exists_fixedPointPoly_root_notMem_finset c hp hsep B hBcard
  have hFz : (quadratic c)^[p] z = z := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hzroot)
  refine ⟨z, hzroot, hFz, ?_⟩
  intro q hqA
  exact eval_ne_zero_of_notMem_roots_biUnion hqA (hA0 q hqA) hzB

/-- Dynamic form of finite-family polynomial avoidance. -/
theorem exists_periodic_point_avoiding_polys_of_sum_natDegree_lt (c : ℂ) {p : ℕ}
    (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable) (A : Finset (Polynomial ℂ))
    (hA0 : ∀ q ∈ A, q ≠ 0) (hdeg : (∑ q ∈ A, q.natDegree) < 2 ^ p) :
    ∃ z, (quadratic c)^[p] z = z ∧ ∀ q ∈ A, q.eval z ≠ 0 := by
  obtain ⟨z, _hzroot, hFz, havoid⟩ :=
    exists_fixedPointPoly_root_avoiding_polys_of_sum_natDegree_lt c hp hsep A hA0 hdeg
  exact ⟨z, hFz, havoid⟩

end Bottcher
