import GaloisForLFunctions.HTGeometry.CDGATensorAlgebraUnit

/-!
# The product of single-bidegree elements, and the two inclusions

A single-bidegree element multiplies with another by a one-term sum: only the splitting given by the
two bidegrees survives, the others killing one of the two factors.  With the units of the two
algebras this gives the two inclusions of a tensor product of algebras.

* `HTGeometry.tensorAlgMul_tensorSingle` : the product of two single-bidegree elements.
* `HTGeometry.tensorCDGAInclLeft`, `HTGeometry.tensorCDGAInclRight` : the two inclusions.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  (A : CDGAStructure R X) (B : CDGAStructure R Y)

/-- **The product of two single-bidegree elements is a one-term sum.** -/
theorem tensorAlgMul_tensorSingle {a b n : ℕ} (h : a + b = n)
    (r : {ab : ℕ × ℕ // ab.1 + ab.2 = a}) (s : {ab : ℕ × ℕ // ab.1 + ab.2 = b})
    (z : TensorProduct R (X r.1.1) (Y r.1.2)) (w : TensorProduct R (X s.1.1) (Y s.1.2))
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (hp1 : r.1.1 + s.1.1 = p.1.1) (hp2 : r.1.2 + s.1.2 = p.1.2) :
    tensorAlgMul A B h (tensorSingle (M := X) (N := Y) r z)
        (tensorSingle (M := X) (N := Y) s w) p
      = tensorPairₗ A B hp1 hp2 z w := by
  classical
  show (∑ rs : Splitting a b p, splittingTerm A B (tensorSingle (M := X) (N := Y) r z)
    (tensorSingle (M := X) (N := Y) s w) rs) = _
  rw [Finset.sum_eq_single_of_mem (⟨(r, s), ⟨hp1, hp2⟩⟩ : Splitting a b p) (Finset.mem_univ _)
    (fun rs _ hne => ?_)]
  · show tensorPairₗ A B hp1 hp2 (tensorSingle (M := X) (N := Y) r z r)
      (tensorSingle (M := X) (N := Y) s w s) = _
    rw [tensorSingle_same, tensorSingle_same]
  · by_cases hr : rs.1.1 = r
    · exfalso
      apply hne
      subst hr
      have e1 : rs.1.1.1.1 + rs.1.2.1.1 = p.1.1 := rs.2.1
      have e2 : rs.1.1.1.2 + rs.1.2.1.2 = p.1.2 := rs.2.2
      have e3 : rs.1.1.1.1 + s.1.1 = p.1.1 := hp1
      have e4 : rs.1.1.1.2 + s.1.2 = p.1.2 := hp2
      exact Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext
        (Nat.add_left_cancel (e1.trans e3.symm)) (Nat.add_left_cancel (e2.trans e4.symm)))))
    · show tensorPairₗ A B rs.2.1 rs.2.2 (tensorSingle (M := X) (N := Y) r z rs.1.1)
        (tensorSingle (M := X) (N := Y) s w rs.1.2) = 0
      rw [tensorSingle_ne _ hr, map_zero, LinearMap.zero_apply]

end GaloisForLFunctions.HTGeometry
