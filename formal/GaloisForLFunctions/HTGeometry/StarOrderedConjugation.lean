import Mathlib.Analysis.CStarAlgebra.CStarMatrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem star_conjugate_nonneg_of_nonneg {R : Type*} [NonUnitalRing R]
    [PartialOrder R] [StarRing R] [StarOrderedRing R]
    {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ star c * a * c := by
  obtain ⟨p, hp, hap⟩ := (StarOrderedRing.le_iff 0 a).mp ha
  have hclosed : star c * p * c ∈
      AddSubmonoid.closure (Set.range fun s : R => star s * s) := by
    refine AddSubmonoid.closure_induction
      (motive := fun p _ => star c * p * c ∈
        AddSubmonoid.closure (Set.range fun s : R => star s * s)) ?_ ?_ ?_ hp
    · intro x hx
      obtain ⟨s, rfl⟩ := hx
      apply AddSubmonoid.subset_closure
      refine ⟨s * c, ?_⟩
      simp only [star_mul]
      noncomm_ring
    · simp
    · intro x y _ _ hx hy
      rw [mul_add, add_mul]
      exact AddSubmonoid.add_mem _ hx hy
  have haeq : a = p := by simpa using hap
  rw [haeq]
  exact (StarOrderedRing.le_iff 0 (star c * p * c)).mpr
    ⟨star c * p * c, hclosed, by simp⟩

theorem cstarMatrix_diagonal_nonneg_of_nonneg
    {A ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Fintype ι] (M : CStarMatrix ι ι A) (hM : 0 ≤ M) (k : ι) : 0 ≤ M k k := by
  obtain ⟨p, hp, hMp⟩ := (StarOrderedRing.le_iff 0 M).mp hM
  have hdiag : 0 ≤ p k k := by
    refine AddSubmonoid.closure_induction
      (motive := fun p _ => 0 ≤ p k k) ?_ ?_ ?_ hp
    · intro X hX
      obtain ⟨S, rfl⟩ := hX
      change 0 ≤ (star S * S) k k
      rw [CStarMatrix.mul_apply]
      simp only [CStarMatrix.star_apply]
      exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg (S i k)
    · simp
    · intro X Y _ _ hX hY
      simpa using add_nonneg hX hY
  have hMeq : M = p := by simpa using hMp
  rw [hMeq]
  exact hdiag

end GaloisForLFunctions.HTGeometry
