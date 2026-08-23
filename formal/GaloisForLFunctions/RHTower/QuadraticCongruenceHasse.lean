import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse

/-!
# Hasse principle for reducible quadratic congruence roots

For coprime moduli, the CRT equivalence gives both local detection and global realization for roots
of `x * (x + h) = 0`: two global roots agree exactly when their two local components agree, and
every pair of local roots has one unique global lift.
-/

namespace RHTower

noncomputable section

/-- Coprime quadratic-congruence roots are globally equal exactly when both local CRT roots agree. -/
theorem quadraticCongruenceRoot_hasse_eq_iff
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q * d)] (hcop : q.Coprime d)
    (h : ℤ) (x y : quadraticCongruenceRoots (q * d) h) :
    x = y ↔
      (quadraticCongruenceRootChineseRemainderEquiv hcop h x).1 =
          (quadraticCongruenceRootChineseRemainderEquiv hcop h y).1 ∧
        (quadraticCongruenceRootChineseRemainderEquiv hcop h x).2 =
          (quadraticCongruenceRootChineseRemainderEquiv hcop h y).2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · intro hxy
    apply (quadraticCongruenceRootChineseRemainderEquiv hcop h).injective
    exact Prod.ext hxy.1 hxy.2

/-- Every pair of coprime local quadratic-congruence roots has a unique global CRT root. -/
theorem quadraticCongruenceRoot_hasse_exists_unique
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q * d)] (hcop : q.Coprime d)
    (h : ℤ) (xq : quadraticCongruenceRoots q h)
    (xd : quadraticCongruenceRoots d h) :
    ∃! x : quadraticCongruenceRoots (q * d) h,
      (quadraticCongruenceRootChineseRemainderEquiv hcop h x).1 = xq ∧
        (quadraticCongruenceRootChineseRemainderEquiv hcop h x).2 = xd := by
  let e := quadraticCongruenceRootChineseRemainderEquiv hcop h
  obtain ⟨x, hx⟩ := e.surjective (xq, xd)
  have hxq : (e x).1 = xq := congrArg Prod.fst hx
  have hxd : (e x).2 = xd := congrArg Prod.snd hx
  refine ⟨x, ⟨hxq, hxd⟩, ?_⟩
  intro y hy
  apply e.injective
  apply Prod.ext
  · exact hy.1.trans hxq.symm
  · exact hy.2.trans hxd.symm

end


end RHTower
