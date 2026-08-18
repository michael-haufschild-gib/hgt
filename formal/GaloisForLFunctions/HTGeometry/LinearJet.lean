import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn

/-!
# Jets commute with a continuous linear map

On an open set where a map into a complex Banach space is holomorphic, composing with a continuous
linear map commutes with every iterated derivative.  In particular the jets of a component of a
vector-valued function are the components of its jets.

This is what lets a relation between the values of one family and the jets of another be read as an
autonomous relation on the jet of the pair.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- **Iterated derivatives commute with a continuous linear map.** -/
theorem iteratedDeriv_clm_comp_eqOn {U : Set ℂ} (hU : IsOpen U) (L : E →L[ℂ] F) {u : ℂ → E}
    (hu : DifferentiableOn ℂ u U) (k : ℕ) :
    Set.EqOn (iteratedDeriv k (fun z => L (u z))) (fun z => L (iteratedDeriv k u z)) U := by
  induction k with
  | zero =>
      intro z _
      simp [iteratedDeriv_zero]
  | succ j ih =>
      intro z hz
      have hju : DifferentiableOn ℂ (iteratedDeriv j u) U := differentiableOn_iteratedDeriv hU hu j
      have hev : iteratedDeriv j (fun z => L (u z)) =ᶠ[nhds z] fun w => L (iteratedDeriv j u w) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hz) ih
      have hdu : HasDerivAt (iteratedDeriv j u) (iteratedDeriv (j + 1) u z) z := by
        have := (hju.differentiableAt (hU.mem_nhds hz)).hasDerivAt
        rw [iteratedDeriv_succ]
        exact this
      have hL : HasDerivAt (fun w => L (iteratedDeriv j u w)) (L (iteratedDeriv (j + 1) u z)) z :=
        L.hasFDerivAt.comp_hasDerivAt z hdu
      rw [iteratedDeriv_succ, hev.deriv_eq, hL.deriv]

end GaloisForLFunctions.HTGeometry
