import GaloisForLFunctions.RHTower.ApproximationNumberLowerBound
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm

/-!
# Lower bounds for rectangular approximation numbers

The square approximation-number lower bound already converts uniform expansion
on an `(n+1)`-dimensional subspace into a lower bound for `a_n`.  Rectangular
operators need the same statement on their domain, without an artificial
square enlargement.  The proof is the same sharp dimension argument: every
rank-at-most-`n` approximant kills a nonzero vector of the test subspace.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Uniform expansion on an `(n+1)`-dimensional domain subspace bounds the
`n`th rectangular approximation number from below. -/
theorem le_rectApproxNumber_of_subspace
    {T : E →L[ℂ] F} {n : ℕ} {c : ℝ}
    (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (hdim : n + 1 ≤ Module.finrank ℂ W)
    (hlb : ∀ w ∈ W, c * ‖w‖ ≤ ‖T w‖) :
    c ≤ rectApproxNumber T n := by
  refine le_csInf (rectApproxNumber_set_nonempty T n) ?_
  rintro r ⟨A, ⟨V, hVfd, hVle, hVmem⟩, rfl⟩
  classical
  let g : W →ₗ[ℂ] V :=
    { toFun := fun w => ⟨A (w : E), hVmem (w : E)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp
      map_smul' := by
        intro a b
        apply Subtype.ext
        simp }
  have hrank : Module.finrank ℂ (LinearMap.range g) +
      Module.finrank ℂ (LinearMap.ker g) = Module.finrank ℂ W :=
    LinearMap.finrank_range_add_finrank_ker g
  have hrange : Module.finrank ℂ (LinearMap.range g) ≤ n :=
    le_trans (Submodule.finrank_le _) hVle
  have hkerpos : 0 < Module.finrank ℂ (LinearMap.ker g) := by omega
  haveI : Nontrivial (LinearMap.ker g) :=
    Module.nontrivial_of_finrank_pos hkerpos
  obtain ⟨x, hx⟩ := exists_ne (0 : LinearMap.ker g)
  set w : E := ((x : W) : E) with hw
  have hwW : w ∈ W := (x : W).2
  have hwne : w ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hAw : A w = 0 := by
    have hgx : g (x : W) = 0 := LinearMap.mem_ker.mp x.2
    exact congrArg Subtype.val hgx
  have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hexp : c * ‖w‖ ≤ ‖(T - A) w‖ := by
    have := hlb w hwW
    simpa [hAw] using this
  have hop : ‖(T - A) w‖ ≤ ‖T - A‖ * ‖w‖ :=
    (T - A).le_opNorm w
  have hmul : c * ‖w‖ ≤ ‖T - A‖ * ‖w‖ := le_trans hexp hop
  exact le_of_mul_le_mul_right (by linarith) hnormpos

end RHTower
