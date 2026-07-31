import GaloisForLFunctions.RHTower.SchattenApproximation

/-!
# Lower bounds for approximation numbers

The approximation-number layer had only the upper bound: any operator of rank at most `n` bounds
`a_n` from above.  Every *computation* of an approximation number needs the other half, and it was
missing.

The missing half is a dimension count.  If some subspace of dimension `n + 1` is uniformly expanded
by `T` — every vector in it satisfies `c ‖w‖ ≤ ‖T w‖` — then no operator of rank at most `n` can
approximate `T` better than `c`, because such an operator must kill a nonzero vector of that
subspace.  Consequently `c ≤ a_n(T)`.

This is the reusable half: with it, an approximation number is pinned from both sides by exhibiting
one truncation and one expanded subspace.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Approximation numbers are bounded below by uniform expansion on a subspace.**  If `T`
expands every vector of an `(n+1)`-dimensional subspace by at least `c`, then no operator of rank
at most `n` approximates `T` to within less than `c`. -/
theorem le_approxNumber_of_subspace
    {T : H →L[ℂ] H} {n : ℕ} {c : ℝ}
    (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hdim : n + 1 ≤ Module.finrank ℂ W)
    (hlb : ∀ w ∈ W, c * ‖w‖ ≤ ‖T w‖) :
    c ≤ approxNumber T n := by
  refine le_csInf (approxNumber_set_nonempty T n) ?_
  rintro r ⟨F, ⟨V, hVfd, hVle, hVmem⟩, rfl⟩
  classical
  let g : W →ₗ[ℂ] V :=
    { toFun := fun w => ⟨F (w : H), hVmem (w : H)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp
      map_smul' := by
        intro a b
        apply Subtype.ext
        simp }
  have hrank : Module.finrank ℂ (LinearMap.range g) + Module.finrank ℂ (LinearMap.ker g) =
      Module.finrank ℂ W := LinearMap.finrank_range_add_finrank_ker g
  have hrange : Module.finrank ℂ (LinearMap.range g) ≤ n :=
    le_trans (Submodule.finrank_le _) hVle
  have hkerpos : 0 < Module.finrank ℂ (LinearMap.ker g) := by omega
  haveI : Nontrivial (LinearMap.ker g) := Module.nontrivial_of_finrank_pos hkerpos
  obtain ⟨x, hx⟩ := exists_ne (0 : LinearMap.ker g)
  set w : H := ((x : W) : H) with hw
  have hwW : w ∈ W := (x : W).2
  have hwne : w ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hFw : F w = 0 := by
    have hgx : g (x : W) = 0 := LinearMap.mem_ker.mp x.2
    exact congrArg Subtype.val hgx
  have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hexp : c * ‖w‖ ≤ ‖(T - F) w‖ := by
    have := hlb w hwW
    simpa [hFw] using this
  have hop : ‖(T - F) w‖ ≤ ‖T - F‖ * ‖w‖ := (T - F).le_opNorm w
  have : c * ‖w‖ ≤ ‖T - F‖ * ‖w‖ := le_trans hexp hop
  exact le_of_mul_le_mul_right (by linarith) hnormpos

/-- With a matching truncation the approximation number is pinned exactly. -/
theorem approxNumber_eq_of_subspace_of_hasRankLE
    {T : H →L[ℂ] H} {n : ℕ} {c : ℝ}
    (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hdim : n + 1 ≤ Module.finrank ℂ W)
    (hlb : ∀ w ∈ W, c * ‖w‖ ≤ ‖T w‖)
    (F : H →L[ℂ] H) (hF : HasRankLE F n) (hnorm : ‖T - F‖ = c) :
    approxNumber T n = c :=
  le_antisymm (hnorm ▸ approxNumber_le T n F hF)
    (le_approxNumber_of_subspace W hdim hlb)

end RHTower

end
