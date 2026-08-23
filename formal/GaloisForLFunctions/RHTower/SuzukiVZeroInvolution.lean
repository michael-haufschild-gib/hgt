import GaloisForLFunctions.RHTower.SuzukiModelSpaceConjugation

noncomputable section

/-!
# `V(0)` under the involution `K`

Suzuki's Remark 5.2 observes that `V(0) = L²(t,∞) ∩ K L²(t,∞)` at `t = 0` is invariant under `K`,
so a nonzero element of `V(0)` produces an eigenvector of `K` in `V(0)` with eigenvalue `±1`: one
of `f ± K f` is nonzero, and `K` sends it to `±` itself.  The invariance is immediate from
`K ∘ K = id`, since membership of `f` in `K L²(0,∞)` exhibits `K f` as the datum it came from.

This reduces the question of whether `V(0)` is nonzero — which Suzuki notes would falsify RH if it
failed — to whether the isometric involution `K` admits an eigenfunction on the ray.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- `V(0)` is invariant under the involution `K`. -/
theorem suzukiKFun_mem_suzukiV0 {f : L2R} (hf : f ∈ suzukiV0) :
    suzukiKFun f ∈ suzukiV0 := by
  obtain ⟨hf1, hf2⟩ := hf
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg, hgf⟩ := hf2
    rw [SetLike.mem_coe] at hg
    have hKf : suzukiKFun f = g := by
      rw [← hgf, suzukiKₛₗ_apply, suzukiKFun_suzukiKFun]
    rw [hKf]
    exact hg
  · exact ⟨f, hf1, rfl⟩

theorem suzukiKFun_add_self (f : L2R) :
    suzukiKFun (f + suzukiKFun f) = f + suzukiKFun f := by
  rw [suzukiKFun_add, suzukiKFun_suzukiKFun, add_comm]

theorem suzukiKFun_sub_self (f : L2R) :
    suzukiKFun (f - suzukiKFun f) = -(f - suzukiKFun f) := by
  have hsub : suzukiKFun (f - suzukiKFun f) = suzukiKFun f - suzukiKFun (suzukiKFun f) := by
    have h := suzukiKFun_add (f - suzukiKFun f) (suzukiKFun f)
    rw [sub_add_cancel] at h
    rw [eq_sub_iff_add_eq]
    exact h.symm
  rw [hsub, suzukiKFun_suzukiKFun]
  abel

/-- **Suzuki Remark 5.2, the eigenvector reduction.**  If `V(0)` contains a nonzero vector then
the involution `K` has an eigenvector in `V(0)` with eigenvalue `1` or `-1`. -/
theorem exists_suzukiK_eigenvector {f : L2R} (hf : f ∈ suzukiV0) (hne : f ≠ 0) :
    ∃ g ∈ suzukiV0, g ≠ 0 ∧ (suzukiKFun g = g ∨ suzukiKFun g = -g) := by
  have hKf : suzukiKFun f ∈ suzukiV0 := suzukiKFun_mem_suzukiV0 hf
  by_cases hplus : f + suzukiKFun f = 0
  · refine ⟨f - suzukiKFun f, suzukiV0.sub_mem hf hKf, ?_, Or.inr (suzukiKFun_sub_self f)⟩
    intro hzero
    have h2 : (2 : ℂ) • f = 0 := by
      have := congrArg₂ (· + ·) hplus hzero
      simp only [add_zero] at this
      rw [two_smul]
      have hsum : f + suzukiKFun f + (f - suzukiKFun f) = f + f := by abel
      rw [hsum] at this
      exact this
    exact hne (by simpa using h2)
  · exact ⟨f + suzukiKFun f, suzukiV0.add_mem hf hKf, hplus,
      Or.inl (suzukiKFun_add_self f)⟩

end RHTower
