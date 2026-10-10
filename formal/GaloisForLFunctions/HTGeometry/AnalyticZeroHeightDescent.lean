import Mathlib

/-!
# Height descent among the zeros of an analytic function

Let `F` be analytic on a preconnected open set `U` and let `K ⊆ U` be compact. Suppose every
non-real zero of `F` in `K` has a non-real zero of `F` in `K` of strictly smaller `|Im|`. Then
either `F` has no non-real zero in `K`, or `F ≡ 0` on `U`
(`AnalyticOnNhd.eqOn_zero_of_imDescent`).

**Proof.** If the set `S` of non-real zeros in `K` were finite and nonempty, an element of minimal
`|Im|` would have a descendant of smaller `|Im|` in `S`. So `S` is infinite, has an accumulation
point in `K`, and the identity theorem applies. No orbit is constructed and no uniform contraction
rate is needed: a strict descent at every step suffices.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Height descent forces vanishing.** -/
theorem AnalyticOnNhd.eqOn_zero_of_imDescent {F : ℂ → ℂ} {U K : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hU : IsPreconnected U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hdesc : ∀ z ∈ K, F z = 0 → z.im ≠ 0 → ∃ w ∈ K, F w = 0 ∧ w.im ≠ 0 ∧ |w.im| < |z.im|)
    {z₀ : ℂ} (h₀ : z₀ ∈ K) (hz₀ : F z₀ = 0) (him : z₀.im ≠ 0) : Set.EqOn F 0 U := by
  set S : Set ℂ := {z | z ∈ K ∧ F z = 0 ∧ z.im ≠ 0} with hS
  have hinf : S.Infinite := by
    intro hfin
    obtain ⟨z, hzS, hmin⟩ :=
      Set.exists_min_image S (fun z => |z.im|) hfin ⟨z₀, h₀, hz₀, him⟩
    obtain ⟨w, hwK, hw0, hwim, hlt⟩ := hdesc z hzS.1 hzS.2.1 hzS.2.2
    exact absurd (hmin w ⟨hwK, hw0, hwim⟩) (not_le.mpr hlt)
  obtain ⟨x, hxK, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK fun z hz => hz.1
  refine hF.eqOn_zero_of_preconnected_of_frequently_eq_zero hU (hKU hxK) ?_
  rw [accPt_iff_frequently] at hacc
  rw [frequently_nhdsWithin_iff]
  exact hacc.mono fun y hy => ⟨hy.2.2.1, hy.1⟩

end GaloisForLFunctions.HTGeometry
