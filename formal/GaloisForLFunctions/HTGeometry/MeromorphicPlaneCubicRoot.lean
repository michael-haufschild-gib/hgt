import GaloisForLFunctions.HTGeometry.MeromorphicPlaneAlgebra
import Mathlib.Tactic

/-!
# Entire representatives of meromorphic cubic roots

At a pole of a meromorphic function, the factors `f` and `f - 3` have the
same negative order. Their cubic product cannot be entire. Normal-form
extension therefore turns every solution in the global meromorphic plane
field into an entire solution, with the identity valid at every point.
-/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry

/-- An entire cubic value rules out every pole of a meromorphic lift. -/
theorem meromorphicOrderAt_nonneg_of_cubic_factor {f d : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hd : AnalyticAt ℂ d z)
    (hrel : (fun w => (f w - 3) * f w ^ 2) =ᶠ[𝓝[≠] z] d) :
    0 ≤ meromorphicOrderAt f z := by
  by_contra hn
  have hn' := lt_of_not_ge hn
  have hc : meromorphicOrderAt (fun _ : ℂ => (-3 : ℂ)) z = 0 := by
    rw [meromorphicOrderAt_const]
    norm_num
  have hsub : meromorphicOrderAt (f - fun _ => 3) z = meromorphicOrderAt f z := by
    have h := meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-3 : ℂ) z)
      (show meromorphicOrderAt f z < meromorphicOrderAt (fun _ : ℂ => (-3 : ℂ)) z by
        rwa [hc])
    convert h using 1
    congr 1
  have ho := hd.meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hrel] at ho
  change 0 ≤ meromorphicOrderAt ((f - fun _ => 3) * f ^ 2) z at ho
  rw [meromorphicOrderAt_mul (hf.sub (MeromorphicAt.const 3 z)) (hf.pow 2),
    meromorphicOrderAt_pow hf, hsub] at ho
  cases hx : meromorphicOrderAt f z with
  | top => simp [hx] at hn'
  | coe n =>
    rw [hx] at ho hn'
    change (↑(0 : ℤ) : WithTop ℤ) ≤ ↑(n + 2 * n) at ho
    have ho' := WithTop.coe_le_coe.mp ho
    have hn'' : n < 0 := WithTop.coe_lt_coe.mp hn'
    omega

/-- Filling removable values turns every meromorphic cubic-factor solution into an entire one. -/
theorem entire_cubic_factor_of_meromorphic {f d : ℂ → ℂ}
    (hf : ∀ z, MeromorphicAt f z) (hd : Differentiable ℂ d)
    (hrel : ∀ z, (fun w => (f w - 3) * f w ^ 2) =ᶠ[𝓝[≠] z] d) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z, (h z - 3) * h z ^ 2 = d z := by
  let h := toMeromorphicNFOn f Set.univ
  have hfon : MeromorphicOn f Set.univ := fun z _ => hf z
  have hheq (z : ℂ) : h =ᶠ[𝓝[≠] z] f :=
    hfon.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have han (z : ℂ) : AnalyticAt ℂ h z := by
    apply ((meromorphicNFOn_toMeromorphicNFOn f Set.univ)
      (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hfon (Set.mem_univ z)]
    exact meromorphicOrderAt_nonneg_of_cubic_factor (hf z) (hd.analyticAt z) (hrel z)
  refine ⟨h, fun z => (han z).differentiableAt, fun z => ?_⟩
  have he : (fun w => (h w - 3) * h w ^ 2) =ᶠ[𝓝[≠] z] d := by
    filter_upwards [hheq z, hrel z] with w hw hr
    rwa [hw]
  exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (((han z).continuousAt.sub continuousAt_const).mul ((han z).continuousAt.pow 2))
    hd.continuous.continuousAt).mp he).eq_of_nhds

/-- A cubic-factor equation in the actual meromorphic plane has an entire representative. -/
theorem entire_cubic_factor_of_plane {d : ℂ → ℂ} (hd : Differentiable ℂ d)
    (x : MeromorphicPlane)
    (hrel : (x - 3) * x ^ 2 = ofMeromorphic d (fun z => (hd.analyticAt z).meromorphicAt)) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z, (h z - 3) * h z ^ 2 = d z := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  let P : Polynomial ℂ := (Polynomial.X - Polynomial.C 3) * Polynomial.X ^ 2
  have hp : Polynomial.aeval (ofMeromorphic f hf) P =
      ofMeromorphic d (fun z => (hd.analyticAt z).meromorphicAt) := by
    simpa only [P, map_mul, map_sub, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, map_ofNat] using hrel
  have he := (ofMeromorphic_eq_iff (meromorphicAt_polyEval hf P)
    (fun z => (hd.analyticAt z).meromorphicAt)).mp
      ((aeval_ofMeromorphic P hf).symm.trans hp)
  apply entire_cubic_factor_of_meromorphic hf hd
  intro z
  simpa [P] using he z

end GaloisForLFunctions.HTGeometry
