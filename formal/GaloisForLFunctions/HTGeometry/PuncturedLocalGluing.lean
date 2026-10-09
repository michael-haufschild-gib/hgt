import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousOn

/-!
# Gluing continuous extensions across isolated punctures

An open-source map extends globally when it has a continuous local extension
at every omitted point and each omitted point is isolated from the others.
The construction also preserves a specified projection identity.
-/

open Topology Set Function Filter

namespace GaloisForLFunctions.HTGeometry

/-- Local continuous extensions at isolated omitted points glue globally, while
preserving any specified projection identity. -/
theorem exists_continuous_extension_of_punctured_local_extensions
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} (hU : IsOpen U)
    (hpuncture : ∀ a ∉ U, U ∈ 𝓝[≠] a) (f : C(U, Y)) (p : Y → Z) (h : X → Z)
    (hpf : ∀ x : U, p (f x) = h x)
    (hlocal : ∀ a ∉ U, ∃ g : X → Y, ContinuousAt g a ∧
      (∀ᶠ z in 𝓝[≠] a, ∀ hz : z ∈ U, g z = f ⟨z, hz⟩) ∧ p (g a) = h a) :
    ∃ F : C(X, Y), (∀ x : U, F x = f x) ∧ ∀ x, p (F x) = h x := by
  classical
  choose g hg hge hgp using hlocal
  let F : X → Y := fun x => if hx : x ∈ U then f ⟨x, hx⟩ else g x hx x
  have hF_on (x : U) : F x = f x := by simp only [F, dif_pos x.property]
  have hFcont : ContinuousOn F U := by
    apply continuousOn_iff_continuous_restrict.mpr
    convert f.continuous using 1
    funext x
    exact hF_on x
  have hFc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro a
    by_cases ha : a ∈ U
    · exact hFcont.continuousAt (hU.mem_nhds ha)
    · have he : F =ᶠ[𝓝 a] g a ha := by
        have hpunc : F =ᶠ[𝓝[≠] a] g a ha := by
          filter_upwards [hpuncture a ha, hge a ha] with z hz hzg
          change (if hx : z ∈ U then f ⟨z, hx⟩ else g z hx z) = g a ha z
          rw [dif_pos hz]
          exact (hzg hz).symm
        have hn := eventually_nhdsWithin_iff.mp hpunc
        filter_upwards [hn] with z hz
        by_cases hza : z = a
        · subst z
          simp only [F, dif_neg ha]
        · exact hz hza
      exact (hg a ha).congr_of_eventuallyEq he
  refine ⟨⟨F, hFc⟩, hF_on, ?_⟩
  intro x
  by_cases hx : x ∈ U
  · simpa only [ContinuousMap.coe_mk, F, dif_pos hx] using hpf ⟨x, hx⟩
  · simpa only [ContinuousMap.coe_mk, F, dif_neg hx] using hgp x hx

end GaloisForLFunctions.HTGeometry
