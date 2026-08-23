import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Connected.Basic

/-!
# Isolated limits and connectedness from locally constant functions

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §9 and §10.

Two topological facts used in the source.  A net converging to an isolated point is eventually
equal to it — this is why a limit of characters whose value at a root of unity is `1` again has
value `1` there, the roots of unity of a fixed order being discrete.  And a space on which every
locally constant Boolean function is constant is preconnected — this is the passage from
`H⁰ (X , ℝ) = ℝ` to the connectedness of `X`.
-/

namespace HTGeometry

/-- **Deninger, Proposition 9.1, the closedness step.**  A net converging to an isolated point is
eventually equal to it: if the roots of unity of order `N` form a discrete subset then
`P_n (ζ) → P (ζ)` forces `P_n (ζ) = P (ζ)` eventually. -/
theorem eventually_eq_of_tendsto_isolated {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    {f : ι → X} {x : X} (hf : Filter.Tendsto f l (nhds x)) (hx : {x} ∈ nhds x) :
    ∀ᶠ i in l, f i = x := hf hx

/-- **Deninger, the Remark after Proposition 10.3.**  A space on which every locally constant
Boolean function is constant is preconnected. -/
theorem preconnectedSpace_of_isLocallyConstant_const {X : Type*} [TopologicalSpace X]
    (h : ∀ f : X → Bool, IsLocallyConstant f → ∀ a b : X, f a = f b) : PreconnectedSpace X := by
  classical
  refine ⟨?_⟩
  rintro u v hu hv hcover ⟨a, -, hau⟩ ⟨b, -, hbv⟩
  by_contra hcon
  have hdisj : ∀ x : X, x ∈ u → x ∉ v := fun x hx hxv =>
    hcon ⟨x, Set.mem_univ x, hx, hxv⟩
  have hcompl : uᶜ = v := by
    ext x
    constructor
    · intro hx
      rcases hcover (Set.mem_univ x) with hxu | hxv
      · exact absurd hxu hx
      · exact hxv
    · intro hx hxu
      exact hdisj x hxu hx
  have hbu : b ∉ u := fun hb => hdisj b hb hbv
  have hloc : IsLocallyConstant (fun x : X => decide (x ∈ u)) := by
    refine IsLocallyConstant.iff_isOpen_fiber.2 fun y => ?_
    cases y with
    | false =>
      have hset : (fun x : X => decide (x ∈ u)) ⁻¹' {false} = uᶜ := by
        ext x; simp
      rw [hset, hcompl]
      exact hv
    | true =>
      have hset : (fun x : X => decide (x ∈ u)) ⁻¹' {true} = u := by
        ext x; simp
      rw [hset]
      exact hu
  have hab := h _ hloc a b
  rw [decide_eq_decide] at hab
  exact hbu (hab.mp hau)

end HTGeometry
