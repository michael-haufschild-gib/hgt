import GaloisForLFunctions.HTGeometry.OrderedPolynomialCoveringMonodromy
import GaloisForLFunctions.HTGeometry.OrderedPolynomialMeridianTransposition

open Polynomial Set Topology
open scoped unitInterval Classical
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- The positive simple-critical circle is a transposition in the actual covering monodromy. -/
theorem exists_positiveCircle_monodromyPerm_isSwap {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (valuesWithConstant v)) (j : Fin (n + 1)) :
    ∃ r : ℝ, 0 < r ∧ ∃ b : PolynomialRegularValue v,
      (b : ℂ) = valuesWithConstant v j + (r ^ 2 : ℝ) ∧
      ∃ γ : Path b b,
        (∀ t, (γ t : ℂ) = positiveCirclePath (valuesWithConstant v j) (r ^ 2) t) ∧
        ((isCoveringMap_polynomialCoverMap v).monodromyPerm b (.mk γ)).IsSwap := by
  obtain ⟨r, hr, hav, hswap⟩ := exists_positiveCircle_rootLoopTransport_isSwap v hv j
  let c := valuesWithConstant v j
  let base : ℂ := c + (r ^ 2 : ℝ)
  have hb : ∀ k, base ≠ valuesWithConstant v k := by
    intro k
    have h := hav 0 k
    rw [(positiveCirclePath c (r ^ 2)).source] at h
    exact h
  let b : PolynomialRegularValue v := ⟨base, hb⟩
  let γ : Path b b :=
    { toFun := fun t => ⟨positiveCirclePath c (r ^ 2) t, hav t⟩
      continuous_toFun := (positiveCirclePath c (r ^ 2)).continuous.subtype_mk _
      source' := Subtype.ext (positiveCirclePath c (r ^ 2)).source
      target' := Subtype.ext (positiveCirclePath c (r ^ 2)).target }
  let E := rootFiberCoverEquiv v b
  let ρ := rootLoopTransport v (positiveCirclePath c (r ^ 2)) hav
  let nativePerm := (isCoveringMap_polynomialCoverMap v).monodromyPerm b (.mk γ)
  have hcompat : ∀ z : RootFiber v base, E (ρ z) = nativePerm (E z) := by
    intro z
    exact rootLoopTransport_eq_covering_monodromy v γ z
  obtain ⟨x, y, hxy, hρ⟩ := hswap
  change ρ = Equiv.swap x y at hρ
  refine ⟨r, hr, b, rfl, γ, fun _ => rfl, E x, E y, ?_, ?_⟩
  · exact fun h => hxy (E.injective h)
  · change nativePerm = Equiv.swap (E x) (E y)
    apply Equiv.ext
    intro w
    obtain ⟨z, rfl⟩ := E.surjective w
    rw [← hcompat z, hρ]
    by_cases hzx : z = x
    · subst z
      simp
    by_cases hzy : z = y
    · subst z
      simp
    have hex : E z ≠ E x := fun h => hzx (E.injective h)
    have hey : E z ≠ E y := fun h => hzy (E.injective h)
    simp [Equiv.swap_apply_def, hzx, hzy, hex, hey]

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
