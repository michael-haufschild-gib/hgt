import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Invertible multipliers give exact charts of a multiplier kernel

For two subspaces `Hp`, `Hm` of a Banach space and a bounded operator `u`, the *multiplier kernel*

`S(u) = {f ∈ Hp : u f ∈ Hm}`

is a subspace.  If `D` is invertible and preserves `Hp`, `N` is invertible and preserves `Hm`, and
`N` commutes with `u`, then the deformed multiplier `u N D⁻¹` has

`S(u N D⁻¹) = D S(u)`,

and `D` is a topological isomorphism from `S(u)` onto it: it is bounded, and bounded below by
`‖D⁻¹‖⁻¹`.

A concrete supply of such `D` is the Neumann series: if a closed subspace is invariant under `T`
and `‖T‖ < 1`, then `1 - T` is invertible and maps that subspace *onto* itself.
-/

namespace HTGeometry

section Chart

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- `S(u) = {f ∈ Hp : u f ∈ Hm}`. -/
def multiplierKernel (Hp Hm : Submodule ℂ H) (u : H →L[ℂ] H) : Submodule ℂ H :=
  Hp ⊓ Submodule.comap (u : H →ₗ[ℂ] H) Hm

theorem mem_multiplierKernel {Hp Hm : Submodule ℂ H} {u : H →L[ℂ] H} {f : H} :
    f ∈ multiplierKernel Hp Hm u ↔ f ∈ Hp ∧ u f ∈ Hm := Iff.rfl

variable [CompleteSpace H]

/-- **Exact chart of a multiplier kernel.**  `S(u N D⁻¹) = D S(u)`. -/
theorem multiplierKernel_deformed (Hp Hm : Submodule ℂ H) (u D N : H →L[ℂ] H)
    (hD : IsUnit D) (hN : IsUnit N) (hDp : Submodule.map (D : H →ₗ[ℂ] H) Hp = Hp)
    (hNm : Submodule.map (N : H →ₗ[ℂ] H) Hm = Hm) (hcomm : u * N = N * u) :
    multiplierKernel Hp Hm (u * N * Ring.inverse D)
      = Submodule.map (D : H →ₗ[ℂ] H) (multiplierKernel Hp Hm u) := by
  have hDinv : ∀ x : H, D (Ring.inverse D x) = x := by
    intro x
    have := congrArg (fun T : H →L[ℂ] H => T x) (Ring.mul_inverse_cancel D hD)
    simpa using this
  have hinvD : ∀ x : H, Ring.inverse D (D x) = x := by
    intro x
    have := congrArg (fun T : H →L[ℂ] H => T x) (Ring.inverse_mul_cancel D hD)
    simpa using this
  have hNinj : Function.Injective (N : H → H) := by
    intro x y hxy
    have hx := congrArg (fun T : H →L[ℂ] H => T x) (Ring.inverse_mul_cancel N hN)
    have hy := congrArg (fun T : H →L[ℂ] H => T y) (Ring.inverse_mul_cancel N hN)
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply_eq_self] at hx hy
    rw [← hx, ← hy, hxy]
  apply le_antisymm
  · rintro h ⟨hhp, hht⟩
    refine ⟨Ring.inverse D h, ⟨?_, ?_⟩, hDinv h⟩
    · obtain ⟨g, hg, hgD⟩ := hDp ▸ hhp
      have : Ring.inverse D h = g := by rw [← hgD]; exact hinvD g
      rw [this]; exact hg
    · have hval : (u * N * Ring.inverse D) h = N (u (Ring.inverse D h)) := by
        have : (u * N * Ring.inverse D) h = u (N (Ring.inverse D h)) := rfl
        rw [this]
        have := congrArg (fun T : H →L[ℂ] H => T (Ring.inverse D h)) hcomm
        simpa using this
      rw [hval] at hht
      obtain ⟨z, hz, hzN⟩ := hNm ▸ hht
      have : u (Ring.inverse D h) = z := hNinj (by rw [hzN])
      rw [this]; exact hz
  · rintro _ ⟨f, ⟨hfp, hfm⟩, rfl⟩
    constructor
    · exact hDp ▸ ⟨f, hfp, rfl⟩
    · have hval : (u * N * Ring.inverse D) (D f) = N (u f) := by
        have h1 : (u * N * Ring.inverse D) (D f) = u (N (Ring.inverse D (D f))) := rfl
        rw [h1, hinvD f]
        have := congrArg (fun T : H →L[ℂ] H => T f) hcomm
        simpa using this
      rw [hval]
      exact hNm ▸ ⟨u f, hfm, rfl⟩

/-- The chart is bounded below by the reciprocal norm of the inverse multiplier. -/
theorem norm_le_norm_inverse_mul_norm_apply {D : H →L[ℂ] H} (hD : IsUnit D) (f : H) :
    ‖f‖ ≤ ‖Ring.inverse D‖ * ‖D f‖ := by
  have hinvD : Ring.inverse D (D f) = f := by
    have := congrArg (fun T : H →L[ℂ] H => T f) (Ring.inverse_mul_cancel D hD)
    simpa using this
  calc ‖f‖ = ‖Ring.inverse D (D f)‖ := by rw [hinvD]
    _ ≤ ‖Ring.inverse D‖ * ‖D f‖ := ContinuousLinearMap.le_opNorm _ _

end Chart

section Neumann

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- **A strict contraction leaves an invariant closed subspace exactly invariant.**  If `K` is a
closed subspace invariant under `T` and `‖T‖ < 1`, then `1 - T` maps `K` onto `K`. -/
theorem map_one_sub_eq_of_norm_lt_one {K : Submodule ℂ H} (hK : IsClosed (K : Set H))
    {T : H →L[ℂ] H} (hTK : ∀ x ∈ K, T x ∈ K) (hT : ‖T‖ < 1) :
    Submodule.map ((1 - T : H →L[ℂ] H) : H →ₗ[ℂ] H) K = K := by
  haveI : CompleteSpace K := hK.completeSpace_coe
  set T' : K →L[ℂ] K := ((T ∘L K.subtypeL).codRestrict K (fun x => hTK x x.2)) with hT'
  have hT'norm : ‖T'‖ < 1 := by
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_) hT
    have : ‖T' x‖ = ‖T (x : H)‖ := rfl
    rw [this]
    exact ContinuousLinearMap.le_opNorm _ _
  have hunit : IsUnit (1 - T') := (Units.oneSub T' hT'norm).isUnit
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have : (1 - T : H →L[ℂ] H) x = x - T x := by simp
    rw [show ((1 - T : H →L[ℂ] H) : H →ₗ[ℂ] H) x = x - T x by simpa using this]
    exact K.sub_mem hx (hTK x hx)
  · intro y hy
    obtain ⟨u, hu⟩ := hunit
    refine ⟨((u⁻¹ : (K →L[ℂ] K)ˣ) : K →L[ℂ] K) ⟨y, hy⟩, Submodule.coe_mem _, ?_⟩
    have hcancel : (1 - T') (((u⁻¹ : (K →L[ℂ] K)ˣ) : K →L[ℂ] K) ⟨y, hy⟩) = ⟨y, hy⟩ := by
      have : ((1 - T') * ((u⁻¹ : (K →L[ℂ] K)ˣ) : K →L[ℂ] K)) = 1 := by
        rw [← hu]; exact u.mul_inv
      exact congrArg (fun S : K →L[ℂ] K => S ⟨y, hy⟩) this
    have := congrArg (Subtype.val) hcancel
    simpa [T', ContinuousLinearMap.codRestrict] using this

end Neumann

end HTGeometry
