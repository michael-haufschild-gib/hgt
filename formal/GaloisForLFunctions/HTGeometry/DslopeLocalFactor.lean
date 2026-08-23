import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Divided slopes from a local linear factor

`dslope f a` is the analytic continuation of `z ↦ (f z - f a) / (z - a)` across `a`.  When `f`
is known concretely as `(z - a) * g` on a neighbourhood of `a`, with `g` differentiable there,
the divided slope *is* `g` near `a`; in particular it is differentiable at `a`.

This is the tool that removes the singularity of a quotient `f / (· - a)` at a zero of `f`
without any appeal to a domain of holomorphy: only the factorization is needed.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **A local linear factor identifies the divided slope.**  If `f` factors as `(z - a) * g`
near `a` with `g` differentiable at `a`, then `dslope f a` agrees with `g` near `a`. -/
theorem dslope_eventuallyEq_of_localFactor {f g : 𝕜 → 𝕜} {a : 𝕜}
    (hg : DifferentiableAt 𝕜 g a) (hfac : f =ᶠ[𝓝 a] fun z => (z - a) * g z) :
    dslope f a =ᶠ[𝓝 a] g := by
  have hf0 : f a = 0 := by
    have := hfac.self_of_nhds
    simpa using this
  have hderiv : deriv f a = g a := by
    have hb : HasDerivAt (fun w : 𝕜 => w - a) 1 a := (hasDerivAt_id a).sub_const a
    have hmul : HasDerivAt (fun z : 𝕜 => (z - a) * g z) (g a) a := by
      simpa [Pi.mul_def] using hb.mul hg.hasDerivAt
    exact (hmul.congr_of_eventuallyEq hfac).deriv
  filter_upwards [hfac] with z hz
  rcases eq_or_ne z a with rfl | hne
  · rw [dslope_same]; exact hderiv
  · rw [dslope_of_ne _ hne, slope_def_field, hz, hf0, sub_zero]
    field_simp

/-- Consequently the divided slope is differentiable at the factorization point. -/
theorem differentiableAt_dslope_of_localFactor {f g : 𝕜 → 𝕜} {a : 𝕜}
    (hg : DifferentiableAt 𝕜 g a) (hfac : f =ᶠ[𝓝 a] fun z => (z - a) * g z) :
    DifferentiableAt 𝕜 (dslope f a) a :=
  hg.congr_of_eventuallyEq (dslope_eventuallyEq_of_localFactor hg hfac)

/-- **Holomorphy near a point makes the divided slope holomorphic at it.**  This is the
removable-singularity theorem in the form every quotient computation needs. -/
theorem differentiableAt_dslope_of_eventually_differentiableAt {f : ℂ → ℂ} {a : ℂ}
    (hf : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ f z) : DifferentiableAt ℂ (dslope f a) a := by
  obtain ⟨s, hs, hopen, hmem⟩ := eventually_nhds_iff.mp hf
  have hson : DifferentiableOn ℂ f s := fun z hz => (hs z hz).differentiableWithinAt
  have hd : DifferentiableOn ℂ (dslope f a) s :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds hmem)).mpr hson
  exact hd.differentiableAt (hopen.mem_nhds hmem)

end GaloisForLFunctions.HTGeometry
