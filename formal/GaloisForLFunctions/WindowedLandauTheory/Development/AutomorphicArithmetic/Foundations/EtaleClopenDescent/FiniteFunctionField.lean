import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! A finite algebra of affine functions spans a finite extension when
its fractions generate the function field. -/

namespace GlobalTheory.SchemeCohomology

/-- If a ring map is finite and the coefficient ring maps into a subfield,
the field of fractions of its image is finite over that subfield. -/
theorem finiteDimensional_of_finite_fraction_image {A B F L : Type*}
    [CommRing A] [CommRing B] [Field F] [Field L] [Algebra F L]
    (φ : A →+* B) (hφ : φ.Finite) (g : B →+* L)
    (hcoeff : ∀ a, g (φ a) ∈ Set.range (algebraMap F L))
    (hfrac : ∀ z : L, ∃ a b : B, g b ≠ 0 ∧ z * g b = g a) :
    FiniteDimensional F L := by
  letI := φ.toAlgebra
  letI : Module.Finite A B := hφ
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := B)
  let M : Submodule F L := Submodule.span F (g '' (S : Set B))
  have hM : M.FG := Submodule.fg_span (S.finite_toSet.image g)
  have hmem (b : B) : g b ∈ M := by
    have hb : b ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact M.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact M.add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨c, hc⟩ := hcoeff a
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← hc, ← Algebra.smul_def]
      exact M.smul_mem c hx
  let R := Algebra.adjoin F (Set.range g)
  have hR : R.toSubmodule ≤ M := by
    rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.2 fun x hx => ?_
    have hx' : x ∈ g.range.toSubmonoid := Submonoid.closure_le.2 (fun _ hy => hy) hx
    obtain ⟨b, rfl⟩ := hx'
    exact hmem b
  have hRfg : R.toSubmodule.FG := by
    letI : FiniteDimensional F M := (Submodule.fg_iff_finiteDimensional M).mp hM
    exact (Submodule.fg_iff_finiteDimensional _).mpr
      (FiniteDimensional.of_injective (Submodule.inclusion hR) (Submodule.inclusion_injective hR))
  have htop : M = ⊤ := by
    apply eq_top_iff.2
    intro z _
    obtain ⟨a, b, hb, e⟩ := hfrac z
    have hbR : g b ∈ R := Algebra.subset_adjoin ⟨b, rfl⟩
    have hint : IsIntegral F (g b) := IsIntegral.of_mem_of_fg R hRfg _ hbR
    have hinv : (g b)⁻¹ ∈ R := R.inv_mem_of_algebraic (x := ⟨g b, hbR⟩) hint.isAlgebraic
    have hz : z = g a * (g b)⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [hz]
    exact hR (R.mul_mem (Algebra.subset_adjoin ⟨a, rfl⟩) hinv)
  exact ⟨htop ▸ hM⟩

end GlobalTheory.SchemeCohomology
