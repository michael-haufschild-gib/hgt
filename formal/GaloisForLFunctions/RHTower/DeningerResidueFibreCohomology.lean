import GaloisForLFunctions.RHTower.DeningerFlasqueAcyclic

/-!
# Cohomology of the fibre of a residue morphism

If the residue morphism of sheaves is onto, its fibre is the kernel, and the long exact sequence of
sheaf cohomology compares the fibre with the source.  When the residue target is acyclic — which is
the amplitude statement for the prime-packet and skyscraper targets — the comparison is an
isomorphism in every degree above one, and is onto in degree one.  So all the higher cohomology of
the fibre is the higher cohomology of the source, and the only new information sits in low degrees.

* `deningerKernelShortExact` : an epimorphism of sheaves has a short exact kernel sequence.
* `deningerFibre_ext_bijective` : above degree one the fibre and the source agree.
* `deningerFibre_ext_surjective` : in degree one the comparison is onto.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

universe w u

variable {X : TopCat.{u}} [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

omit [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)] in
/-- **The kernel sequence of an epimorphism of sheaves is short exact**: this is the fibre of a
surjective residue morphism. -/
theorem deningerKernelShortExact {G D : TopCat.Sheaf AddCommGrpCat.{u} X} (f : G ⟶ D) [Epi f] :
    (ShortComplex.mk (kernel.ι f) f (by simp)).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := inferInstance
  epi_g := inferInstance

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}

/-- **Above degree one the fibre and the source have the same cohomology**, when the residue target
is acyclic. -/
theorem deningerFibre_ext_bijective (hS : S.ShortExact)
    (hD : ∀ (U : Opens X) (m : ℕ) (x : deningerSheafCohomology.{w} U S.X₃ (m + 1)), x = 0)
    (U : Opens X) (n : ℕ) :
    Function.Bijective (fun x : deningerSheafCohomology.{w} U S.X₁ (n + 2) =>
      x.comp (Ext.mk₀ S.f) (add_zero (n + 2))) := by
  constructor
  · intro x y hxy
    have hxy' : x.comp (Ext.mk₀ S.f) (add_zero (n + 2)) =
        y.comp (Ext.mk₀ S.f) (add_zero (n + 2)) := hxy
    have hsub : (x - y).comp (Ext.mk₀ S.f) (add_zero (n + 2)) = 0 := by
      have h1 : (x - y).comp (Ext.mk₀ S.f) (add_zero (n + 2)) =
          x.comp (Ext.mk₀ S.f) (add_zero (n + 2)) -
            y.comp (Ext.mk₀ S.f) (add_zero (n + 2)) := by
        rw [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, ← sub_eq_add_neg]
      rw [h1, hxy', sub_self]
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (deningerOpenFree U) hS (x - y) hsub
      (n₀ := n + 1) rfl
    have hz : x₃ = 0 := hD U n x₃
    have : x - y = 0 := by rw [← hx₃, hz]; apply Ext.zero_comp
    exact sub_eq_zero.1 this
  · intro y
    have hy : y.comp (Ext.mk₀ S.g) (add_zero (n + 2)) = 0 := hD U (n + 1) _
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ (deningerOpenFree U) hS y hy
    exact ⟨x, hx⟩

/-- **In degree one the comparison from the fibre to the source is onto**, when the residue target
is acyclic. -/
theorem deningerFibre_ext_surjective (hS : S.ShortExact)
    (hD : ∀ (U : Opens X) (m : ℕ) (x : deningerSheafCohomology.{w} U S.X₃ (m + 1)), x = 0)
    (U : Opens X) :
    Function.Surjective (fun x : deningerSheafCohomology.{w} U S.X₁ 1 =>
      x.comp (Ext.mk₀ S.f) (add_zero 1)) := by
  intro y
  have hy : y.comp (Ext.mk₀ S.g) (add_zero 1) = 0 := hD U 0 _
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ (deningerOpenFree U) hS y hy
  exact ⟨x, hx⟩

end RHTower
