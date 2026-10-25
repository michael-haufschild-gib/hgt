import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Commuting families in finite dimension have common eigenvectors

An arbitrary commuting family on a nonzero finite complex space has a common
eigenvector. Restriction to a proper eigenspace reduces the dimension.
-/
section

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

/-- Every commuting family on a nonzero finite complex vector space has a common eigenvector. -/
theorem exists_common_eigenvector_family
    {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (f : ι → Module.End ℂ V) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ∃ (x : V) (χ : ι → ℂ), x ≠ 0 ∧ ∀ i, f i x = χ i • x := by
  classical
  generalize hdim : Module.finrank ℂ V = n
  induction n using Nat.strongRecOn generalizing V with
  | ind n ih =>
      by_cases hall : ∀ i, ∃ z : ℂ, f i = z • (1 : Module.End ℂ V)
      · choose χ hχ using hall
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        refine ⟨x, χ, hx, fun i => ?_⟩
        rw [hχ i]
        rfl
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨z, hz⟩ := (f i).exists_eigenvalue
        let E := (f i).eigenspace z
        have hEbot : E ≠ ⊥ := hz
        have hEtop : E ≠ ⊤ := by
          intro h
          apply hi z
          ext x
          change f i x = z • x
          apply Module.End.mem_eigenspace_iff.mp
          change x ∈ E
          rw [h]
          trivial
        have hmaps (j : ι) : Set.MapsTo (f j) E E := by
          intro x hx
          have hix := Module.End.mem_eigenspace_iff.mp hx
          apply Module.End.mem_eigenspace_iff.mpr
          calc
            f i (f j x) = f j (f i x) := LinearMap.congr_fun (hcomm i j).eq x
            _ = z • f j x := by rw [hix, map_smul]
        let g (j : ι) : Module.End ℂ E := (f j).restrict (hmaps j)
        have hg (j k : ι) : Commute (g j) (g k) := by
          ext x
          exact LinearMap.congr_fun (hcomm j k).eq x
        letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hEbot
        have hlt : Module.finrank ℂ E < n := by
          rw [← hdim]
          exact Submodule.finrank_lt hEtop
        obtain ⟨x, χ, hx, hχ⟩ := ih (Module.finrank ℂ E) hlt g hg rfl
        refine ⟨(x : V), χ, fun h => hx (Subtype.ext h), fun j => ?_⟩
        exact congrArg Subtype.val (hχ j)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_common_eigenvector_family
end
end

