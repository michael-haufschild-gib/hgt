import GaloisForLFunctions.HTGeometry.GroupCharacter.RegularDecomposition
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Characters of the `G`-stable subspaces of the group algebra

`rho hN g` is the action of `g` on a `G`-stable `ℂ`-subspace `N` of `ℂ[G]`, and `chi hN g` is its
trace.  The main result is `sum_chi`, the raw form of column orthogonality: for any internal direct
sum decomposition of `ℂ[G]` into `G`-stable subspaces, the characters add up to the character of the
regular representation.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra

variable {G : Type u} [Group G] [Fintype G]

/-- The action of `g` on a `G`-stable subspace. -/
noncomputable def rho {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) :
    ↥N →ₗ[ℂ] ↥N := (regLeft G g).restrict (hN g)

omit [Fintype G] in
@[simp] theorem rho_coe {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G)
    (v : ↥N) : ((rho hN g v : ↥N) : MonoidAlgebra ℂ G) = regLeft G g (v : MonoidAlgebra ℂ G) :=
  rfl

omit [Fintype G] in
theorem rho_one {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    rho hN 1 = LinearMap.id := by
  ext v
  simp [rho_coe, regLeft_apply]

omit [Fintype G] in
theorem rho_mul {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g h : G) :
    rho hN (g * h) = (rho hN g) ∘ₗ (rho hN h) := by
  ext v
  simp only [rho_coe, LinearMap.coe_comp, Function.comp_apply, regLeft_apply]
  rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

/-- The character of a `G`-stable subspace. -/
noncomputable def chi {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) : ℂ :=
  LinearMap.trace ℂ ↥N (rho hN g)

theorem chi_one {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    chi hN 1 = (Module.finrank ℂ ↥N : ℂ) := by
  rw [chi, rho_one, LinearMap.trace_id]

/-- **Column orthogonality, raw form.** -/
theorem sum_chi [DecidableEq G] {n : ℕ} {N : Fin n → Submodule ℂ (MonoidAlgebra ℂ G)}
    (hN : ∀ i, IsGStable G (N i)) (hint : DirectSum.IsInternal N) (g : G) :
    ∑ i, chi (hN i) g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  rw [← trace_regLeft G g]
  exact (LinearMap.trace_eq_sum_trace_restrict hint (fun i => hN i g)).symm

end GaloisForLFunctions.HTGeometry.GroupCharacter
