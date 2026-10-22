import GaloisForLFunctions.RHTower.Deninger.DeningerAmalgamationUniversalDescent
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Real.Basic

/-!
# The finite logarithmic residue square

In the split log-toric coordinate a lattice vector is its kernel part plus a multiple of the
uniformizer, so its logarithmic differential is the kernel logarithmic differential plus that
multiple of `dz/z`.  The residue reads the second coordinate, so the residue of the logarithmic
differential of a lattice vector is its valuation: that is the commutative residue square, and it
is the tame residue in degree one.

Changing the uniformizer inside the kernel changes only the first coordinate, so the residue is
independent of the splitting.  A functional that kills the kernel part and normalizes the
uniformizer is the residue, which is the characterization the square rests on.

Specialization together with the residue is a map into a split square-zero extension: the universal
property of the exterior algebra lifts the valuation, and products of two positive-degree
generators vanish.

* `deningerFiniteResidue_logDifferential` : the residue square `(9)`--`(10)`.
* `deningerFiniteResidue_uniformizer_change` : independence of the splitting.
* `deningerFiniteResidue_unique` : the characterization `(7)`.
* `deningerFiniteResidueLift` : the square-zero lift.
-/

namespace RHTower

section ResidueSquare

variable {K Om : Type*} [AddCommGroup K] [Module ℝ K] [AddCommGroup Om] [Module ℝ Om]

/-- The valuation of the split log-toric coordinate: the uniformizer exponent. -/
def deningerValuation : (K × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ K ℝ

/-- The logarithmic differential in the split coordinate: the kernel differential on the kernel
part, and the uniformizer exponent on `dz/z`. -/
def deningerLogDifferential (dlogK : K →ₗ[ℝ] Om) : (K × ℝ) →ₗ[ℝ] (Om × ℝ) :=
  LinearMap.prodMap dlogK LinearMap.id

/-- The logarithmic residue: the coefficient of `dz/z`. -/
def deningerFiniteResidue : (Om × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ Om ℝ

@[simp]
theorem deningerFiniteResidue_apply (w : Om) (c : ℝ) :
    deningerFiniteResidue (w, c) = c := rfl

/-- **The residue square `(9)`--`(10)`.**  The residue of the logarithmic differential of a lattice
vector is its valuation. -/
theorem deningerFiniteResidue_logDifferential (dlogK : K →ₗ[ℝ] Om) (a : K × ℝ) :
    deningerFiniteResidue (deningerLogDifferential dlogK a) = deningerValuation a := rfl

/-- **The residue is the tame residue in degree one**: as maps out of the lattice, the residue of
the logarithmic differential and the valuation are the same map. -/
theorem deningerFiniteResidue_comp_logDifferential (dlogK : K →ₗ[ℝ] Om) :
    (deningerFiniteResidue (Om := Om)).comp (deningerLogDifferential dlogK)
      = deningerValuation (K := K) := by
  refine LinearMap.ext fun a => ?_
  exact deningerFiniteResidue_logDifferential dlogK a

/-- **Independence of the splitting.**  Changing the uniformizer by a kernel vector changes only
the kernel component of the logarithmic differential, so the residue is unchanged. -/
theorem deningerFiniteResidue_uniformizer_change (dlogK : K →ₗ[ℝ] Om) (u : K) (a : K × ℝ) :
    deningerFiniteResidue
        (deningerLogDifferential dlogK a + ((deningerValuation a) • dlogK u, 0))
      = deningerFiniteResidue (deningerLogDifferential dlogK a) := by
  show (deningerLogDifferential dlogK a).2 + 0 = (deningerLogDifferential dlogK a).2
  rw [add_zero]

/-- **The characterization `(7)`.**  A functional killing the kernel part and normalizing the
uniformizer is the residue. -/
theorem deningerFiniteResidue_unique (r : (Om × ℝ) →ₗ[ℝ] ℝ) (hker : ∀ w : Om, r (w, 0) = 0)
    (hone : r (0, 1) = 1) : r = deningerFiniteResidue := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨w, c⟩ := z
  have hsplit : ((w, c) : Om × ℝ) = (w, 0) + c • ((0 : Om), (1 : ℝ)) := by
    refine Prod.ext ?_ ?_
    · show w = w + c • (0 : Om)
      rw [smul_zero, add_zero]
    · show c = 0 + c • (1 : ℝ)
      rw [smul_eq_mul, mul_one, zero_add]
  rw [hsplit, map_add, map_smul, hker w, hone, smul_eq_mul, mul_one, zero_add, ← hsplit,
    deningerFiniteResidue_apply]

end ResidueSquare

section SquareZeroLift

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The residue direction of the split square-zero extension at a finite place. -/
noncomputable def deningerFiniteResidueGenerator (lam : V →ₗ[ℝ] ℝ) :
    V →ₗ[ℝ] TrivSqZeroExt ℝ ℝ :=
  (TrivSqZeroExt.inrHom ℝ ℝ).comp lam

theorem deningerFiniteResidueGenerator_sq (lam : V →ₗ[ℝ] ℝ) (v : V) :
    deningerFiniteResidueGenerator lam v * deningerFiniteResidueGenerator lam v = 0 :=
  TrivSqZeroExt.inr_mul_inr ℝ (lam v) (lam v)

/-- **The square-zero lift of the finite residue.**  Specialization plus residue is an algebra map
into the split square-zero extension. -/
noncomputable def deningerFiniteResidueLift (lam : V →ₗ[ℝ] ℝ) :
    ExteriorAlgebra ℝ V →ₐ[ℝ] TrivSqZeroExt ℝ ℝ :=
  ExteriorAlgebra.lift ℝ ⟨deningerFiniteResidueGenerator lam, deningerFiniteResidueGenerator_sq lam⟩

@[simp]
theorem deningerFiniteResidueLift_iota (lam : V →ₗ[ℝ] ℝ) (v : V) :
    deningerFiniteResidueLift lam (ExteriorAlgebra.ι ℝ v) = TrivSqZeroExt.inr (lam v) := by
  rw [deningerFiniteResidueLift, ExteriorAlgebra.lift_ι_apply]
  rfl

/-- **Products of two positive-degree generators vanish**, so the two square-zero lifts agree on
the whole free unit algebra and not only in degree one. -/
theorem deningerFiniteResidueLift_mul_eq_zero (lam : V →ₗ[ℝ] ℝ) (v w : V) :
    deningerFiniteResidueLift lam (ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.ι ℝ w) = 0 := by
  rw [map_mul, deningerFiniteResidueLift_iota, deningerFiniteResidueLift_iota]
  exact TrivSqZeroExt.inr_mul_inr ℝ (lam v) (lam w)

end SquareZeroLift

end RHTower
