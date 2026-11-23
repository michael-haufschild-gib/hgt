import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLogarithmicForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularChartFormProduct
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Exterior degrees above the dimension contribute zero to the
global trace and to each local determinant coefficient. -/

noncomputable section

open GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

private theorem trace_eq_zero_of_bot {k ι M : Type} [Field k] [LinearOrder ι]
    [AddCommGroup M] [Module k M] (A : Finset ι → Submodule k M) (h : ∀ I, A I = ⊥) (q : ℤ)
    (f : (cech A).H q →ₗ[k] (cech A).H q) : LinearMap.trace k _ f = 0 := by
  have hz (x : (cech A).Z q) : x.val = 0 := by
    funext I
    have hI := (Submodule.mem_pi.mp x.property.1) I (Set.mem_univ I)
    simp only [h, ite_self, Submodule.mem_bot] at hI
    exact hI
  letI : Subsingleton ((cech A).Z q) :=
    ⟨fun x y => Subtype.ext ((hz x).trans (hz y).symm)⟩
  letI : Subsingleton ((cech A).H q) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  rw [Subsingleton.elim f 0, map_zero]

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
  [Algebra F E] [IsScalarTower k F E] {d : ℕ} {x : Fin (d + 1) → F}

/-- The trace vanishes on rational Čech cohomology in exterior degree
greater than the dimension. -/
theorem IsFinCover.trace_rationalCech_eq_zero_of_dim_lt (h : IsFinCover k E x)
    {a : ℕ} (ha : d < a) (q : ℤ)
    (u : (cech (fun I => omB k E (rB k E x I) a)).H q →ₗ[k]
      (cech (fun I => omB k E (rB k E x I) a)).H q) : LinearMap.trace k _ u = 0 := by
  apply trace_eq_zero_of_bot _ _ q u
  intro I
  apply bot_unique
  intro z hz
  exact (Submodule.mem_bot k).mpr (h.topDegreeForms.2.2 a ha z (omB_le_degree hz))

/-- The fixed-point numerator has no coefficient above the dimension. -/
theorem coeff_det_one_add_X_smul_eq_zero_of_dim_lt {a : ℕ} (ha : d < a)
    (M : Matrix (Fin d) (Fin d) k) :
    (Matrix.det (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C)).coeff a = 0 := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Finset.powersetCard_eq_empty.2 (by simpa only [Finset.card_univ, Fintype.card_fin] using ha),
    Finset.sum_empty]

end GlobalTheory.PD
