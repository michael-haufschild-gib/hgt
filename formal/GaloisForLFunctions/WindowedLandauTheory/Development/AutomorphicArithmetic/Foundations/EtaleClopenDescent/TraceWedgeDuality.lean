import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TraceWedgePairing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExteriorBaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free

/-! The traced top wedge identifies a rational exterior degree with
the dual of its complementary degree over the projective coordinate field. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology KaehlerDifferential
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}

/-- The rational form in the second factor defines an F-linear
functional on the first factor by the traced top coefficient. -/
def traceWedgeDual (τ : DR k E →ₗ[E] E) :
    ExteriorDifferentials k E q →ₗ[F] Module.Dual F (ExteriorDifferentials k E p) where
  toFun b :=
    { toFun := fun a => Algebra.trace F E (τ ((a : DR k E) * (b : DR k E)))
      map_add' := fun a a' => by rw [Submodule.coe_add, add_mul, map_add, map_add]
      map_smul' := fun c a => by
        change Algebra.trace F E (τ (((algebraMap F E c) • (a : DR k E)) * (b : DR k E))) = _
        rw [smul_mul_assoc, map_smul, IsScalarTower.algebraMap_smul E, map_smul]
        rfl }
  map_add' b b' := by
    ext a
    change Algebra.trace F E (τ ((a : DR k E) * ((b + b' : ExteriorDifferentials k E q) : DR k E))) = _
    simp only [Submodule.coe_add, mul_add, map_add]
    rfl
  map_smul' c b := by
    ext a
    change Algebra.trace F E (τ ((a : DR k E) * ((algebraMap F E c) • (b : DR k E)))) = _
    rw [mul_smul_comm, map_smul, IsScalarTower.algebraMap_smul E, map_smul]
    rfl

theorem traceWedgeDual_apply (τ : DR k E →ₗ[E] E) (a : ExteriorDifferentials k E p)
    (b : ExteriorDifferentials k E q) :
    traceWedgeDual (F := F) τ b a = Algebra.trace F E (τ ((a : DR k E) * (b : DR k E))) := rfl

/-- Every functional in the testing degree is represented by a
complementary rational form. -/
theorem IsFinCover.traceWedgeDual_bijective (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d) :
    Function.Bijective (traceWedgeDual (F := F) (p := p) (q := q) τ) := by
  letI := h.fin
  obtain ⟨b, _⟩ := h.exists_coordinateDifferentialBasis
  let P := ExteriorDifferentials k E p
  let Q := ExteriorDifferentials k E q
  letI : Module.Finite E P := Module.Finite.of_basis (b.exteriorPower p)
  letI : Module.Finite E Q := Module.Finite.of_basis (b.exteriorPower q)
  letI : Module.Finite F P := Module.Finite.trans E P
  letI : Module.Finite F Q := Module.Finite.trans E Q
  let e : Q →ₗ[F] Module.Dual F P := traceWedgeDual τ
  have he : Function.Injective e := by
    refine LinearMap.ker_eq_bot.mp ?_
    rw [LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    refine h.trace_wedge_pairing_nondegenerate τ hτ hpq y.property (fun a ha => ?_)
    have heval := LinearMap.congr_fun hy (⟨a, ha⟩ : P)
    exact heval
  have hdim : Module.finrank F Q = Module.finrank F (Module.Dual F P) := by
    rw [Subspace.dual_finrank_eq, ← Module.finrank_mul_finrank F E Q, ← Module.finrank_mul_finrank F E P]
    rw [h.finrank_exteriorDifferentials_complement hpq]
  exact ⟨he, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp he⟩

end GlobalTheory.PD
