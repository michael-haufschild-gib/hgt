import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicCoefficientLattice
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalSystem

/-! Dividing the logarithmic volume by the field degree gives a
regularity-preserving section of the trace of the top coefficient. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- The traced coefficient in the logarithmic volume basis. -/
def traceTopCoefficient (τ : DR k E →ₗ[E] E) : ExteriorDifferentials k E d →ₗ[F] F :=
  (Algebra.trace F E).comp ((τ.comp (ExteriorDifferentials k E d).subtype).restrictScalars F)

theorem IsFinCover.traceTopCoefficient_mem (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (I : Finset (Fin (d + 1)))
    {w : ExteriorDifferentials k E d} (hw : w ∈ regularExteriorLattice (rB k E x I) d) :
    traceTopCoefficient (F := F) τ w ∈ logCoefficientLattice k x I :=
  h.trace_logarithmic_coefficient_mem_lattice τ hτ (w : DR k E) hw

/-- The section of traced top coefficients sends regular coefficients
to regular forms on every nonempty intersection. -/
theorem IsFinCover.exists_logarithmicTraceSection (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) :
    ∃ s : F →ₗ[F] ExteriorDifferentials k E d,
      (∀ c, traceTopCoefficient τ (s c) = c) ∧
      (∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ c ∈ logCoefficientLattice k x I,
        s c ∈ regularExteriorLattice (rB k E x I) d) := by
  letI := h.fin
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  let n : F := Module.finrank F E
  have hn : n ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Module.finrank_pos (R := F) (M := E)))
  let ω : ExteriorDifferentials k E d := exteriorPower.ιMulti E d fun j =>
    (algebraMap F E (x j.succ / x 0))⁻¹ • D k E (algebraMap F E (x j.succ / x 0))
  let s := (LinearMap.id : F →ₗ[F] F).smulRight (n⁻¹ • ω)
  have htr : traceTopCoefficient (F := F) τ ω = n := by
    change Algebra.trace F E (τ (vol0 k E x)) = n
    rw [hτ.1]
    simpa only [map_one, nsmul_eq_mul, mul_one] using
      (Algebra.trace_algebraMap (R := F) (S := E) (1 : F))
  refine ⟨s, ?_, ?_⟩
  · intro c
    change traceTopCoefficient (F := F) τ (c • n⁻¹ • ω) = c
    rw [map_smul, map_smul, htr]
    change c * (n⁻¹ * n) = c
    rw [inv_mul_cancel₀ hn, mul_one]
  · intro I hI c hc
    obtain ⟨i, hi⟩ := hI
    let a : F := ∏ l, x l / x i
    let b : F := logCoefficientScale x i
    have hba : b * a = 1 := by
      change (∏ l, x i / x l) * (∏ l, x l / x i) = 1
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun l _ => by rw [div_mul_div_cancel₀ (h.pd.ne l), div_self (h.pd.ne i)]
    have hbc : b * c ∈ rA k x I := (h.pd.mem_logCoefficientLattice_iff hi).mp hc
    have hnI : n⁻¹ ∈ rA k x I := by
      rw [show n⁻¹ = algebraMap k F ((Module.finrank F E : k)⁻¹) by simp [n]]
      exact Subalgebra.algebraMap_mem _ _
    have hregular : a • ω ∈ regularExteriorLattice (rB k E x I) d := by
      obtain ⟨ε, hv⟩ := volume_chart_change (K := E) h.pd i
      have hmem : (ExteriorAlgebra.ιMulti E d fun l =>
          D k E (algebraMap F E (x (i.succAbove l) / x i))) ∈ omB k E (rB k E x I) d := by
        refine Submodule.subset_span ⟨1, one_mem _, fun l => algebraMap F E (x (i.succAbove l) / x i),
          fun l => ?_, (one_smul E _).symm⟩
        exact isIntegral_algebraMap (x := (⟨_, Algebra.subset_adjoin ⟨i, hi, i.succAbove l, rfl⟩⟩ : rA k x I))
      rw [hv] at hmem
      have he : ε⁻¹ • (ε • algebraMap F E a • vol0 k E x) = algebraMap F E a • vol0 k E x := by
        rw [smul_smul, inv_mul_cancel, one_smul]
      change algebraMap F E a • vol0 k E x ∈ omB k E (rB k E x I) d
      rw [← he, Units.smul_def]
      exact zsmul_mem hmem _
    have hcoef : (n⁻¹ * (b * c)) * a = c * n⁻¹ := by
      calc
        _ = (b * a) * (c * n⁻¹) := by ac_rfl
        _ = _ := by rw [hba, one_mul]
    have hm := smul_mem_regularExteriorLattice I d (n⁻¹ * (b * c))
      ((rA k x I).mul_mem hnI hbc) (a • ω) hregular
    rw [smul_smul, hcoef, ← smul_smul] at hm
    exact hm

end GlobalTheory.PD
