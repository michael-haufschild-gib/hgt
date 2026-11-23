import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartTraceDuality
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveVolumeChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LaurentResidueBoundary
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularChartFormProduct

/-! The projective residue of the field trace vanishes on regular
top forms from every proper chart intersection. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- Use the affine volume on a chart to test regularity of the trace of
the logarithmic coefficient. -/
theorem IsFinCover.trace_logarithmic_coefficient_mem_chart (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I)
    (w : DR k E) (hw : w ∈ omB k E (rB k E x I) d) :
    (∏ j, x i / x j) * Algebra.trace F E (τ w) ∈ rA k x I := by
  let a : F := ∏ j, x i / x j
  let c : F := ∏ j, x j / x i
  let q := algebraMap F E a * τ w
  have hac : a * c = 1 := by
    change (∏ j, x i / x j) * (∏ j, x j / x i) = 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => by
      rw [div_mul_div_cancel₀ (h.pd.ne j), div_self (h.pd.ne i)]
  have hq : q * algebraMap F E c = τ w := by
    change algebraMap F E a * τ w * algebraMap F E c = τ w
    rw [mul_right_comm, ← map_mul, hac, map_one, one_mul]
  have hwd : w ∈ (⋀[E]^d Ω[E⁄k]).restrictScalars k :=
    omB_le_degree (B := rB k E x I) (p := d) hw
  have hwvol : w = τ w • vol0 k E x := h.topDegreeForms.2.1 τ hτ w hwd
  obtain ⟨ε, hε⟩ := volume_chart_change (K := E) h.pd i
  have hregular : q • (ExteriorAlgebra.ιMulti E d fun j =>
      D k E (algebraMap F E (chartCoordinates x i j))) ∈ omB k E (rB k E x I) d := by
    change q • (ExteriorAlgebra.ιMulti E d fun j =>
      D k E (algebraMap F E (x (i.succAbove j) / x i))) ∈ _
    rw [hε, Units.smul_def, ← Int.cast_smul_eq_zsmul E,
      smul_comm q (((ε : ℤ) : E)), smul_smul q (algebraMap F E c), hq, ← hwvol,
      Int.cast_smul_eq_zsmul]
    exact zsmul_mem hw _
  have htr := (h.intersection_trace_dual_iff hi q).mpr hregular 1
  simp only [Subalgebra.coe_one, mul_one] at htr
  have e : Algebra.trace F E q = a * Algebra.trace F E (τ w) := by
    calc
      _ = Algebra.trace F E (a • τ w) :=
        congrArg (Algebra.trace F E) (Algebra.smul_def a (τ w)).symm
      _ = _ := by rw [map_smul, smul_eq_mul]
  rwa [e] at htr

/-- The residue of the traced top coefficient vanishes on regular forms
from an intersection missing any standard chart. -/
theorem IsFinCover.traced_residue_eq_zero_of_missing_chart (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∉ I) (hI : I.Nonempty)
    (w : DR k E) (hw : w ∈ omB k E (rB k E x I) d) :
    ρ (Algebra.trace F E (τ w)) = 0 := by
  obtain ⟨j, hj⟩ := hI
  exact residue_eq_zero_of_missing_chart h.pd ρ hρ hi hj _
    (h.trace_logarithmic_coefficient_mem_chart τ hτ hj w hw)

end GlobalTheory.PD
