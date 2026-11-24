import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartLocalAlgebra
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FormDenominatorLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularChartFormProduct

/-! A regular form at an affine point admits a denominator from the
chart algebra that is nonzero at the point. -/

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  (B : Subalgebra k L) (p : ℕ)

/-- The regular forms are a module over the chart's regular functions. -/
def chartFormLattice : Submodule B (DR k L) where
  __ := (omB k L B p).toAddSubmonoid
  smul_mem' r v hv := by
    change (r : L) • v ∈ omB k L B p
    exact smul_mem_omB r.property hv

theorem chartFormLattice_restrictScalars : (chartFormLattice B p).restrictScalars k = omB k L B p :=
  Submodule.ext fun _ => Iff.rfl

/-- Clear the regularity denominator of a form on the point-local
chart without changing its exterior degree. -/
theorem exists_chartForm_denominator (e : B →ₐ[k] k) (w : DR k L)
    (hw : w ∈ omB k L (loc B e) p) :
    ∃ u : (RingHom.ker e.toRingHom).primeCompl, (u.val : L) • w ∈ omB k L B p := by
  let C := loc B e
  let S := (RingHom.ker e.toRingHom).primeCompl
  letI : Algebra B C := localChartAlgebra B e
  letI : IsScalarTower B C L := localChart_tower B e
  letI : IsScalarTower k B C := localChart_baseTower B e
  letI : IsLocalization S C := localChart_isLocalization B e
  let ω : ExteriorDifferentials k L p := ⟨w, omB_le_degree hw⟩
  have hω := (mem_omB_iff_pullback_range C ω).mp hw
  obtain ⟨u, hu⟩ := (mem_formRange_localization_iff S ω).mp hω
  exact ⟨u, (mem_omB_iff_pullback_range B ((u : B) • ω)).mpr hu⟩

end GlobalTheory.WH
