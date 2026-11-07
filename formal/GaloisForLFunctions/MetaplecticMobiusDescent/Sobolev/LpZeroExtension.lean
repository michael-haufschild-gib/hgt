/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license; see LICENSE and NOTICE in the parent directory.
Adapted from rellich-kondrachov, MeasureTheory/Function/LpSpace/Restrict.lean.
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Isometric extension by zero from a restricted measure -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev
namespace LpExtension
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1≤p)]
  {s : Set α} (hs : MeasurableSet s)

private def extendFun (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator f)

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
private lemma extendFun_coe (f : Lp E p (μ.restrict s)) :
    (extendFun hs f : α → E) =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp _

/-- Extension by zero is linear on almost-everywhere classes. -/
def extendLinear : Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ where
  toFun := extendFun hs
  map_add' f g := by
    apply Lp.ext
    have hadd := (ae_restrict_iff' hs).mp (Lp.coeFn_add f g)
    filter_upwards [extendFun_coe hs (f+g),extendFun_coe hs f,extendFun_coe hs g,
      Lp.coeFn_add (extendFun hs f) (extendFun hs g),hadd] with x hfg hf hg he ha
    by_cases hx : x∈s
    · simpa only [hfg,he,hf,hg,Set.indicator_of_mem hx,Pi.add_apply] using ha hx
    · simp only [hfg,he,hf,hg,Set.indicator_of_notMem hx,Pi.add_apply,zero_add]
  map_smul' c f := by
    change extendFun hs (c • f)=c • extendFun hs f
    apply Lp.ext
    have hsmul := (ae_restrict_iff' hs).mp (Lp.coeFn_smul c f)
    filter_upwards [extendFun_coe hs (c • f),extendFun_coe hs f,
      Lp.coeFn_smul c (extendFun hs f),hsmul] with x hcf hf he ha
    by_cases hx : x∈s
    · simpa only [hcf,he,hf,Set.indicator_of_mem hx,Pi.smul_apply] using ha hx
    · simp only [hcf,he,hf,Set.indicator_of_notMem hx,Pi.smul_apply,smul_zero]

/-- Extension preserves the full `Lᵖ` norm. -/
def extendIsometry : Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toLinearMap := extendLinear hs
  norm_map' f := by
    change ‖((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator f)‖=‖f‖
    rw [Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict hs]
    exact rfl

lemma extendIsometry_coe (f : Lp E p (μ.restrict s)) :
    (extendIsometry hs f : α → E) =ᵐ[μ] s.indicator f := extendFun_coe hs f

#print axioms extendIsometry
end LpExtension
end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev
