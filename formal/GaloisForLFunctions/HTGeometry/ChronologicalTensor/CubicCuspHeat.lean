import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspFlow
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionHeat
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Heat derived from the actual normalization-defect dynamics

Each summand is a diagonal coefficient of the induced quotient flow in the
proved quotient basis. Its geometric heat series is therefore derived from the
physical observation algebra. Subtracting this heat from an actual continuous
reference integral produces the previously audited Bose defect kernel.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial Module MeasureTheory


def cubicCuspModeHeat (u : ℝ) (n : ℕ) : ℝ :=
  cubicCuspDefectBasis.repr
    (cubicCuspDefectFlow (Real.exp (-Real.exp u)) (cubicCuspDefectBasis n)) n

theorem cubicCuspHeat_parameter (u : ℝ) : Real.exp (-Real.exp u) ∈ Ioo (0:ℝ) 1 :=
  ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos u))⟩

theorem cubicCuspModeHeat_eq (u : ℝ) (n : ℕ) :
    cubicCuspModeHeat u n=Real.exp (-((n+1 : ℕ) : ℝ)*Real.exp u) := by
  unfold cubicCuspModeHeat
  rw [cubicCuspDefectFlow_spectrum,map_smul,Module.Basis.repr_self]
  simp only [Finsupp.smul_apply,Finsupp.single_eq_same,smul_eq_mul,mul_one]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

def cubicCuspHeat (u : ℝ) : ℝ := ∑' n : ℕ, cubicCuspModeHeat u n

theorem cubicCuspHeat_hasSum (u : ℝ) :
    HasSum (cubicCuspModeHeat u) (1/(Real.exp (Real.exp u)-1)) := by
  let b := Real.exp u
  let q := Real.exp (-b)
  have hb : 0 < b := Real.exp_pos u
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb)
  have hgeo := hasSum_geometric_of_lt_one (Real.exp_pos (-b)).le hq
  have hmul := hgeo.mul_left q
  have hterm (n : ℕ) : cubicCuspModeHeat u n=q*q^n := by
    rw [cubicCuspModeHeat_eq]
    calc
      _ = Real.exp (((n+1 : ℕ) : ℝ)*(-b)) := by congr 1; ring
      _ = (Real.exp (-b))^(n+1) := Real.exp_nat_mul (-b) (n+1)
      _ = q*q^n := by rw [pow_succ,mul_comm]
  have he : 1 < Real.exp b := Real.one_lt_exp_iff.mpr hb
  have hden : Real.exp b-1 ≠ 0 := ne_of_gt (sub_pos.mpr he)
  have hvalue : q*(1-q)⁻¹=1/(Real.exp b-1) := by
    dsimp only [q]
    rw [Real.exp_neg]
    field_simp
  change HasSum (fun n : ℕ => q*q^n) (q*(1-q)⁻¹) at hmul
  rw [hvalue] at hmul
  change HasSum (fun n => cubicCuspModeHeat u n) (1/(Real.exp b-1))
  simpa only [hterm] using hmul

theorem cubicCuspHeat_eq (u : ℝ) : cubicCuspHeat u=1/(Real.exp (Real.exp u)-1) :=
  (cubicCuspHeat_hasSum u).tsum_eq

def cubicCuspContinuousHeat (t : ℝ) : ℝ := ∫ x : ℝ in Ioi 0, Real.exp (-t*x)

theorem cubicCuspContinuousHeat_integrable :
    ∀ t ∈ Ioi (0:ℝ), IntegrableOn (fun x : ℝ => Real.exp (-t*x)) (Ioi 0) := by
  intro t ht
  exact integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 0

theorem cubicCuspContinuousHeat_eq :
    EqOn cubicCuspContinuousHeat (fun t => 1/t) (Ioi 0) := by
  intro t ht
  unfold cubicCuspContinuousHeat
  rw [integral_exp_mul_Ioi (neg_neg_of_pos ht)]
  simp

def cubicCuspKernel (t : ℝ) : ℂ :=
  if 0<t then ((cubicCuspContinuousHeat t-cubicCuspHeat (Real.log t) : ℝ) : ℂ) else 0

theorem cubicCuspKernel_eq (t : ℝ) : cubicCuspKernel t=(fusionBoseDefect t : ℂ) := by
  by_cases ht : 0<t
  · have hcont := cubicCuspContinuousHeat_eq ht
    have hheat := cubicCuspHeat_eq (Real.log t)
    rw [Real.exp_log ht] at hheat
    simp only [cubicCuspKernel,if_pos ht,hcont,hheat,fusionBoseDefect]
  · simp [cubicCuspKernel,fusionBoseDefect,ht]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
