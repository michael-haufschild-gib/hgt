import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairFlow
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspHeat
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite repair heat and its matching continuous reference

The finite heat is the sum of actual quotient-flow diagonal coefficients.
It equals the truncated geometric heat series. Integrating the same exponential
on the finite interval gives the matching continuous reference. Their difference
is exactly the original normalization-defect kernel times 1-exp(-k t).
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial Module MeasureTheory


def cubicFiniteModeHeat (k : ℕ) (u : ℝ) (i : Fin k) : ℝ :=
  (cubicFiniteDefectBasis k).repr
    (cubicFiniteDefectFlow k (Real.exp (-Real.exp u)) (cubicFiniteDefectBasis k i)) i

theorem cubicFiniteModeHeat_eq (k : ℕ) (u : ℝ) (i : Fin k) :
    cubicFiniteModeHeat k u i=Real.exp (-((i.val+1 : ℕ) : ℝ)*Real.exp u) := by
  unfold cubicFiniteModeHeat
  rw [cubicFiniteDefectFlow_spectrum,map_smul,Module.Basis.repr_self]
  simp only [Finsupp.smul_apply,Finsupp.single_eq_same,smul_eq_mul,mul_one]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

def cubicFiniteHeat (k : ℕ) (u : ℝ) : ℝ := ∑ i : Fin k, cubicFiniteModeHeat k u i

theorem cubicFiniteHeat_partialSum (k : ℕ) (u : ℝ) :
    cubicFiniteHeat k u=∑ n ∈ Finset.range k, cubicCuspModeHeat u n := by
  unfold cubicFiniteHeat
  simp_rw [cubicFiniteModeHeat_eq,cubicCuspModeHeat_eq]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => Real.exp (-((n+1:ℕ):ℝ)*Real.exp u)) k

theorem cubicFiniteHeat_eq (k : ℕ) (u : ℝ) :
    cubicFiniteHeat k u=(1-Real.exp (-(k:ℝ)*Real.exp u))/(Real.exp (Real.exp u)-1) := by
  let q := Real.exp (-Real.exp u)
  have hq : q ≠ 1 := ne_of_lt (cubicCuspHeat_parameter u).2
  have he : Real.exp (Real.exp u)-1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (Real.exp_pos u)))
  have hterm (n : ℕ) : cubicCuspModeHeat u n=q*q^n := by
    rw [cubicCuspModeHeat_eq]
    calc
      _ = Real.exp (((n+1 : ℕ) : ℝ)*(-Real.exp u)) := by congr 1; ring
      _ = q^(n+1) := Real.exp_nat_mul _ _
      _ = q*q^n := by rw [pow_succ,mul_comm]
  rw [cubicFiniteHeat_partialSum]
  simp_rw [hterm]
  rw [← Finset.mul_sum,geom_sum_eq hq]
  have hk : Real.exp (-(k:ℝ)*Real.exp u)=q^k := by
    rw [neg_mul,← mul_neg]
    exact Real.exp_nat_mul _ _
  rw [hk]
  dsimp only [q]
  rw [Real.exp_neg]
  have he2 : 1-Real.exp (Real.exp u) ≠ 0 := sub_ne_zero.mpr (ne_of_lt (Real.one_lt_exp_iff.mpr (Real.exp_pos u)))
  field_simp [he2]
  ring

def cubicFiniteContinuousHeat (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..(k:ℝ), Real.exp (-t*x)

theorem cubicFiniteContinuousHeat_eq (k : ℕ) :
    EqOn (cubicFiniteContinuousHeat k)
      (fun t => (1-Real.exp (-(k:ℝ)*t))/t) (Ioi 0) := by
  intro t ht
  unfold cubicFiniteContinuousHeat
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr (ne_of_gt ht)),integral_exp]
  simp only [mul_zero,Real.exp_zero,smul_eq_mul]
  rw [neg_mul,neg_mul,mul_comm t (k:ℝ)]
  field_simp
  ring

def cubicFiniteKernel (k : ℕ) (t : ℝ) : ℂ :=
  if 0<t then ((cubicFiniteContinuousHeat k t-cubicFiniteHeat k (Real.log t) : ℝ) : ℂ) else 0

theorem cubicFiniteKernel_factor (k : ℕ) (t : ℝ) :
    cubicFiniteKernel k t=(1-(Real.exp (-(k:ℝ)*t) : ℂ))*cubicCuspKernel t := by
  by_cases ht : 0<t
  · have hc := cubicFiniteContinuousHeat_eq k ht
    have hh := cubicFiniteHeat_eq k (Real.log t)
    rw [Real.exp_log ht] at hh
    rw [cubicCuspKernel_eq]
    simp only [cubicFiniteKernel,hc,hh,fusionBoseDefect,if_pos ht]
    push_cast
    ring
  · simp [cubicFiniteKernel,cubicCuspKernel,ht]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
