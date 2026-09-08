import GaloisForLFunctions.RHTower.CCMArchimedeanQuantizedCalculus
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

/-!
# A closed two-channel nonlocal Cauchy resolvent on the corpus's Hardy carrier

The signed negative Cauchy projection is constructed from the existing Fourier
unitary and half-line cutoff. Independent Schwartz coefficients are normalized
by `4(1 + seminorm₀₀)`; this discharges smallness explicitly for every input.
Right multiplication by the nonlocal jump perturbation has norm at most `5/16`.
Its Cauchy compression therefore has an unconditional inverse, with unique
solutions and global forcing-data Lipschitz constant `16/11`.

This applies the inverse-equation mechanism of Propositions 4.3–4.4 of
Yan–Zhang–Zhu, arXiv:2607.19649, to the existing Connes–Consani/Sonin L² carrier.
The coefficients are prescribed normalized Schwartz symbols, not claimed to
arise from a nonlinear direct-scattering map.
-/

open MeasureTheory Complex
open scoped SchwartzMap
namespace RHTower.FokasLenells
noncomputable section

abbrev Boundary := SoninL2 × SoninL2

def smallMultiplier (f : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  (((4*(1+SchwartzMap.seminorm ℂ 0 0 f))⁻¹ : ℝ) : ℂ) • ccmSchwartzMultiplier f

theorem smallMultiplier_bound (f : 𝓢(ℝ, ℂ)) (u : SoninL2) :
    ‖smallMultiplier f u‖ ≤ (1/4 : ℝ)*‖u‖ := by
  let S : ℝ := SchwartzMap.seminorm ℂ 0 0 f
  have hS : 0 ≤ S := apply_nonneg (SchwartzMap.seminorm ℂ 0 0) f
  have hd : 0 < 4*(1+S) := by positivity
  have hratio : (4*(1+S))⁻¹*S ≤ (1/4 : ℝ) := by
    rw [inv_mul_eq_div, div_le_iff₀ hd]
    linarith
  have hM : ‖ccmSchwartzMultiplier f u‖ ≤ S*‖u‖ :=
    le_trans ((ccmSchwartzMultiplier f).le_opNorm u)
      (mul_le_mul_of_nonneg_right (norm_ccmSchwartzMultiplier_le f) (norm_nonneg u))
  change ‖((↑((4*(1+S))⁻¹) : ℂ) • ccmSchwartzMultiplier f) u‖ ≤ _
  simp only [smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  calc
    (4*(1+S))⁻¹ * ‖ccmSchwartzMultiplier f u‖ ≤
        (4*(1+S))⁻¹ * (S*‖u‖) := mul_le_mul_of_nonneg_left hM (by positivity)
    _ ≤ (1/4 : ℝ)*‖u‖ := by nlinarith [norm_nonneg u]

/-- The signed negative Cauchy projection, built from the corpus's Fourier unitary. -/
def negativeCauchy : SoninL2 →L[ℂ] SoninL2 :=
  -(fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    indicatorCutoff (Set.Iio 0) measurableSet_Iio ∘L
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap)

theorem negativeCauchy_bound (u : SoninL2) : ‖negativeCauchy u‖ ≤ ‖u‖ := by
  change ‖-(fourierUnitary (indicatorCutoff (Set.Iio 0) measurableSet_Iio
    (fourierUnitary.symm u)))‖ ≤ ‖u‖
  rw [norm_neg, fourierUnitary.norm_map]
  have hnorm : ‖indicatorCutoff (Set.Iio 0) measurableSet_Iio‖ ≤ 1 := by
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    exact Submodule.starProjection_norm_le _
  have h := (indicatorCutoff (Set.Iio 0) measurableSet_Iio).le_opNorm (fourierUnitary.symm u)
  calc
    _ ≤ ‖indicatorCutoff (Set.Iio 0) measurableSet_Iio‖ * ‖fourierUnitary.symm u‖ := h
    _ ≤ ‖u‖ := by simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg (fourierUnitary.symm u))

/-- Right multiplication by the two-channel nonlocal jump perturbation. -/
def jumpPerturbation (a b : 𝓢(ℝ, ℂ)) : Boundary →L[ℂ] Boundary :=
  ((-smallMultiplier a).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)).prod
    (((smallMultiplier b).comp (ContinuousLinearMap.fst ℂ SoninL2 SoninL2)) -
      (((smallMultiplier a).comp (smallMultiplier b)).comp
        (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)))

theorem jumpPerturbation_bound (a b : 𝓢(ℝ, ℂ)) (u : Boundary) :
    ‖jumpPerturbation a b u‖ ≤ (5/16 : ℝ)*‖u‖ := by
  change max ‖-(smallMultiplier a u.2)‖
    ‖smallMultiplier b u.1 - smallMultiplier a (smallMultiplier b u.2)‖ ≤ _
  rw [max_le_iff, norm_neg]
  have h₁ := smallMultiplier_bound a u.2
  have h₂ := smallMultiplier_bound b u.1
  have h₃ := smallMultiplier_bound a (smallMultiplier b u.2)
  have h₄ := smallMultiplier_bound b u.2
  have hf := norm_fst_le u
  have hs := norm_snd_le u
  constructor
  · nlinarith [norm_nonneg u]
  · have ht := norm_sub_le (smallMultiplier b u.1)
      (smallMultiplier a (smallMultiplier b u.2))
    nlinarith

def cauchyOperator (a b : 𝓢(ℝ, ℂ)) : Boundary →L[ℂ] Boundary :=
  (negativeCauchy.prodMap negativeCauchy).comp (jumpPerturbation a b)

theorem cauchyOperator_bound (a b : 𝓢(ℝ, ℂ)) (u : Boundary) :
    ‖cauchyOperator a b u‖ ≤ (5/16 : ℝ)*‖u‖ := by
  apply le_trans _ (jumpPerturbation_bound a b u)
  change max ‖negativeCauchy (jumpPerturbation a b u).1‖
    ‖negativeCauchy (jumpPerturbation a b u).2‖ ≤
    max ‖(jumpPerturbation a b u).1‖ ‖(jumpPerturbation a b u).2‖
  exact max_le_max (negativeCauchy_bound _) (negativeCauchy_bound _)

theorem norm_cauchyOperator_lt_one (a b : 𝓢(ℝ, ℂ)) : ‖cauchyOperator a b‖ < 1 := by
  have h := (cauchyOperator a b).opNorm_le_bound (by positivity : (0:ℝ) ≤ 5/16)
    (cauchyOperator_bound a b)
  linarith

def resolventUnit (a b : 𝓢(ℝ, ℂ)) : (Boundary →L[ℂ] Boundary)ˣ :=
  Units.oneSub (cauchyOperator a b) (norm_cauchyOperator_lt_one a b)

def solution (a b : 𝓢(ℝ, ℂ)) (d : Boundary) : Boundary :=
  ((resolventUnit a b)⁻¹ : (Boundary →L[ℂ] Boundary)ˣ).val d

theorem solution_equation (a b : 𝓢(ℝ, ℂ)) (d : Boundary) :
    solution a b d - cauchyOperator a b (solution a b d) = d := by
  have h := DFunLike.congr_fun (resolventUnit a b).val_inv d
  simpa [resolventUnit, Units.val_oneSub, solution,
    mul_apply_eq_comp, sub_apply] using h

/-- Uniform inverse bound for every pair of normalized Schwartz coefficients. -/
theorem solution_bound (a b : 𝓢(ℝ, ℂ)) (d : Boundary) :
    ‖solution a b d‖ ≤ (16/11 : ℝ)*‖d‖ := by
  have he := (sub_eq_iff_eq_add).mp (solution_equation a b d)
  have hn : ‖solution a b d‖ ≤ ‖d‖ + ‖cauchyOperator a b (solution a b d)‖ := by
    calc
      _ = ‖d + cauchyOperator a b (solution a b d)‖ := congrArg norm he
      _ ≤ _ := norm_add_le _ _
  have hb := cauchyOperator_bound a b (solution a b d)
  linarith

/-- Unique solvability of the actual two-channel L² Cauchy equation. -/
theorem existsUnique_solution (a b : 𝓢(ℝ, ℂ)) (d : Boundary) :
    ∃! u : Boundary, u - cauchyOperator a b u = d := by
  refine ⟨solution a b d, solution_equation a b d, ?_⟩
  intro u hu
  have he : u-solution a b d = cauchyOperator a b (u-solution a b d) := by
    rw [map_sub]
    have h₁ := (sub_eq_iff_eq_add).mp hu
    have h₂ := (sub_eq_iff_eq_add).mp (solution_equation a b d)
    calc
      u-solution a b d = (d+cauchyOperator a b u) -
        (d+cauchyOperator a b (solution a b d)) := congrArg₂ (·-·) h₁ h₂
      _ = _ := by abel
  have hb := cauchyOperator_bound a b (u-solution a b d)
  rw [← he] at hb
  have hz : ‖u-solution a b d‖ = 0 := by linarith [norm_nonneg (u-solution a b d)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The inverse equation is globally Lipschitz in its inhomogeneous data. -/
theorem solution_lipschitz (a b : 𝓢(ℝ, ℂ)) (d e : Boundary) :
    ‖solution a b d-solution a b e‖ ≤ (16/11 : ℝ)*‖d-e‖ := by
  have hs : solution a b (d-e) = solution a b d-solution a b e := by
    exact map_sub ((resolventUnit a b)⁻¹ : (Boundary →L[ℂ] Boundary)ˣ).val d e
  rw [← hs]
  exact solution_bound a b (d-e)

end
end RHTower.FokasLenells
