import Mathlib.Analysis.Distribution.Sobolev

/-! Actual Laplacian Sobolev gain in every finite-dimensional Euclidean space. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian Real ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem euclidean_multiplier_add {a b : E → ℂ} (ha : a.HasTemperateGrowth)
    (hb : b.HasTemperateGrowth) (u : 𝓢'(E,ℂ)) :
    fourierMultiplierCLM ℂ (a+b) u = fourierMultiplierCLM ℂ a u+fourierMultiplierCLM ℂ b u := by
  simp [fourierMultiplierCLM_apply,smulLeftCLM_add ha hb]

/-- The Fourier-normalized Bessel potential identity holds in the actual ambient dimension. -/
theorem besselPotential_two_euclidean (u : 𝓢'(E,ℂ)) :
    besselPotential E ℂ 2 u = u-(((2*Real.pi)^2:ℝ)⁻¹:ℂ) • (Δ u) := by
  have hb : besselPotential E ℂ 2 u =
      u+fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (‖x‖^2)) u := by
    simp only [besselPotential,show (2:ℝ)/2 = 1 by norm_num,Real.rpow_one,
      Complex.ofReal_add,Complex.ofReal_one]
    have hm := euclidean_multiplier_add (a := fun _ : E => (1:ℂ))
      (b := fun x : E => Complex.ofReal (‖x‖^2)) (by fun_prop) (by fun_prop) u
    simpa only [Pi.add_def,fourierMultiplierCLM_const,one_smul,ContinuousLinearMap.id_apply] using hm
  rw [hb,laplacian_eq_fourierMultiplierCLM]
  simp only [sub_eq_add_neg,neg_smul,smul_neg,neg_neg]
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
  simp

/-- A Euclidean Sobolev distribution gains two derivatives when its actual Laplacian
has the same Sobolev order; the statement includes dimension three. -/
theorem euclidean_sobolev_gain_two {s : ℝ} {u : 𝓢'(E,ℂ)}
    (hu : MemSobolev s 2 u) (hd : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  have hb := hu.sub (hd.smul (((2*Real.pi)^2:ℝ)⁻¹:ℂ))
  rw [← besselPotential_two_euclidean,memSobolev_besselPotential_iff] at hb
  simpa only [add_comm] using hb

end
end GaloisForLFunctions.HTGeometry
