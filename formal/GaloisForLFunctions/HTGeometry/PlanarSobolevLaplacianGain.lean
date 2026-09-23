import Mathlib.Analysis.Distribution.Sobolev

/-!
The exact Fourier-normalized Bessel potential identity proves a two-derivative planar Sobolev gain from the actual Laplacian.
-/

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian Real ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem multiplier_add {a b : ℂ → ℂ} (ha : a.HasTemperateGrowth)
    (hb : b.HasTemperateGrowth) (u : 𝓢'(ℂ,ℂ)) :
    fourierMultiplierCLM ℂ (a+b) u = fourierMultiplierCLM ℂ a u + fourierMultiplierCLM ℂ b u := by
  simp [fourierMultiplierCLM_apply,smulLeftCLM_add ha hb]

/-- The order-two Bessel potential is the actual shifted planar Laplacian,
with the Fourier transform's precise `2*pi` normalization. -/
theorem besselPotential_two_planar (u : 𝓢'(ℂ,ℂ)) :
    besselPotential ℂ ℂ 2 u = u - (((2*Real.pi)^(2 : ℕ) : ℝ)⁻¹ : ℂ) • (Δ u) := by
  have hb : besselPotential ℂ ℂ 2 u = u + fourierMultiplierCLM ℂ (fun x : ℂ => Complex.ofReal (‖x‖^(2 : ℕ))) u := by
    simp only [besselPotential,show (2:ℝ)/2 = 1 by norm_num,Real.rpow_one,
      Complex.ofReal_add,Complex.ofReal_one]
    have hm := multiplier_add (a := fun _ : ℂ => (1:ℂ))
      (b := fun x : ℂ => Complex.ofReal (‖x‖^(2 : ℕ))) (by fun_prop) (by fun_prop) u
    simpa only [Pi.add_def,fourierMultiplierCLM_const,one_smul,ContinuousLinearMap.id_apply] using hm
  rw [hb,laplacian_eq_fourierMultiplierCLM]
  simp only [sub_eq_add_neg,neg_smul,smul_neg,neg_neg]
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
  simp

/-- An L² Sobolev function whose actual Laplacian has the same Sobolev order gains
 two derivatives; no elliptic regularity axiom is supplied. -/
theorem planar_sobolev_gain_two {s : ℝ} {u : 𝓢'(ℂ,ℂ)}
    (hu : MemSobolev s 2 u) (hd : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  have hb := hu.sub (hd.smul (((2*Real.pi)^(2 : ℕ) : ℝ)⁻¹ : ℂ))
  rw [← besselPotential_two_planar,memSobolev_besselPotential_iff] at hb
  simpa only [add_comm] using hb

end
end GaloisForLFunctions.HTGeometry
