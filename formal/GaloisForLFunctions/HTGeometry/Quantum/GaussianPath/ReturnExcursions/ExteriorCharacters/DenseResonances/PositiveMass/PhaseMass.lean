import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Positive real correlations of a weighted family of phases -/

open Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
noncomputable section
variable {I : Type*}

private theorem positive_minorant (z : ℂ) (hz : ‖z‖=1) :
    1+2*z.re+(z^2).re ≤ 4*max 0 z.re := by
  have hnorm := Complex.sq_norm z
  rw [hz,one_pow,Complex.normSq_apply] at hnorm
  have hsq : z.re^2≤|z.re| := by
    have ha := (Complex.abs_re_le_norm z).trans_eq hz
    simpa only [←sq, sq_abs,mul_one] using mul_le_mul_of_nonneg_left ha (abs_nonneg z.re)
  rw [sq,Complex.mul_re]
  rcases le_total 0 z.re with h | h
  · simp only [max_eq_right h,abs_of_nonneg h] at hsq ⊢
    nlinarith only [hsq,hnorm]
  · simp only [max_eq_left h,abs_of_nonpos h] at hsq ⊢
    nlinarith only [hsq,hnorm]

private theorem corr_sum (F : Finset I) (a : I → ℂ) :
    (∑ i ∈ F, ∑ j ∈ F, (a i*conj (a j)).re)=‖∑ i ∈ F, a i‖^2 := by
  simp_rw [←Complex.re_sum,←mul_sum,←map_sum,←sum_mul,Complex.mul_conj,Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- The total positive real pair mass is at least one quarter of the
squared total weight. The first and second Fourier moments each
contribute a nonnegative square. -/
theorem positive_phase_mass (F : Finset I) (r : I → ℝ) (p : I → ℂ)
    (hr : ∀ i∈F, 0≤r i) (hp : ∀ i∈F, ‖p i‖=1) :
    (∑ i ∈ F, r i)^2 ≤ 4*∑ i ∈ F, ∑ j ∈ F, r i*r j*max 0 (p i*conj (p j)).re := by
  let a (k : ℕ) (i : I) := (r i:ℂ)*(p i)^k
  have he (k : ℕ) (i j : I) :
      (a k i*conj (a k j)).re=r i*r j*((p i*conj (p j))^k).re := by
    dsimp only [a]
    rw [map_mul,Complex.conj_ofReal,map_pow,mul_pow]
    rw [show (r i:ℂ)*p i^k*((r j:ℂ)*conj (p j)^k)=
      ((r i*r j:ℝ):ℂ)*(p i^k*conj (p j)^k) by push_cast; ring,Complex.re_ofReal_mul]
  have h (i) (hi : i∈F) (j) (hj : j∈F) :
      r i*r j+2*(a 1 i*conj (a 1 j)).re+(a 2 i*conj (a 2 j)).re ≤
        4*(r i*r j*max 0 (p i*conj (p j)).re) := by
    have hh := mul_le_mul_of_nonneg_left (positive_minorant (p i*conj (p j))
      (by rw [norm_mul,Complex.norm_conj,hp i hi,hp j hj,mul_one])) (mul_nonneg (hr i hi) (hr j hj))
    rw [he,he,pow_one]
    linarith only [hh]
  have ht := sum_le_sum (fun i hi => sum_le_sum (fun j hj => h i hi j hj))
  simp only [sum_add_distrib,←mul_sum,←sum_mul,corr_sum] at ht
  nlinarith only [ht,sq_nonneg ‖∑ i ∈ F, a 1 i‖,sq_nonneg ‖∑ i ∈ F, a 2 i‖]

/-- The same bound holds directly for complex amplitudes, including zeros. -/
theorem positive_amplitude_mass (F : Finset I) (a : I → ℂ) :
    (∑ i ∈ F, ‖a i‖)^2 ≤ 4*∑ i ∈ F, ∑ j ∈ F, max 0 (a i*conj (a j)).re := by
  let p (i : I) := if a i=0 then 1 else a i/(‖a i‖:ℝ)
  have hp (i : I) : ‖p i‖=1 := by
    by_cases hi : a i=0
    · simp [p,hi]
    · simp [p,hi,norm_ne_zero_iff.mpr hi]
  have ha (i : I) : a i=(‖a i‖:ℂ)*p i := by
    by_cases hi : a i=0
    · simp [hi]
    · have hn : (‖a i‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr hi
      simp only [p,if_neg hi]
      rw [mul_comm,div_mul_cancel₀ _ hn]
  have he (i j : I) : max 0 (a i*conj (a j)).re=‖a i‖*‖a j‖*max 0 (p i*conj (p j)).re := by
    have heq : a i*conj (a j)=((‖a i‖*‖a j‖:ℝ):ℂ)*(p i*conj (p j)) := by
      calc
        _ = ((‖a i‖:ℂ)*p i)*conj ((‖a j‖:ℂ)*p j) := congrArg₂ (·*·) (ha i) (congrArg conj (ha j))
        _ = _ := by rw [map_mul,Complex.conj_ofReal,Complex.ofReal_mul]; ring
    rw [heq,Complex.re_ofReal_mul,mul_max_of_nonneg _ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)),mul_zero]
  simp_rw [he]
  exact positive_phase_mass F (fun i => ‖a i‖) p (fun _ _ => norm_nonneg _) (fun i _ => hp i)

#print axioms positive_amplitude_mass
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
