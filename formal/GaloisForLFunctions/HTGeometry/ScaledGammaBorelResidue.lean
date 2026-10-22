import GaloisForLFunctions.HTGeometry.GammaOrientedAlienCharge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAntiPickIdentity

/-!
# Scaled Gamma polar Borel residues

This file realizes the scaled alien character as an actual analytic residue.  The polar part of
the formal Borel transform of a positive affine Gamma packet is the finite sum of the classical
kernels

`m * exp (-(mu / lambda) * xi) * xi / (exp (xi / lambda) - 1)`.

At every nonzero frequency `xi = 2*pi*i*t`, its residue is exactly
`2*pi*i*t * scaledGammaAlienChargeAt a t`.  Both lattice and off-lattice factors are handled;
the latter are holomorphic at the selected frequency and contribute zero residue.
-/

open Complex Filter Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def scaledGammaBorelPolarTerm (f : PositiveAffineGammaFactor) (ξ : ℂ) : ℂ :=
  (f.multiplicity : ℂ) *
    Complex.exp (-(f.offset / (f.scale : ℂ)) * ξ) * ξ /
      (Complex.exp (ξ / (f.scale : ℂ)) - 1)

def scaledGammaBorelPolarPart {d : ℕ}
    (a : Fin d → PositiveAffineGammaFactor) (ξ : ℂ) : ℂ :=
  ∑ i, scaledGammaBorelPolarTerm (a i) ξ

noncomputable def scaledGammaBorelResidueChargeTerm
    (f : PositiveAffineGammaFactor) (t : ℝ) : ℂ := by
  classical
  exact if ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℝ) * f.scale then
    (f.multiplicity : ℂ) * (f.scale : ℂ) *
      Complex.exp
        (-2 * (Real.pi : ℂ) * Complex.I *
          ((t / f.scale : ℝ) : ℂ) * f.offset)
  else 0

theorem exp_two_pi_I_real_ratio_eq_one_iff_lattice
    {scale : ℝ} (hscale : 0 < scale) (t : ℝ) :
    Complex.exp
        ((2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) / (scale : ℂ)) = 1 ↔
      ∃ k : ℤ, t = (k : ℝ) * scale := by
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hsC : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale.ne'
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨k, ?_⟩
    have hcast : (t : ℂ) = (k : ℂ) * (scale : ℂ) := by
      apply (mul_left_cancel₀ hpi)
      calc
        (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ) =
            ((2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) /
              (scale : ℂ)) * (scale : ℂ) := by field_simp
        _ = ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) *
              (scale : ℂ) := by rw [hk]
        _ = (2 * (Real.pi : ℂ) * Complex.I) *
              ((k : ℂ) * (scale : ℂ)) := by ring
    exact_mod_cast hcast
  · rintro ⟨k, rfl⟩
    rw [show (2 * (Real.pi : ℂ) * Complex.I *
          ((((k : ℤ) : ℝ) * scale : ℝ) : ℂ)) / (scale : ℂ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I k

theorem scaledGammaBorelPolarTerm_residue
    (f : PositiveAffineGammaFactor) (t : ℝ) (ht : t ≠ 0) :
    Tendsto
      (fun ξ : ℂ =>
        (ξ - 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
          scaledGammaBorelPolarTerm f ξ)
      (nhdsWithin (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
        ({2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)}ᶜ))
      (nhds ((2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
        scaledGammaBorelResidueChargeTerm f t)) := by
  classical
  let ξ₀ : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
  let numerator : ℂ → ℂ := fun ξ =>
    (f.multiplicity : ℂ) *
      Complex.exp (-(f.offset / (f.scale : ℂ)) * ξ) * ξ
  let denominator : ℂ → ℂ := fun ξ =>
    Complex.exp (ξ / (f.scale : ℂ)) - 1
  have hsC : (f.scale : ℂ) ≠ 0 := by exact_mod_cast f.scale_pos.ne'
  by_cases hlat : ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℝ) * f.scale
  · obtain ⟨k, hk, htk⟩ := hlat
    have hexp : Complex.exp (ξ₀ / (f.scale : ℂ)) = 1 := by
      apply (exp_two_pi_I_real_ratio_eq_one_iff_lattice f.scale_pos t).mpr
      exact ⟨k, htk⟩
    have hinner : HasDerivAt (fun ξ : ℂ => ξ / (f.scale : ℂ))
        ((f.scale : ℂ)⁻¹) ξ₀ := by
      simpa [div_eq_mul_inv] using
        (hasDerivAt_id ξ₀).mul_const ((f.scale : ℂ)⁻¹)
    have hden : HasDerivAt denominator ((f.scale : ℂ)⁻¹) ξ₀ := by
      have h := (Complex.hasDerivAt_exp (ξ₀ / (f.scale : ℂ))).comp ξ₀ hinner
      have h' := h.sub_const 1
      simpa [denominator, hexp] using h'
    have hden0 : denominator ξ₀ = 0 := by simp [denominator, hexp]
    have hden' : (f.scale : ℂ)⁻¹ ≠ 0 := inv_ne_zero hsC
    have hnum : ContinuousAt numerator ξ₀ := by
      dsimp only [numerator]
      fun_prop
    have hres := RHTower.tendsto_residue_of_simple_zero
      hden hden0 hden' hnum
    rw [scaledGammaBorelResidueChargeTerm, if_pos ⟨k, hk, htk⟩]
    have hratio : t / f.scale = (k : ℝ) := by
      rw [htk]
      field_simp [f.scale_pos.ne']
    have hexponent :
        -(f.offset / (f.scale : ℂ)) * ξ₀ =
          -2 * (Real.pi : ℂ) * Complex.I *
            ((t / f.scale : ℝ) : ℂ) * f.offset := by
      dsimp only [ξ₀]
      push_cast
      field_simp [hsC]
    have hvalue : numerator ξ₀ / (f.scale : ℂ)⁻¹ =
        ξ₀ * ((f.multiplicity : ℂ) * (f.scale : ℂ) *
          Complex.exp
            (-2 * (Real.pi : ℂ) * Complex.I *
              ((t / f.scale : ℝ) : ℂ) * f.offset)) := by
      rw [show numerator ξ₀ =
          (f.multiplicity : ℂ) *
            Complex.exp
              (-2 * (Real.pi : ℂ) * Complex.I *
                ((t / f.scale : ℝ) : ℂ) * f.offset) * ξ₀ by
        simp only [numerator]
        rw [hexponent]]
      field_simp [hsC]
    rw [← hvalue]
    simpa only [scaledGammaBorelPolarTerm, numerator, denominator, ξ₀] using hres
  · have hden0 : denominator ξ₀ ≠ 0 := by
      intro hz
      have hexp : Complex.exp (ξ₀ / (f.scale : ℂ)) = 1 := by
        simpa [denominator] using sub_eq_zero.mp hz
      obtain ⟨k, htk⟩ :=
        (exp_two_pi_I_real_ratio_eq_one_iff_lattice f.scale_pos t).mp (by
          simpa [ξ₀] using hexp)
      have hk : k ≠ 0 := by
        intro hk0
        rw [hk0] at htk
        simp only [Int.cast_zero, zero_mul] at htk
        exact ht htk
      exact hlat ⟨k, hk, htk⟩
    rw [scaledGammaBorelResidueChargeTerm, if_neg hlat, mul_zero]
    have hsub : Tendsto (fun ξ : ℂ => ξ - ξ₀)
        (nhdsWithin ξ₀ ({ξ₀}ᶜ)) (nhds 0) := by
      have h : Tendsto (fun ξ : ℂ => ξ - ξ₀) (nhds ξ₀)
          (nhds (ξ₀ - ξ₀)) :=
        (continuousAt_id.sub continuousAt_const).tendsto
      simpa only [nhdsWithin, sub_self] using h.mono_left inf_le_left
    have hterm : Tendsto (scaledGammaBorelPolarTerm f)
        (nhdsWithin ξ₀ ({ξ₀}ᶜ))
        (nhds (scaledGammaBorelPolarTerm f ξ₀)) := by
      have hc : ContinuousAt (scaledGammaBorelPolarTerm f) ξ₀ := by
        unfold scaledGammaBorelPolarTerm
        fun_prop
      exact hc.tendsto.mono_left inf_le_left
    simpa only [ξ₀, zero_mul] using hsub.mul hterm

/-- Equation `(10)`: residue of the complete finite polar Borel part is the scaled alien
character multiplied by the universal pole coordinate. -/
theorem scaledGammaBorelPolarPart_residue {d : ℕ}
    (a : Fin d → PositiveAffineGammaFactor) (t : ℝ) (ht : t ≠ 0) :
    Tendsto
      (fun ξ : ℂ =>
        (ξ - 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
          scaledGammaBorelPolarPart a ξ)
      (nhdsWithin (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
        ({2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)}ᶜ))
      (nhds ((2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
        scaledGammaAlienChargeAt a t)) := by
  classical
  let ξ₀ : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
  have hsum : Tendsto
      (fun ξ : ℂ => ∑ i,
        (ξ - ξ₀) * scaledGammaBorelPolarTerm (a i) ξ)
      (nhdsWithin ξ₀ ({ξ₀}ᶜ))
      (nhds (∑ i, ξ₀ * scaledGammaBorelResidueChargeTerm (a i) t)) := by
    apply tendsto_finsetSum
    intro i hi
    simpa only [ξ₀] using scaledGammaBorelPolarTerm_residue (a i) t ht
  have hcharge :
      ∑ i, scaledGammaBorelResidueChargeTerm (a i) t =
        scaledGammaAlienChargeAt a t := by
    rw [scaledGammaAlienChargeAt]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [← hcharge, Finset.mul_sum]
  convert hsum using 1
  funext ξ
  rw [scaledGammaBorelPolarPart, Finset.mul_sum]

end

end GaloisForLFunctions.HTGeometry
