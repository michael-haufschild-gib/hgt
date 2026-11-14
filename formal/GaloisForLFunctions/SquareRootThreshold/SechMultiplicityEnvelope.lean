import GaloisForLFunctions.SquareRootThreshold.SechBoundaryMultiplicity
import GaloisForLFunctions.RHTower.PerturbedDip

/-!
# The uniform multiplicity envelope across the quasi-Riemann strip

The secant fibre bound becomes a cosine envelope after multiplication by its
positive denominator. A uniform Lipschitz estimate in the strip width passes
to the limiting width `3/8`, including the two outer boundaries.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.RHTower
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

private theorem sech_envelope_parameter_le {d x : ℝ} (hd : 0 ≤ d) (hx : |x| ≤ 3/8) :
    ((3/8+d)/Real.pi)*Real.cos (Real.pi/(2*(3/8+d))*x) ≤
      (3/(8*Real.pi))*Real.cos ((4*Real.pi/3)*x)+d := by
  let a := (3:ℝ)/8+d
  let u := Real.pi/(2*a)*x
  let v := (4*Real.pi/3)*x
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 ≤ 4*Real.pi*d/(3*a) := by positivity
  have he : u-v = -(4*Real.pi*d/(3*a))*x := by
    dsimp only [u,v]
    field_simp [ha.ne'] <;> dsimp only [a] <;> ring
  have hangle : |u-v| ≤ (4*Real.pi/3)*d := by
    rw [he,abs_mul,abs_neg,abs_of_nonneg hc]
    calc
      _ ≤ (4*Real.pi*d/(3*a))*(3/8) := mul_le_mul_of_nonneg_left hx hc
      _ = Real.pi*d/(2*a) := by field_simp [ha.ne'] <;> ring
      _ ≤ Real.pi*d/(3/4) := div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by dsimp [a]; linarith only [hd])
      _ = _ := by ring
  have hcos : Real.cos u-Real.cos v ≤ (4*Real.pi/3)*d :=
    (le_abs_self _).trans ((RHTower.abs_cos_sub_cos_le u v).trans hangle)
  have hfirst := mul_le_mul_of_nonneg_left (Real.cos_le_one u)
    (div_nonneg hd Real.pi_pos.le)
  have hsecond := mul_le_mul_of_nonneg_left hcos
    (show 0 ≤ 3/(8*Real.pi) by positivity)
  have hcancel : (3/(8*Real.pi))*((4*Real.pi/3)*d)=d/2 := by
    field_simp [Real.pi_ne_zero] <;> ring
  rw [hcancel] at hsecond
  have hdpi : d/Real.pi ≤ d/2 := div_le_div_of_nonneg_left hd (by norm_num)
    (by linarith only [Real.pi_gt_three])
  change (a/Real.pi)*Real.cos u ≤ (3/(8*Real.pi))*Real.cos v+d
  have hsplit : (a/Real.pi)*Real.cos u = (3/(8*Real.pi))*Real.cos v +
      (d/Real.pi)*Real.cos u + (3/(8*Real.pi))*(Real.cos u-Real.cos v) := by
    dsimp only [a]
    ring
  rw [hsplit]
  linarith only [hfirst,hsecond,hdpi]

/-- Multiplying the positive secant weight gives a pointwise cosine bound. -/
theorem exists_zero_multiplicity_cos_bound {a ε : ℝ}
    (ha : (3:ℝ)/8 < a) (hahalf : a < 1/2) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
        ((a/Real.pi+ε)*Real.cos (Real.pi/(2*a)*(ρ.re-1/2)))*Real.log |ρ.im| := by
  obtain ⟨T₀,hT₀,hbound⟩ := exists_fibre_sech_multiplicity_bound ha hahalf hε
  refine ⟨T₀,hT₀,fun ρ hρre hρzero hT => ?_⟩
  have hf : ∀ z ∈ ({ρ} : Finset ℂ), 0 < z.re ∧ riemannZeta z = 0 ∧ z.im = ρ.im := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst z
    exact ⟨hρre,hρzero,rfl⟩
  have hh := hbound ρ.im hT _ hf
  simp only [Finset.sum_singleton] at hh
  have hstrip := riemannZeta_zero_mem_quasiRH_strip hρre hρzero
  have hdepth : |ρ.re-1/2| < a := abs_lt.mpr
    ⟨by linarith only [hstrip.1,ha],by linarith only [hstrip.2,ha]⟩
  have hw := sechStripWeight_re_pos (by linarith only [ha] : 0 < a) (T := ρ.im) hdepth
  rw [sechStripWeight_same_height a ρ.im rfl,Complex.ofReal_re] at hw
  have hc : 0 < Real.cos (Real.pi/(2*a)*(ρ.re-1/2)) := inv_pos.mp hw
  calc
    _ = (((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
        (Real.cos (Real.pi/(2*a)*(ρ.re-1/2)))⁻¹) *
          Real.cos (Real.pi/(2*a)*(ρ.re-1/2)) := by
      rw [mul_assoc,inv_mul_cancel₀ hc.ne',mul_one]
    _ ≤ ((a/Real.pi+ε)*Real.log |ρ.im|)*Real.cos (Real.pi/(2*a)*(ρ.re-1/2)) :=
      mul_le_mul_of_nonneg_right hh hc.le
    _ = _ := by ring

/-- The limiting strip width gives a uniform cosine envelope for all nontrivial
zeta zeros at large absolute height. -/
theorem exists_zero_multiplicity_cosine_envelope {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
        ((3/(8*Real.pi))*Real.cos ((4*Real.pi/3)*(ρ.re-1/2))+ε)*Real.log |ρ.im| := by
  let d := min (1/16 : ℝ) (ε/2)
  let a := (3:ℝ)/8+d
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hdlo : d ≤ 1/16 := min_le_left _ _
  have hdhi : d ≤ ε/2 := min_le_right _ _
  have ha : (3:ℝ)/8 < a := by dsimp [a]; linarith only [hd]
  have hahalf : a < 1/2 := by dsimp [a]; linarith only [hdlo]
  obtain ⟨T₀,hT₀,hbound⟩ := exists_zero_multiplicity_cos_bound ha hahalf
    (show 0 < ε/2 by positivity)
  refine ⟨T₀,hT₀,fun ρ hρre hρzero hT => ?_⟩
  have hstrip := riemannZeta_zero_mem_quasiRH_strip hρre hρzero
  have hx : |ρ.re-1/2| ≤ 3/8 := abs_le.mpr
    ⟨by linarith only [hstrip.1],by linarith only [hstrip.2]⟩
  have hparam := sech_envelope_parameter_le hd.le hx
  change (a/Real.pi)*Real.cos (Real.pi/(2*a)*(ρ.re-1/2)) ≤
    (3/(8*Real.pi))*Real.cos ((4*Real.pi/3)*(ρ.re-1/2))+d at hparam
  have herr := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi/(2*a)*(ρ.re-1/2)))
    (show 0 ≤ ε/2 by positivity)
  have hcoef : (a/Real.pi+ε/2)*Real.cos (Real.pi/(2*a)*(ρ.re-1/2)) ≤
      (3/(8*Real.pi))*Real.cos ((4*Real.pi/3)*(ρ.re-1/2))+ε := by
    nlinarith only [hparam,herr,hdhi]
  exact (hbound ρ hρre hρzero hT).trans (mul_le_mul_of_nonneg_right hcoef
    (Real.log_nonneg (by linarith only [hT₀.trans hT])))

/-- Multiplicity is sublogarithmic on either outer boundary of the quasi-Riemann strip. -/
theorem exists_outer_boundary_multiplicity_le_epsilon_log {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ ρ : ℂ, (ρ.re = 1/8 ∨ ρ.re = 7/8) →
      riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ ε*Real.log |ρ.im| := by
  obtain ⟨T₀,hT₀,hbound⟩ := exists_zero_multiplicity_cosine_envelope hε
  refine ⟨T₀,hT₀,fun ρ hρ hz hT => ?_⟩
  have hre : 0 < ρ.re := by rcases hρ with h | h <;> rw [h] <;> norm_num
  have hh := hbound ρ hre hz hT
  rcases hρ with hl | hr
  · have he : (4*Real.pi/3)*(ρ.re-1/2) = -(Real.pi/2) := by rw [hl]; ring
    simpa only [he,Real.cos_neg,Real.cos_pi_div_two,mul_zero,zero_add] using hh
  · have he : (4*Real.pi/3)*(ρ.re-1/2) = Real.pi/2 := by rw [hr]; ring
    simpa only [he,Real.cos_pi_div_two,mul_zero,zero_add] using hh

end GaloisForLFunctions.SquareRootThreshold

#print axioms GaloisForLFunctions.SquareRootThreshold.exists_zero_multiplicity_cosine_envelope
#print axioms GaloisForLFunctions.SquareRootThreshold.exists_outer_boundary_multiplicity_le_epsilon_log
