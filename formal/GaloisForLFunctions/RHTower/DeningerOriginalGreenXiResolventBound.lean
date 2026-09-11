import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.RHTower.Sieve.ZetaUniformStripZeroFree

/-!
# Original prime Green resolvent: a uniform whole-divisor envelope

The original denominator is retained. The actual zero-free region and
functional equation supply its quantitative lower bound at every Xi zero.
-/

open Complex
noncomputable section
namespace RHTower

/-- The original translation resolvent costs at most one inverse real Mellin weight. -/
theorem deningerOriginalGreen_inverse_norm_le {L : ℝ} (hL : 0 < L)
    {s : ℂ} (hs : 0 < s.re) :
    ‖(1-Complex.exp (-s*(L : ℂ)))⁻¹‖ ≤ 1+1/(s.re*L) := by
  let x : ℝ := s.re*L
  have hx : 0 < x := mul_pos hs hL
  have hx1 : 0 < 1+x := by linarith
  have he : 1+x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have heinv : Real.exp (-x) ≤ 1/(1+x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hx1 he
  have heNorm : ‖Complex.exp (-s*(L : ℂ))‖ = Real.exp (-x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [x, Complex.mul_re]
  have hsub : 1-Real.exp (-x) ≤ ‖1-Complex.exp (-s*(L : ℂ))‖ := by
    simpa only [norm_one,heNorm] using norm_sub_norm_le (1 : ℂ) (Complex.exp (-s*(L : ℂ)))
  have hlow : x/(1+x) ≤ ‖1-Complex.exp (-s*(L : ℂ))‖ := by
    calc
      _ = 1-1/(1+x) := by field_simp; ring
      _ ≤ 1-Real.exp (-x) := sub_le_sub_left heinv 1
      _ ≤ _ := hsub
  rw [norm_inv, ← one_div]
  calc
    _ ≤ 1/(x/(1+x)) := one_div_le_one_div_of_le (div_pos hx hx1) hlow
    _ = 1+1/(s.re*L) := by dsimp [x]; field_simp; ring

/-- One quantitative lower margin works at all actual Xi zeros, including their reflections. -/
theorem exists_deningerXi_real_part_margin :
    ∃ E : ℝ, 2 ≤ E ∧ ∀ rho : XiDivisorSupport,
      1 / Real.log (E+|(rho : ℂ).im|)^2 < (rho : ℂ).re := by
  obtain ⟨L0,hL0,hfree⟩ := Sieve.exists_zeta_uniform_strip_zero_free
  refine ⟨Real.exp L0, by linarith [Real.add_one_le_exp L0], ?_⟩
  intro rho
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hrefpos : 0 < (1-(rho : ℂ)).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  have hrefne : 1-(rho : ℂ) ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.sub_re,Complex.one_re] at hr
    linarith [hstrip.1]
  have hz : riemannZeta (1-(rho : ℂ)) = 0 := by
    apply (xi_eq_zero_iff hrefpos hrefne).mp
    rw [xi_one_sub]
    exact xi_eq_zero_of_mem_divisor_support rho
  have hKpos : 0 < Real.exp L0+|(rho : ℂ).im| :=
    add_pos_of_pos_of_nonneg (Real.exp_pos _) (abs_nonneg _)
  have hlog : L0 ≤ Real.log (Real.exp L0+|(rho : ℂ).im|) :=
    (Real.le_log_iff_exp_le hKpos).mpr (le_add_of_nonneg_right (abs_nonneg _))
  by_contra h
  apply hfree (1-(rho : ℂ)) (Real.exp L0+|(rho : ℂ).im|) hlog
    (by simp only [Complex.sub_im,Complex.one_im,zero_sub,abs_neg]; linarith [Real.exp_pos L0])
    (by simp only [Complex.sub_re,Complex.one_re]; linarith) hrefne hz

/-- A polynomial envelope uniform in the original prime and every actual Xi divisor point. -/
theorem exists_deningerOriginalPrimeGreen_inverse_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Nat.Primes) (rho : XiDivisorSupport),
      ‖(1-Complex.exp (-(rho : ℂ)*(Real.log (p : ℕ) : ℂ)))⁻¹‖ ≤
        C*(1+|(rho : ℂ).im|)^2 := by
  obtain ⟨E,hE,hmargin⟩ := exists_deningerXi_real_part_margin
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1+E^2/Real.log 2, by positivity, ?_⟩
  intro p rho
  let t : ℝ := |(rho : ℂ).im|
  let K : ℝ := E+t
  have ht : 0 ≤ t := abs_nonneg _
  have hK : 0 < K := by dsimp [K]; linarith
  have hlogK : 0 < Real.log K := Real.log_pos (by dsimp [K]; linarith)
  have hp : Real.log 2 ≤ Real.log (p : ℕ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.property.two_le)
  have hp0 : 0 < Real.log (p : ℕ) := hlog2.trans_le hp
  have hs := (xi_divisor_support_re_mem_open_unit rho).1
  have hm : 1/Real.log K^2 ≤ (rho : ℂ).re := (hmargin rho).le
  have hprod : (1/Real.log K^2)*Real.log 2 ≤ (rho : ℂ).re*Real.log (p : ℕ) :=
    mul_le_mul hm hp hlog2.le hs.le
  have hb : ‖(1-Complex.exp (-(rho : ℂ)*(Real.log (p : ℕ) : ℂ)))⁻¹‖ ≤
      1+Real.log K^2/Real.log 2 := by
    calc
      _ ≤ 1+1/((rho : ℂ).re*Real.log (p : ℕ)) := deningerOriginalGreen_inverse_norm_le hp0 hs
      _ ≤ 1+1/((1/Real.log K^2)*Real.log 2) :=
        add_le_add le_rfl (one_div_le_one_div_of_le (by positivity) hprod)
      _ = _ := by field_simp
  have hKl : K ≤ E*(1+t) := by dsimp [K]; nlinarith
  have hlogsq : Real.log K^2 ≤ E^2*(1+t)^2 := by
    calc
      _ ≤ K^2 := pow_le_pow_left₀ hlogK.le (by linarith [Real.log_le_sub_one_of_pos hK]) 2
      _ ≤ (E*(1+t))^2 := pow_le_pow_left₀ hK.le hKl 2
      _ = _ := by ring
  calc
    _ ≤ 1+Real.log K^2/Real.log 2 := hb
    _ ≤ 1+(E^2*(1+t)^2)/Real.log 2 := add_le_add le_rfl (div_le_div_of_nonneg_right hlogsq hlog2.le)
    _ ≤ (1+t)^2+(E^2*(1+t)^2)/Real.log 2 := add_le_add (by nlinarith : (1 : ℝ) ≤ (1+t)^2) le_rfl
    _ = _ := by dsimp [t]; ring

end RHTower
