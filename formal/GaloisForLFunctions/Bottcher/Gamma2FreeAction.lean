import Mathlib
open Matrix CongruenceSubgroup UpperHalfPlane Complex
open scoped MatrixGroups UpperHalfPlane


/-
# Γ(2) acts freely on ℍ (no elliptic elements)

The freeness needed for the quotient covering `ℍ → ℍ/PΓ(2)` (`#35`), hence — via `λ̄` properness — for
`λ : ℍ → ℂ∖{0,1}` to be a covering, the three-value-Montel lift, Fatou density, and the hRigid dynamical
input. Proven directly: a fixed point of `γ ∈ Γ(2)` gives `c·z²+(d−a)·z−b=0`; if `c=0` then `b=0,d=a` and
`a²=1` so `γ=±I`; if `c≠0` the non-real root forces `tr²<4`, so the even trace (Γ(2): `a,d` odd) is `0`,
giving `a²+bc=−1` — impossible mod 4 (`a` odd ⟹ `a²≡1`; `b,c` even ⟹ `bc≡0`).
-/

namespace Bottcher

theorem gamma2_fix_eq_one_or_neg_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ Γ(2)) {z : ℍ} (h : γ • z = z) : γ = 1 ∨ γ = -1 := by
  set a : ℤ := γ.1 0 0 with ha
  set b : ℤ := γ.1 0 1 with hb
  set c : ℤ := γ.1 1 0 with hc
  set d : ℤ := γ.1 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have h2 := γ.2; rw [Matrix.det_fin_two] at h2
    simp only [ha, hb, hc, hd]; linarith [h2]
  rw [Gamma_mem] at hγ
  obtain ⟨ha2, hb2, hc2, hd2⟩ := hγ
  have hpa : Odd a := ZMod.intCast_eq_one_iff_odd.mp ha2
  have hpb : Even b := ZMod.intCast_eq_zero_iff_even.mp hb2
  have hpc : Even c := ZMod.intCast_eq_zero_iff_even.mp hc2
  have hpd : Odd d := ZMod.intCast_eq_one_iff_odd.mp hd2
  -- real/imag of z
  set x : ℝ := (z : ℂ).re with hx
  set y : ℝ := (z : ℂ).im with hy
  have hypos : 0 < y := z.im_pos
  -- the complex fixed-point equation: c z² + (d-a) z - b = 0
  have hden : (c : ℂ) * (z : ℂ) + (d : ℂ) ≠ 0 := by
    intro h0
    have him0 : ((c : ℂ) * (z : ℂ) + (d : ℂ)).im = 0 := by rw [h0]; simp
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_im, Complex.intCast_re,
      zero_mul, add_zero] at him0
    -- him0 : c * y = 0 (roughly)
    have hc0 : (c : ℝ) = 0 := by
      rcases mul_eq_zero.mp him0 with h1 | h1
      · exact_mod_cast h1
      · exact absurd h1 (ne_of_gt hypos)
    have hcz : c = 0 := by exact_mod_cast hc0
    rw [hcz] at h0; simp at h0
    have hd0 : (d : ℝ) = 0 := by exact_mod_cast (by simpa using h0)
    have : d = 0 := by exact_mod_cast hd0
    rw [hcz, this] at hdet; simp at hdet
  have key : (c : ℂ) * (z : ℂ) ^ 2 + ((d : ℂ) - (a : ℂ)) * (z : ℂ) - (b : ℂ) = 0 := by
    have happ : ((γ • z : ℍ) : ℂ)
        = ((a : ℂ) * (z : ℂ) + (b : ℂ)) / ((c : ℂ) * (z : ℂ) + (d : ℂ)) := by
      rw [UpperHalfPlane.specialLinearGroup_apply]
      push_cast [ha, hb, hc, hd]
      rfl
    rw [h, eq_div_iff hden] at happ
    linear_combination happ
  -- split into real and imaginary parts via z = x + y i
  have hzc : (z : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I := by
    rw [hx, hy]; exact (Complex.re_add_im (z : ℂ)).symm
  rw [hzc, Complex.ext_iff] at key
  obtain ⟨hreC, himC⟩ := key
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
    Complex.zero_re, Complex.zero_im, mul_zero, zero_mul, mul_one, add_zero, zero_add,
    sub_zero] at hreC himC
  -- from imag part (factor y > 0): 2 c x + (d - a) = 0
  have him : 2 * (c:ℝ) * x + ((d:ℝ) - a) = 0 := by
    have hy0 : y ≠ 0 := ne_of_gt hypos
    have hfac : ((2:ℝ) * c * x + ((d:ℝ) - a)) * y = 0 := by nlinarith [himC]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · linarith [h1]
    · exact absurd h1 hy0
  rcases eq_or_ne c 0 with hc0 | hcne
  · -- c = 0 ⟹ d = a (him), b = 0 (real part), a² = 1 ⟹ γ = ±1
    have hcR : (c:ℝ) = 0 := by exact_mod_cast hc0
    rw [hcR] at him hreC
    have hda : d = a := by
      have : (d:ℝ) = a := by linarith [him]
      exact_mod_cast this
    have hdaR : (d:ℝ) = a := by exact_mod_cast hda
    have hb0 : b = 0 := by
      have hbR : (b:ℝ) = 0 := by rw [hdaR] at hreC; nlinarith [hreC]
      exact_mod_cast hbR
    have ha1 : a * a = 1 := by
      have := hdet; rw [hda, hc0, hb0] at this; linarith [this]
    rcases mul_self_eq_one_iff.mp ha1 with h1 | h1
    · left
      have e00 : γ.1 0 0 = 1 := ha.symm.trans h1
      have e01 : γ.1 0 1 = 0 := hb.symm.trans hb0
      have e10 : γ.1 1 0 = 0 := hc.symm.trans hc0
      have e11 : γ.1 1 1 = 1 := hd.symm.trans (hda.trans h1)
      refine Subtype.ext (Matrix.ext fun i j => ?_)
      fin_cases i <;> fin_cases j <;>
        simp [e00, e01, e10, e11, Matrix.SpecialLinearGroup.coe_one]
    · right
      have hd1 : d = -1 := hda.trans h1
      have e00 : γ.1 0 0 = -1 := ha.symm.trans h1
      have e01 : γ.1 0 1 = 0 := hb.symm.trans hb0
      have e10 : γ.1 1 0 = 0 := hc.symm.trans hc0
      have e11 : γ.1 1 1 = -1 := hd.symm.trans hd1
      refine Subtype.ext (Matrix.ext fun i j => ?_)
      have hneg : ∀ i j, ((-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) i j
          = -(1 : Matrix (Fin 2) (Fin 2) ℤ) i j := fun i j => by
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply]
      fin_cases i <;> fin_cases j <;>
        simp [e00, e01, e10, e11, hneg]
  · -- c ≠ 0: 4 c² y² = 4 - (a+d)² ⟹ (a+d)²<4 ⟹ tr=0 ⟹ a²+bc=-1, impossible mod 4
    exfalso
    have hcR : (c:ℝ) ≠ 0 := by exact_mod_cast hcne
    have hdetR : (a:ℝ)*d - b*c = 1 := by exact_mod_cast hdet
    have htr : 4 * (c:ℝ)^2 * y^2 = 4 - ((a:ℝ)+d)^2 := by
      linear_combination (-4*(c:ℝ))*hreC + (2*(c:ℝ)*x + ((d:ℝ)-(a:ℝ)))*him + 4*hdetR
    have hy2 : 0 < (c:ℝ)^2 * y^2 := by positivity
    have htrbound : ((a:ℝ)+d)^2 < 4 := by nlinarith [htr, hy2]
    have htri : ((a + d) * (a + d) : ℤ) < 4 := by
      have h' : (((a + d) * (a + d) : ℤ) : ℝ) < 4 := by push_cast; nlinarith [htrbound]
      exact_mod_cast h'
    obtain ⟨ak, hak⟩ := hpa
    obtain ⟨dk, hdk⟩ := hpd
    obtain ⟨bk, hbk⟩ := hpb
    obtain ⟨ck, hck⟩ := hpc
    rw [hak, hdk] at htri
    have hs : (ak + dk + 1) * (ak + dk + 1) < 1 := by nlinarith [htri]
    have hnn : 0 ≤ (ak + dk + 1) * (ak + dk + 1) := mul_self_nonneg _
    have hs0 : (ak + dk + 1) * (ak + dk + 1) = 0 := by omega
    have hsz : ak + dk + 1 = 0 := mul_self_eq_zero.mp hs0
    have htr0 : a + d = 0 := by omega
    have hda : d = -a := by omega
    have key2 : a * a + b * c = -1 := by rw [hda] at hdet; nlinarith [hdet]
    have hexp : 4 * (ak * ak + ak + bk * ck) = -2 := by
      rw [hak, hbk, hck] at key2; nlinarith [key2]
    omega

end Bottcher
