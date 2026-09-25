import GaloisForLFunctions.RHTower.SelbergEisensteinKernel
import GaloisForLFunctions.RHTower.SelbergRamanujanBound
import GaloisForLFunctions.RHTower.SelbergPoincareContinuation

open Complex MeasureTheory Metric UpperHalfPlane
open scoped FourierTransform

/-!
# The non-constant part of the `Γ(N)` Eisenstein series is holomorphic on `Re s > 1/2`

`E^*(z,s) = Σ_{c≠0, n≠0} c^{-2s} N^{-s} 𝓕ker_{0,y/N,s}(n) e(nx/N) S_N(0,n;c)` (`Estar`). The Ramanujan bound
`|S_N(0,n;c)| ≤ (N|n|)²` and the fourth-order decay `|𝓕ker_0(n)| ≪ n^{-4}` give the product majorant
`|c|^{-2σ₁} · C n^{-2}` locally uniformly in `s` (`norm_eterm_le`), so `E^*(z,·)` is holomorphic on `Re s > 1/2`
(`differentiableAt_Estar`).
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinStar
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.RHTower.SelbergEisensteinKernel
  GaloisForLFunctions.RHTower.SelbergRamanujanBound

variable (N : ℕ) [NeZero N]

/-- The non-constant Kloosterman terms of the `Γ(N)` Eisenstein series. -/
noncomputable def eterm (s : ℂ) (z : ℍ) (p : ℤ × ℤ) : ℂ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else
    cexp (-s * (Real.log ((p.1 : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
      (𝓕 (ker 0 (z.im / N) s) p.2 * cexp (2 * Real.pi * Complex.I * p.2 * z.re / N) * ksum N 0 p.1 p.2)

/-- The non-constant part `E^*(z,s)` of the Eisenstein series. -/
noncomputable def Estar (s : ℂ) (z : ℍ) : ℂ := ∑' p : ℤ × ℤ, eterm N s z p

/-- The uniform constant. -/
noncomputable def econst (y σ₁ σ₂ R : ℝ) : ℝ :=
  109 * ((1 + R) / (y / N)) ^ 4 * (((y / N) ^ (1 - σ₂) + (y / N) ^ (1 - σ₁)) * cst σ₁) *
    (N : ℝ) ^ 2 / (2 * Real.pi) ^ 4

theorem norm_eterm_le (z : ℍ) {s : ℂ} {σ₁ σ₂ R : ℝ} (hσ₁ : 1 / 2 < σ₁) (h1 : σ₁ ≤ s.re) (h2 : s.re ≤ σ₂)
    (hs : ‖s‖ ≤ R) (p : ℤ × ℤ) :
    ‖eterm N s z p‖ ≤ (if p.1 = 0 then 0 else |(p.1 : ℝ)| ^ (-(2 * σ₁))) *
      (if p.2 = 0 then 0 else econst N z.im σ₁ σ₂ R * |(p.2 : ℝ)| ^ (-(2 : ℝ))) := by
  unfold eterm
  by_cases hp : p.1 = 0 ∨ p.2 = 0
  · rw [if_pos hp, norm_zero]
    have hR : 0 ≤ R := (norm_nonneg s).trans hs
    have hc := cst_nonneg σ₁
    have hy : 0 < z.im / N := div_pos z.im_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    have he : 0 ≤ econst N z.im σ₁ σ₂ R := by unfold econst; positivity
    split_ifs <;> positivity
  push Not at hp
  obtain ⟨hc, hk⟩ := hp
  rw [if_neg (not_or.mpr ⟨hc, hk⟩), if_neg hc, if_neg hk]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN : (0 : ℝ) < N := by linarith
  have hy : 0 < z.im / N := div_pos z.im_pos hN
  have hc2 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ p.1 ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs p.1]
    exact_mod_cast this
  have hE := norm_exp_neg_mul_log (s := s) hc2 h1
  have hEN := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 (by linarith)
  rw [neg_zero, Real.rpow_zero] at hEN
  have hcsq : ((p.1 : ℝ) ^ 2) ^ (-σ₁) = |(p.1 : ℝ)| ^ (-(2 * σ₁)) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; push_cast; ring_nf
  rw [hcsq] at hE
  -- Fourier factor
  have hs' : 1 / 2 < s.re := by linarith
  have hF := norm_fourier_ker0_le_four (y := z.im / N) (s := s) hy hs' (p.2 : ℝ)
  have hk1 : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hvv : vv (z.im / N) s ≤ (1 + R) / (z.im / N) := by
    unfold vv; gcongr
  have hX : (z.im / N) ^ (1 - s.re) * cst s.re ≤ ((z.im / N) ^ (1 - σ₂) + (z.im / N) ^ (1 - σ₁)) * cst σ₁ :=
    mul_le_mul (rpow_le_add hy (by linarith) (by linarith)) (cst_anti hσ₁ h1) (cst_nonneg _) (by positivity)
  have hF' : ‖𝓕 (ker 0 (z.im / N) s) (p.2 : ℝ)‖ ≤
      109 * ((1 + R) / (z.im / N)) ^ 4 * (((z.im / N) ^ (1 - σ₂) + (z.im / N) ^ (1 - σ₁)) * cst σ₁) /
        ((2 * Real.pi) ^ 4 * |(p.2 : ℝ)| ^ 4) := by
    rw [le_div_iff₀ (by positivity)]
    have hv := vv_nonneg (y := z.im / N) (s := s) hy
    have := cst_nonneg s.re
    calc ‖𝓕 (ker 0 (z.im / N) s) (p.2 : ℝ)‖ * ((2 * Real.pi) ^ 4 * |(p.2 : ℝ)| ^ 4)
        = (2 * Real.pi * |(p.2 : ℝ)|) ^ 4 * ‖𝓕 (ker 0 (z.im / N) s) (p.2 : ℝ)‖ := by ring
      _ ≤ 109 * vv (z.im / N) s ^ 4 * ((z.im / N) ^ (1 - s.re) * cst s.re) := hF
      _ ≤ _ := by gcongr
  have hK := norm_ksum_zero_le N hc hk
  have hK' : ‖ksum N 0 p.1 p.2‖ ≤ (N : ℝ) ^ 2 * |(p.2 : ℝ)| ^ 2 := by
    refine hK.trans (le_of_eq ?_); simp [mul_pow, Nat.cast_natAbs]
  have hexp : ‖cexp (2 * Real.pi * Complex.I * p.2 * z.re / N)‖ = 1 := norm_cexp_two_pi_I_div _ _ _
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hexp, mul_one]
  have hk2 : |(p.2 : ℝ)| ^ (-(2 : ℝ)) = (|(p.2 : ℝ)| ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _)]; norm_cast
  rw [hk2]
  set A := 109 * ((1 + R) / (z.im / N)) ^ 4 * (((z.im / N) ^ (1 - σ₂) + (z.im / N) ^ (1 - σ₁)) * cst σ₁)
  have hA : 0 ≤ A := by have := cst_nonneg σ₁; have : 0 ≤ R := (norm_nonneg s).trans hs; simp only [A]; positivity
  have hk4 : 0 < |(p.2 : ℝ)| := by linarith
  calc ‖cexp (-s * (Real.log ((p.1 : ℝ) ^ 2) : ℂ))‖ * ‖cexp (-s * (Real.log N : ℂ))‖ *
        (‖𝓕 (ker 0 (z.im / N) s) (p.2 : ℝ)‖ * ‖ksum N 0 p.1 p.2‖)
      ≤ |(p.1 : ℝ)| ^ (-(2 * σ₁)) * 1 * (A / ((2 * Real.pi) ^ 4 * |(p.2 : ℝ)| ^ 4) *
          ((N : ℝ) ^ 2 * |(p.2 : ℝ)| ^ 2)) := by
        gcongr
    _ = |(p.1 : ℝ)| ^ (-(2 * σ₁)) * (econst N z.im σ₁ σ₂ R * (|(p.2 : ℝ)| ^ 2)⁻¹) := by
        simp only [econst, A]; field_simp

theorem summable_ite_abs {b : ℝ} (hb : 1 < b) (C : ℝ) (hC : 0 ≤ C) :
    Summable (fun n : ℤ => if n = 0 then 0 else C * |(n : ℝ)| ^ (-b)) := by
  refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
    ((Real.summable_abs_int_rpow hb).mul_left C)
  split_ifs
  · positivity
  · exact le_rfl

/-- **Holomorphy of the non-constant part of the Eisenstein series** on `Re s > 1/2`. -/
theorem differentiableAt_Estar (z : ℍ) {s₀ : ℂ} (h : 1 / 2 < s₀.re) :
    DifferentiableAt ℂ (fun s => Estar N s z) s₀ := by
  set r := (s₀.re - 1 / 2) / 2
  have hr : 0 < r := by simp only [r]; linarith
  set σ₁ := s₀.re - r
  set σ₂ := s₀.re + r
  set R := ‖s₀‖ + r
  have hσ₁ : 1 / 2 < σ₁ := by simp only [σ₁, r]; linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hy : 0 < z.im / N := div_pos z.im_pos hN
  have he : 0 ≤ econst N z.im σ₁ σ₂ R := by
    have := cst_nonneg σ₁; have : 0 ≤ R := by simp only [R]; positivity
    unfold econst; positivity
  set f : ℤ → ℝ := fun c => if c = 0 then 0 else 1 * |(c : ℝ)| ^ (-(2 * σ₁))
  set g : ℤ → ℝ := fun k => if k = 0 then 0 else econst N z.im σ₁ σ₂ R * |(k : ℝ)| ^ (-(2 : ℝ))
  have hf : Summable f := summable_ite_abs (by linarith) 1 zero_le_one
  have hg : Summable g := summable_ite_abs (by norm_num) _ he
  unfold Estar
  apply GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated hr
    (bound := fun p : ℤ × ℤ => f p.1 * g p.2)
  · intro p s hs
    obtain ⟨h1, _, _⟩ := ball_props hs
    apply DifferentiableAt.differentiableWithinAt
    unfold eterm
    by_cases hp : p.1 = 0 ∨ p.2 = 0
    · simp only [if_pos hp]; exact differentiableAt_const _
    simp only [if_neg hp]
    refine ((differentiable_exp_neg_mul _).differentiableAt.mul (differentiable_exp_neg_mul _).differentiableAt).mul ?_
    exact ((differentiableAt_fourier_ker le_rfl hy
      (by linarith) _).mul_const _).mul_const _
  · intro p s hs
    obtain ⟨h1, h2, h3⟩ := ball_props hs
    refine (norm_eterm_le N z hσ₁ h1 h2 h3 p).trans (le_of_eq ?_)
    simp only [f, g, one_mul]; rfl
  · exact Summable.mul_of_nonneg hf hg (fun c => by simp only [f]; split_ifs <;> positivity)
      (fun k => by simp only [g]; split_ifs <;> positivity)

end GaloisForLFunctions.RHTower.SelbergEisensteinStar
