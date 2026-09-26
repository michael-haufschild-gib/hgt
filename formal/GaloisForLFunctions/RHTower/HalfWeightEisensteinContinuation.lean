import GaloisForLFunctions.RHTower.HalfWeightRegularisedCoefficients

/-!
# Analytic continuation of the weight-½ Eisenstein series across `Re w = 1/2`

With `ρ(w) = (4w-3)(4w-2)ζ(4w-1)` (entire, `regF`), the regularised series

`E*(z,w) = 2 (ρ(w) y^w + y^{1-w} φ*(w) + Σ_{n≠0} Φ_1(w)(n) e(nx) D*_n(w))`

(`Estar`) satisfies:

* `Estar_eq`: `E*(z,w) = ρ(w) E(z,w)` for `Re w > 1` (trivial nebentypus, level `4M`);
* `differentiableAt_Estar`: `w ↦ E*(z,w)` is holomorphic on the half-plane `Re w > 1/4`;
* `Estar_smul`: `E*(δz, w) = j(δ,z) E*(z,w)` for `δ ∈ Γ₀(4M)` on the whole half-plane (identity
  theorem on the convex half-plane from `Re w > 1`).

The proof of holomorphy is by locally uniform convergence (`Complex.differentiableOn_tsum_of_summable_norm`):
on a closed ball in `Re w > 1/4`, `‖Φ_K(w)(ξ)‖ ≤ C|ξ|^{-K}` (`exists_bound_PhiK`, every `K`, the
transforms being independent of `K`) and `‖D*_n(w)‖ ≤ C|n|^{e}` with
`e = 4 + γ(4Re w-1) + β(2Re w-1/2)` (`exists_bound_Dstar`); choosing `K ≥ e + 2` gives a summable
majorant `C|n|^{-2}`.

So the weight-½ Eisenstein series of level `4M` continues meromorphically to `Re w > 1/4` with
poles only at `w = 3/4` and at the zeros of `ζ(4w-1)`, all in `Re w < 1/2` except `3/4`.
-/

open Real Complex Filter Topology Metric CongruenceSubgroup
open scoped FourierTransform MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.SelbergPoincareKernel

noncomputable section

/-! ### Uniform bounds on closed balls of the spectral parameter -/

theorem re_ge_of_mem_closedBall {w₀ w : ℂ} {r : ℝ} (hw : w ∈ closedBall w₀ r) :
    w₀.re - r ≤ w.re ∧ w.re ≤ w₀.re + r := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have := abs_re_le_norm (w - w₀)
  simp only [Complex.sub_re] at this
  constructor <;> linarith [abs_le.1 (this.trans hw)]

theorem abs_im_le_of_mem_closedBall {w₀ w : ℂ} {r : ℝ} (hw : w ∈ closedBall w₀ r) :
    |w.im| ≤ |w₀.im| + r := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have h := abs_im_le_norm (w - w₀)
  simp only [Complex.sub_im] at h
  have := abs_sub_abs_le_abs_sub w.im w₀.im
  linarith

theorem norm_le_of_mem_closedBall {w₀ w : ℂ} {r : ℝ} (hw : w ∈ closedBall w₀ r) (c : ℂ) :
    ‖w + c‖ ≤ ‖w₀‖ + r + ‖c‖ := by
  rw [mem_closedBall, dist_eq_norm] at hw
  calc ‖w + c‖ = ‖(w - w₀) + w₀ + c‖ := by ring_nf
    _ ≤ ‖w - w₀‖ + ‖w₀‖ + ‖c‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ _ := by linarith

/-- **Uniform decay of the kernel transforms**: on a closed ball in `Re w > 0`,
`‖Φ_K(w)(ξ)‖ ≤ C |ξ|^{-K}`. -/
theorem exists_bound_PhiK {y : ℝ} (hy : 0 < y) {K : ℕ} (hK : 1 ≤ K) {w₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hτ : 0 < w₀.re - r) :
    ∃ C, 0 ≤ C ∧ ∀ w ∈ closedBall w₀ r, ∀ ξ : ℝ, ξ ≠ 0 →
      ‖PhiK y K w ξ‖ ≤ C * |ξ| ^ (-(K : ℝ)) := by
  set a : ℝ := ‖w₀‖ + r + 1 / 4
  set b : ℝ := |w₀.im| + r
  set τ₁ := w₀.re - r
  set τ₂ := w₀.re + r
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set C : ℝ := ((2 * a + 2 * K) / (2 * Real.pi)) ^ K * Real.exp (2 * Real.pi * b) *
    ((y ^ (-(τ₁ + K - 1)) + y ^ (-(τ₂ + K - 1))) * cst ((2 * τ₁ + K) / 2))
  have hcst : 0 ≤ cst ((2 * τ₁ + K) / 2) :=
    MeasureTheory.integral_nonneg fun t => by positivity
  have ha : 0 ≤ a := by positivity
  refine ⟨C, by positivity, fun w hw ξ hξ => ?_⟩
  obtain ⟨hre1, hre2⟩ := re_ge_of_mem_closedBall hw
  have hwre : 1 < 2 * w.re + K := by linarith
  have h := norm_PhiK_le hy hξ K hwre
  refine h.trans ?_
  have hξ0 : 0 < |ξ| := abs_pos.2 hξ
  have h1 : ‖w + 1 / 4‖ ≤ a := by
    have := norm_le_of_mem_closedBall hw (1 / 4); simp only [a]; norm_num at this ⊢; linarith
  have h2 : ‖w - 1 / 4‖ ≤ a := by
    have := norm_le_of_mem_closedBall hw (-(1 / 4)); rw [← sub_eq_add_neg] at this
    simp only [a]; norm_num at this ⊢; linarith
  have hA : (‖w + 1 / 4‖ + ‖w - 1 / 4‖ + 2 * K) / (2 * Real.pi * |ξ|) ≤
      (2 * a + 2 * K) / (2 * Real.pi) * |ξ|⁻¹ := by
    rw [show (2 * a + 2 * K) / (2 * Real.pi) * |ξ|⁻¹ = (2 * a + 2 * K) / (2 * Real.pi * |ξ|) by
      field_simp]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hE : Real.exp (2 * Real.pi * |w.im|) ≤ Real.exp (2 * Real.pi * b) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_im_le_of_mem_closedBall hw) (by positivity))
  have hY : y ^ (1 - w.re - K) ≤ y ^ (-(τ₁ + K - 1)) + y ^ (-(τ₂ + K - 1)) := by
    rw [show 1 - w.re - K = -(w.re + K - 1) by ring]
    exact rpow_neg_le_add hy (by simp only [τ₁]; linarith) (by simp only [τ₂]; linarith)
  have hc : cst ((2 * w.re + K) / 2) ≤ cst ((2 * τ₁ + K) / 2) :=
    cst_anti (by simp only [τ₁]; linarith) (by simp only [τ₁]; linarith)
  have hpow : ((‖w + 1 / 4‖ + ‖w - 1 / 4‖ + 2 * K) / (2 * Real.pi * |ξ|)) ^ K ≤
      ((2 * a + 2 * K) / (2 * Real.pi)) ^ K * |ξ| ^ (-(K : ℝ)) := by
    rw [Real.rpow_neg hξ0.le, Real.rpow_natCast, ← inv_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hA K
  calc ((‖w + 1 / 4‖ + ‖w - 1 / 4‖ + 2 * K) / (2 * Real.pi * |ξ|)) ^ K *
        Real.exp (2 * Real.pi * |w.im|) * (y ^ (1 - w.re - K) * cst ((2 * w.re + K) / 2))
      ≤ (((2 * a + 2 * K) / (2 * Real.pi)) ^ K * |ξ| ^ (-(K : ℝ))) * Real.exp (2 * Real.pi * b) *
          ((y ^ (-(τ₁ + K - 1)) + y ^ (-(τ₂ + K - 1))) * cst ((2 * τ₁ + K) / 2)) := by
        have hc0 : 0 ≤ cst ((2 * w.re + K) / 2) := MeasureTheory.integral_nonneg fun t => by positivity
        refine mul_le_mul (mul_le_mul hpow hE (by positivity) (by positivity))
          (mul_le_mul hY hc (by positivity) (by positivity)) (by positivity) (by positivity)
    _ = C * |ξ| ^ (-(K : ℝ)) := by simp only [C]; ring

theorem continuous_Gbound : Continuous Gbound := by
  unfold Gbound
  have hF : Continuous RHTower.zetaResidueFactor := RHTower.differentiable_zetaResidueFactor.continuous
  fun_prop

/-- The exponent `e(τ) = 4 + γ(4τ-1) + β(2τ-1/2)`. -/
def expE (τ : ℝ) : ℝ := 4 + gammaE (4 * τ - 1) + betaE (2 * τ - 1 / 2)

theorem expE_anti {τ₁ τ : ℝ} (h1 : 1 / 4 < τ₁) (h : τ₁ ≤ τ) : expE τ ≤ expE τ₁ := by
  unfold expE
  have := gammaE_anti (σ₁ := 4 * τ₁ - 1) (σ₂ := 4 * τ - 1) (by linarith) (by linarith)
  have := betaE_anti (σ₁ := 2 * τ₁ - 1 / 2) (σ₂ := 2 * τ - 1 / 2) (by linarith) (by linarith)
  linarith

theorem expE_nonneg {τ : ℝ} (h1 : 1 / 4 < τ) : 0 ≤ expE τ := by
  unfold expE
  have := gammaE_nonneg (σ := 4 * τ - 1) (by linarith)
  have := betaE_nonneg (σ := 2 * τ - 1 / 2) (by linarith)
  linarith

/-- **Uniform polynomial bound for the regularised coefficients** on a closed ball in
`Re w > 1/4`: `‖D*_n(w)‖ ≤ C |n|^{e(Re w₀ - r)}`. -/
theorem exists_bound_Dstar {M : ℕ} (hM : 0 < M) {w₀ : ℂ} {r : ℝ} (h1 : 1 / 4 < w₀.re - r) :
    ∃ C, 0 ≤ C ∧ ∀ w ∈ closedBall w₀ r, ∀ n : ℤ, ∀ hn : n ≠ 0,
      ‖Dstar hn hM w‖ ≤ C * |(n : ℝ)| ^ expE (w₀.re - r) := by
  have hcont : ContinuousOn (fun w : ℂ => Real.sqrt 2 * ‖4 * w - 2‖ * Gbound (2 * w - 1 / 2))
      (closedBall w₀ r) :=
    (Continuous.continuousOn (by
      have := continuous_Gbound
      fun_prop))
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall w₀ r).exists_bound_of_continuousOn hcont
  set e := expE (w₀.re - r)
  have he : 0 ≤ e := expE_nonneg h1
  refine ⟨max C₁ 0 * (4 * M : ℝ) ^ e, by positivity, fun w hw n hn => ?_⟩
  obtain ⟨hre1, hre2⟩ := re_ge_of_mem_closedBall hw
  have hD := norm_Dstar_le hn hM (w := w) (by linarith)
  have hk := kmod_one_le hn hM
  have hC : Real.sqrt 2 * ‖4 * w - 2‖ * Gbound (2 * w - 1 / 2) ≤ max C₁ 0 := by
    have := hC₁ w hw
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hexp : (kmod n M : ℝ) ^ (4 + gammaE (4 * w.re - 1) + betaE (2 * w.re - 1 / 2)) ≤
      (kmod n M : ℝ) ^ e :=
    Real.rpow_le_rpow_of_exponent_le hk (expE_anti h1 hre1)
  have hkm : (kmod n M : ℝ) = (4 * M : ℝ) * |(n : ℝ)| := by
    simp only [kmod]; push_cast; rw [Nat.cast_natAbs, Int.cast_abs]; ring
  have hG : 0 ≤ Real.sqrt 2 * ‖4 * w - 2‖ * Gbound (2 * w - 1 / 2) := by
    unfold Gbound; have := stripC_pos; positivity
  calc ‖Dstar hn hM w‖ ≤ Real.sqrt 2 * ‖4 * w - 2‖ * Gbound (2 * w - 1 / 2) *
        (kmod n M : ℝ) ^ (4 + gammaE (4 * w.re - 1) + betaE (2 * w.re - 1 / 2)) := hD
    _ ≤ max C₁ 0 * (kmod n M : ℝ) ^ e :=
        mul_le_mul hC hexp (by positivity) (le_max_right _ _)
    _ = max C₁ 0 * (4 * M : ℝ) ^ e * |(n : ℝ)| ^ e := by
        rw [hkm, Real.mul_rpow (by positivity) (abs_nonneg _)]; ring


/-! ### The regularised Eisenstein series -/

section Assembly

variable (M : ℕ) [NeZero M]

/-- The regularised coefficient `D*_n(w)`, total in `n`. -/
def DstarZ (n : ℤ) (w : ℂ) : ℂ :=
  if h : n = 0 then 0 else Dstar h (Nat.pos_of_ne_zero (NeZero.ne M)) w

/-- The regularising factor `ρ(w) = (4w-3)(4w-2)ζ(4w-1)`. -/
def regF (w : ℂ) : ℂ := (4 * w - 3) * RHTower.zetaResidueFactor (4 * w - 1)

theorem differentiable_regF : Differentiable ℂ regF := by
  unfold regF
  exact ((differentiable_id.const_mul 4).sub_const 3).mul
    (RHTower.differentiable_zetaResidueFactor.comp ((differentiable_id.const_mul 4).sub_const 1))

/-- The terms of the regularised Fourier expansion. -/
def aTerm (z : UpperHalfPlane) (w : ℂ) (n : ℤ) : ℂ :=
  if n = 0 then ((z.im : ℝ) : ℂ) ^ (1 - w) * phiStar M w
  else PhiK z.im 1 w n * cexp (2 * π * I * n * z.re) * DstarZ M n w

/-- **The regularised weight-½ Eisenstein series** `E*(z,w) = ρ(w) E(z,w)`, defined for all `w`. -/
def Estar (z : UpperHalfPlane) (w : ℂ) : ℂ :=
  2 * (regF w * ((z.im : ℝ) : ℂ) ^ w + ∑' n : ℤ, aTerm M z w n)

theorem aTerm_eq {z : UpperHalfPlane} {w : ℂ} (hw : 1 < w.re) (n : ℤ) :
    aTerm M z w n = regF w * (𝓕 (kerH z.im w) n * cexp (2 * π * I * n * z.re) *
      Dser M (1 : DirichletCharacter ℂ (4 * M)) n w) := by
  have hy := z.im_pos
  unfold aTerm
  split_ifs with hn
  · subst hn
    have h := Dser_zero_mul_integral M hy (w := w) (by linarith)
    rw [phiStar_eq M (by linarith), Int.cast_zero, fourier_zero_eq_integral]
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, regF]
    rw [mul_comm (∫ x, kerH z.im w x), h]
    ring
  · have hξ : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [← fourier_kerH_eq_PhiK hy hξ 1 (by linarith), DstarZ, dif_neg hn, Dstar_eq hn _ (by linarith),
      regF]
    ring

/-- `E*` continues `ρ(w) E(z,w)` from `Re w > 1`. -/
theorem Estar_eq {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    Estar M z w = regF w * eisHalf M (1 : DirichletCharacter ℂ (4 * M)) w z := by
  rw [eisHalf_eq_coeffs M _ hw z, Estar]
  have h1 : (1 : DirichletCharacter ℂ (4 * M)) (-1) = 1 := MulChar.one_apply isUnit_one.neg
  rw [h1, map_one, show (1 : ℂ) + 1 = 2 by norm_num]
  simp_rw [aTerm_eq M hw]
  rw [tsum_mul_left]
  ring

theorem continuous_cexp_mode (n : ℤ) (x : ℝ) : ‖cexp (2 * π * I * n * x)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **Holomorphy of the regularised Eisenstein series** on the half-plane `Re w > 1/4`. -/
theorem differentiableAt_Estar (z : UpperHalfPlane) {w₀ : ℂ} (h1 : 1 / 4 < w₀.re) :
    DifferentiableAt ℂ (Estar M z) w₀ := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hy := z.im_pos
  set r := (w₀.re - 1 / 4) / 2 with hr
  have hr0 : 0 < r := by simp only [hr]; linarith
  have hl : 1 / 4 < w₀.re - r := by simp only [hr]; linarith
  set e := expE (w₀.re - r)
  set K : ℕ := ⌈e⌉₊ + 2 with hK
  have hK1 : 1 ≤ K := by omega
  have heK : e - K ≤ -2 := by
    have := Nat.le_ceil e
    have : ((⌈e⌉₊ + 2 : ℕ) : ℝ) = (⌈e⌉₊ : ℝ) + 2 := by push_cast; ring
    rw [hK, this]; linarith
  obtain ⟨CP, hCP0, hCP⟩ := exists_bound_PhiK hy hK1 hr0 (by linarith)
  obtain ⟨CD, hCD0, hCD⟩ := exists_bound_Dstar hM hl
  -- the constant term on the closed ball
  have hc0 : ContinuousOn (fun w => ((z.im : ℝ) : ℂ) ^ (1 - w) * phiStar M w) (closedBall w₀ r) := by
    intro w hw
    obtain ⟨hre1, _⟩ := re_ge_of_mem_closedBall hw
    have hyC : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    exact ((((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hyC)).mul
      (differentiableAt_phiStar M (by linarith))).continuousAt.continuousWithinAt
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall w₀ r).exists_bound_of_continuousOn hc0
  set u : ℤ → ℝ := fun n => (if n = 0 then C0 else 0) + CP * CD * |(n : ℝ)| ^ (-2 : ℝ)
  have hsu : Summable u :=
    (hasSum_ite_eq (0 : ℤ) C0).summable.add ((Real.summable_abs_int_rpow (b := 2) (by norm_num)).mul_left _)
  have hbound : ∀ (n : ℤ) (w : ℂ), w ∈ ball w₀ r → ‖aTerm M z w n‖ ≤ u n := by
    intro n w hw
    have hwc : w ∈ closedBall w₀ r := ball_subset_closedBall hw
    obtain ⟨hre1, hre2⟩ := re_ge_of_mem_closedBall hwc
    simp only [u]
    by_cases hn : n = 0
    · subst hn
      simp only [aTerm, if_true, Int.cast_zero, abs_zero]
      rw [Real.zero_rpow (by norm_num), mul_zero, add_zero]
      exact hC0 w hwc
    · simp only [aTerm, if_neg hn, zero_add]
      have hξ : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
      have hPhi : PhiK z.im 1 w n = PhiK z.im K w n :=
        PhiK_eq_PhiK hy hξ hK1 (by push_cast; linarith)
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      rw [hPhi, norm_mul, norm_mul, continuous_cexp_mode, mul_one, DstarZ, dif_neg hn]
      have hP := hCP w hwc n hξ
      have hD := hCD w hwc n hn
      calc ‖PhiK z.im K w n‖ * ‖Dstar hn hM w‖
          ≤ (CP * |(n : ℝ)| ^ (-(K : ℝ))) * (CD * |(n : ℝ)| ^ e) :=
            mul_le_mul hP hD (norm_nonneg _) (by positivity)
        _ = CP * CD * |(n : ℝ)| ^ (e - K) := by
            rw [Real.rpow_sub (by linarith)]
            rw [Real.rpow_neg (by linarith)]
            ring
        _ ≤ CP * CD * |(n : ℝ)| ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 heK) (by positivity)
  have hdiff : ∀ n : ℤ, DifferentiableOn ℂ (fun w => aTerm M z w n) (ball w₀ r) := by
    intro n w hw
    obtain ⟨hre1, _⟩ := re_ge_of_mem_closedBall (ball_subset_closedBall hw)
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hn : n = 0
    · subst hn
      have hyC : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
      simp only [aTerm, if_true]
      exact (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hyC)).mul
        (differentiableAt_phiStar M (by linarith))
    · simp only [aTerm, if_neg hn]
      have hP := differentiableAt_PhiK hy (n : ℝ) 1 (w₀ := w) (by push_cast; linarith)
      have hD : DifferentiableAt ℂ (fun w => DstarZ M n w) w := by
        simp only [DstarZ, dif_neg hn]
        exact differentiableAt_Dstar hn hM (by linarith)
      exact (hP.mul_const _).mul hD
  have hsum := Complex.differentiableOn_tsum_of_summable_norm hsu hdiff isOpen_ball hbound
  have hsumAt : DifferentiableAt ℂ (fun w => ∑' n : ℤ, aTerm M z w n) w₀ :=
    hsum.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr0))
  have hyC : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hlead : DifferentiableAt ℂ (fun w => regF w * ((z.im : ℝ) : ℂ) ^ w) w₀ :=
    (differentiable_regF w₀).mul (differentiableAt_id.const_cpow (Or.inl hyC))
  unfold Estar
  exact (hlead.add hsumAt).const_mul 2

/-- **Automorphy of the continued series**: `E*(δz, w) = j(δ,z) E*(z,w)` on `Re w > 1/4`. -/
theorem Estar_smul (z : UpperHalfPlane) (δ : Gamma0 (4 * M)) {w : ℂ} (h1 : 1 / 4 < w.re) :
    Estar M ((δ : SL(2, ℤ)) • z) w = jU δ z * Estar M z w := by
  set U : Set ℂ := {w : ℂ | 1 / 4 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 4)).isPreconnected
  have hf : DifferentiableOn ℂ (fun w => Estar M ((δ : SL(2, ℤ)) • z) w) U := fun w hw =>
    (differentiableAt_Estar M _ hw).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun w => jU δ z * Estar M z w) U := fun w hw =>
    ((differentiableAt_Estar M z hw).const_mul _).differentiableWithinAt
  have hw₁ : (9 / 8 : ℂ) ∈ U := by simp only [hU, Set.mem_setOf_eq]; norm_num
  have hev : (fun w => Estar M ((δ : SL(2, ℤ)) • z) w) =ᶠ[𝓝 (9 / 8 : ℂ)] (fun w => jU δ z * Estar M z w) := by
    have ho : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (by norm_num)] with w hw
    rw [Estar_eq M hw, Estar_eq M hw, eisHalf_smul,
      MulChar.one_apply (isUnit_d M δ)]
    ring
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hUc hw₁ hev h1

end Assembly
