import GaloisForLFunctions.RHTower.JointAncestryClusterPhase
import GaloisForLFunctions.RHTower.JointAncestryZeroTailBound

/-!
# Per-point estimates for the log-weight amplification

Fix the centre `ξ`, the window `(A, B]`, the scale `τ ≥ 0` and the twist `φ ∈ [0, π/2]`.  For a
point `s` with both shifts `Re(ξ − s)` and `Re(s + ξ̄ − 1)` at most `ε ≤ 1/4`, and with deviations at
most `1/2`, the test value is (`exists_jasLogWeightValue_eq_exp_of_shift`)

`V(s) = w_s exp(τ E(s) + R)`,   `‖R‖ ≤ r = 16 τ² (log B)²/√A`,

`E(s) = e^{iφ} S₁ + e^{−iφ} S₂`, `S₁ = S(ξ − s)`, `S₂ = S(s + ξ̄ − 1)`.  This file records the
estimates used in the amplification:

* `Re E ≤ cos φ · Re S₁ + sin φ · |Im S₁| + ‖S₂‖` and
  `Im E = sin φ · Re S₁ + cos φ · Im S₁ + Im(e^{−iφ} S₂)`;
* at real arguments `S` is real and nonnegative (`jasLogWeightSum_ofReal`);
* if `‖S₁‖ ≤ M` then `|Im S₁| ≤ M √(2λ)` with `λ = 1 − Re S₁/M` (`abs_im_le_sqrt_two_mul`): the
  imaginary part of a near-coherent prime sum is controlled by its real deficit.
-/

open Complex
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-! ## The value form -/

/-- The log-weight term is at most `log B (A+1)^{ε−1}` on the window. -/
theorem log_div_mul_exp_le {A B : ℕ} {p : Nat.Primes} (hp : p ∈ jasPrimeWindow A B) {ε : ℝ}
    (hε : ε ≤ 1) :
    Real.log p / p * Real.exp (ε * Real.log p) ≤
      Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) := by
  have hpw := mem_jasPrimeWindow.mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hpA : (A : ℝ) + 1 ≤ p := by exact_mod_cast hpw.1
  have hpB : (p : ℝ) ≤ B := by exact_mod_cast hpw.2
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
  have hrw : Real.log p / p * Real.exp (ε * Real.log p) =
      Real.log p * Real.exp ((ε - 1) * Real.log p) := by
    rw [show (ε - 1) * Real.log p = ε * Real.log p + -Real.log p by ring, Real.exp_add,
      Real.exp_neg, Real.exp_log hp0]
    ring
  rw [hrw]
  refine mul_le_mul (Real.log_le_log hp0 hpB) ?_ (Real.exp_pos _).le
    (Real.log_nonneg (by linarith [hpA, hp0]))
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
    (Real.log_le_log (by positivity) hpA) (by linarith))

/-- **The value form.** -/
theorem exists_jasLogWeightValue_eq_exp_of_shift {ξ s : ℂ} {A B : ℕ} (hA : 1 ≤ A) {τ ε : ℝ}
    (hτ : 0 ≤ τ) (hε : ε ≤ 1 / 4) (φ : ℝ) (h₁ : (ξ - s).re ≤ ε) (h₂ : (s + conj ξ - 1).re ≤ ε)
    (hdev : 2 * τ * Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) ≤ 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A ∧
      jasLogWeightValue ξ A B τ φ s =
        (1 / (s * (1 - s))) * cexp ((τ : ℂ) * jasLogWeightExponent ξ A B φ s + R) := by
  have hdevp : ∀ p ∈ jasPrimeWindow A B,
      ‖jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p - 1‖ ≤ 1 / 2 := by
    intro p hp
    have ha : 0 ≤ τ * (Real.log p / p) := mul_nonneg hτ (log_div_nonneg_prime p)
    refine (norm_jasLogWeightLocal_sub_one_le_of_re_le ξ s ha φ p h₁ h₂).trans ?_
    have hb := log_div_mul_exp_le hp (ε := ε) (by linarith)
    calc 2 * (τ * (Real.log p / p)) * Real.exp (ε * Real.log p)
        = 2 * τ * (Real.log p / p * Real.exp (ε * Real.log p)) := by ring
      _ ≤ 2 * τ * (Real.log B * Real.exp ((ε - 1) * Real.log (A + 1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 1 / 2 := by linarith
  obtain ⟨R, hR, hprod⟩ := exists_jasLogWeightValue_eq_exp ξ A B τ φ s hdevp
  refine ⟨R, hR.trans (sum_sq_norm_jasLogWeightLocal_sub_one_le ξ s hA hτ φ
    (by linarith) (by linarith)), ?_⟩
  rw [jasLogWeightValue, hprod, div_eq_mul_one_div, mul_comm]

/-! ## The exponent -/

theorem re_jasLogWeightExponent (ξ : ℂ) (A B : ℕ) (φ : ℝ) (s : ℂ) :
    (jasLogWeightExponent ξ A B φ s).re =
      Real.cos φ * (jasLogWeightSum A B (ξ - s)).re -
        Real.sin φ * (jasLogWeightSum A B (ξ - s)).im +
      (cexp (((-φ : ℝ) : ℂ) * I) * jasLogWeightSum A B (s + conj ξ - 1)).re := by
  rw [jasLogWeightExponent, Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

theorem im_jasLogWeightExponent (ξ : ℂ) (A B : ℕ) (φ : ℝ) (s : ℂ) :
    (jasLogWeightExponent ξ A B φ s).im =
      Real.sin φ * (jasLogWeightSum A B (ξ - s)).re +
        Real.cos φ * (jasLogWeightSum A B (ξ - s)).im +
      (cexp (((-φ : ℝ) : ℂ) * I) * jasLogWeightSum A B (s + conj ξ - 1)).im := by
  rw [jasLogWeightExponent, Complex.add_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

theorem norm_cexp_negTwist_mul (φ : ℝ) (z : ℂ) : ‖cexp (((-φ : ℝ) : ℂ) * I) * z‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `Re E ≤ cos φ Re S₁ + sin φ |Im S₁| + ‖S₂‖` for `sin φ ≥ 0`. -/
theorem re_jasLogWeightExponent_le (ξ : ℂ) (A B : ℕ) {φ : ℝ} (hφ : 0 ≤ Real.sin φ) (s : ℂ) :
    (jasLogWeightExponent ξ A B φ s).re ≤
      Real.cos φ * (jasLogWeightSum A B (ξ - s)).re +
        Real.sin φ * |(jasLogWeightSum A B (ξ - s)).im| +
      ‖jasLogWeightSum A B (s + conj ξ - 1)‖ := by
  rw [re_jasLogWeightExponent]
  have h1 : -(Real.sin φ * (jasLogWeightSum A B (ξ - s)).im) ≤
      Real.sin φ * |(jasLogWeightSum A B (ξ - s)).im| := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_le_abs _) hφ
  have h2 := (Complex.re_le_norm (cexp (((-φ : ℝ) : ℂ) * I) *
    jasLogWeightSum A B (s + conj ξ - 1))).trans (norm_cexp_negTwist_mul φ _).le
  linarith

/-! ## Real arguments -/

/-- At a real argument the window sum is real and nonnegative. -/
theorem jasLogWeightSum_ofReal (A B : ℕ) (x : ℝ) :
    jasLogWeightSum A B (x : ℂ) =
      ((∑ p ∈ jasPrimeWindow A B, Real.log p / p * Real.exp (x * Real.log p) : ℝ) : ℂ) := by
  rw [jasLogWeightSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_exp]

theorem jasLogWeightSum_ofReal_nonneg (A B : ℕ) (x : ℝ) :
    0 ≤ ∑ p ∈ jasPrimeWindow A B, Real.log p / p * Real.exp (x * Real.log p) :=
  Finset.sum_nonneg fun p _ => mul_nonneg (log_div_nonneg_prime p) (Real.exp_pos _).le

/-! ## Imaginary parts of near-coherent sums -/

/-- If `‖S‖ ≤ M` then `|Im S| ≤ M √(2(1 − Re S/M))`. -/
theorem abs_im_le_sqrt_two_mul {S : ℂ} {M : ℝ} (hM : 0 < M) (hS : ‖S‖ ≤ M) :
    |S.im| ≤ M * Real.sqrt (2 * (1 - S.re / M)) := by
  have hsq : S.im ^ 2 ≤ 2 * M ^ 2 * (1 - S.re / M) := by
    have h1 : S.re ^ 2 + S.im ^ 2 ≤ M ^ 2 := by
      have := Complex.sq_norm S
      rw [Complex.normSq_apply] at this
      nlinarith [norm_nonneg S]
    have h2 : 2 * M ^ 2 * (1 - S.re / M) = 2 * M ^ 2 - 2 * M * S.re := by field_simp
    rw [h2]
    nlinarith [sq_nonneg (S.re - M)]
  have hrhs : 0 ≤ 2 * (1 - S.re / M) := by
    have : S.re ≤ M := (Complex.re_le_norm S).trans hS
    have : S.re / M ≤ 1 := (div_le_one hM).mpr this
    linarith
  calc |S.im| = Real.sqrt (S.im ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (M ^ 2 * (2 * (1 - S.re / M))) := Real.sqrt_le_sqrt (by nlinarith)
    _ = M * Real.sqrt (2 * (1 - S.re / M)) := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM.le]

/-! ## The three point estimates -/

/-- The size of a test value. -/
theorem norm_jasLogWeightValue_le_of_shift {ξ s : ℂ} {A B : ℕ} (hA : 1 ≤ A) {τ ε : ℝ}
    (hτ : 0 ≤ τ) (hε : ε ≤ 1 / 4) (φ : ℝ) (h₁ : (ξ - s).re ≤ ε) (h₂ : (s + conj ξ - 1).re ≤ ε)
    (hdev : 2 * τ * Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) ≤ 1 / 2) :
    ‖jasLogWeightValue ξ A B τ φ s‖ ≤
      ‖1 / (s * (1 - s))‖ * Real.exp (τ * (jasLogWeightExponent ξ A B φ s).re +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A) := by
  obtain ⟨R, hR, hV⟩ := exists_jasLogWeightValue_eq_exp_of_shift hA hτ hε φ h₁ h₂ hdev
  rw [hV, norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hre : ((τ : ℂ) * jasLogWeightExponent ξ A B φ s + R).re =
      τ * (jasLogWeightExponent ξ A B φ s).re + R.re := by
    rw [Complex.add_re, Complex.re_ofReal_mul]
  rw [hre]
  linarith [(Complex.re_le_norm R).trans hR]

/-- **The target.**  With the twist chosen so that `arg w_ξ + τ(M − S_B) sin φ = π`, the target value
has real part at most `−|w_ξ| e^{τ M cos φ − r}/2`. -/
theorem re_jasLogWeightValue_target_le {ξ : ℂ} {A B : ℕ} (hA : 1 ≤ A) {τ ε φ : ℝ}
    (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ Real.pi / 2)
    (hξ : ξ.re ≤ 1 / 2)
    (hdev : 2 * τ * Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) ≤ 1 / 2)
    (hr : 16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A ≤ 1)
    (hwξ : 1 / (ξ * (1 - ξ)) ≠ 0)
    (harg : (1 / (ξ * (1 - ξ))).arg + τ * (jasLogMass A B -
      ∑ p ∈ jasPrimeWindow A B, Real.log p / p * Real.exp ((2 * ξ.re - 1) * Real.log p)) *
        Real.sin φ = Real.pi) :
    (jasLogWeightValue ξ A B τ φ ξ).re ≤
      -(‖1 / (ξ * (1 - ξ))‖ * Real.exp (τ * jasLogMass A B * Real.cos φ -
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A)) / 2 := by
  set M := jasLogMass A B with hM
  set SB := ∑ p ∈ jasPrimeWindow A B, Real.log p / p * Real.exp ((2 * ξ.re - 1) * Real.log p)
    with hSB
  set r := 16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A with hr'
  have h₁ : (ξ - ξ).re ≤ ε := by simpa using hε0
  have h₂ : (ξ + conj ξ - 1).re ≤ ε := by simp; linarith
  obtain ⟨R, hR, hV⟩ := exists_jasLogWeightValue_eq_exp_of_shift hA hτ hε φ h₁ h₂ hdev
  -- the target exponent
  have hreal : ξ + conj ξ - 1 = ((2 * ξ.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hE : jasLogWeightExponent ξ A B φ ξ =
      cexp ((φ : ℂ) * I) * (M : ℂ) + cexp (((-φ : ℝ) : ℂ) * I) * (SB : ℂ) := by
    rw [jasLogWeightExponent, sub_self, jasLogWeightSum_zero, hreal, jasLogWeightSum_ofReal]
  have hEre : (jasLogWeightExponent ξ A B φ ξ).re = (M + SB) * Real.cos φ := by
    rw [hE, Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp [Real.cos_neg]
    ring
  have hEim : (jasLogWeightExponent ξ A B φ ξ).im = (M - SB) * Real.sin φ := by
    rw [hE, Complex.add_im, Complex.mul_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp [Real.sin_neg]
    ring
  set z : ℂ := (τ : ℂ) * jasLogWeightExponent ξ A B φ ξ + R with hz
  have hzim : z.im - τ * (M - SB) * Real.sin φ = R.im := by
    rw [hz, Complex.add_im, Complex.im_ofReal_mul, hEim]; ring
  have hzre : τ * M * Real.cos φ - r ≤ z.re := by
    rw [hz, Complex.add_re, Complex.re_ofReal_mul, hEre]
    have hSB0 : 0 ≤ SB := jasLogWeightSum_ofReal_nonneg A B _
    have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
    have := neg_le_of_abs_le ((Complex.abs_re_le_norm R).trans hR)
    nlinarith [mul_nonneg (mul_nonneg hτ hSB0) hcos]
  have hharg : (1 / (ξ * (1 - ξ))).arg + τ * (M - SB) * Real.sin φ = Real.pi := harg
  have hlt := re_mul_cexp_le_neg_half hwξ hharg
    (by rw [hzim]; exact (Complex.abs_im_le_norm R).trans (hR.trans hr))
  rw [hV]
  refine hlt.trans ?_
  have := Real.exp_le_exp.mpr hzre
  have h0 := norm_nonneg (1 / (ξ * (1 - ξ)))
  nlinarith

/-- **Aligned points.**  If the phase of `w_s e^{τE(s)}` stays within `π/2 − r` of the target phase
modulo `2π`, the point contributes non-positively. -/
theorem re_jasLogWeightValue_nonpos_of_aligned {ξ s : ℂ} {A B : ℕ} (hA : 1 ≤ A) {τ ε φ y₀ : ℝ}
    (hτ : 0 ≤ τ) (hε : ε ≤ 1 / 4) (h₁ : (ξ - s).re ≤ ε) (h₂ : (s + conj ξ - 1).re ≤ ε)
    (hdev : 2 * τ * Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) ≤ 1 / 2)
    (hwξ : 1 / (ξ * (1 - ξ)) ≠ 0) (hy₀ : (1 / (ξ * (1 - ξ))).arg + y₀ = Real.pi) {k : ℤ}
    (halign : |((1 / (s * (1 - s))) / (1 / (ξ * (1 - ξ)))).arg +
        (τ * (jasLogWeightExponent ξ A B φ s).im - y₀) - 2 * Real.pi * k| +
      16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A ≤ Real.pi / 2) :
    (jasLogWeightValue ξ A B τ φ s).re ≤ 0 := by
  obtain ⟨R, hR, hV⟩ := exists_jasLogWeightValue_eq_exp_of_shift hA hτ hε φ h₁ h₂ hdev
  rw [hV]
  refine re_mul_cexp_nonpos_of_aligned hwξ hy₀ (k := k) ?_
  have him : ((τ : ℂ) * jasLogWeightExponent ξ A B φ s + R).im =
      τ * (jasLogWeightExponent ξ A B φ s).im + R.im := by
    rw [Complex.add_im, Complex.im_ofReal_mul]
  rw [him]
  have hRim := (Complex.abs_im_le_norm R).trans hR
  calc |((1 / (s * (1 - s))) / (1 / (ξ * (1 - ξ)))).arg +
        (τ * (jasLogWeightExponent ξ A B φ s).im + R.im - y₀) - 2 * Real.pi * k|
      = |(((1 / (s * (1 - s))) / (1 / (ξ * (1 - ξ)))).arg +
          (τ * (jasLogWeightExponent ξ A B φ s).im - y₀) - 2 * Real.pi * k) + R.im| := by
        ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

end

end RHTower
