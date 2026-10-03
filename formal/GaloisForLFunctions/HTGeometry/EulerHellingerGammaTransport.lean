import GaloisForLFunctions.HTGeometry.HalfLineMellinMultiplier
import GaloisForLFunctions.HTGeometry.PrimeGammaRelativeModularTransport
import GaloisForLFunctions.HTGeometry.GammaCriticalLineModulus
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness

/-!
# The unique dilation-equivariant Mellin transport between the two Euler gauges

On `H = L²((0,∞), dt)` the two dilation orbits

* `h_λ = ψ^{(6)}_λ`, `h_λ(t) = √(8/15) λ³ t^{5/2} e^{-λt}` (order-six aperture gauge),
* `f_λ = √(216/115)(ψ^{(3)}_λ - 2^{-3/2} ψ^{(3)}_{2λ})`, `f_λ(t) = √(864/115) λ^{3/2} t (e^{-λt} - e^{-2λt})`
  (cubic Hellinger gauge)

consist of unit vectors (**(EHGM.3)–(EHGM.5)**).  Their Mellin transforms on the unitary line are
`√(8/15) Γ(3-iθ) λ^{iθ}` and `√(864/115) Γ(3/2-iθ) λ^{iθ} (1 - 2^{-3/2+iθ})`, `θ = 2πξ`
(**(EHGM.12)**), so the multiplier

`m(ξ) = (18/√23) Γ(3/2-iθ)/Γ(3-iθ) (1 - 2^{-3/2} 2^{iθ})`  (**(EHGM.13)**)

maps every `h_λ` to `f_λ` (**(EHGM.15)**).  The symbol is continuous, bounded, nowhere zero and
`|m| ≤ 18 |θ|^{-3/2}` for `|θ| ≥ 1` (**(EHGM.14)**), from `|Γ(1/2+it)|² = π/cosh πt` and
`|Γ(1+it)|² = πt/sinh πt`.  Hence `M` is injective with dense, non-closed range.  It is the unique
bounded dilation-equivariant operator with `h_1 ↦ f_1`, because the `h_λ` are total.

`Q = M^*M - I` satisfies `⟨h_λ, Q h_λ⟩ = 0` for every `λ` (**(EHGM.19)**) but is indefinite:
`|m(0)|² = (81π/92)(9/8 - 1/√2) > 243/230 > 1` (**(EHGM.20)**) while `|m| → 0`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace FourierTransform ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The two gauges -/

/-- The cubic Hellinger vector `f_λ = √(216/115)(ψ^{(3)}_λ - 2^{-3/2} ψ^{(3)}_{2λ})`. -/
def hellingerVector {lam : ℝ} (hlam : 0 < lam) : HalfLineL2 :=
  ((Real.sqrt (216 / 115) : ℝ) : ℂ) •
    (gammaCoherentVector 3 hlam - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) •
      gammaCoherentVector 3 (by positivity : (0 : ℝ) < 2 * lam))

theorem two_rpow_neg_three_halves_sq : ((2 : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / 8 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `k₃(λ, 2λ) = (2√2/3)³ = 16√2/27`. -/
theorem cubicGram_double {lam : ℝ} (hlam : 0 < lam) :
    (2 * Real.sqrt (lam * (2 * lam)) / (lam + 2 * lam)) ^ 3 = 16 * Real.sqrt 2 / 27 := by
  have h1 : Real.sqrt (lam * (2 * lam)) = lam * Real.sqrt 2 := by
    rw [show lam * (2 * lam) = lam ^ 2 * 2 by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam.le]
  rw [h1]
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  field_simp
  rw [h2]
  norm_num

theorem two_rpow_neg_three_halves_mul_sqrt_two : (2 : ℝ) ^ (-(3 / 2 : ℝ)) * Real.sqrt 2 = 1 / 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]
  norm_num

/-- **(EHGM.4)** `‖f_λ‖ = 1`. -/
theorem norm_hellingerVector {lam : ℝ} (hlam : 0 < lam) : ‖hellingerVector hlam‖ = 1 := by
  have h2lam : (0 : ℝ) < 2 * lam := by positivity
  set c : ℝ := (2 : ℝ) ^ (-(3 / 2 : ℝ))
  have hinner : ⟪hellingerVector hlam, hellingerVector hlam⟫_ℂ = 1 := by
    rw [hellingerVector, inner_smul_left, inner_smul_right,
      inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_smul_left, inner_smul_right, inner_gammaCoherentVector, inner_gammaCoherentVector,
      inner_gammaCoherentVector, inner_gammaCoherentVector]
    simp only [Complex.conj_ofReal]
    have e1 : (2 * Real.sqrt (lam * lam) / (lam + lam)) ^ 3 = 1 := by
      rw [Real.sqrt_mul_self hlam.le]; field_simp; ring
    have e2 : (2 * Real.sqrt (2 * lam * (2 * lam)) / (2 * lam + 2 * lam)) ^ 3 = 1 := by
      rw [Real.sqrt_mul_self h2lam.le]; field_simp; ring
    have e3 := cubicGram_double hlam
    have e4 : (2 * Real.sqrt (2 * lam * lam) / (2 * lam + lam)) ^ 3 = 16 * Real.sqrt 2 / 27 := by
      rw [show 2 * lam * lam = lam * (2 * lam) by ring, show 2 * lam + lam = lam + 2 * lam by ring, e3]
    rw [e1, e2, e3, e4]
    have hc2 : c ^ 2 = 1 / 8 := two_rpow_neg_three_halves_sq
    have hcs : c * Real.sqrt 2 = 1 / 2 := two_rpow_neg_three_halves_mul_sqrt_two
    have h216 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 216 / 115 by norm_num)
    have : ((Real.sqrt (216 / 115) * Real.sqrt (216 / 115) *
        (1 - c * (16 * Real.sqrt 2 / 27) - c * (16 * Real.sqrt 2 / 27) + c ^ 2) : ℝ) : ℂ) = 1 := by
      rw [h216]
      norm_cast
      nlinarith [hcs, hc2]
    rw [← this]
    push_cast
    ring
  have hsq : ‖hellingerVector hlam‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, hinner]
    simp
  have h0 := norm_nonneg (hellingerVector hlam)
  nlinarith [sq_nonneg (‖hellingerVector hlam‖ - 1)]

/-! ## Dilation orbits -/

theorem gammaCoherentVector_congr (k : ℕ) [NeZero k] {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t')
    (h : t = t') : gammaCoherentVector k ht = gammaCoherentVector k ht' := by
  subst h
  rfl

/-- `ψ^{(k)}_{κt}(s) = √κ ψ^{(k)}_t(κ s)`. -/
theorem gammaCoherentProfile_dilation (k : ℕ) {κ t s : ℝ} (hκ : 0 < κ) (hs : 0 < s) :
    gammaCoherentProfile k (κ * t) s = Real.sqrt κ * gammaCoherentProfile k t (κ * s) := by
  have hF : (0 : ℝ) ≤ ((k - 1).factorial : ℝ) := by positivity
  unfold gammaCoherentProfile
  rw [show (2 * (κ * t)) ^ k / ((k - 1).factorial : ℝ) = κ ^ k * ((2 * t) ^ k / ((k - 1).factorial : ℝ)) by
      rw [mul_pow, mul_pow]; ring,
    Real.sqrt_mul (pow_nonneg hκ.le k), Real.mul_rpow hκ.le hs.le,
    show Real.sqrt (κ ^ k) = Real.sqrt κ * κ ^ (((k : ℝ) - 1) / 2) by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hκ.le,
        ← Real.rpow_add hκ]
      congr 1
      ring,
    show -(t * (κ * s)) = -(κ * t * s) by ring]
  ring

/-- **(EHGM.2)** `D_κ ψ^{(k)}_t = ψ^{(k)}_{κt}`. -/
theorem halfLineDilation_gammaCoherentVector (k : ℕ) [NeZero k] {κ t : ℝ} (hκ : 0 < κ) (ht : 0 < t) :
    halfLineDilation κ (gammaCoherentVector k ht) = gammaCoherentVector k (mul_pos hκ ht) := by
  refine halfLineDilation_eq_of_ae hκ (gammaCoherentVector_ae k ht)
    (gammaCoherentVector_ae k (mul_pos hκ ht)) fun s hs => ?_
  rw [gammaCoherentProfile_dilation k hκ hs]
  push_cast
  ring

/-- **(EHGM.2)** `h_λ = D_λ h_1`. -/
theorem halfLineDilation_sixth {lam : ℝ} (hlam : 0 < lam) :
    halfLineDilation lam (gammaCoherentVector 6 one_pos) = gammaCoherentVector 6 hlam := by
  rw [halfLineDilation_gammaCoherentVector 6 hlam one_pos]
  exact gammaCoherentVector_congr 6 _ _ (mul_one lam)

/-- **(EHGM.2)** `f_λ = D_λ f_1`. -/
theorem halfLineDilation_hellingerVector {lam : ℝ} (hlam : 0 < lam) :
    halfLineDilation lam (hellingerVector one_pos) = hellingerVector hlam := by
  rw [hellingerVector, hellingerVector, map_smul, map_sub, map_smul,
    halfLineDilation_gammaCoherentVector 3 hlam one_pos, halfLineDilation_gammaCoherentVector 3 hlam,
    gammaCoherentVector_congr 3 (mul_pos hlam one_pos) hlam (mul_one lam),
    gammaCoherentVector_congr 3 (mul_pos hlam (by norm_num : (0 : ℝ) < 2 * 1)) (by positivity : (0 : ℝ) < 2 * lam)
      (by ring)]

/-! ## Mellin coordinates -/

/-- `𝓜ψ^{(k)}_t(ξ) = √(2^k/(k-1)!) Γ((k/2) - 2πiξ) t^{2πiξ}`. -/
theorem halfLineMellinUnitary_gammaCoherentVector_eq (k : ℕ) [NeZero k] {t : ℝ} (ht : 0 < t) :
    (halfLineMellinUnitary (gammaCoherentVector k ht) : ℝ → ℂ) =ᵐ[volume] fun ξ =>
      (Real.sqrt (2 ^ k / ((k - 1).factorial : ℝ)) : ℂ) *
        Complex.Gamma (1 / 2 - 2 * Real.pi * ξ * I + (((k : ℝ) - 1) / 2 : ℝ)) *
          (t : ℂ) ^ (2 * Real.pi * ξ * I) := by
  filter_upwards [halfLineMellinUnitary_gammaCoherentVector k ht] with ξ hξ
  rw [hξ, mellin_gammaCoherentProfile ht]
  · congr 2
    ring
  · have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne k)
    simp only [add_re, sub_re, div_ofNat_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_zero, re_ofNat, im_ofNat]
    norm_num
    linarith

/-- The transport symbol `m(ξ) = (18/√23) Γ(3/2-2πiξ)/Γ(3-2πiξ) (1 - 2^{-3/2} 2^{2πiξ})`. -/
def ehgmSymbol (ξ : ℝ) : ℂ :=
  ((18 / Real.sqrt 23 : ℝ) : ℂ) *
    (Complex.Gamma (3 / 2 - 2 * Real.pi * ξ * I) / Complex.Gamma (3 - 2 * Real.pi * ξ * I)) *
      (1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I))

theorem Gamma_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.Gamma z ≠ 0 :=
  Complex.Gamma_ne_zero fun m hm => by
    have := congrArg Complex.re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem Gamma_three_halves_sub_ne_zero (ξ : ℝ) : Complex.Gamma (3 / 2 - 2 * Real.pi * ξ * I) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by simp)

theorem Gamma_three_sub_ne_zero (ξ : ℝ) : Complex.Gamma (3 - 2 * Real.pi * ξ * I) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by simp)

theorem norm_two_cpow_mul_I (ξ : ℝ) : ‖(2 : ℂ) ^ (2 * Real.pi * ξ * I)‖ = 1 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  simp

theorem one_sub_two_factor_ne_zero (ξ : ℝ) :
    (1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I)) ≠ 0 := by
  intro h
  have h1 : (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I) = 1 := by
    linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_mul, norm_two_cpow_mul_I, mul_one, Complex.norm_real, norm_one,
    Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num) _)] at h2
  have h3 : (2 : ℝ) ^ (-(3 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  linarith

/-- **(EHGM.14)** `m(ξ) ≠ 0` for every real `ξ`. -/
theorem ehgmSymbol_ne_zero (ξ : ℝ) : ehgmSymbol ξ ≠ 0 := by
  unfold ehgmSymbol
  refine mul_ne_zero (mul_ne_zero ?_ (div_ne_zero (Gamma_three_halves_sub_ne_zero ξ)
    (Gamma_three_sub_ne_zero ξ))) (one_sub_two_factor_ne_zero ξ)
  exact_mod_cast (div_pos (by norm_num : (0 : ℝ) < 18) (Real.sqrt_pos.2 (by norm_num))).ne'

/-- **(EHGM.14)** `m` is continuous. -/
theorem continuous_ehgmSymbol : Continuous ehgmSymbol := by
  have hlin : ∀ c : ℂ, Continuous fun ξ : ℝ => c - 2 * Real.pi * ξ * I := fun c =>
    continuous_const.sub (((continuous_const.mul Complex.continuous_ofReal)).mul continuous_const)
  have hG : ∀ c : ℂ, 0 < c.re → Continuous fun ξ : ℝ => Complex.Gamma (c - 2 * Real.pi * ξ * I) :=
    fun c hc => continuous_iff_continuousAt.2 fun ξ =>
      (Complex.continuousAt_Gamma _ fun m hm => by
        have := congrArg Complex.re hm
        simp at this
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp (hlin c).continuousAt
  have hexpo : Continuous fun ξ : ℝ => (2 * Real.pi * ξ * I : ℂ) :=
    (continuous_const.mul Complex.continuous_ofReal).mul continuous_const
  have hcpow : Continuous fun ξ : ℝ => (2 : ℂ) ^ (2 * Real.pi * ξ * I) :=
    hexpo.const_cpow (Or.inl two_ne_zero)
  unfold ehgmSymbol
  refine (continuous_const.mul ((hG (3 / 2) (by norm_num)).div (hG 3 (by norm_num))
    Gamma_three_sub_ne_zero)).mul (continuous_const.sub (continuous_const.mul hcpow))

/-! ## Size of the symbol -/

/-- `|Γ(3/2 + iy)|² = (1/4 + y²) π / cosh(πy)`. -/
theorem norm_sq_Gamma_three_halves (y : ℝ) :
    ‖Complex.Gamma (3 / 2 + y * I)‖ ^ 2 = (1 / 4 + y ^ 2) * (Real.pi / Real.cosh (Real.pi * y)) := by
  have hz : (1 / 2 : ℂ) + y * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [show (3 / 2 : ℂ) + y * I = ((1 / 2 : ℂ) + y * I) + 1 by ring, Complex.Gamma_add_one _ hz, norm_mul,
    mul_pow, normSq_Gamma_half_add_mul_I]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- `|Γ(3 + iy)|² = (4 + y²)(1 + y²) πy / sinh(πy)` for `y ≠ 0`. -/
theorem norm_sq_Gamma_three {y : ℝ} (hy : y ≠ 0) :
    ‖Complex.Gamma (3 + y * I)‖ ^ 2 =
      (4 + y ^ 2) * (1 + y ^ 2) * (Real.pi * y / Real.sinh (Real.pi * y)) := by
  have h1 : (2 : ℂ) + y * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 : (1 : ℂ) + y * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [show (3 : ℂ) + y * I = ((2 : ℂ) + y * I) + 1 by ring, Complex.Gamma_add_one _ h1,
    show (2 : ℂ) + y * I = ((1 : ℂ) + y * I) + 1 by ring, Complex.Gamma_add_one _ h2, norm_mul,
    norm_mul, mul_pow, mul_pow, RHTower.norm_Gamma_one_add_mul_I_sq hy]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

theorem gammaRatio_bound {a S K : ℝ} (ha : 1 ≤ a) (hS : 0 < S) (hSK : S ≤ K) :
    (1 / 4 + a ^ 2) * (Real.pi / K) / ((4 + a ^ 2) * (1 + a ^ 2) * (Real.pi * a / S)) ≤ 1 / a ^ 3 := by
  have hK : 0 < K := hS.trans_le hSK
  have ha0 : 0 < a := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h1 : (1 / 4 + a ^ 2) * a ^ 2 ≤ (4 + a ^ 2) * (1 + a ^ 2) := by nlinarith
  have hpi := Real.pi_pos
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hSK (by positivity : (0 : ℝ) ≤ a * ((4 + a ^ 2) * (1 + a ^ 2))),
    mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ a * S)]

/-- **(EHGM.14) Decay.**  For `|2πξ| ≥ 1`, `|m(ξ)|² ≤ 324/|2πξ|³`. -/
theorem norm_sq_ehgmSymbol_le {ξ : ℝ} (hξ : 1 ≤ |2 * Real.pi * ξ|) :
    ‖ehgmSymbol ξ‖ ^ 2 ≤ 324 / |2 * Real.pi * ξ| ^ 3 := by
  set a : ℝ := |2 * Real.pi * ξ| with ha_def
  set y : ℝ := -(2 * Real.pi * ξ) with hy
  have ha0 : 0 < a := by linarith
  have hy0 : y ≠ 0 := by
    intro h
    have : a = 0 := by rw [ha_def, show 2 * Real.pi * ξ = -y by rw [hy]; ring, h, neg_zero, abs_zero]
    linarith
  have e1 : (3 / 2 : ℂ) - 2 * Real.pi * ξ * I = 3 / 2 + y * I := by rw [hy]; push_cast; ring
  have e2 : (3 : ℂ) - 2 * Real.pi * ξ * I = 3 + y * I := by rw [hy]; push_cast; ring
  have hya : |y| = a := by rw [hy, abs_neg]
  have hysq : y ^ 2 = a ^ 2 := by rw [← hya, sq_abs]
  have hcosh : Real.cosh (Real.pi * y) = Real.cosh (Real.pi * a) := by
    rw [← hya, ← Real.cosh_abs (Real.pi * y), abs_mul, abs_of_pos Real.pi_pos]
  have hsinh : Real.pi * y / Real.sinh (Real.pi * y) = Real.pi * a / Real.sinh (Real.pi * a) := by
    rcases lt_or_gt_of_ne hy0 with h | h
    · rw [← hya, abs_of_neg h, show Real.pi * -y = -(Real.pi * y) by ring, Real.sinh_neg,
        neg_div_neg_eq]
    · rw [← hya, abs_of_pos h]
  have hS : 0 < Real.sinh (Real.pi * a) := Real.sinh_pos_iff.2 (mul_pos Real.pi_pos ha0)
  have hSK : Real.sinh (Real.pi * a) ≤ Real.cosh (Real.pi * a) := (Real.sinh_lt_cosh _).le
  have hratio : ‖Complex.Gamma (3 / 2 + y * I) / Complex.Gamma (3 + y * I)‖ ^ 2 ≤ 1 / a ^ 3 := by
    rw [norm_div, div_pow, norm_sq_Gamma_three_halves, norm_sq_Gamma_three hy0, hcosh, hsinh, hysq]
    exact gammaRatio_bound hξ hS hSK
  have hc : (2 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hc0 : 0 ≤ (2 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hfac : ‖1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_two_cpow_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hc0]
    linarith
  have h18 : ‖((18 / Real.sqrt 23 : ℝ) : ℂ)‖ ^ 2 = 324 / 23 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  unfold ehgmSymbol
  rw [e1, e2, norm_mul, norm_mul, mul_pow, mul_pow, h18]
  have hf2 : ‖1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I)‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I))]
  have hr0 := sq_nonneg ‖Complex.Gamma (3 / 2 + y * I) / Complex.Gamma (3 + y * I)‖
  have ha3 : 0 < a ^ 3 := by positivity
  calc 324 / 23 * ‖Complex.Gamma (3 / 2 + y * I) / Complex.Gamma (3 + y * I)‖ ^ 2 *
        ‖1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I)‖ ^ 2
      ≤ 324 / 23 * (1 / a ^ 3) * 4 := by gcongr
    _ ≤ 324 / a ^ 3 := by
        rw [show (324 : ℝ) / 23 * (1 / a ^ 3) * 4 = (1296 / 23) / a ^ 3 by ring]
        exact div_le_div_of_nonneg_right (by norm_num) ha3.le

theorem norm_ehgmSymbol_le_of_large {ξ : ℝ} (hξ : 1 ≤ |2 * Real.pi * ξ|) : ‖ehgmSymbol ξ‖ ≤ 18 := by
  have h := norm_sq_ehgmSymbol_le hξ
  have h3 : 1 ≤ |2 * Real.pi * ξ| ^ 3 := one_le_pow₀ hξ
  have h4 : ‖ehgmSymbol ξ‖ ^ 2 ≤ 18 ^ 2 := by
    refine h.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [norm_nonneg (ehgmSymbol ξ)]

theorem exists_bound_ehgmSymbol : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ‖ehgmSymbol ξ‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := -(1 / (2 * Real.pi))) (b := 1 / (2 * Real.pi))).exists_bound_of_continuousOn
    continuous_ehgmSymbol.continuousOn
  refine ⟨max C₁ 18, le_max_of_le_right (by norm_num), fun ξ => ?_⟩
  by_cases hξ : ξ ∈ Icc (-(1 / (2 * Real.pi))) (1 / (2 * Real.pi))
  · exact (hC₁ ξ hξ).trans (le_max_left _ _)
  · refine (norm_ehgmSymbol_le_of_large ?_).trans (le_max_right _ _)
    have hpi := Real.pi_pos
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hξ
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    rcases hξ with h | h
    · have : 1 / (2 * Real.pi) < |ξ| := by
        rw [abs_of_neg (by linarith [div_pos one_pos (by positivity : (0 : ℝ) < 2 * Real.pi)])]
        linarith
      rw [div_lt_iff₀ (by positivity)] at this
      linarith
    · have : 1 / (2 * Real.pi) < |ξ| := by
        rw [abs_of_pos (by linarith [div_pos one_pos (by positivity : (0 : ℝ) < 2 * Real.pi)])]
        exact h
      rw [div_lt_iff₀ (by positivity)] at this
      linarith

/-- A uniform bound for the symbol. -/
def ehgmSymbolBound : ℝ := Classical.choose exists_bound_ehgmSymbol

theorem ehgmSymbolBound_nonneg : 0 ≤ ehgmSymbolBound := (Classical.choose_spec exists_bound_ehgmSymbol).1

theorem norm_ehgmSymbol_le_bound (ξ : ℝ) : ‖ehgmSymbol ξ‖ ≤ ehgmSymbolBound :=
  (Classical.choose_spec exists_bound_ehgmSymbol).2 ξ

/-- **(EHGM.14)** `|m|` is arbitrarily small on intervals. -/
theorem ehgmSymbol_small (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : ℝ, a < b ∧ ∀ ξ ∈ Icc a b, ‖ehgmSymbol ξ‖ ≤ ε := by
  have hpi := Real.pi_pos
  set R := (1 + 324 / ε ^ 2) / (2 * Real.pi)
  refine ⟨R, R + 1, by linarith, fun ξ hξ => ?_⟩
  have hR : 2 * Real.pi * R = 1 + 324 / ε ^ 2 := by
    simp only [R]
    field_simp
  have hR1 : 1 ≤ 2 * Real.pi * R := by rw [hR]; linarith [div_pos (by norm_num : (0 : ℝ) < 324) (pow_pos hε 2)]
  have hξR : 2 * Real.pi * R ≤ |2 * Real.pi * ξ| := by
    rw [abs_of_pos (by nlinarith [hξ.1, hR1])]
    nlinarith [hξ.1]
  have h1 := norm_sq_ehgmSymbol_le (hR1.trans hξR)
  have h3 : 324 / ε ^ 2 ≤ |2 * Real.pi * ξ| ^ 3 := by
    have h4 : 2 * Real.pi * R ≤ (2 * Real.pi * R) ^ 3 := le_self_pow₀ hR1 (by norm_num)
    have h5 : (2 * Real.pi * R) ^ 3 ≤ |2 * Real.pi * ξ| ^ 3 :=
      pow_le_pow_left₀ (by linarith) hξR 3
    linarith
  have h6 : ‖ehgmSymbol ξ‖ ^ 2 ≤ ε ^ 2 := by
    refine h1.trans ?_
    rw [div_le_iff₀ (by linarith [div_pos (by norm_num : (0 : ℝ) < 324) (pow_pos hε 2)])]
    rw [div_le_iff₀ (pow_pos hε 2)] at h3
    linarith
  nlinarith [norm_nonneg (ehgmSymbol ξ)]

/-- **(EHGM.20)** `|m(0)|² = (81π/92)(9/8 - 1/√2)`. -/
theorem norm_sq_ehgmSymbol_zero :
    ‖ehgmSymbol 0‖ ^ 2 = 81 * Real.pi / 92 * (9 / 8 - 1 / Real.sqrt 2) := by
  have hG3 : Complex.Gamma 3 = 2 := by
    have := Complex.Gamma_nat_eq_factorial 2
    norm_num at this ⊢
  have hG32 : Complex.Gamma (3 / 2) = (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num),
      Complex.Gamma_one_half_eq]
  have hnorm : ‖(Real.pi : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt Real.pi := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Real.sqrt_eq_rpow]
    norm_num
  set c : ℝ := (2 : ℝ) ^ (-(3 / 2 : ℝ))
  have hc2 : c ^ 2 = 1 / 8 := two_rpow_neg_three_halves_sq
  have hcs : c * Real.sqrt 2 = 1 / 2 := two_rpow_neg_three_halves_mul_sqrt_two
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  unfold ehgmSymbol
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, sub_zero, Complex.cpow_zero, mul_one]
  rw [hG3, hG32, norm_mul, norm_mul, norm_div, norm_mul, hnorm, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  norm_num
  have hs23 := Real.sq_sqrt (show (0 : ℝ) ≤ 23 by norm_num)
  have hspi := Real.sq_sqrt Real.pi_pos.le
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have e : (18 / Real.sqrt 23 * (1 / 2 * Real.sqrt Real.pi / 2) * (1 - c)) ^ 2 =
      324 / 23 * (Real.pi / 16) * (1 - c) ^ 2 := by
    rw [show 18 / Real.sqrt 23 * (1 / 2 * Real.sqrt Real.pi / 2) * (1 - c) =
      18 / Real.sqrt 23 * (Real.sqrt Real.pi / 4) * (1 - c) by ring, mul_pow, mul_pow, div_pow, div_pow,
      hs23, hspi]
    norm_num
  have h2c : 2 * c = (Real.sqrt 2)⁻¹ := by
    field_simp
    linarith
  rw [e, show (1 - c) ^ 2 = 9 / 8 - 2 * c by nlinarith [hc2], h2c]
  ring

/-- **(EHGM.20)** `|m(0)|² > 243/230 > 1`. -/
theorem one_lt_norm_sq_ehgmSymbol_zero : 243 / 230 < ‖ehgmSymbol 0‖ ^ 2 ∧ 1 < ‖ehgmSymbol 0‖ ^ 2 := by
  rw [norm_sq_ehgmSymbol_zero]
  have hpi := Real.pi_gt_three
  have hs2 : 1 / Real.sqrt 2 < 29 / 40 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num), one_mul]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h1 : 243 / 230 < 81 * Real.pi / 92 * (9 / 8 - 1 / Real.sqrt 2) := by
    have : (0 : ℝ) < 9 / 8 - 1 / Real.sqrt 2 := by linarith
    nlinarith
  exact ⟨h1, by linarith⟩

/-! ## The transport -/

/-- **(EHGM.13)** The Mellin transport `M` with symbol `m`. -/
def ehgmTransport : HalfLineL2 →L[ℂ] HalfLineL2 :=
  mellinMultiplier continuous_ehgmSymbol.measurable ehgmSymbolBound_nonneg norm_ehgmSymbol_le_bound

theorem ehgm_constant : 18 / Real.sqrt 23 * Real.sqrt (8 / 15) = 2 * Real.sqrt (216 / 115) := by
  have h1 : (18 / Real.sqrt 23 * Real.sqrt (8 / 15)) ^ 2 = (2 * Real.sqrt (216 / 115)) ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num),
      Real.sq_sqrt (by norm_num)]
    norm_num
  exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h1

/-- **(EHGM.15)** `M h_λ = f_λ` for every `λ > 0`. -/
theorem ehgmTransport_sixth {lam : ℝ} (hlam : 0 < lam) :
    ehgmTransport (gammaCoherentVector 6 hlam) = hellingerVector hlam := by
  have h2lam : (0 : ℝ) < 2 * lam := by positivity
  apply halfLineMellinUnitary.injective
  refine Lp.ext ?_
  have hf : (halfLineMellinUnitary (hellingerVector hlam) : ℝ → ℂ) =ᵐ[volume] fun ξ =>
      ((Real.sqrt (216 / 115) : ℝ) : ℂ) * ((halfLineMellinUnitary (gammaCoherentVector 3 hlam) : ℝ → ℂ) ξ -
        (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (halfLineMellinUnitary (gammaCoherentVector 3 h2lam) : ℝ → ℂ) ξ) := by
    rw [hellingerVector, map_smul, map_sub, map_smul]
    filter_upwards [Lp.coeFn_smul ((Real.sqrt (216 / 115) : ℝ) : ℂ)
        (halfLineMellinUnitary (gammaCoherentVector 3 hlam) -
          (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) • halfLineMellinUnitary (gammaCoherentVector 3 h2lam)),
      Lp.coeFn_sub (halfLineMellinUnitary (gammaCoherentVector 3 hlam))
        ((((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) • halfLineMellinUnitary (gammaCoherentVector 3 h2lam)),
      Lp.coeFn_smul (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
        (halfLineMellinUnitary (gammaCoherentVector 3 h2lam))] with ξ h1 h2 h3
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  filter_upwards [coeFn_halfLineMellinUnitary_mellinMultiplier continuous_ehgmSymbol.measurable
      ehgmSymbolBound_nonneg norm_ehgmSymbol_le_bound (gammaCoherentVector 6 hlam),
    halfLineMellinUnitary_gammaCoherentVector_eq 6 hlam, hf,
    halfLineMellinUnitary_gammaCoherentVector_eq 3 hlam,
    halfLineMellinUnitary_gammaCoherentVector_eq 3 h2lam] with ξ h1 h2 h3 h4 h5
  change (halfLineMellinUnitary (ehgmTransport (gammaCoherentVector 6 hlam)) : ℝ → ℂ) ξ = _ at h1
  rw [h1, h2, h3, h4, h5]
  have e6 : (1 / 2 : ℂ) - 2 * Real.pi * ξ * I + (((((6 : ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ) =
      3 - 2 * Real.pi * ξ * I := by push_cast; ring
  have e3 : (1 / 2 : ℂ) - 2 * Real.pi * ξ * I + (((((3 : ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ) =
      3 / 2 - 2 * Real.pi * ξ * I := by push_cast; ring
  have hsq6 : Real.sqrt (2 ^ 6 / ((6 - 1).factorial : ℝ)) = Real.sqrt (8 / 15) := by norm_num [Nat.factorial]
  have hsq3 : Real.sqrt (2 ^ 3 / ((3 - 1).factorial : ℝ)) = 2 := by
    have h : Real.sqrt (2 ^ 3 / ((3 - 1).factorial : ℝ)) = Real.sqrt (2 ^ 2) := by
      norm_num [Nat.factorial]
    rw [h, Real.sqrt_sq (by norm_num)]
  rw [e6, e3, hsq6, hsq3]
  have hcpow : ((2 * lam : ℝ) : ℂ) ^ (2 * Real.pi * ξ * I) =
      (2 : ℂ) ^ (2 * Real.pi * ξ * I) * (lam : ℂ) ^ (2 * Real.pi * ξ * I) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) hlam.le]
    norm_num
  rw [hcpow]
  have hG := Gamma_three_sub_ne_zero ξ
  have hk' : ((18 / Real.sqrt 23 : ℝ) : ℂ) * ((Real.sqrt (8 / 15) : ℝ) : ℂ) =
      ((Real.sqrt (216 / 115) : ℝ) : ℂ) * 2 := by
    rw [← Complex.ofReal_mul, ehgm_constant]
    push_cast
    ring
  unfold ehgmSymbol
  set A := Complex.Gamma (3 / 2 - 2 * Real.pi * ξ * I)
  set B := Complex.Gamma (3 - 2 * Real.pi * ξ * I)
  set F := (1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I))
  set L := (lam : ℂ) ^ (2 * Real.pi * ξ * I)
  calc ((18 / Real.sqrt 23 : ℝ) : ℂ) * (A / B) * F * (((Real.sqrt (8 / 15) : ℝ) : ℂ) * B * L)
      = ((18 / Real.sqrt 23 : ℝ) : ℂ) * ((Real.sqrt (8 / 15) : ℝ) : ℂ) * (A / B * B) * F * L := by ring
    _ = ((Real.sqrt (216 / 115) : ℝ) : ℂ) * 2 * A * F * L := by rw [div_mul_cancel₀ A hG, hk']
    _ = _ := by simp only [F]; push_cast; ring

/-- **(EHGM.12)** `𝓜 h_1 = √(8/15) Γ(3 - 2πiξ)`. -/
theorem halfLineMellinUnitary_sixth_one :
    (halfLineMellinUnitary (gammaCoherentVector 6 (one_pos : (0 : ℝ) < 1)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ((Real.sqrt (8 / 15) : ℝ) : ℂ) * Complex.Gamma (3 - 2 * Real.pi * ξ * I) := by
  filter_upwards [halfLineMellinUnitary_gammaCoherentVector_eq 6 (one_pos : (0 : ℝ) < 1)] with ξ h
  rw [h]
  have e6 : (1 / 2 : ℂ) - 2 * Real.pi * ξ * I + (((((6 : ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ) =
      3 - 2 * Real.pi * ξ * I := by push_cast; ring
  have hsq6 : Real.sqrt (2 ^ 6 / ((6 - 1).factorial : ℝ)) = Real.sqrt (8 / 15) := by
    norm_num [Nat.factorial]
  rw [e6, hsq6, Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- **(EHGM.12)** `𝓜 f_1 = √(864/115) Γ(3/2 - 2πiξ) (1 - 2^{-3/2} 2^{2πiξ})`. -/
theorem halfLineMellinUnitary_hellingerVector_one :
    (halfLineMellinUnitary (hellingerVector (one_pos : (0 : ℝ) < 1)) : ℝ → ℂ) =ᵐ[volume] fun ξ =>
      ((Real.sqrt (864 / 115) : ℝ) : ℂ) * Complex.Gamma (3 / 2 - 2 * Real.pi * ξ * I) *
        (1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I)) := by
  rw [← ehgmTransport_sixth]
  filter_upwards [coeFn_halfLineMellinUnitary_mellinMultiplier continuous_ehgmSymbol.measurable
      ehgmSymbolBound_nonneg norm_ehgmSymbol_le_bound (gammaCoherentVector 6 (one_pos : (0 : ℝ) < 1)),
    halfLineMellinUnitary_sixth_one] with ξ h1 h2
  change (halfLineMellinUnitary (ehgmTransport (gammaCoherentVector 6 (one_pos : (0 : ℝ) < 1))) :
    ℝ → ℂ) ξ = _ at h1
  rw [h1, h2]
  have hG := Gamma_three_sub_ne_zero ξ
  have h864 : Real.sqrt (864 / 115) = Real.sqrt (216 / 115) * 2 := by
    rw [show (864 / 115 : ℝ) = (216 / 115) * 2 ^ 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hk' : ((18 / Real.sqrt 23 : ℝ) : ℂ) * ((Real.sqrt (8 / 15) : ℝ) : ℂ) =
      ((Real.sqrt (864 / 115) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ehgm_constant, h864]
    push_cast
    ring
  unfold ehgmSymbol
  set A := Complex.Gamma (3 / 2 - 2 * Real.pi * ξ * I)
  set B := Complex.Gamma (3 - 2 * Real.pi * ξ * I)
  set F := (1 - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (2 : ℂ) ^ (2 * Real.pi * ξ * I))
  calc ((18 / Real.sqrt 23 : ℝ) : ℂ) * (A / B) * F * (((Real.sqrt (8 / 15) : ℝ) : ℂ) * B)
      = ((18 / Real.sqrt 23 : ℝ) : ℂ) * ((Real.sqrt (8 / 15) : ℝ) : ℂ) * (A / B * B) * F := by ring
    _ = _ := by rw [div_mul_cancel₀ A hG, hk']

theorem norm_norm_ehgmSymbol_le_bound (ξ : ℝ) : ‖((‖ehgmSymbol ξ‖ : ℝ) : ℂ)‖ ≤ ehgmSymbolBound := by
  rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_ehgmSymbol_le_bound ξ

/-- **(EHGM.15)** `M` is dilation-equivariant. -/
theorem ehgmTransport_halfLineDilation (κ : ℝ) (u : HalfLineL2) :
    ehgmTransport (halfLineDilation κ u) = halfLineDilation κ (ehgmTransport u) :=
  mellinMultiplier_halfLineDilation _ _ _ κ u

/-- **Uniqueness of the transport.**  A bounded dilation-equivariant operator with `h_1 ↦ f_1` is `M`:
it agrees with `M` on every `h_λ`, and the `h_λ` are total. -/
theorem eq_ehgmTransport_of_equivariant (A : HalfLineL2 →L[ℂ] HalfLineL2)
    (hA : ∀ κ, 0 < κ → ∀ u, A (halfLineDilation κ u) = halfLineDilation κ (A u))
    (h1 : A (gammaCoherentVector 6 one_pos) = hellingerVector one_pos) : A = ehgmTransport := by
  have hdense := (Submodule.dense_iff_topologicalClosure_eq_top).2 (gammaCoherent_primeClock_total 6 ∅)
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro _ ⟨p, rfl⟩
  have hl := primeClock_pos p.1
  simp only
  rw [← halfLineDilation_sixth hl, hA _ hl, h1, halfLineDilation_hellingerVector hl,
    ehgmTransport_halfLineDilation, ehgmTransport_sixth one_pos, halfLineDilation_hellingerVector hl]

/-- **(EHGM.14)** `M` is injective with dense, non-closed range; it is not bounded below. -/
theorem ehgmTransport_properties :
    Function.Injective ehgmTransport ∧ DenseRange ehgmTransport ∧
      ¬ IsClosed (Set.range ehgmTransport) ∧
      ¬ ∃ c > 0, ∀ u : HalfLineL2, c * ‖u‖ ≤ ‖ehgmTransport u‖ :=
  ⟨mellinMultiplier_injective _ _ _ ehgmSymbol_ne_zero,
    denseRange_mellinMultiplier _ _ _ ehgmSymbol_ne_zero,
    not_isClosed_range_mellinMultiplier _ _ _ ehgmSymbol_ne_zero ehgmSymbol_small,
    not_boundedBelow_mellinMultiplier _ _ _ ehgmSymbol_small⟩

/-- **(EHGM.16)–(EHGM.17) Phase quotient.**  `⟨M u, M v⟩ = ⟨|M| u, |M| v⟩`. -/
theorem inner_ehgmTransport_eq_modulus (u v : HalfLineL2) :
    ⟪ehgmTransport u, ehgmTransport v⟫_ℂ =
      ⟪mellinMultiplier (measurable_norm_symbol continuous_ehgmSymbol.measurable) ehgmSymbolBound_nonneg
          norm_norm_ehgmSymbol_le_bound u,
        mellinMultiplier (measurable_norm_symbol continuous_ehgmSymbol.measurable) ehgmSymbolBound_nonneg
          norm_norm_ehgmSymbol_le_bound v⟫_ℂ :=
  inner_mellinMultiplier_eq_modulus _ _ _ ehgmSymbol_ne_zero u v

theorem ehgmTransport_eq_phase_comp_modulus :
    ehgmTransport =
      mellinMultiplier (measurable_phase_symbol continuous_ehgmSymbol.measurable) zero_le_one
          (fun ξ => (norm_phase_symbol ehgmSymbol_ne_zero ξ).le) ∘L
        mellinMultiplier (measurable_norm_symbol continuous_ehgmSymbol.measurable) ehgmSymbolBound_nonneg
          norm_norm_ehgmSymbol_le_bound :=
  mellinMultiplier_eq_phase_comp_modulus _ _ _ ehgmSymbol_ne_zero

/-! ## The metric anomaly `Q = M^*M - I` -/

/-- **(EHGM.18)** `Q = M^*M - I`. -/
def ehgmAnomaly : HalfLineL2 →L[ℂ] HalfLineL2 :=
  ContinuousLinearMap.adjoint ehgmTransport ∘L ehgmTransport - 1

theorem re_inner_ehgmAnomaly (u : HalfLineL2) :
    (⟪u, ehgmAnomaly u⟫_ℂ).re = ‖ehgmTransport u‖ ^ 2 - ‖u‖ ^ 2 := by
  rw [ehgmAnomaly, sub_apply, ContinuousLinearMap.comp_apply,
    one_apply_eq_self, inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
    Complex.sub_re, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
  rfl

/-- **(EHGM.19) Cellwise neutrality.**  `⟨h_λ, Q h_λ⟩ = 0`. -/
theorem inner_ehgmAnomaly_sixth {lam : ℝ} (hlam : 0 < lam) :
    ⟪gammaCoherentVector 6 hlam, ehgmAnomaly (gammaCoherentVector 6 hlam)⟫_ℂ = 0 := by
  rw [ehgmAnomaly, sub_apply, ContinuousLinearMap.comp_apply,
    one_apply_eq_self, inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
    ehgmTransport_sixth hlam, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    norm_hellingerVector, norm_gammaCoherentVector, sub_self]

/-- **(EHGM.20) Indefiniteness.**  `Q` has a positive and a negative region. -/
theorem ehgmAnomaly_indefinite :
    (∃ u : HalfLineL2, 0 < (⟪u, ehgmAnomaly u⟫_ℂ).re) ∧
      ∃ v : HalfLineL2, (⟪v, ehgmAnomaly v⟫_ℂ).re < 0 := by
  have key : ∀ (a b c : ℝ), a < b → 0 ≤ c →
      ∃ u : HalfLineL2, u ≠ 0 ∧ ((∀ ξ ∈ Icc a b, c ≤ ‖ehgmSymbol ξ‖) → c * ‖u‖ ≤ ‖ehgmTransport u‖) ∧
        ((∀ ξ ∈ Icc a b, ‖ehgmSymbol ξ‖ ≤ c) → ‖ehgmTransport u‖ ≤ c * ‖u‖) := by
    intro a b c hab hc
    have hmeas : MeasurableSet (Icc a b) := measurableSet_Icc
    have hfin : volume (Icc a b) ≠ ∞ := by simp
    set w : Lp ℂ 2 (volume : Measure ℝ) := indicatorConstLp 2 hmeas hfin (1 : ℂ)
    have hw : w ≠ 0 := by
      intro h0
      have := congrArg norm h0
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_zero] at this
      simp only [norm_one, one_mul] at this
      rw [Real.volume_real_Icc_of_le hab.le] at this
      have hp : (0 : ℝ) < (b - a) ^ (1 / (2 : ℝ≥0∞).toReal) := Real.rpow_pos_of_pos (by linarith) _
      linarith
    set u := halfLineMellinUnitary.symm w
    have hu : ‖u‖ = ‖w‖ := halfLineMellinUnitary.symm.norm_map w
    have hMu : ‖ehgmTransport u‖ = ‖lpBoundedMulCLM (p := 2) (μ := volume)
        continuous_ehgmSymbol.measurable ehgmSymbolBound_nonneg norm_ehgmSymbol_le_bound w‖ := by
      rw [← halfLineMellinUnitary.norm_map]
      change ‖halfLineMellinUnitary (mellinMultiplier _ _ _ u)‖ = _
      rw [halfLineMellinUnitary_mellinMultiplier, LinearIsometryEquiv.apply_symm_apply]
    have hu0 : u ≠ 0 := by
      intro h
      apply hw
      rw [← LinearIsometryEquiv.apply_symm_apply halfLineMellinUnitary w]
      change halfLineMellinUnitary u = 0
      rw [h, map_zero]
    refine ⟨u, hu0, fun hlow => ?_, fun hup => ?_⟩
    · rw [hMu, hu]
      by_cases hc0 : c = 0
      · rw [hc0, zero_mul]; exact norm_nonneg _
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have h := Lp.norm_le_mul_norm_of_ae_le_mul (c := c⁻¹) (f := w)
        (g := lpBoundedMulCLM (p := 2) (μ := volume) continuous_ehgmSymbol.measurable
          ehgmSymbolBound_nonneg norm_ehgmSymbol_le_bound w) (by
          filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) continuous_ehgmSymbol.measurable
              ehgmSymbolBound_nonneg norm_ehgmSymbol_le_bound w,
            indicatorConstLp_coeFn (p := 2) (hs := hmeas) (hμs := hfin) (c := (1 : ℂ))] with ξ h1 h2
          rw [h1, norm_mul]
          by_cases hξ : ξ ∈ Icc a b
          · have := hlow ξ hξ
            rw [← mul_assoc]
            exact le_mul_of_one_le_left (norm_nonneg _) (by
              rw [← div_eq_inv_mul, one_le_div hcpos]; exact this)
          · rw [h2, Set.indicator_of_notMem hξ, norm_zero]
            positivity)
      rw [inv_mul_eq_div, le_div_iff₀ hcpos] at h
      linarith
    · rw [hMu, hu]
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) continuous_ehgmSymbol.measurable
          ehgmSymbolBound_nonneg norm_ehgmSymbol_le_bound w,
        indicatorConstLp_coeFn (p := 2) (hs := hmeas) (hμs := hfin) (c := (1 : ℂ))] with ξ h1 h2
      rw [h1, norm_mul]
      by_cases hξ : ξ ∈ Icc a b
      · exact mul_le_mul_of_nonneg_right (hup ξ hξ) (norm_nonneg _)
      · rw [h2, Set.indicator_of_notMem hξ, norm_zero, mul_zero, mul_zero]
  refine ⟨?_, ?_⟩
  · -- near zero `|m| > 1`
    obtain ⟨_, h1⟩ := one_lt_norm_sq_ehgmSymbol_zero
    have h0 : 1 < ‖ehgmSymbol 0‖ := by nlinarith [norm_nonneg (ehgmSymbol 0)]
    set r := (1 + ‖ehgmSymbol 0‖) / 2
    have hr1 : 1 < r := by simp only [r]; linarith
    have hrm : r < ‖ehgmSymbol 0‖ := by simp only [r]; linarith
    have hcont := (continuous_norm.comp continuous_ehgmSymbol).continuousAt (x := 0)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds hrm))
    obtain ⟨u, hu0, hlow, -⟩ := key (-(δ / 2)) (δ / 2) r (by linarith) (by linarith)
    have h := hlow fun ξ hξ => (hball (by
      rw [Real.dist_eq, sub_zero]
      rw [abs_lt]; constructor <;> linarith [hξ.1, hξ.2])).le
    refine ⟨u, ?_⟩
    rw [re_inner_ehgmAnomaly]
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have h2 : (r * ‖u‖) ^ 2 ≤ ‖ehgmTransport u‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    have hr2 : 1 < r ^ 2 := by nlinarith
    have h3 : ‖u‖ ^ 2 < (r * ‖u‖) ^ 2 := by
      rw [mul_pow]
      nlinarith [pow_pos hun 2]
    linarith
  · obtain ⟨a, b, hab, hsmall⟩ := ehgmSymbol_small (1 / 2) (by norm_num)
    obtain ⟨v, hv0, -, hup⟩ := key a b (1 / 2) hab (by norm_num)
    have h := hup hsmall
    refine ⟨v, ?_⟩
    rw [re_inner_ehgmAnomaly]
    have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have h2 : ‖ehgmTransport v‖ ^ 2 ≤ (1 / 2 * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith

end GaloisForLFunctions.HTGeometry
