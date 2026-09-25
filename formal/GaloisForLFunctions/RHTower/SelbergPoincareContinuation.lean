import GaloisForLFunctions.RHTower.SelbergKloostermanCongruence
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

open Complex MeasureTheory Topology Metric
open scoped FourierTransform

/-!
# Holomorphic continuation of the `Γ(N)` Poincaré series to `Re s > 3/4`

On a ball in `s` with `σ₁ ≤ Re s ≤ σ₂`, `|s| ≤ R`, the kernel Fourier coefficients satisfy
`|𝓕ker(n)| ≤ 2 (y^{1-σ₂} + y^{1-σ₁}) C_{σ₁} (1 + D)/(1 + n²)` (`norm_fourier_ker_le_uniform`) and depend
holomorphically on `s` (`differentiableAt_fourier_ker`). With Weil's bound for `S_N` (`norm_ksum_le`) and the
summability of `|c|^{-2σ} kmaxU(±m; |c|N)` for `σ > 3/4` (`summable_cw`), the Fourier–Kloosterman form `Q_m(z,s)`
is holomorphic on `Re s > 3/4` (`differentiableAt_Q`) and obeys `|Q_m(z,s)| ≤ C (y^{-6} + y^3)` locally uniformly
in `s` for `Re s ≤ 3` (`norm_Q_le_poly`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincareContinuation
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.KloostermanUniform GaloisForLFunctions.RHTower.SelbergKloostermanCongruence

/-- A power between two exponents is bounded by the sum of the extreme powers. -/
theorem rpow_le_add {y a lo hi : ℝ} (hy : 0 < y) (h1 : lo ≤ a) (h2 : a ≤ hi) : y ^ a ≤ y ^ lo + y ^ hi := by
  rcases le_or_gt 1 y with hy1 | hy1
  · exact (Real.rpow_le_rpow_of_exponent_le hy1 h2).trans (le_add_of_nonneg_left (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy hy1.le h1).trans (le_add_of_nonneg_right (by positivity))

theorem cst_anti {σ₁ σ : ℝ} (h : 1 / 2 < σ₁) (h' : σ₁ ≤ σ) : cst σ ≤ cst σ₁ := by
  unfold cst
  apply integral_mono (integrable_one_add_sq (by linarith)) (integrable_one_add_sq h)
  intro t
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg t]) (by linarith)

/-- The uniform second-derivative constant. -/
noncomputable def dmax (β y R : ℝ) : ℝ := (R / y + 2 * Real.pi * β / y ^ 2) ^ 2 + (2 * R / y ^ 2 + 4 * Real.pi * β / y ^ 3)

theorem dconst_le {β y R : ℝ} {β₀ : ℝ} {s : ℂ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hy : 0 < y) (hs : ‖s‖ ≤ R) :
    dconst β y s ≤ dmax β₀ y R := by
  unfold dconst dmax
  have h1 : ‖s‖ / y + 2 * Real.pi * β / y ^ 2 ≤ R / y + 2 * Real.pi * β₀ / y ^ 2 := by gcongr
  have h0 : 0 ≤ ‖s‖ / y + 2 * Real.pi * β / y ^ 2 := by positivity
  gcongr

/-- **Uniform Fourier bound**: `|𝓕ker(n)| ≤ 2 (y^{1-σ₂} + y^{1-σ₁}) C_{σ₁} (1 + D)/(1 + n²)`. -/
theorem norm_fourier_ker_le_uniform {β β₀ y R σ₁ σ₂ : ℝ} {s : ℂ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hy : 0 < y)
    (hσ₁ : 1 / 2 < σ₁) (h1 : σ₁ ≤ s.re) (h2 : s.re ≤ σ₂) (hs : ‖s‖ ≤ R) (n : ℤ) :
    ‖𝓕 (ker β y s) n‖ ≤ 2 * ((y ^ (1 - σ₂) + y ^ (1 - σ₁)) * cst σ₁) * (1 + dmax β₀ y R) / (1 + (n : ℝ) ^ 2) := by
  have hs' : 1 / 2 < s.re := by linarith
  set X := (y ^ (1 - σ₂) + y ^ (1 - σ₁)) * cst σ₁
  have hc0 : 0 ≤ cst σ₁ := cst_nonneg _
  have hX : y ^ (1 - s.re) * cst s.re ≤ X :=
    mul_le_mul (rpow_le_add hy (by linarith) (by linarith)) (cst_anti hσ₁ h1) (cst_nonneg _) (by positivity)
  have hX0 : 0 ≤ X := by positivity
  have hD : dconst β y s ≤ dmax β₀ y R := dconst_le hβ hβ₀ hy hs
  have hD0 : 0 ≤ dconst β y s := by unfold dconst; positivity
  have hDm : 0 ≤ dmax β₀ y R := hD0.trans hD
  have hn2 : 0 < 1 + (n : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hn2]
  by_cases hn : n = 0
  · subst hn
    have := (norm_fourier_ker_le hβ hy hs' 0).trans hX
    simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_one]
    nlinarith
  · have hsq := norm_fourier_ker_le_sq hβ hy hs' n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
      exact_mod_cast this
    have hpi : (4 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    have hF := norm_nonneg (𝓕 (ker β y s) n)
    have hsq' : (2 * Real.pi * |(n : ℝ)|) ^ 2 = (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by rw [mul_pow, sq_abs]
    rw [hsq'] at hsq
    have h3 : (n : ℝ) ^ 2 * ‖𝓕 (ker β y s) n‖ ≤ dmax β₀ y R * X := by
      have : 4 * ((n : ℝ) ^ 2 * ‖𝓕 (ker β y s) n‖) ≤ dmax β₀ y R * X := by
        calc 4 * ((n : ℝ) ^ 2 * ‖𝓕 (ker β y s) n‖) ≤ (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 * ‖𝓕 (ker β y s) n‖ := by
              nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hF]
          _ ≤ dconst β y s * (y ^ (1 - s.re) * cst s.re) := hsq
          _ ≤ dmax β₀ y R * X := mul_le_mul hD hX (mul_nonneg (by positivity) (cst_nonneg _)) hDm
      nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hF]
    have h4 : ‖𝓕 (ker β y s) n‖ ≤ X := (norm_fourier_ker_le hβ hy hs' n).trans hX
    nlinarith [mul_nonneg hDm hX0]

theorem differentiable_ker (β y x : ℝ) : Differentiable ℂ (fun s : ℂ => ker β y s x) := by
  unfold ker
  exact ((differentiable_id.mul_const _).sub_const _).cexp

theorem re_mem_of_mem_ball {s₀ s : ℂ} {r : ℝ} (hs : s ∈ ball s₀ r) : s₀.re - r < s.re ∧ s.re < s₀.re + r := by
  have h := (Complex.abs_re_le_norm (s - s₀)).trans_lt (mem_ball_iff_norm.mp hs)
  rw [Complex.sub_re, abs_lt] at h
  constructor <;> linarith [h.1, h.2]

/-- `s ↦ 𝓕 ker_s(ξ)` is holomorphic on `Re s > 1/2`. -/
theorem differentiableAt_fourier_ker {β y : ℝ} (hβ : 0 ≤ β) (hy : 0 < y) {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) (ξ : ℝ) :
    DifferentiableAt ℂ (fun s => 𝓕 (ker β y s) ξ) s₀ := by
  set r := (s₀.re - 1 / 2) / 2
  have hr : 0 < r := by simp only [r]; linarith
  simp_rw [Real.fourier_real_eq, Circle.smul_def, smul_eq_mul]
  apply GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated hr
    (bound := fun x => wt y x ^ (s₀.re - r) + wt y x ^ (s₀.re + r))
  · intro s _
    have hk := continuous_ker (β := β) (s := s) hy
    have he : Continuous (fun x : ℝ => ((𝐞 (-(x * ξ)) : Circle) : ℂ)) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
    exact (he.mul hk).aestronglyMeasurable
  · intro x
    exact ((differentiable_ker β y x).const_mul _).differentiableOn
  · intro x s hs
    obtain ⟨h1, h2⟩ := re_mem_of_mem_ball hs
    rw [norm_mul, Circle.norm_coe, one_mul]
    exact (norm_ker_le hβ hy s x).trans (rpow_le_add (wt_pos hy x) h1.le h2.le)
  · exact (integrable_wt_rpow hy (by simp only [r]; linarith)).add (integrable_wt_rpow hy (by simp only [r]; linarith))

/-- The `c`-weights `|c|^{-2σ} kmaxU(sgn(c) m; |c|N)`. -/
noncomputable def cw (N m : ℕ) (σ : ℝ) (c : ℤ) : ℝ :=
  if c = 0 then 0 else ((c : ℝ) ^ 2) ^ (-σ) * kmaxU (c.sign * m) (c.natAbs * N)

theorem cw_nonneg (N m : ℕ) (σ : ℝ) (c : ℤ) : 0 ≤ cw N m σ c := by
  unfold cw; split_ifs
  · exact le_rfl
  · exact mul_nonneg (by positivity) (kmaxU_nonneg _ _)

theorem cw_nat (N : ℕ) (hN : 0 < N) (σ : ℝ) (k : ℕ) (n : ℤ) (hk : 0 < k) :
    ((k : ℝ) ^ 2) ^ (-σ) * kmaxU n (k * N) = (N : ℝ) ^ (2 * σ) * gw (kmaxU n) σ (k * N) := by
  unfold gw
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast
  rw [Real.mul_rpow hk'.le hN'.le, ← Real.rpow_natCast, ← Real.rpow_mul hk'.le]
  have : (N : ℝ) ^ (2 * σ) * (N : ℝ) ^ (-2 * σ) = 1 := by
    rw [← Real.rpow_add hN']; simp
  calc (k : ℝ) ^ ((2 : ℕ) * -σ) * kmaxU n (k * N) =
      ((N : ℝ) ^ (2 * σ) * (N : ℝ) ^ (-2 * σ)) * ((k : ℝ) ^ ((2 : ℕ) * -σ) * kmaxU n (k * N)) := by
        rw [this, one_mul]
    _ = _ := by push_cast; ring_nf

/-- **Summability of the `c`-weights** for `m ≠ 0`, `σ > 3/4`. -/
theorem summable_cw (N m : ℕ) (hN : 0 < N) (hm : m ≠ 0) {σ : ℝ} (hσ : 3 / 4 < σ) : Summable (cw N m σ) := by
  have hinj : Function.Injective (fun k : ℕ => k * N) := fun a b h => Nat.eq_of_mul_eq_mul_right hN h
  have hsum : ∀ n : ℤ, n ≠ 0 → Summable (fun k : ℕ => (N : ℝ) ^ (2 * σ) * gw (kmaxU n) σ (k * N)) :=
    fun n hn => ((kmaxU_summable hn hσ).comp_injective hinj).mul_left _
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine Summable.of_nonneg_of_le (fun k => cw_nonneg N m σ _) (fun k => ?_) (hsum m hm')
    unfold cw
    split_ifs with hk
    · exact mul_nonneg (by positivity) (gw_nonneg (kmaxU_nonneg _) _)
    · have hk' : 0 < k := by omega
      rw [Int.sign_natCast_of_ne_zero (by omega), one_mul, Int.natAbs_natCast, Int.cast_natCast]
      exact le_of_eq (cw_nat N hN σ k m hk')
  · refine Summable.of_nonneg_of_le (fun k => cw_nonneg N m σ _) (fun k => ?_) (hsum (-m) (neg_ne_zero.mpr hm'))
    unfold cw
    split_ifs with hk
    · exact mul_nonneg (by positivity) (gw_nonneg (kmaxU_nonneg _) _)
    · have hk' : 0 < k := by omega
      rw [Int.sign_neg, Int.sign_natCast_of_ne_zero (by omega), Int.natAbs_neg, Int.natAbs_natCast,
        Int.cast_neg, Int.cast_natCast, neg_sq, neg_one_mul]
      exact le_of_eq (cw_nat N hN σ k (-m) hk')

theorem summable_inv_one_add_sq : Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left 2 |>.add
      (summable_of_ne_finset_zero (s := {0}) (f := fun n : ℤ => if n = 0 then (1 : ℝ) else 0)
        (fun n hn => by simp at hn; simp [hn])))
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, if_false, add_zero]
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
      exact_mod_cast this
    have hp : (0 : ℝ) < (n : ℝ) ^ 2 := by linarith
    calc 1 / (1 + (n : ℝ) ^ 2) ≤ 1 / (n : ℝ) ^ 2 := one_div_le_one_div_of_le hp (by linarith)
      _ ≤ 2 * (1 / (n : ℝ) ^ 2) := by have : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
                                      linarith

theorem norm_exp_neg_mul_log {s : ℂ} {a σ : ℝ} (ha : 1 ≤ a) (hσ : σ ≤ s.re) :
    ‖cexp (-s * (Real.log a : ℂ))‖ ≤ a ^ (-σ) := by
  rw [Complex.norm_exp, Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  have hl := Real.log_nonneg ha
  have : (-s * (Real.log a : ℂ)).re = -s.re * Real.log a := by simp [Complex.mul_re]
  rw [this]; nlinarith

theorem norm_cexp_two_pi_I_div (n : ℤ) (x : ℝ) (N : ℕ) : ‖cexp (2 * Real.pi * Complex.I * n * x / N)‖ = 1 := by
  rw [show 2 * Real.pi * Complex.I * n * x / N = ((2 * Real.pi * n * x / N : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The `n`-independent part of the Fourier bound at height `y/N`. -/
noncomputable def bndX (N m : ℕ) (y σ₁ σ₂ R : ℝ) : ℝ :=
  2 * (((y / N) ^ (1 - σ₂) + (y / N) ^ (1 - σ₁)) * cst σ₁) * (1 + dmax ((m : ℝ) / (N : ℝ) ^ 2) (y / N) R)

theorem bndX_nonneg (N m : ℕ) {y : ℝ} (hy : 0 < y) (σ₁ σ₂ R : ℝ) (hR : 0 ≤ R) : 0 ≤ bndX N m y σ₁ σ₂ R := by
  unfold bndX dmax
  have := cst_nonneg σ₁
  by_cases hN : (N : ℝ) = 0
  · simp [hN]; positivity
  have hN' : 0 < (N : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg N) (Ne.symm hN)
  have : 0 < y / N := div_pos hy hN'
  positivity

variable (N m : ℕ) [NeZero N] (z : UpperHalfPlane)

theorem norm_Qc_term_le {c : ℤ} (hc : c ≠ 0) {s : ℂ} {σ₁ σ₂ R : ℝ} (hσ₁ : 1 / 2 < σ₁) (h1 : σ₁ ≤ s.re)
    (h2 : s.re ≤ σ₂) (hs : ‖s‖ ≤ R) (n : ℤ) :
    ‖𝓕 (ker (m / ((c : ℝ) ^ 2 * N) / N) (z.im / N) s) n * cexp (2 * Real.pi * Complex.I * n * z.re / N) *
        ksum N m c n‖ ≤ bndX N m z.im σ₁ σ₂ R / (1 + (n : ℝ) ^ 2) * kmaxU (c.sign * m) (c.natAbs * N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hc2 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ c ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs c]
    exact_mod_cast this
  have hβ : 0 ≤ (m : ℝ) / ((c : ℝ) ^ 2 * N) / N := by positivity
  have hβ₀ : (m : ℝ) / ((c : ℝ) ^ 2 * N) / N ≤ (m : ℝ) / (N : ℝ) ^ 2 := by
    rw [div_div, show (N : ℝ) ^ 2 = 1 * N * N by ring]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have := mul_pos hN hN
    nlinarith
  rw [norm_mul, norm_mul, norm_cexp_two_pi_I_div, mul_one]
  apply mul_le_mul _ (norm_ksum_le N m hc n) (norm_nonneg _) (by
    unfold bndX; have := bndX_nonneg N m z.im_pos σ₁ σ₂ R ((norm_nonneg s).trans hs); unfold bndX at this
    positivity)
  have := norm_fourier_ker_le_uniform hβ hβ₀ (div_pos z.im_pos hN) hσ₁ h1 h2 hs n
  simpa only [bndX] using this

/-- `Z = Σ_n 1/(1+n²)`. -/
noncomputable def zsum : ℝ := ∑' n : ℤ, 1 / (1 + (n : ℝ) ^ 2)

theorem norm_Qc_le (c : ℤ) {s : ℂ} {σ₁ σ₂ R : ℝ} (hσ₁ : 1 / 2 < σ₁) (h1 : σ₁ ≤ s.re)
    (h2 : s.re ≤ σ₂) (hs : ‖s‖ ≤ R) :
    ‖Qc N m s z c‖ ≤ cw N m σ₁ c * (bndX N m z.im σ₁ σ₂ R * zsum) := by
  unfold Qc
  by_cases hc : c = 0
  · simp [hc, cw]
  rw [if_neg hc]
  unfold cw; rw [if_neg hc]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hc2 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ c ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs c]
    exact_mod_cast this
  have hE := norm_exp_neg_mul_log (s := s) hc2 h1
  have hEN := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 (by linarith)
  rw [neg_zero, Real.rpow_zero] at hEN
  set K := kmaxU (c.sign * m) (c.natAbs * N)
  have hK : 0 ≤ K := kmaxU_nonneg _ _
  have hX : 0 ≤ bndX N m z.im σ₁ σ₂ R := bndX_nonneg N m z.im_pos σ₁ σ₂ R ((norm_nonneg s).trans hs)
  have hbsum : Summable (fun n : ℤ => bndX N m z.im σ₁ σ₂ R / (1 + (n : ℝ) ^ 2) * K) := by
    have := (summable_inv_one_add_sq.mul_left (bndX N m z.im σ₁ σ₂ R)).mul_right K
    refine this.congr (fun n => ?_); ring
  have hterm := norm_Qc_term_le N m z hc hσ₁ h1 h2 hs
  have hT : ‖∑' n : ℤ, 𝓕 (ker (m / ((c : ℝ) ^ 2 * N) / N) (z.im / N) s) n *
      cexp (2 * Real.pi * Complex.I * n * z.re / N) * ksum N m c n‖ ≤ K * (bndX N m z.im σ₁ σ₂ R * zsum) := by
    refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hbsum)).trans ?_
    refine (Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hbsum) hbsum).trans
      (le_of_eq ?_)
    rw [zsum, ← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr; intro n; ring
  rw [norm_mul, norm_mul]
  have hc0 : 0 ≤ ((c : ℝ) ^ 2) ^ (-σ₁) := by positivity
  calc ‖cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ))‖ * ‖cexp (-s * (Real.log N : ℂ))‖ * _ ≤
      ((c : ℝ) ^ 2) ^ (-σ₁) * 1 * (K * (bndX N m z.im σ₁ σ₂ R * zsum)) :=
        mul_le_mul (mul_le_mul hE hEN (norm_nonneg _) hc0) hT (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem ball_props {s₀ s : ℂ} {r : ℝ} (hs : s ∈ ball s₀ r) :
    s₀.re - r ≤ s.re ∧ s.re ≤ s₀.re + r ∧ ‖s‖ ≤ ‖s₀‖ + r := by
  obtain ⟨h1, h2⟩ := re_mem_of_mem_ball hs
  refine ⟨h1.le, h2.le, ?_⟩
  have := mem_ball_iff_norm.mp hs
  calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by ring_nf
    _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
    _ ≤ ‖s₀‖ + r := by linarith

theorem differentiable_exp_neg_mul (L : ℝ) : Differentiable ℂ (fun s : ℂ => cexp (-s * (L : ℂ))) :=
  (differentiable_id.neg.mul_const _).cexp

theorem differentiableOn_Qc (c : ℤ) {s₀ : ℂ} {r σ₁ σ₂ R : ℝ} (hσ₁ : 1 / 2 < σ₁)
    (hb : ∀ s ∈ ball s₀ r, σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ ‖s‖ ≤ R) :
    DifferentiableOn ℂ (fun s => Qc N m s z c) (ball s₀ r) := by
  intro s₁ hs₁
  apply DifferentiableAt.differentiableWithinAt
  by_cases hc : c = 0
  · simp only [Qc, if_pos hc]; exact differentiableAt_const _
  simp only [Qc, if_neg hc]
  refine (((differentiable_exp_neg_mul _).differentiableAt).mul
    ((differentiable_exp_neg_mul _).differentiableAt)).mul ?_
  set ρ := r - dist s₁ s₀
  have hρ : 0 < ρ := by simp only [ρ]; linarith [mem_ball.mp hs₁]
  have hsub : ball s₁ ρ ⊆ ball s₀ r := ball_subset_ball' (by simp only [ρ]; linarith)
  set K := kmaxU (c.sign * m) (c.natAbs * N)
  apply GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated hρ
    (bound := fun n : ℤ => bndX N m z.im σ₁ σ₂ R / (1 + (n : ℝ) ^ 2) * K)
  · intro n s hs
    obtain ⟨h1, _, _⟩ := hb s (hsub hs)
    apply DifferentiableAt.differentiableWithinAt
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact ((differentiableAt_fourier_ker (by positivity) (div_pos z.im_pos hN) (by linarith) n).mul_const _).mul_const _
  · intro n s hs
    obtain ⟨h1, h2, h3⟩ := hb s (hsub hs)
    exact norm_Qc_term_le N m z hc hσ₁ h1 h2 h3 n
  · have := (summable_inv_one_add_sq.mul_left (bndX N m z.im σ₁ σ₂ R)).mul_right K
    refine this.congr (fun n => ?_); ring

/-- **Holomorphy of the continued Poincaré series** on `Re s > 3/4` (`m ≠ 0`). -/
theorem differentiableAt_Q (hm : m ≠ 0) {s₀ : ℂ} (h : 3 / 4 < s₀.re) :
    DifferentiableAt ℂ (fun s => Q N m s z) s₀ := by
  set r := (s₀.re - 3 / 4) / 2
  have hr : 0 < r := by simp only [r]; linarith
  set σ₁ := s₀.re - r
  set σ₂ := s₀.re + r
  set R := ‖s₀‖ + r
  have hσ₁ : 3 / 4 < σ₁ := by simp only [σ₁, r]; linarith
  have hb : ∀ s ∈ ball s₀ r, σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ ‖s‖ ≤ R := fun s hs => ball_props hs
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  unfold Q
  apply DifferentiableAt.add
  · apply DifferentiableAt.mul_const
    exact differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast z.im_pos.ne'))
  · apply GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated hr
      (bound := fun c => cw N m σ₁ c * (bndX N m z.im σ₁ σ₂ R * zsum))
    · intro c; exact differentiableOn_Qc N m z c (by linarith) hb
    · intro c s hs
      obtain ⟨h1, h2, h3⟩ := hb s hs
      exact norm_Qc_le N m z c (by linarith) h1 h2 h3
    · exact (summable_cw N m hN hm hσ₁).mul_right _

/-! ### A polynomial bound in the height -/

theorem pow_le_one_add {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : k ≤ 4) : u ^ k ≤ 1 + u ^ 4 := by
  rcases le_or_gt u 1 with h | h
  · have : u ^ k ≤ 1 := pow_le_one₀ hu h
    linarith [pow_nonneg hu 4]
  · have : u ^ k ≤ u ^ 4 := pow_le_pow_right₀ h.le hk
    linarith

/-- The constant bounding `1 + dmax`. -/
noncomputable def bconst (β₀ R : ℝ) : ℝ := 1 + 2 * R ^ 2 + 2 * (2 * Real.pi * β₀) ^ 2 + 2 * R + 4 * Real.pi * β₀

theorem one_add_dmax_le {β₀ y R : ℝ} (hβ₀ : 0 ≤ β₀) (hy : 0 < y) (hR : 0 ≤ R) :
    1 + dmax β₀ y R ≤ bconst β₀ R * (1 + (y⁻¹) ^ 4) := by
  unfold dmax bconst
  set u := y⁻¹
  have hu : 0 ≤ u := by positivity
  have e1 : R / y = R * u := by simp [u, div_eq_mul_inv]
  have e2 : ∀ k : ℕ, ∀ a : ℝ, a / y ^ k = a * u ^ k := fun k a => by simp [u, div_eq_mul_inv, inv_pow]
  rw [e1, e2 2, e2 2, e2 3]
  have h2 := pow_le_one_add hu (k := 2) (by norm_num)
  have h3 := pow_le_one_add hu (k := 3) (by norm_num)
  have hsq : (R * u + 2 * Real.pi * β₀ * u ^ 2) ^ 2 ≤ 2 * R ^ 2 * u ^ 2 + 2 * (2 * Real.pi * β₀) ^ 2 * u ^ 4 := by
    nlinarith [sq_nonneg (R * u - 2 * Real.pi * β₀ * u ^ 2)]
  have hc : 0 ≤ 2 * Real.pi * β₀ := by positivity
  have hu4 : 0 ≤ u ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * R ^ 2),
    mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * R),
    mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * β₀)]

theorem rpow_mul_one_add_le {y σ : ℝ} (hy : 0 < y) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3) :
    y ^ (1 - σ) * (1 + (y⁻¹) ^ 4) ≤ 2 * (y ^ (-6 : ℝ) + y ^ (3 : ℝ)) := by
  have hinv : (y⁻¹) ^ 4 = y ^ (-4 : ℝ) := by
    rw [Real.rpow_neg hy.le, inv_pow]; norm_cast
  rw [hinv, mul_add, mul_one, ← Real.rpow_add hy]
  have a := rpow_le_add hy (show (-6 : ℝ) ≤ 1 - σ by linarith) (show 1 - σ ≤ 3 by linarith)
  have b := rpow_le_add hy (show (-6 : ℝ) ≤ 1 - σ + -4 by linarith) (show 1 - σ + -4 ≤ 3 by linarith)
  linarith

theorem scaled_le {y : ℝ} (hy : 0 < y) {N : ℝ} (hN : 1 ≤ N) :
    (y / N) ^ (-6 : ℝ) + (y / N) ^ (3 : ℝ) ≤ N ^ (6 : ℝ) * (y ^ (-6 : ℝ) + y ^ (3 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  rw [Real.div_rpow hy.le hN0.le, Real.div_rpow hy.le hN0.le]
  have e : N ^ (-6 : ℝ) = (N ^ (6 : ℝ))⁻¹ := Real.rpow_neg hN0.le 6
  rw [e, div_inv_eq_mul]
  have h6 : 1 ≤ N ^ (6 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have h3 : 1 ≤ N ^ (3 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hy3 : 0 ≤ y ^ (3 : ℝ) := by positivity
  have : y ^ (3 : ℝ) / N ^ (3 : ℝ) ≤ y ^ (3 : ℝ) := div_le_self hy3 h3
  have hy6 : 0 ≤ y ^ (-6 : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h6 hy3]

theorem bndX_le_poly {y σ₁ σ₂ R : ℝ} (hy : 0 < y) (h1 : 1 / 2 ≤ σ₁) (h12 : σ₁ ≤ σ₂) (h2 : σ₂ ≤ 3) (hR : 0 ≤ R) :
    bndX N m y σ₁ σ₂ R ≤ 8 * cst σ₁ * bconst ((m : ℝ) / (N : ℝ) ^ 2) R * (N : ℝ) ^ (6 : ℝ) *
      (y ^ (-6 : ℝ) + y ^ (3 : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hy' : 0 < y / N := div_pos hy (by linarith)
  have hβ₀ : 0 ≤ (m : ℝ) / (N : ℝ) ^ 2 := by positivity
  have hD := one_add_dmax_le hβ₀ hy' hR
  have hc := cst_nonneg σ₁
  set B := bconst ((m : ℝ) / (N : ℝ) ^ 2) R
  have hB : 0 ≤ B := by simp only [B, bconst]; positivity
  have a1 := rpow_mul_one_add_le hy' (by linarith) h2 (σ := σ₂)
  have a2 := rpow_mul_one_add_le hy' h1 (by linarith) (σ := σ₁)
  have hsc := scaled_le hy hN1
  set u := (y / N)⁻¹
  unfold bndX
  have hp : 0 ≤ (y / N) ^ (1 - σ₂) + (y / N) ^ (1 - σ₁) := by positivity
  calc 2 * (((y / N) ^ (1 - σ₂) + (y / N) ^ (1 - σ₁)) * cst σ₁) * (1 + dmax ((m : ℝ) / (N : ℝ) ^ 2) (y / N) R)
      ≤ 2 * (((y / N) ^ (1 - σ₂) + (y / N) ^ (1 - σ₁)) * cst σ₁) * (B * (1 + u ^ 4)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = 2 * cst σ₁ * B * ((y / N) ^ (1 - σ₂) * (1 + u ^ 4) + (y / N) ^ (1 - σ₁) * (1 + u ^ 4)) := by ring
    _ ≤ 2 * cst σ₁ * B * (2 * ((y / N) ^ (-6 : ℝ) + (y / N) ^ (3 : ℝ)) +
          2 * ((y / N) ^ (-6 : ℝ) + (y / N) ^ (3 : ℝ))) := by gcongr
    _ = 8 * cst σ₁ * B * ((y / N) ^ (-6 : ℝ) + (y / N) ^ (3 : ℝ)) := by ring
    _ ≤ 8 * cst σ₁ * B * ((N : ℝ) ^ (6 : ℝ) * (y ^ (-6 : ℝ) + y ^ (3 : ℝ))) := by gcongr
    _ = _ := by ring

omit [NeZero N] in
theorem norm_main_le (s : ℂ) : ‖(z.im : ℂ) ^ s * cexp (2 * Real.pi * Complex.I * m * (z : ℂ) / N)‖ ≤ z.im ^ s.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]
  have : ‖cexp (2 * Real.pi * Complex.I * m * (z : ℂ) / N)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    have h : (2 * Real.pi * Complex.I * m * (z : ℂ) / N).re = -(2 * Real.pi * m * z.im / N) := by
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
      field_simp
    rw [h]
    have : 0 ≤ 2 * Real.pi * m * z.im / N := by have := z.im_pos; positivity
    linarith
  calc z.im ^ s.re * ‖cexp (2 * Real.pi * Complex.I * m * (z : ℂ) / N)‖ ≤ z.im ^ s.re * 1 :=
        mul_le_mul_of_nonneg_left this (by have := z.im_pos; positivity)
    _ = _ := mul_one _

/-- The constant of the polynomial bound. -/
noncomputable def qconst (N m : ℕ) (σ₁ R : ℝ) : ℝ :=
  1 + (∑' c, cw N m σ₁ c) * zsum * (8 * cst σ₁ * bconst ((m : ℝ) / (N : ℝ) ^ 2) R * (N : ℝ) ^ (6 : ℝ))

/-- **Polynomial bound**: for `3/4 < σ₁ ≤ Re s ≤ σ₂ ≤ 3`, `‖s‖ ≤ R`: `|Q(z,s)| ≤ C (y^{-6} + y^3)`. -/
theorem norm_Q_le_poly (hm : m ≠ 0) {s : ℂ} {σ₁ σ₂ R : ℝ} (hσ₁ : 3 / 4 < σ₁) (hσ₂ : σ₂ ≤ 3) (h1 : σ₁ ≤ s.re)
    (h2 : s.re ≤ σ₂) (hs : ‖s‖ ≤ R) :
    ‖Q N m s z‖ ≤ qconst N m σ₁ R * (z.im ^ (-6 : ℝ) + z.im ^ (3 : ℝ)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hR : 0 ≤ R := (norm_nonneg s).trans hs
  have hy := z.im_pos
  set P := z.im ^ (-6 : ℝ) + z.im ^ (3 : ℝ)
  have hP : 0 ≤ P := by positivity
  have hcw := summable_cw N m hN hm hσ₁
  have hbound : ∀ c, ‖Qc N m s z c‖ ≤ cw N m σ₁ c * (bndX N m z.im σ₁ σ₂ R * zsum) :=
    fun c => norm_Qc_le N m z c (by linarith) h1 h2 hs
  have hsumQ : Summable (fun c => ‖Qc N m s z c‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hcw.mul_right _)
  have hT : ‖∑' c, Qc N m s z c‖ ≤ (∑' c, cw N m σ₁ c) * (bndX N m z.im σ₁ σ₂ R * zsum) := by
    refine (norm_tsum_le_tsum_norm hsumQ).trans ?_
    rw [← tsum_mul_right]
    exact Summable.tsum_le_tsum hbound hsumQ (hcw.mul_right _)
  have hmain := (norm_main_le N m z s).trans (rpow_le_add hy (show (-6 : ℝ) ≤ s.re by linarith)
    (show s.re ≤ 3 by linarith))
  have hX := bndX_le_poly N m hy (by linarith) (h1.trans h2) hσ₂ hR
  have hZ : 0 ≤ zsum := tsum_nonneg (fun n => by positivity)
  have hC : 0 ≤ ∑' c, cw N m σ₁ c := tsum_nonneg (cw_nonneg N m σ₁)
  unfold Q qconst
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ P + (∑' c, cw N m σ₁ c) * (bndX N m z.im σ₁ σ₂ R * zsum) := add_le_add hmain hT
    _ ≤ P + (∑' c, cw N m σ₁ c) * ((8 * cst σ₁ * bconst ((m : ℝ) / (N : ℝ) ^ 2) R * (N : ℝ) ^ (6 : ℝ) * P) * zsum) := by
        gcongr
    _ = _ := by ring

end GaloisForLFunctions.RHTower.SelbergPoincareContinuation
