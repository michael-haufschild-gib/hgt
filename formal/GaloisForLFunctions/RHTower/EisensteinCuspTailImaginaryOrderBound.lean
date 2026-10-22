import GaloisForLFunctions.RHTower.BesselKImaginaryOrderUniformBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment

/-!
# The nonconstant part of the completed Eisenstein series on the critical line

On the line `Re s = 1/2` the centred parameter is `u = it`, the Whittaker coefficient
`n^{u} Σ_{d ∣ n} d^{−2u}` has modulus at most the number of divisors `d(n)`, and the Fourier phases are
unimodular, so the signed square-root Whittaker tail at height `Y ∈ [1/2, 1]` is bounded by

`√Y · Σ_{n ≥ 1} d(n) · ‖K_{2πnY}(it)‖`.

For `n ≤ ⌈t⌉` the uniform bound `‖K_x(it)‖ ≤ e(log(πt)+1)e^{−πt/2}` applies and the divisor sum is
`≤ ⌈t⌉(1 + log ⌈t⌉)`; for `n > ⌈t⌉` the trivial bound `‖K_x(it)‖ ≤ e·e^{−x}` with `x ≥ πn` gives a
geometric tail.  Altogether the nonconstant part of `E*(·, 1/2 + it)` on the compact part of the
fundamental domain is `O((t+1)(1 + log(t+1))(1 + log(πt))·e^{−πt/2})`, the same exponential scale as
its constant term `ξ(1+2it) y^{1/2+it} + ξ(2it) y^{1/2−it}` but two powers of `t` smaller.
-/

open Complex MeasureTheory Set Finset

namespace RHTower

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

noncomputable section

/-- Trivial bound for the modified Bessel function of imaginary order at argument `x ≥ 1`:
`‖K_x(iτ)‖ ≤ e·e^{−x}`, from `x cosh u ≥ x + u − 1`. -/
theorem norm_modifiedBesselKOrder_I_mul_le_exp {x : ℝ} (hx : 1 ≤ x) (τ : ℝ) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤ Real.exp 1 * Real.exp (-x) := by
  have hx0 : 0 < x := by linarith
  unfold modifiedBesselKOrder
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      ‖besselOrderKernel x ((τ : ℂ) * I) u‖ ≤ Real.exp (1 - x) * Real.exp (-u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    unfold besselOrderKernel
    rw [norm_mul, Complex.norm_exp]
    have hcosh : Complex.cosh ((τ : ℂ) * I * (u : ℂ)) = Complex.cos ((τ * u : ℝ) : ℂ) := by
      rw [show (τ : ℂ) * I * (u : ℂ) = ((τ * u : ℝ) : ℂ) * I by push_cast; ring, Complex.cosh_mul_I]
    rw [hcosh, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-(x : ℂ) * Complex.cosh (u : ℂ)).re = -x * Real.cosh u := by
      simp [Complex.cosh_ofReal_re]
    rw [hre]
    have hcos := Real.abs_cos_le_one (τ * u)
    have hexp : Real.exp (-x * Real.cosh u) ≤ Real.exp (1 - x) * Real.exp (-u) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : 1 + u ^ 2 / 4 ≤ Real.cosh u := by
        rw [Real.cosh_eq]
        have h2 := Real.quadratic_le_exp_of_nonneg hu0.le
        have h3 := Real.add_one_le_exp (-u)
        linarith
      nlinarith [sq_nonneg (u - 2)]
    calc Real.exp (-x * Real.cosh u) * |Real.cos (τ * u)|
        ≤ Real.exp (-x * Real.cosh u) * 1 :=
          mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
      _ ≤ Real.exp (1 - x) * Real.exp (-u) := by rw [mul_one]; exact hexp
  calc (∫ u in Ioi (0 : ℝ), ‖besselOrderKernel x ((τ : ℂ) * I) u‖)
      ≤ ∫ u in Ioi (0 : ℝ), Real.exp (1 - x) * Real.exp (-u) :=
        setIntegral_mono_on (integrableOn_besselOrderKernel hx0 _).norm
          ((integrableOn_exp_neg_Ioi 0).const_mul _) measurableSet_Ioi hpt
    _ = Real.exp (1 - x) * Real.exp (-0) := by rw [integral_const_mul, integral_exp_neg_Ioi]
    _ = Real.exp 1 * Real.exp (-x) := by
        rw [neg_zero, Real.exp_zero, mul_one, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]

/-- On the line the Whittaker coefficient has modulus at most the number of divisors. -/
theorem norm_whittakerCoefficient_I_mul_le (τ : ℝ) (n : D4BMPositiveIndex) :
    ‖d4BMCompletedEisensteinWhittakerCoefficient ((τ : ℂ) * I) n‖ ≤ (n.1.divisors.card : ℝ) := by
  unfold d4BMCompletedEisensteinWhittakerCoefficient
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos n.2]
  have hre : ((τ : ℂ) * I).re = 0 := by simp
  rw [hre, Real.rpow_zero, one_mul]
  refine (norm_sum_le _ _).trans ?_
  have hone : ∀ d ∈ n.1.divisors, ‖(d : ℂ) ^ (-2 * ((τ : ℂ) * I))‖ = 1 := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [Complex.norm_natCast_cpow_of_pos hd0]
    simp
  rw [Finset.sum_congr rfl hone]
  simp

/-- The `N`-th term of the zero-jet signed square-root Whittaker tail on the line. -/
def eisensteinLineTailTerm (t : ℝ) (negative : Bool) (x Y : ℝ) (N : ℕ) : ℂ :=
  (d4BMCompletedEisensteinWhittakerCoefficient ((t : ℂ) * I) ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ (0 : ℕ) * d4BMCompletedEisensteinFourierPhase negative N x) *
    (Real.sqrt Y : ℂ) * (Y : ℂ) ^ (0 : ℕ) *
    modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)

theorem signedSqrtWhittakerTail_eq_tsum (t : ℝ) (negative : Bool) (x Y : ℝ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail ((t : ℂ) * I) ((t : ℂ) * I) negative x 0 0 Y =
      ∑' N : ℕ, eisensteinLineTailTerm t negative x Y N := rfl

/-- Termwise majorant: `d(N+1)·√Y·‖K_{2π(N+1)Y}(it)‖`. -/
theorem norm_eisensteinLineTailTerm_le (t : ℝ) (negative : Bool) (x : ℝ) {Y : ℝ} (_hY : 0 ≤ Y)
    (N : ℕ) :
    ‖eisensteinLineTailTerm t negative x Y N‖ ≤
      ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖ := by
  unfold eisensteinLineTailTerm
  simp only [pow_zero, mul_one]
  rw [norm_mul, norm_mul, norm_mul, d4BM_norm_completedEisensteinFourierPhase, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg Y)]
  have hc := norm_whittakerCoefficient_I_mul_le t ⟨N + 1, by omega⟩
  have hK := norm_nonneg (modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I))
  have hs := Real.sqrt_nonneg Y
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hs) hK

/-- The Bessel argument `2π(N+1)Y` is at least `1` for `Y ≥ 1/2`. -/
theorem one_le_two_pi_mul_succ_mul {Y : ℝ} (hY1 : 1 / 2 ≤ Y) (N : ℕ) :
    1 ≤ 2 * Real.pi * ((N : ℝ) + 1) * Y := by
  have hπ := Real.pi_gt_three
  have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have h1 : (1 : ℝ) / 2 * 1 ≤ Y * ((N : ℝ) + 1) := mul_le_mul hY1 hN (by norm_num) (by linarith)
  have h2 : 2 * Real.pi * ((N : ℝ) + 1) * Y = 2 * Real.pi * (Y * ((N : ℝ) + 1)) := by ring
  rw [h2]
  nlinarith

/-- The divisor-weighted Bessel majorant at height `Y ≥ 1/2` is dominated by `e·(N+1)·e^{−π(N+1)}`. -/
theorem divisorBesselMajorant_le (t : ℝ) {Y : ℝ} (hY1 : 1 / 2 ≤ Y) (hY2 : Y ≤ 1) (N : ℕ) :
    ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖ ≤
      Real.exp 1 * ((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
  have hπ := Real.pi_gt_three
  have hx : 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) * Y := one_le_two_pi_mul_succ_mul hY1 N
  have hK := norm_modifiedBesselKOrder_I_mul_le_exp hx t
  have hd : ((N + 1 : ℕ).divisors.card : ℝ) ≤ (N : ℝ) + 1 := by
    have := Nat.card_divisors_le_self (N + 1)
    exact_mod_cast this
  have hsqrt : Real.sqrt Y ≤ 1 := Real.sqrt_le_one.mpr hY2
  have hsqrt0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hexp : Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)) ≤ Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    nlinarith
  have hK' : ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖ ≤
      Real.exp 1 * Real.exp (-(Real.pi * ((N : ℝ) + 1))) :=
    hK.trans (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le)
  have hd0 : (0 : ℝ) ≤ ((N + 1 : ℕ).divisors.card : ℝ) := by positivity
  calc ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
        ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖
      ≤ ((N : ℝ) + 1) * 1 * (Real.exp 1 * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) := by
          gcongr
    _ = Real.exp 1 * ((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by ring

/-- `(N+1)·e^{−π(N+1)} ≤ e^{−2}·(e^{−2})^N`. -/
theorem nat_mul_exp_neg_pi_le (N : ℕ) :
    ((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) ≤
      Real.exp (-2) * Real.exp (-2) ^ N := by
  have hπ := Real.pi_gt_three
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : ((N : ℝ) + 1) ≤ Real.exp ((N : ℝ) + 1) := by
    have := Real.add_one_le_exp ((N : ℝ) + 1)
    linarith
  have hpow : Real.exp (-2) ^ N = Real.exp (-2 * (N : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow, ← Real.exp_add]
  calc ((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1)))
      ≤ Real.exp ((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (((N : ℝ) + 1) - Real.pi * ((N : ℝ) + 1)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-2 + -2 * (N : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith

/-- The tail terms are summable in norm. -/
theorem summable_norm_eisensteinLineTailTerm (t : ℝ) (negative : Bool) (x : ℝ) {Y : ℝ}
    (hY1 : 1 / 2 ≤ Y) (hY2 : Y ≤ 1) :
    Summable (fun N : ℕ => ‖eisensteinLineTailTerm t negative x Y N‖) := by
  have hgeom : Summable (fun N : ℕ => Real.exp 1 * (Real.exp (-2) * Real.exp (-2) ^ N)) :=
    ((summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _).mul_left _
  refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_) hgeom
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  calc ‖eisensteinLineTailTerm t negative x Y N‖
      ≤ ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt Y *
          ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖ :=
        norm_eisensteinLineTailTerm_le t negative x hY0 N
    _ ≤ Real.exp 1 * ((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) :=
        divisorBesselMajorant_le t hY1 hY2 N
    _ ≤ Real.exp 1 * (Real.exp (-2) * Real.exp (-2) ^ N) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (nat_mul_exp_neg_pi_le N) (Real.exp_pos _).le

/-- Reindexing the head sum of divisor counts. -/
theorem sum_range_card_divisors_succ_le (N₀ : ℕ) (hN₀ : 1 ≤ N₀) :
    ∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) ≤
      (N₀ : ℝ) * (1 + Real.log (N₀ : ℝ)) := by
  have h := Sieve.sum_card_divisors_pow_le_polylog 1 N₀ hN₀
  have hre : ∑ n ∈ Finset.Icc 1 N₀, ((n.divisors.card : ℝ) ^ 1) =
      ∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) := by
    have hIcc : Finset.Icc 1 N₀ = Finset.Ico 1 (N₀ + 1) := by
      ext n
      simp
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    simp only [pow_one, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun N _ => ?_)
    rw [add_comm]
  rw [hre] at h
  simpa using h

/-- **The signed square-root Whittaker tail on the line.**  For `t ≥ 1` and `1/2 ≤ Y ≤ 1`, the
zero-jet tail is at most `5·(t+1)(1 + log(t+1))(1 + log(πt))·e^{−πt/2}`. -/
theorem norm_signedSqrtWhittakerTail_I_mul_le {t : ℝ} (ht : 1 ≤ t) (negative : Bool) (x : ℝ)
    {Y : ℝ} (hY1 : 1 / 2 ≤ Y) (hY2 : Y ≤ 1) :
    ‖d4BMCompletedEisensteinSignedSqrtWhittakerTail ((t : ℂ) * I) ((t : ℂ) * I) negative x 0 0 Y‖
      ≤ 5 * (t + 1) * (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)) *
          Real.exp (-(Real.pi * t) / 2) := by
  have hπ := Real.pi_gt_three
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hsum := summable_norm_eisensteinLineTailTerm t negative x hY1 hY2
  rw [signedSqrtWhittakerTail_eq_tsum]
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  -- the majorant `g`
  set g : ℕ → ℝ := fun N => ((N + 1 : ℕ).divisors.card : ℝ) *
    ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖ with hg
  have hg_nonneg : ∀ N, 0 ≤ g N := fun N => by positivity
  have hterm : ∀ N, ‖eisensteinLineTailTerm t negative x Y N‖ ≤ g N := by
    intro N
    refine (norm_eisensteinLineTailTerm_le t negative x hY0 N).trans ?_
    simp only [hg]
    have hs : Real.sqrt Y ≤ 1 := Real.sqrt_le_one.mpr hY2
    have := norm_nonneg (modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I))
    have hd0 : (0 : ℝ) ≤ ((N + 1 : ℕ).divisors.card : ℝ) := by positivity
    nlinarith [mul_nonneg hd0 this]
  have hg_le : ∀ N, g N ≤ Real.exp 1 * ((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
    intro N
    have h := divisorBesselMajorant_le t hY1 hY2 N
    simp only [hg]
    have hs : Real.sqrt Y ≤ 1 := Real.sqrt_le_one.mpr hY2
    have hs0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
    have hK := norm_nonneg (modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I))
    have hd0 : (0 : ℝ) ≤ ((N + 1 : ℕ).divisors.card : ℝ) := by positivity
    have hx : 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) * Y := one_le_two_pi_mul_succ_mul hY1 N
    have hKb := norm_modifiedBesselKOrder_I_mul_le_exp hx t
    have hd : ((N + 1 : ℕ).divisors.card : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast Nat.card_divisors_le_self (N + 1)
    have hexp : Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * Y)) ≤
        Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
      apply Real.exp_le_exp.mpr
      have : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      nlinarith
    calc ((N + 1 : ℕ).divisors.card : ℝ) *
          ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)‖
        ≤ ((N : ℝ) + 1) * (Real.exp 1 * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) := by
          gcongr
          exact hKb.trans (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le)
      _ = Real.exp 1 * ((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by ring
  have hgsum : Summable g := by
    have hgeom : Summable (fun N : ℕ => Real.exp 1 * (Real.exp (-2) * Real.exp (-2) ^ N)) :=
      ((summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _).mul_left _
    refine Summable.of_nonneg_of_le hg_nonneg (fun N => ?_) hgeom
    refine (hg_le N).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (nat_mul_exp_neg_pi_le N) (Real.exp_pos _).le
  refine (hsum.tsum_le_tsum hterm hgsum).trans ?_
  -- split at N₀ = ⌈t⌉
  set N₀ : ℕ := ⌈t⌉₊ with hN₀def
  have hN₀1 : 1 ≤ N₀ := Nat.one_le_iff_ne_zero.mpr (by
    rw [hN₀def]; exact (Nat.ceil_pos.mpr (by linarith)).ne')
  have hN₀t : t ≤ (N₀ : ℝ) := Nat.le_ceil t
  have hN₀t1 : (N₀ : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
  rw [← hgsum.sum_add_tsum_nat_add N₀]
  -- head
  have hlogπt : 0 ≤ Real.log (Real.pi * t) := Real.log_nonneg (by nlinarith)
  have hE : 0 < Real.exp (-(Real.pi * t) / 2) := Real.exp_pos _
  have hhead : ∑ N ∈ Finset.range N₀, g N ≤
      Real.exp 1 * (Real.log (Real.pi * t) + 1) * Real.exp (-(Real.pi * t) / 2) *
        ((N₀ : ℝ) * (1 + Real.log (N₀ : ℝ))) := by
    have hbound : ∀ N ∈ Finset.range N₀, g N ≤ ((N + 1 : ℕ).divisors.card : ℝ) *
        (Real.exp 1 * (Real.log (Real.pi * t) + 1) * Real.exp (-(Real.pi * t) / 2)) := by
      intro N _
      simp only [hg]
      have hx : 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) * Y := one_le_two_pi_mul_succ_mul hY1 N
      have hK := norm_modifiedBesselKOrder_I_mul_le hx ht
      exact mul_le_mul_of_nonneg_left hK (by positivity)
    calc ∑ N ∈ Finset.range N₀, g N
        ≤ ∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ) *
            (Real.exp 1 * (Real.log (Real.pi * t) + 1) * Real.exp (-(Real.pi * t) / 2)) :=
          Finset.sum_le_sum hbound
      _ = (∑ N ∈ Finset.range N₀, ((N + 1 : ℕ).divisors.card : ℝ)) *
            (Real.exp 1 * (Real.log (Real.pi * t) + 1) * Real.exp (-(Real.pi * t) / 2)) := by
          rw [Finset.sum_mul]
      _ ≤ ((N₀ : ℝ) * (1 + Real.log (N₀ : ℝ))) *
            (Real.exp 1 * (Real.log (Real.pi * t) + 1) * Real.exp (-(Real.pi * t) / 2)) :=
          mul_le_mul_of_nonneg_right (sum_range_card_divisors_succ_le N₀ hN₀1) (by positivity)
      _ = Real.exp 1 * (Real.log (Real.pi * t) + 1) * Real.exp (-(Real.pi * t) / 2) *
            ((N₀ : ℝ) * (1 + Real.log (N₀ : ℝ))) := by ring
  -- tail
  have htail : ∑' N : ℕ, g (N + N₀) ≤ ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) := by
    have hshift : Summable (fun N : ℕ => g (N + N₀)) := (summable_nat_add_iff N₀).mpr hgsum
    have hmaj : ∀ N : ℕ, g (N + N₀) ≤
        ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) *
          (Real.exp (-1) * Real.exp (-2) ^ N) := by
      intro N
      refine (hg_le (N + N₀)).trans ?_
      have hcast : ((N + N₀ : ℕ) : ℝ) = (N : ℝ) + (N₀ : ℝ) := by push_cast; ring
      rw [hcast]
      -- (N + N₀ + 1) ≤ (N₀ + 1)(N + 1) and e^{−π(N+N₀+1)} = e^{−πN₀} e^{−π(N+1)}
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hN₀ : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg N₀
      have h1 : (N : ℝ) + (N₀ : ℝ) + 1 ≤ ((N₀ : ℝ) + 1) * ((N : ℝ) + 1) := by nlinarith
      have h2 : Real.exp (-(Real.pi * ((N : ℝ) + (N₀ : ℝ) + 1))) =
          Real.exp (-(Real.pi * (N₀ : ℝ))) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
        rw [← Real.exp_add]; ring_nf
      have h3 : Real.exp (-(Real.pi * (N₀ : ℝ))) ≤ Real.exp (-(Real.pi * t) / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have h4 := nat_mul_exp_neg_pi_le N
      have h5 : Real.exp 1 * Real.exp (-2) = Real.exp (-1) := by
        rw [← Real.exp_add]; norm_num
      calc Real.exp 1 * ((N : ℝ) + (N₀ : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + (N₀ : ℝ) + 1)))
          = Real.exp 1 * ((N : ℝ) + (N₀ : ℝ) + 1) *
              (Real.exp (-(Real.pi * (N₀ : ℝ))) * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) := by
            rw [h2]
        _ ≤ Real.exp 1 * (((N₀ : ℝ) + 1) * ((N : ℝ) + 1)) *
              (Real.exp (-(Real.pi * t) / 2) * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) := by
            gcongr
        _ = ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) *
              (Real.exp 1 * (((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1))))) := by ring
        _ ≤ ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) *
              (Real.exp 1 * (Real.exp (-2) * Real.exp (-2) ^ N)) := by
            gcongr
        _ = ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) *
              (Real.exp (-1) * Real.exp (-2) ^ N) := by
            rw [← mul_assoc (Real.exp 1), h5]
    have hgeom : Summable (fun N : ℕ => ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) *
        (Real.exp (-1) * Real.exp (-2) ^ N)) :=
      ((summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _).mul_left _
    have hin : Summable (fun N : ℕ => Real.exp (-1) * Real.exp (-2) ^ N) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _
    refine (hshift.tsum_le_tsum hmaj hgeom).trans ?_
    rw [Summable.tsum_mul_left _ hin]
    have hgt : ∑' N : ℕ, (Real.exp (-1) * Real.exp (-2) ^ N) =
        Real.exp (-1) * (1 - Real.exp (-2))⁻¹ := by
      rw [Summable.tsum_mul_left _ (summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by norm_num))), tsum_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by norm_num))]
    rw [hgt]
    have hle1 : Real.exp (-1) * (1 - Real.exp (-2))⁻¹ ≤ 1 := by
      have he2 : Real.exp (-2) ≤ 1 / 4 := by
        have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        rw [Real.exp_neg]
        rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        norm_num at h ⊢
        linarith
      have he1 : Real.exp (-1) ≤ 1 / 2 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        rw [Real.exp_neg]
        rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        linarith
      have hpos : 0 < 1 - Real.exp (-2) := by linarith
      rw [mul_inv_le_iff₀ hpos]
      linarith
    have hN₀pos : 0 ≤ ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) := by positivity
    calc ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) * (Real.exp (-1) * (1 - Real.exp (-2))⁻¹)
        ≤ ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) * 1 :=
          mul_le_mul_of_nonneg_left hle1 hN₀pos
      _ = ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) := by ring
  -- combine
  have hlogN₀ : Real.log (N₀ : ℝ) ≤ Real.log (t + 1) :=
    Real.log_le_log (by exact_mod_cast hN₀1) hN₀t1.le
  have hlogt1 : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hA : 0 ≤ (N₀ : ℝ) * (1 + Real.log (N₀ : ℝ)) := by
    have : 0 ≤ Real.log (N₀ : ℝ) := Real.log_nonneg (by exact_mod_cast hN₀1)
    positivity
  have hB : (N₀ : ℝ) * (1 + Real.log (N₀ : ℝ)) ≤ (t + 1) * (1 + Real.log (t + 1)) := by
    apply mul_le_mul hN₀t1.le (by linarith) (by
      have : 0 ≤ Real.log (N₀ : ℝ) := Real.log_nonneg (by exact_mod_cast hN₀1)
      linarith) (by linarith)
  have hC : (N₀ : ℝ) + 1 ≤
      2 * ((t + 1) * (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t))) := by
    have h1 : (N₀ : ℝ) + 1 ≤ 2 * (t + 1) := by linarith
    have h2 : (1 : ℝ) ≤ (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)) := by nlinarith
    have h4 : 0 ≤ 2 * (t + 1) * ((1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)) - 1) := by
      apply mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hD : Real.exp 1 * (Real.log (Real.pi * t) + 1) * ((N₀ : ℝ) * (1 + Real.log (N₀ : ℝ))) ≤
      3 * (t + 1) * (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)) := by
    have hL : 0 ≤ Real.log (Real.pi * t) + 1 := by linarith
    calc Real.exp 1 * (Real.log (Real.pi * t) + 1) * ((N₀ : ℝ) * (1 + Real.log (N₀ : ℝ)))
        ≤ 3 * (Real.log (Real.pi * t) + 1) * ((t + 1) * (1 + Real.log (t + 1))) := by
          gcongr
      _ = 3 * (t + 1) * (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)) := by ring
  calc (∑ N ∈ Finset.range N₀, g N) + ∑' N : ℕ, g (N + N₀)
      ≤ Real.exp 1 * (Real.log (Real.pi * t) + 1) * Real.exp (-(Real.pi * t) / 2) *
          ((N₀ : ℝ) * (1 + Real.log (N₀ : ℝ))) +
        ((N₀ : ℝ) + 1) * Real.exp (-(Real.pi * t) / 2) := add_le_add hhead htail
    _ = (Real.exp 1 * (Real.log (Real.pi * t) + 1) * ((N₀ : ℝ) * (1 + Real.log (N₀ : ℝ))) +
          ((N₀ : ℝ) + 1)) * Real.exp (-(Real.pi * t) / 2) := by ring
    _ ≤ (3 * (t + 1) * (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)) +
          2 * ((t + 1) * (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)))) *
          Real.exp (-(Real.pi * t) / 2) := by
        gcongr
    _ = 5 * (t + 1) * (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)) *
          Real.exp (-(Real.pi * t) / 2) := by ring

/-- **The nonconstant part of the completed Eisenstein series on the line**, at heights
`1/2 ≤ Y ≤ 1`: at most `20·(t+1)(1 + log(t+1))(1 + log(πt))·e^{−πt/2}`. -/
theorem norm_eisensteinCuspTailPart_I_mul_le {t : ℝ} (ht : 1 ≤ t) (x : ℝ) {Y : ℝ}
    (hY1 : 1 / 2 ≤ Y) (hY2 : Y ≤ 1) :
    ‖d4BMCompletedEisensteinCuspTailPart .scalar ((t : ℂ) * I) x Y‖ ≤
      20 * (t + 1) * (1 + Real.log (t + 1)) * (1 + Real.log (Real.pi * t)) *
        Real.exp (-(Real.pi * t) / 2) := by
  unfold d4BMCompletedEisensteinCuspTailPart d4BMCompletedEisensteinFullSignedZeroWord
  rw [norm_mul, Complex.norm_ofNat]
  have h1 := norm_signedSqrtWhittakerTail_I_mul_le ht false x hY1 hY2
  have h2 := norm_signedSqrtWhittakerTail_I_mul_le ht true x hY1 hY2
  have hsum := norm_add_le
    (d4BMCompletedEisensteinSignedSqrtWhittakerTail ((t : ℂ) * I) ((t : ℂ) * I) false x 0 0 Y)
    (d4BMCompletedEisensteinSignedSqrtWhittakerTail ((t : ℂ) * I) ((t : ℂ) * I) true x 0 0 Y)
  nlinarith

end

end RHTower
