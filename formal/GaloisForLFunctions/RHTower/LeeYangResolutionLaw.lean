import GaloisForLFunctions.RHTower.LeeYangPrimeStabilityNoGo
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder

/-!
# The Lee–Yang resolution law for `Ξ`

`not_tendsto_lyApprox_mul_XiC` excludes Lee–Yang approximants of `E · XiC` whose frequencies are
bounded below.  This file proves the quantitative form at a single scale.

**Theorem** (`exists_resolution_law`).  Let `E` be entire and zero-free.  There is `R₀` such that for
every `R ≥ R₀` some `ε > 0` has the following property.  If a normalized Lee–Yang restriction is
`ε`-close to `E · XiC` on the disc of radius `R + 2`, then its datum has total degree `S ≥ R/64`.
Moreover at least half of that degree sits on variables of frequency at most
`2 (64 log (R+1) + 2π)/R`.

For rational fields `q^{−iz}` this forces denominators of size `≫ R / log R`
(`exists_den_ge_of_rational_freq`).

**Proof.**
* Rouché at two admissible radii `T₀ ∈ (R, R+1)` and `T₁ ∈ (R/2, R/2+1)` gives the approximant the
  zero counts of `E · XiC`.
* Those counts lie between the symmetric `ξ`-masses `M(T − 1)` and `M(T)`.
* The linear count `|c(T) − 2TD| ≤ 2S` gives `c₀T₁ − c₁T₀ ≤ 2S(T₀ + T₁)`.
* Riemann–von Mangoldt with an `O(log T)` remainder gives
  `T₁ M(T₀ − 1) − T₀ M(T₁) ≥ (log 2/2π) R² (1 + o(1)) ≥ R²/16`.
* The density bound `2πD = Σ Dⱼ λⱼ ≤ log T₀ + 2πS/T₀` then confines the frequency mass.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower.LeeYangCount

noncomputable section

/-! ## Symmetric `ξ`-mass in discs -/

/-- The centered coordinate of a `ξ`-divisor support. -/
def centerOf (ρ : XiDivisorSupport) : ℂ := ((ρ : ℂ) - 1 / 2) * (-I)

theorem neg_I_mul_I : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring

theorem XiC_centerOf (ρ : XiDivisorSupport) : XiC (centerOf ρ) = xi (ρ : ℂ) := by
  rw [XiC, centerOf]
  congr 1
  rw [mul_assoc, neg_I_mul_I, mul_one]
  ring

theorem centerOf_injective : Function.Injective centerOf := by
  intro a b hab
  apply Subtype.ext
  have := congrArg (fun w => w * I + 1 / 2) hab
  simp only [centerOf] at this
  rw [mul_assoc, neg_I_mul_I, mul_one, mul_assoc, neg_I_mul_I, mul_one] at this
  linear_combination this

theorem re_centerOf (ρ : XiDivisorSupport) : (centerOf ρ).re = (ρ : ℂ).im := by
  simp [centerOf, Complex.mul_re]

theorem norm_centerOf_lt {ρ : XiDivisorSupport} {T : ℝ} (h : |(ρ : ℂ).im| ≤ T - 1) :
    ‖centerOf ρ‖ < T := by
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support ρ)
  rw [centerOf, norm_mul, norm_neg, Complex.norm_I, mul_one]
  have hn : ‖(ρ : ℂ) - 1 / 2‖ ≤ |((ρ : ℂ) - 1 / 2).re| + |((ρ : ℂ) - 1 / 2).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have hre : |((ρ : ℂ) - 1 / 2).re| < 1 / 2 := by
    rw [abs_lt]
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    constructor <;> linarith
  have him : |((ρ : ℂ) - 1 / 2).im| ≤ T - 1 := by
    simpa only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero] using h
  linarith

variable {E : ℂ → ℂ}

private theorem differentiableXiC : Differentiable ℂ XiC := fun z =>
  (XiC_analytic z (mem_univ z)).differentiableAt

theorem zeroMult_mul_XiC (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0) (z : ℂ) :
    zeroMult (fun w => E w * XiC w) z = (analyticOrderAt XiC z).toNat := by
  have hmul : analyticOrderAt (fun w => E w * XiC w) z =
      analyticOrderAt E z + analyticOrderAt XiC z :=
    analyticOrderAt_mul (hE.analyticAt z) (differentiableXiC.analyticAt z)
  have h0 : analyticOrderAt E z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr (hEne z))
  rw [zeroMult, hmul, h0, zero_add]

theorem zeroMult_centerOf (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    (ρ : XiDivisorSupport) :
    zeroMult (fun w => E w * XiC w) (centerOf ρ) = xiSupportMultiplicity ρ := by
  rw [zeroMult_mul_XiC hE hEne, centerOf, analyticOrderAt_XiC_centeredCoordinate,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat]

/-- Supports whose centers lie in the disc are counted by the disc. -/
theorem sum_le_re_zeroSumBall (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0) {T : ℝ}
    (hT : 0 < T) (hsph : ∀ z ∈ sphere (0 : ℂ) T, E z * XiC z ≠ 0)
    (S : Finset XiDivisorSupport) (hS : ∀ ρ ∈ S, ‖centerOf ρ‖ < T) :
    ∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℝ) ≤ (zeroSumBall (fun z => E z * XiC z) 0 T).re := by
  classical
  have hFd : Differentiable ℂ (fun z => E z * XiC z) := hE.mul differentiableXiC
  obtain ⟨Z, -, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall (c := 0) hT (lt_add_one T)
    isOpen_univ (subset_univ _) hFd.differentiableOn hsph
  have hsub : S.image centerOf ⊆ Z := by
    intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
    have hball : centerOf ρ ∈ ball (0 : ℂ) T := mem_ball_zero_iff.mpr (hS ρ hρ)
    refine (hZzero _ hball).mp ?_
    show E (centerOf ρ) * XiC (centerOf ρ) = 0
    rw [XiC_centerOf, xi_eq_zero_of_mem_divisor_support ρ, mul_zero]
  have hcount : ∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℝ) =
      ∑ z ∈ S.image centerOf, (zeroMult (fun w => E w * XiC w) z : ℝ) := by
    rw [Finset.sum_image fun a _ b _ h => centerOf_injective h]
    exact Finset.sum_congr rfl fun ρ _ => by rw [zeroMult_centerOf hE hEne]
  rw [hcount, hsum, Complex.re_sum]
  simp only [Complex.natCast_re]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

/-- The disc count is carried by the supports whose centers lie in the disc. -/
theorem re_zeroSumBall_le_sum (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0) {T : ℝ}
    (hT : 0 < T) (hsph : ∀ z ∈ sphere (0 : ℂ) T, E z * XiC z ≠ 0)
    (S : Finset XiDivisorSupport) (hS : ∀ ρ : XiDivisorSupport, ‖centerOf ρ‖ < T → ρ ∈ S) :
    (zeroSumBall (fun z => E z * XiC z) 0 T).re ≤ ∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℝ) := by
  classical
  have hFd : Differentiable ℂ (fun z => E z * XiC z) := hE.mul differentiableXiC
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall (c := 0) hT (lt_add_one T)
    isOpen_univ (subset_univ _) hFd.differentiableOn hsph
  have hsub : Z ⊆ S.image centerOf := by
    intro z hz
    have hb := hZball z hz
    have hzero : E z * XiC z = 0 := (hZzero z hb).mpr hz
    have hX : xi (1 / 2 + z * I) = 0 := by
      have := (mul_eq_zero.mp hzero).resolve_left (hEne z)
      rwa [XiC] at this
    set ρ : XiDivisorSupport := ⟨1 / 2 + z * I, mem_xi_divisor_support_of_eq_zero hX⟩
    have hc : centerOf ρ = z := by
      simp only [centerOf, ρ]
      rw [add_sub_cancel_left, mul_assoc]
      have : I * (-I) = (1 : ℂ) := by rw [mul_neg, I_mul_I, neg_neg]
      rw [this, mul_one]
    refine Finset.mem_image.mpr ⟨ρ, hS ρ ?_, hc⟩
    rw [hc]
    exact mem_ball_zero_iff.mp hb
  have hcount : ∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℝ) =
      ∑ z ∈ S.image centerOf, (zeroMult (fun w => E w * XiC w) z : ℝ) := by
    rw [Finset.sum_image fun a _ b _ h => centerOf_injective h]
    exact Finset.sum_congr rfl fun ρ _ => by rw [zeroMult_centerOf hE hEne]
  rw [hcount, hsum, Complex.re_sum]
  simp only [Complex.natCast_re]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

theorem xiSymmetricMass_real_eq {T : ℝ} (hT : 0 ≤ T) :
    (xiSymmetricMass T : ℝ) =
      ∑ ρ ∈ (xiSupportsUpTo_finite T).toFinset, (xiSupportMultiplicity ρ : ℝ) := by
  rw [xiSymmetricMass_eq_support_sum hT]
  push_cast
  rfl

/-- `M(T − 1) ≤ c(T)`. -/
theorem xiSymmetricMass_pred_le_zeroSumBall (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    {T : ℝ} (hT : 1 ≤ T) (hsph : ∀ z ∈ sphere (0 : ℂ) T, E z * XiC z ≠ 0) :
    (xiSymmetricMass (T - 1) : ℝ) ≤ (zeroSumBall (fun z => E z * XiC z) 0 T).re := by
  rw [xiSymmetricMass_real_eq (by linarith)]
  refine sum_le_re_zeroSumBall hE hEne (by linarith) hsph _ fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  exact norm_centerOf_lt hρ

/-- `c(T) ≤ M(T)`. -/
theorem re_zeroSumBall_le_xiSymmetricMass (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    {T : ℝ} (hT : 0 < T) (hsph : ∀ z ∈ sphere (0 : ℂ) T, E z * XiC z ≠ 0) :
    (zeroSumBall (fun z => E z * XiC z) 0 T).re ≤ (xiSymmetricMass T : ℝ) := by
  rw [xiSymmetricMass_real_eq hT.le]
  refine re_zeroSumBall_le_sum hE hEne hT hsph _ fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset]
  show |(ρ : ℂ).im| ≤ T
  rw [← re_centerOf]
  exact (Complex.abs_re_le_norm _).trans hρ.le

/-! ## Riemann–von Mangoldt on two scales -/

theorem log_le_log_add_div {x K : ℝ} (hx : 0 < x) (hK : 0 < K) :
    Real.log x ≤ Real.log K + x / K := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hK)
  rw [Real.log_div hx.ne' hK.ne'] at h
  linarith

theorem log_nineteen_tenths_ge : (16 / 25 : ℝ) ≤ Real.log (19 / 10) := by
  have h1 : Real.log (19 / 10) = Real.log 2 + Real.log (19 / 20) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 19 / 20 by norm_num)
  have h3 := Real.log_two_gt_d9
  norm_num at h2
  linarith

theorem one_le_log_routeKRVMBase : 1 ≤ Real.log routeKRVMBase := by
  rw [routeKRVMBase, Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

/-- Riemann–von Mangoldt for the symmetric mass `M(T) = 2N(T)`, with `O(log T)` remainder. -/
theorem exists_xiSymmetricMass_log_remainder :
    ∃ C : ℝ, 0 < C ∧ ∃ Ts : ℝ, 4 ≤ Ts ∧ ∀ T : ℝ, Ts ≤ T →
      |(xiSymmetricMass T : ℝ) -
          (T / Real.pi * (Real.log T - Real.log routeKRVMBase) + 7 / 4)| ≤
        2 * C * Real.log T := by
  obtain ⟨C, hC, Ts, hTs, hrem⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨C, hC, Ts, hTs, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have h := hrem T hT
  have hsym : (xiSymmetricMass T : ℝ) = 2 * (xiZeroCount T : ℝ) := by
    exact_mod_cast xiSymmetricMass_eq_two_mul_xiZeroCount hT0.le
  rw [routeKSmoothRVMCount, Real.log_div hT0.ne' routeKRVMBase_pos.ne'] at h
  have heq : (xiSymmetricMass T : ℝ) -
      (T / Real.pi * (Real.log T - Real.log routeKRVMBase) + 7 / 4) =
      2 * ((xiZeroCount T : ℝ) -
        (T / (2 * Real.pi) * (Real.log T - Real.log routeKRVMBase) + 7 / 8)) := by
    rw [hsym]
    field_simp
    ring
  rw [heq, abs_mul, abs_two]
  linarith

/-- The two-scale window computation, with every logarithm and mass as a free real variable. -/
theorem window_core {R T₀ T₁ C K lK P LR La Lb lB Ma Mb : ℝ}
    (hC : 0 < C) (hK : K = 100 * (1 + 8 * C)) (hP : P = C * lK)
    (hR64 : 64 ≤ R) (hRK : 160 + 40 * lK + 320 * P ≤ R) (hlB1 : 1 ≤ lB)
    (h0 : R ≤ T₀) (h0' : T₀ ≤ R + 1) (h1 : R / 2 ≤ T₁) (h1' : T₁ ≤ R / 2 + 1)
    (hLR0 : 0 ≤ LR) (hLRK : LR ≤ lK + (R + 1) / K)
    (hLa0 : 0 ≤ La) (hLaR : La ≤ LR) (hLb0 : 0 ≤ Lb) (hLbR : Lb ≤ LR)
    (hsep : 16 / 25 ≤ La - Lb)
    (hMa : -(2 * C * La) ≤ Ma - ((T₀ - 1) / Real.pi * (La - lB) + 7 / 4))
    (hMb : Mb - (T₁ / Real.pi * (Lb - lB) + 7 / 4) ≤ 2 * C * Lb) :
    R ^ 2 / 16 ≤ T₁ * Ma - T₀ * Mb := by
  have hπ3 := Real.pi_gt_three
  have hπ4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  · have e1 : T₁ * ((T₀ - 1) / Real.pi * (La - lB) + 7 / 4 - 2 * C * La) ≤ T₁ * Ma :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : T₀ * Mb ≤ T₀ * (T₁ / Real.pi * (Lb - lB) + 7 / 4 + 2 * C * Lb) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hid : T₁ * ((T₀ - 1) / Real.pi * (La - lB) + 7 / 4 - 2 * C * La) -
        T₀ * (T₁ / Real.pi * (Lb - lB) + 7 / 4 + 2 * C * Lb) =
        T₁ * (T₀ - 1) / Real.pi * (La - Lb) - T₁ / Real.pi * (Lb - lB) +
          7 * (T₁ - T₀) / 4 - 2 * C * (T₁ * La + T₀ * Lb) := by
      ring
    -- the separated main term
    have hprod : R / 2 * (R - 1) ≤ T₁ * (T₀ - 1) :=
      mul_le_mul h1 (by linarith) (by linarith) (by linarith)
    have hq : 0 ≤ T₁ * (T₀ - 1) := mul_nonneg (by linarith) (by linarith)
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = T₁ * (T₀ - 1) / Real.pi := ⟨_, rfl⟩
    have hQ0 : 0 ≤ Q := hQ ▸ div_nonneg hq hπ0.le
    have h16 : Q * (16 / 25) ≤ Q * (La - Lb) := mul_le_mul_of_nonneg_left hsep hQ0
    have hQlow : T₁ * (T₀ - 1) / 3.15 ≤ Q := hQ ▸ div_le_div_of_nonneg_left hq hπ0 hπ4.le
    have hi : R * (R - 1) / 10 ≤ Q * (La - Lb) := by
      have hRR : 0 ≤ R * (R - 1) := mul_nonneg (by linarith) (by linarith)
      have : T₁ * (T₀ - 1) / 3.15 = T₁ * (T₀ - 1) * (20 / 63) := by norm_num [div_eq_mul_inv]
      nlinarith
    -- the boundary term
    have hii : T₁ / Real.pi * (Lb - lB) ≤ R * LR / 3 := by
      have hT₁π : T₁ / Real.pi ≤ T₁ / 3 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) hπ3.le
      have h' : T₁ / Real.pi * (Lb - lB) ≤ T₁ / Real.pi * Lb :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by linarith) hπ0.le)
      have h'' : T₁ / Real.pi * Lb ≤ R / 3 * LR :=
        mul_le_mul (by linarith) hLbR hLb0 (by linarith)
      linarith
    -- the remainder
    have hiii : 2 * C * (T₁ * La + T₀ * Lb) ≤ 6 * C * (R * LR) := by
      have ha := mul_le_mul (show T₁ ≤ R by linarith) hLaR hLa0 (by linarith)
      have hb := mul_le_mul (show T₀ ≤ 2 * R by linarith) hLbR hLb0 (by linarith)
      have hsum : T₁ * La + T₀ * Lb ≤ 3 * (R * LR) := by linarith
      have := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 * C by linarith)
      linarith
    -- the linear absorption
    have hlin : 18 / 5 + (1 / 3 + 6 * C) * LR ≤ 3 / 80 * R := by
      have hA : (1 / 3 + 6 * C) * LR ≤ (1 + 8 * C) * LR :=
        mul_le_mul_of_nonneg_right (by linarith) hLR0
      have hB : (1 + 8 * C) * LR ≤ (1 + 8 * C) * (lK + (R + 1) / K) :=
        mul_le_mul_of_nonneg_left hLRK (by linarith)
      have hC1 : (1 + 8 * C) * ((R + 1) / K) = (R + 1) / 100 := by
        rw [hK, mul_div_assoc', div_eq_div_iff (by positivity) (by norm_num)]
        ring
      have hC2 : (1 + 8 * C) * (lK + (R + 1) / K) = lK + 8 * P + (R + 1) / 100 := by
        rw [mul_add, hC1, hP]
        ring
      linarith
    have hlinR : R * (18 / 5 + (1 / 3 + 6 * C) * LR) ≤ R * (3 / 80 * R) :=
      mul_le_mul_of_nonneg_left hlin (by linarith)
    have hexp : R * (18 / 5 + (1 / 3 + 6 * C) * LR) =
        18 / 5 * R + R * LR / 3 + 6 * C * (R * LR) := by ring
    rw [hexp] at hlinR
    rw [← hQ] at hid
    linarith

/-- The upper mass bound at the outer scale, with every logarithm as a free real variable. -/
theorem window_upper {R T₀ C K lK P L0 lB M0 : ℝ}
    (hC : 0 < C) (hK : K = 100 * (1 + 8 * C)) (hP : P = C * lK) (hlK : 0 ≤ lK)
    (hRK : 160 + 40 * lK + 320 * P ≤ R) (hlB1 : 1 ≤ lB) (h0 : R ≤ T₀)
    (hL0K : L0 ≤ lK + T₀ / K)
    (hM0 : M0 - (T₀ / Real.pi * (L0 - lB) + 7 / 4) ≤ 2 * C * L0) :
    M0 ≤ T₀ / Real.pi * L0 := by
  have hπ4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hKpos : 0 < K := by rw [hK]; linarith
  have hP0 : 0 ≤ P := hP ▸ mul_nonneg hC.le hlK
  have hck : 2 * C / K ≤ 1 / 400 := by
    rw [div_le_iff₀ hKpos]
    linarith
  have hfrac : 2 * C * (T₀ / K) ≤ T₀ / 400 := by
    have h := mul_le_mul_of_nonneg_left hck (show (0 : ℝ) ≤ T₀ by linarith)
    have e : 2 * C * (T₀ / K) = T₀ * (2 * C / K) := by ring
    linarith
  have h := mul_le_mul_of_nonneg_left hL0K (show (0 : ℝ) ≤ 2 * C by linarith)
  have hsplit : 2 * C * (lK + T₀ / K) = 2 * P + 2 * C * (T₀ / K) := by
    rw [hP]; ring
  have hT₀π : T₀ / 4 ≤ T₀ / Real.pi :=
    div_le_div_of_nonneg_left (by linarith) hπ0 (by linarith)
  have hlBT : T₀ / Real.pi ≤ T₀ / Real.pi * lB := by
    have := mul_le_mul_of_nonneg_left hlB1 (div_nonneg (by linarith : (0 : ℝ) ≤ T₀) hπ0.le)
    linarith
  have hexp : T₀ / Real.pi * (L0 - lB) = T₀ / Real.pi * L0 - T₀ / Real.pi * lB := by ring
  linarith

/-- **Two-scale window.**  For `T₀ ∈ [R, R+1]` and `T₁ ∈ [R/2, R/2+1]`, with `R` large,
`T₁ M(T₀ − 1) − T₀ M(T₁) ≥ R²/16` and `M(T₀) ≤ (T₀/π) log T₀`. -/
theorem exists_symmetricMass_window :
    ∃ R₀ : ℝ, 64 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ T₀ T₁ : ℝ, R ≤ T₀ → T₀ ≤ R + 1 → R / 2 ≤ T₁ →
      T₁ ≤ R / 2 + 1 →
      R ^ 2 / 16 ≤ T₁ * (xiSymmetricMass (T₀ - 1) : ℝ) - T₀ * (xiSymmetricMass T₁ : ℝ) ∧
      (xiSymmetricMass T₀ : ℝ) ≤ T₀ / Real.pi * Real.log T₀ := by
  obtain ⟨C, hC, Ts, hTs, hM⟩ := exists_xiSymmetricMass_log_remainder
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 100 * (1 + 8 * C) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hlK : 0 ≤ Real.log K := Real.log_nonneg (by rw [hK]; nlinarith)
  refine ⟨max (max 64 (2 * Ts + 2)) (160 + 40 * Real.log K + 320 * (C * Real.log K)),
    le_trans (le_max_left _ _) (le_max_left _ _), fun R hR T₀ T₁ h0 h0' h1 h1' => ?_⟩
  have hR64 : 64 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRTs : 2 * Ts + 2 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRK : 160 + 40 * Real.log K + 320 * (C * Real.log K) ≤ R := le_trans (le_max_right _ _) hR
  have hlogle : ∀ x : ℝ, 1 ≤ x → x ≤ R + 1 → 0 ≤ Real.log x ∧ Real.log x ≤ Real.log (R + 1) :=
    fun x hx1 hx2 => ⟨Real.log_nonneg hx1, Real.log_le_log (by linarith) hx2⟩
  have hMa := (abs_le.mp (hM (T₀ - 1) (by linarith))).1
  have hMb := (abs_le.mp (hM T₁ (by linarith))).2
  have hM0 := (abs_le.mp (hM T₀ (by linarith))).2
  obtain ⟨hLa0, hLaR⟩ := hlogle (T₀ - 1) (by linarith) (by linarith)
  obtain ⟨hLb0, hLbR⟩ := hlogle T₁ (by linarith) (by linarith)
  have hsep : 16 / 25 ≤ Real.log (T₀ - 1) - Real.log T₁ := by
    have hab : 19 / 10 * T₁ ≤ T₀ - 1 := by linarith
    have h := Real.log_le_log (by linarith) hab
    rw [Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < T₁).ne'] at h
    linarith [log_nineteen_tenths_ge]
  exact ⟨window_core hC hK rfl hR64 hRK one_le_log_routeKRVMBase h0 h0' h1 h1'
    (Real.log_nonneg (by linarith)) (log_le_log_add_div (by linarith) hKpos) hLa0 hLaR hLb0 hLbR
    hsep (by linarith) hMb,
    window_upper hC hK rfl hlK hRK one_le_log_routeKRVMBase h0
      (log_le_log_add_div (by linarith) hKpos) hM0⟩

/-! ## The resolution law -/

theorem two_pi_mul_density {ι : Type} [Fintype ι] (L : LeeYangDatum ι) :
    2 * Real.pi * L.density = ∑ j, (L.P.degreeOf j : ℝ) * L.freq j := by
  rw [LeeYangDatum.density]
  field_simp

theorem degSum_cast {ι : Type} [Fintype ι] (P : MvPolynomial ι ℂ) :
    (degSum P : ℝ) = ∑ j, (P.degreeOf j : ℝ) := by
  rw [degSum]
  push_cast
  rfl

/-- The frequency mass is at most `S · (64 log (R+1) + 2π)/R`. -/
theorem freq_core {R T₀ D S c₀ M₀ L₀ LR : ℝ} (hR : 0 < R) (h0 : R ≤ T₀) (hS : R / 64 ≤ S)
    (hb : -(2 * S) ≤ c₀ - 2 * T₀ * D) (hc : c₀ ≤ M₀) (hM : M₀ ≤ T₀ / Real.pi * L₀)
    (hL : L₀ ≤ LR) (hLR : 0 ≤ LR) :
    2 * Real.pi * D ≤ S * ((64 * LR + 2 * Real.pi) / R) := by
  have hπ := Real.pi_pos
  have hT₀ : 0 < T₀ := by linarith
  have hS0 : 0 ≤ S := by linarith
  have h1 : 2 * T₀ * D ≤ T₀ / Real.pi * L₀ + 2 * S := by linarith
  have h2 : Real.pi * (2 * T₀ * D) ≤ Real.pi * (T₀ / Real.pi * L₀ + 2 * S) :=
    mul_le_mul_of_nonneg_left h1 hπ.le
  have h2' : Real.pi * (T₀ / Real.pi * L₀ + 2 * S) = T₀ * L₀ + 2 * Real.pi * S := by
    field_simp
  have h3 : T₀ * L₀ ≤ T₀ * LR := mul_le_mul_of_nonneg_left hL hT₀.le
  have h6 : 2 * Real.pi * D - LR ≤ 2 * Real.pi * S / T₀ := by
    rw [le_div_iff₀ hT₀]
    linarith
  have h7 : 2 * Real.pi * S / T₀ ≤ 2 * Real.pi * S / R :=
    div_le_div_of_nonneg_left (by positivity) hR h0
  have h8 : 1 ≤ 64 * S / R := by
    rw [le_div_iff₀ hR]
    linarith
  have h9 : LR ≤ 64 * S / R * LR := by
    have := mul_le_mul_of_nonneg_right h8 hLR
    linarith
  have h10 : S * ((64 * LR + 2 * Real.pi) / R) = 64 * S / R * LR + 2 * Real.pi * S / R := by
    ring
  linarith

/-- **Lee–Yang resolution law for `Ξ`.**  For large `R`, every normalized Lee–Yang restriction
uniformly `ε`-close to `E · XiC` on the disc of radius `R + 2` has total degree at least `R/64`.
At least half of that degree sits on variables of frequency at most
`2 (64 log (R+1) + 2π)/R`. -/
theorem exists_resolution_law {E : ℂ → ℂ} (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ ε > 0, ∀ A : LYApprox,
      (∀ z ∈ closedBall (0 : ℂ) (R + 2), ‖A.sect z - E z * XiC z‖ ≤ ε) →
      R / 64 ≤ (degSum A.datum.P : ℝ) ∧
      (degSum A.datum.P : ℝ) / 2 ≤
        ∑ j ∈ Finset.univ.filter
            (fun j => A.datum.freq j ≤ 2 * ((64 * Real.log (R + 1) + 2 * Real.pi) / R)),
          (A.datum.P.degreeOf j : ℝ) := by
  classical
  obtain ⟨R₀, hR₀, hwin⟩ := exists_symmetricMass_window
  refine ⟨R₀, by linarith, fun R hR => ?_⟩
  have hR64 : 64 ≤ R := le_trans hR₀ hR
  have hRpos : 0 < R := by linarith
  have hFd : Differentiable ℂ (fun z => E z * XiC z) := hE.mul differentiableXiC
  have hF0 : E 0 * XiC 0 ≠ 0 := mul_ne_zero (hEne 0) XiC_zero_ne
  obtain ⟨T₀, hT₀, hsph₀⟩ := exists_admissible_radius hFd hF0 R
  obtain ⟨T₁, hT₁, hsph₁⟩ := exists_admissible_radius hFd hF0 (R / 2)
  have hT₀pos : 0 < T₀ := by linarith [hT₀.1]
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  obtain ⟨ε₀, hε₀, hst₀⟩ := exists_eps_zeroSumBall_eq (c := 0) hT₀pos
    (show T₀ < R + 2 by linarith [hT₀.2]) isOpen_univ (subset_univ _) hFd.differentiableOn hsph₀
  obtain ⟨ε₁, hε₁, hst₁⟩ := exists_eps_zeroSumBall_eq (c := 0) hT₁pos
    (show T₁ < R + 2 by linarith [hT₁.2]) isOpen_univ (subset_univ _) hFd.differentiableOn hsph₁
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun A hA => ?_⟩
  obtain ⟨hA₀s, hA₀c⟩ := hst₀ A.sect A.differentiable_sect.differentiableOn
    (fun z hz => (hA z hz).trans (min_le_left _ _))
  obtain ⟨hA₁s, hA₁c⟩ := hst₁ A.sect A.differentiable_sect.differentiableOn
    (fun z hz => (hA z hz).trans (min_le_right _ _))
  have hrestr : ∀ {T : ℝ}, 0 < T → (∀ ζ ∈ sphere (0 : ℂ) T, A.sect ζ ≠ 0) →
      A.datum.restr (T : ℂ) ≠ 0 ∧ A.datum.restr ((-T : ℝ) : ℂ) ≠ 0 := by
    intro T hT h
    exact ⟨fun h' => h _ (by simp [abs_of_pos hT]) (A.sect_eq_zero_iff.mpr h'),
      fun h' => h _ (by simp [abs_of_pos hT]) (A.sect_eq_zero_iff.mpr h')⟩
  obtain ⟨hr₀, hr₀'⟩ := hrestr hT₀pos hA₀s
  obtain ⟨hr₁, hr₁'⟩ := hrestr hT₁pos hA₁s
  have hb₀ := A.abs_zeroSumBall_sub_le hT₀pos hr₀ hr₀'
  have hb₁ := A.abs_zeroSumBall_sub_le hT₁pos hr₁ hr₁'
  rw [hA₀c] at hb₀
  rw [hA₁c] at hb₁
  have hlow := xiSymmetricMass_pred_le_zeroSumBall hE hEne (by linarith [hT₀.1]) hsph₀
  have hup₁ := re_zeroSumBall_le_xiSymmetricMass hE hEne hT₁pos hsph₁
  have hup₀ := re_zeroSumBall_le_xiSymmetricMass hE hEne hT₀pos hsph₀
  obtain ⟨hW, hU⟩ := hwin R hR T₀ T₁ hT₀.1.le hT₀.2.le hT₁.1.le hT₁.2.le
  -- abstraction
  obtain ⟨c₀, hc₀⟩ : ∃ c, c = (zeroSumBall (fun z => E z * XiC z) 0 T₀).re := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = (zeroSumBall (fun z => E z * XiC z) 0 T₁).re := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = A.datum.density := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (degSum A.datum.P : ℝ) := ⟨_, rfl⟩
  rw [← hc₀, ← hD, ← hS] at hb₀
  rw [← hc₁, ← hD, ← hS] at hb₁
  rw [← hc₀] at hlow hup₀
  rw [← hc₁] at hup₁
  rw [abs_le] at hb₀ hb₁
  -- total degree
  have hcross : c₀ * T₁ - c₁ * T₀ ≤ 2 * S * (T₀ + T₁) := by
    have h1 := mul_le_mul_of_nonneg_right (show c₀ ≤ 2 * T₀ * D + 2 * S by linarith) hT₁pos.le
    have h2 := mul_le_mul_of_nonneg_right (show 2 * T₁ * D - 2 * S ≤ c₁ by linarith) hT₀pos.le
    linarith
  have hmass : T₁ * (xiSymmetricMass (T₀ - 1) : ℝ) - T₀ * (xiSymmetricMass T₁ : ℝ) ≤
      c₀ * T₁ - c₁ * T₀ := by
    have h1 := mul_le_mul_of_nonneg_right hlow hT₁pos.le
    have h2 := mul_le_mul_of_nonneg_right hup₁ hT₀pos.le
    linarith
  have hS0 : 0 ≤ S := hS ▸ Nat.cast_nonneg _
  have hSR : R / 64 ≤ S := by
    have h2R := mul_le_mul_of_nonneg_left (show T₀ + T₁ ≤ 2 * R by linarith [hT₀.2, hT₁.2])
      (show (0 : ℝ) ≤ 2 * S by linarith)
    have h4 : R * (R / 64) ≤ R * S := by linarith
    exact le_of_mul_le_mul_left h4 hRpos
  refine ⟨hS ▸ hSR, ?_⟩
  -- frequency mass
  have hLR : 0 ≤ Real.log (R + 1) := Real.log_nonneg (by linarith)
  have hL0 : Real.log T₀ ≤ Real.log (R + 1) := Real.log_le_log hT₀pos hT₀.2.le
  have hfreq := freq_core hRpos hT₀.1.le hSR hb₀.1 hup₀ hU hL0 hLR
  obtain ⟨X, hX⟩ : ∃ X, X = (64 * Real.log (R + 1) + 2 * Real.pi) / R := ⟨_, rfl⟩
  rw [← hX] at hfreq ⊢
  have hXpos : 0 < X := hX ▸ div_pos (by linarith [Real.pi_pos]) hRpos
  rw [hD, two_pi_mul_density] at hfreq
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j => A.datum.freq j ≤ 2 * X) (fun j => (A.datum.P.degreeOf j : ℝ))
  have hfast : ∑ j ∈ Finset.univ.filter (fun j => ¬ A.datum.freq j ≤ 2 * X),
      (A.datum.P.degreeOf j : ℝ) * (2 * X) ≤
      ∑ j ∈ Finset.univ.filter (fun j => ¬ A.datum.freq j ≤ 2 * X),
        (A.datum.P.degreeOf j : ℝ) * A.datum.freq j :=
    Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (not_le.mp (Finset.mem_filter.mp hj).2).le (Nat.cast_nonneg _)
  have hsub : ∑ j ∈ Finset.univ.filter (fun j => ¬ A.datum.freq j ≤ 2 * X),
      (A.datum.P.degreeOf j : ℝ) * A.datum.freq j ≤
      ∑ j, (A.datum.P.degreeOf j : ℝ) * A.datum.freq j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => mul_nonneg (Nat.cast_nonneg _) (A.datum.freq_pos j).le
  rw [← Finset.sum_mul] at hfast
  have hfastX : (∑ j ∈ Finset.univ.filter (fun j => ¬ A.datum.freq j ≤ 2 * X),
      (A.datum.P.degreeOf j : ℝ)) * X ≤ S / 2 * X := by
    linarith
  have hfast' := le_of_mul_le_mul_right hfastX hXpos
  rw [← degSum_cast, ← hS] at hsplit
  linarith

/-- Some variable of an approximating datum has frequency at most `2 (64 log (R+1) + 2π)/R`. -/
theorem exists_slow_variable {E : ℂ → ℂ} (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ ε > 0, ∀ A : LYApprox,
      (∀ z ∈ closedBall (0 : ℂ) (R + 2), ‖A.sect z - E z * XiC z‖ ≤ ε) →
      ∃ j, A.datum.freq j ≤ 2 * ((64 * Real.log (R + 1) + 2 * Real.pi) / R) := by
  classical
  obtain ⟨R₀, hR₀, hlaw⟩ := exists_resolution_law hE hEne
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨ε, hε, h⟩ := hlaw R hR
  refine ⟨ε, hε, fun A hA => ?_⟩
  obtain ⟨h1, h2⟩ := h A hA
  have hpos : (0 : ℝ) < ∑ j ∈ Finset.univ.filter
      (fun j => A.datum.freq j ≤ 2 * ((64 * Real.log (R + 1) + 2 * Real.pi) / R)),
        (A.datum.P.degreeOf j : ℝ) := by
    have : 0 < R / 64 := by linarith
    linarith
  obtain ⟨j, hj, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

/-- A rational `q > 1` satisfies `log q ≥ 1/(den q + 1)`. -/
theorem inv_den_add_one_le_log {q : ℚ} (hq : 1 < q) :
    1 / ((q.den : ℝ) + 1) ≤ Real.log q := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hdQ : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hlt : (q.den : ℚ) < q.num := by
    have h := hq
    rw [← Rat.num_div_den q, lt_div_iff₀ hdQ, one_mul] at h
    exact h
  have hnumZ : (q.den : ℤ) + 1 ≤ q.num := by
    have : (q.den : ℤ) < q.num := by exact_mod_cast hlt
    omega
  have hnumR : (q.den : ℝ) + 1 ≤ q.num := by exact_mod_cast hnumZ
  have hqR : (1 : ℝ) + 1 / q.den ≤ (q : ℝ) := by
    rw [Rat.cast_def, le_div_iff₀ hd]
    have : (1 + 1 / (q.den : ℝ)) * q.den = q.den + 1 := by field_simp
    linarith
  have hpos : (0 : ℝ) < 1 + 1 / q.den := by positivity
  have h1 := Real.one_sub_inv_le_log_of_pos hpos
  have h2 := Real.log_le_log hpos hqR
  have h3 : 1 - (1 + 1 / (q.den : ℝ))⁻¹ = 1 / ((q.den : ℝ) + 1) := by
    field_simp
    ring
  linarith

/-- **Length law for rational fields.**  If every variable of the datum is a rational field
`q^{−iz}`, `q > 1`, then some `q` has denominator at least `R / (2 (64 log (R+1) + 2π)) − 1`. -/
theorem exists_den_ge_of_rational_freq {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hEne : ∀ z, E z ≠ 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ ε > 0, ∀ A : LYApprox, ∀ q : A.ι → ℚ,
      (∀ j, 1 < q j ∧ A.datum.freq j = Real.log (q j)) →
      (∀ z ∈ closedBall (0 : ℂ) (R + 2), ‖A.sect z - E z * XiC z‖ ≤ ε) →
      ∃ j, R / (2 * (64 * Real.log (R + 1) + 2 * Real.pi)) ≤ ((q j).den : ℝ) + 1 := by
  obtain ⟨R₀, hR₀, hslow⟩ := exists_slow_variable hE hEne
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨ε, hε, h⟩ := hslow R hR
  refine ⟨ε, hε, fun A q hq hA => ?_⟩
  obtain ⟨j, hj⟩ := h A hA
  refine ⟨j, ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR
  have hL : 0 ≤ Real.log (R + 1) := Real.log_nonneg (by linarith)
  have hK : 0 < 2 * (64 * Real.log (R + 1) + 2 * Real.pi) := by
    have := Real.pi_pos
    positivity
  have hlog := inv_den_add_one_le_log (hq j).1
  rw [← (hq j).2] at hlog
  have hd : (0 : ℝ) < ((q j).den : ℝ) + 1 := by positivity
  have hle : 1 / (((q j).den : ℝ) + 1) ≤ 2 * ((64 * Real.log (R + 1) + 2 * Real.pi) / R) :=
    hlog.trans hj
  rw [div_le_iff₀ hK]
  rw [div_le_iff₀ hd] at hle
  have e : 2 * ((64 * Real.log (R + 1) + 2 * Real.pi) / R) * (((q j).den : ℝ) + 1) * R =
      2 * (64 * Real.log (R + 1) + 2 * Real.pi) * (((q j).den : ℝ) + 1) := by
    field_simp
  have := mul_le_mul_of_nonneg_right hle hRpos.le
  nlinarith

end

end RHTower.LeeYangCount
