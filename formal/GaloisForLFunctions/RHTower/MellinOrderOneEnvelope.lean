import GaloisForLFunctions.RHTower.CompletedZetaGrowth
import GaloisForLFunctions.HTGeometry.OrderOneEnvelope
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Order-one envelopes for Mellin transforms of theta-type kernels

A kernel with exponential decay at both ends of `(0,∞)` has a Mellin transform of order at most
one.  This packages the modulus estimate `intbound_of_decay` as membership in the growth class
`OrderOneEnvelope`, and supplies the two-sided decay estimate for the modified kernel of an
abstract functional-equation pair from pointwise exponential bounds on its two members.

The head normalization is `t^{-1/2}`.  A pair of weight `k > 1/2` produces the head factor
`t^{-k}`; the excess power is absorbed into the `e^{-p/t}` factor, since `u^m e^{-cu} ≤ e^{m²/c}`
for `u ≥ 1`.
-/

open Filter Set MeasureTheory Complex
open scoped Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- A power is dominated by an exponential on `[1,∞)`: `u ^ m e^{-c u} ≤ e^{m²/c}`.  Writing
`u = v²` and using `log v ≤ v - 1`, the exponent is at most `2mv - cv²`, whose maximum is `m²/c`. -/
theorem rpow_mul_exp_neg_le {m c u : ℝ} (hm : 0 ≤ m) (hc : 0 < c) (hu : 1 ≤ u) :
    u ^ m * Real.exp (-(c * u)) ≤ Real.exp (m ^ 2 / c) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hv : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  have hvnn : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hv1 : 1 ≤ Real.sqrt u := by nlinarith
  have hlogv : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hlogu : Real.log u = 2 * Real.log (Real.sqrt u) := by
    rw [Real.log_sqrt hu0.le]; ring
  have hquad : ∀ v : ℝ, 2 * m * v - c * v ^ 2 ≤ m ^ 2 / c := by
    intro v
    rw [le_div_iff₀ hc]
    nlinarith [sq_nonneg (c * v - m)]
  have hq : 2 * m * Real.sqrt u - c * u ≤ m ^ 2 / c := by
    have hqv := hquad (Real.sqrt u)
    rwa [hv] at hqv
  have hkey : Real.log u * m + -(c * u) ≤ m ^ 2 / c := by
    rw [hlogu]
    nlinarith
  rw [Real.rpow_def_of_pos hu0, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hkey

/-- Absorption of a head power exceeding the normalization `t^{-1/2}` into the `e^{-p/t}` factor. -/
theorem head_bound_absorb {A C p k t : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hp : 0 < p)
    (hk : 1 / 2 ≤ k) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    A * (1 / t) ^ k * (C * Real.exp (-(p / t)))
      ≤ (A * C * Real.exp ((k - 1 / 2) ^ 2 / (p / 2))) * t ^ (-(1 : ℝ) / 2) *
        Real.exp (-(p / 2 / t)) := by
  set u : ℝ := 1 / t with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ ht0]; linarith
  have hsplit : u ^ k = u ^ ((1 : ℝ) / 2) * u ^ (k - 1 / 2) := by
    rw [← Real.rpow_add hu0]; ring_nf
  have hexp : Real.exp (-(p / t)) = Real.exp (-(p / 2 / t)) * Real.exp (-(p / 2 * u)) := by
    rw [← Real.exp_add, hu]
    congr 1
    field_simp
    ring
  have habs : u ^ (k - 1 / 2) * Real.exp (-(p / 2 * u)) ≤ Real.exp ((k - 1 / 2) ^ 2 / (p / 2)) :=
    rpow_mul_exp_neg_le (by linarith) (by linarith) hu1
  have hhalf : u ^ ((1 : ℝ) / 2) = t ^ (-(1 : ℝ) / 2) := by
    rw [hu, one_div t, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le]
    norm_num
  have hAC : 0 ≤ A * C := mul_nonneg hA hC
  have hbase : 0 ≤ u ^ ((1 : ℝ) / 2) * Real.exp (-(p / 2 / t)) := by positivity
  calc A * u ^ k * (C * Real.exp (-(p / t)))
      = (A * C) * (u ^ ((1 : ℝ) / 2) * Real.exp (-(p / 2 / t))) *
          (u ^ (k - 1 / 2) * Real.exp (-(p / 2 * u))) := by
        rw [hsplit, hexp]; ring
    _ ≤ (A * C) * (u ^ ((1 : ℝ) / 2) * Real.exp (-(p / 2 / t))) *
          Real.exp ((k - 1 / 2) ^ 2 / (p / 2)) := by
        exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (A * C * Real.exp ((k - 1 / 2) ^ 2 / (p / 2))) * t ^ (-(1 : ℝ) / 2) *
          Real.exp (-(p / 2 / t)) := by rw [← hhalf]; ring

/-- **Order-one envelope of a Mellin transform.**  A kernel with exponential decay at both ends has
a Mellin transform in the order-one growth class.  The modulus of the transform is bounded by
`∫₀^∞ t^{Re s - 1} ‖F t‖ dt`, and `intbound_of_decay` bounds that by an order-one envelope in
`|Re s| ≤ ‖s‖`. -/
theorem mellin_orderOneEnvelope_of_decay (F : ℝ → ℂ) {C₀ p : ℝ} (hp : 0 < p) (hC₀ : 0 ≤ C₀)
    (hdtop : ∀ t : ℝ, 1 ≤ t → ‖F t‖ ≤ C₀ * Real.exp (-(p * t)))
    (hdhead : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖F t‖ ≤ C₀ * t ^ (-(1 : ℝ) / 2) * Real.exp (-(p / t))) :
    OrderOneEnvelope (mellin F) := by
  obtain ⟨C, hC, hb⟩ := intbound_of_decay F C₀ p hp hC₀ hdtop hdhead
  refine ⟨C, hC, fun s => ?_⟩
  have hstep1 : ‖mellin F s‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * ‖F t‖ := by
    rw [mellin]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have htpos : (0 : ℝ) < t := ht
    show ‖(t : ℂ) ^ (s - 1) • F t‖ = t ^ (s.re - 1) * ‖F t‖
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, sub_re, one_re]
  refine hstep1.trans ((hb s.re).trans (Real.exp_le_exp.mpr ?_))
  rw [orderOneWeight]
  have hσ : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hσnn : 0 ≤ |s.re| := abs_nonneg _
  have hsnn : 0 ≤ ‖s‖ := norm_nonneg s
  have hlog : Real.log (2 + |s.re|) ≤ Real.log (2 + ‖s‖) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlognn : 0 ≤ Real.log (2 + |s.re|) := Real.log_nonneg (by linarith)
  nlinarith [mul_le_mul (show (1 : ℝ) + |s.re| ≤ 1 + ‖s‖ by linarith) hlog hlognn
    (show (0 : ℝ) ≤ 1 + ‖s‖ by linarith), hC.le,
    mul_nonneg (show (0 : ℝ) ≤ 1 + |s.re| by linarith) hlognn]

section FEPair

variable (P : WeakFEPair ℂ)

/-- On `(1,∞)` the modified kernel is the centered kernel. -/
theorem f_modif_of_one_lt {t : ℝ} (ht : 1 < t) : P.f_modif t = P.f t - P.f₀ := by
  rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr ht),
    indicator_of_notMem (notMem_Ioo_of_ge ht.le), add_zero]

/-- On `(1,∞)` the modified partner kernel is the centered partner kernel. -/
theorem g_modif_of_one_lt {t : ℝ} (ht : 1 < t) : P.g_modif t = P.g t - P.g₀ := by
  rw [WeakFEPair.g_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr ht),
    indicator_of_notMem (notMem_Ioo_of_ge ht.le), add_zero]

/-- The modified kernel vanishes at `1`. -/
theorem f_modif_one : P.f_modif 1 = 0 := by
  simp [WeakFEPair.f_modif]

/-- **Two-sided exponential decay of the modified kernel.**  Pointwise exponential decay of the two
centered members of a functional-equation pair produces the head/tail estimate consumed by
`mellin_orderOneEnvelope_of_decay`.  The tail is immediate; the head comes from the kernel
functional equation `f_modif (1/x) = (ε x^k) • g_modif x`, whose excess power `t^{-k}` beyond the
normalization `t^{-1/2}` is absorbed into the exponential. -/
theorem weakFEPair_f_modif_decay {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p) (hk : 1 / 2 ≤ P.k)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖P.f t - P.f₀‖ ≤ C * Real.exp (-(p * t)))
    (hg : ∀ t : ℝ, 1 ≤ t → ‖P.g t - P.g₀‖ ≤ C * Real.exp (-(p * t))) :
    ∃ C₀ q : ℝ, 0 ≤ C₀ ∧ 0 < q ∧
      (∀ t : ℝ, 1 ≤ t → ‖P.f_modif t‖ ≤ C₀ * Real.exp (-(q * t))) ∧
      (∀ t : ℝ, 0 < t → t ≤ 1 → ‖P.f_modif t‖ ≤ C₀ * t ^ (-(1 : ℝ) / 2) * Real.exp (-(q / t))) := by
  set A : ℝ := ‖P.ε‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  set C₀ : ℝ := max C (A * C * Real.exp ((P.k - 1 / 2) ^ 2 / (p / 2))) with hC₀def
  have hC₀ : 0 ≤ C₀ := le_trans hC (le_max_left _ _)
  refine ⟨C₀, p / 2, hC₀, by linarith, ?_, ?_⟩
  · intro t ht
    have hmono : Real.exp (-(p * t)) ≤ Real.exp (-(p / 2 * t)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    rcases eq_or_lt_of_le ht with heq | hlt
    · rw [← heq, f_modif_one]
      simp only [norm_zero]
      positivity
    · rw [f_modif_of_one_lt P hlt]
      calc ‖P.f t - P.f₀‖ ≤ C * Real.exp (-(p * t)) := hf t ht
        _ ≤ C₀ * Real.exp (-(p / 2 * t)) :=
            mul_le_mul (le_max_left _ _) hmono (Real.exp_pos _).le hC₀
  · intro t ht0 ht1
    rcases eq_or_lt_of_le ht1 with heq | hlt
    · rw [heq, f_modif_one]
      simp only [norm_zero]
      positivity
    · have hu0 : (0 : ℝ) < 1 / t := by positivity
      have hu1 : (1 : ℝ) < 1 / t := by rw [lt_div_iff₀ ht0]; linarith
      have hFE := P.hf_modif_FE (1 / t) hu0
      rw [one_div_one_div] at hFE
      rw [hFE, g_modif_of_one_lt P hu1, norm_smul, norm_mul]
      have hrpow : ‖(((1 / t) ^ P.k : ℝ) : ℂ)‖ = (1 / t) ^ P.k := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      rw [hrpow]
      have habs := head_bound_absorb (A := A) (C := C) (p := p) (k := P.k) (t := t)
        hA0 hC hp hk ht0 ht1
      have hstep : A * (1 / t) ^ P.k * ‖P.g (1 / t) - P.g₀‖
          ≤ A * (1 / t) ^ P.k * (C * Real.exp (-(p / t))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := hg (1 / t) hu1.le
        rwa [show p * (1 / t) = p / t by ring] at this
      refine le_trans hstep (le_trans habs ?_)
      have hmax : A * C * Real.exp ((P.k - 1 / 2) ^ 2 / (p / 2)) ≤ C₀ := le_max_right _ _
      have hnn : 0 ≤ t ^ (-(1 : ℝ) / 2) * Real.exp (-(p / 2 / t)) := by positivity
      nlinarith [hnn, hmax]

/-- **Two-sided exponential decay of the kernel of a pair with no constant terms.**  When the
constant terms vanish the kernel itself already has the head/tail shape: the tail is the hypothesis,
and the head comes from the functional equation `f (1/x) = (ε x^k) • g x`. -/
theorem weakFEPair_f_decay {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p) (hk : 1 / 2 ≤ P.k)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖P.f t‖ ≤ C * Real.exp (-(p * t)))
    (hg : ∀ t : ℝ, 1 ≤ t → ‖P.g t‖ ≤ C * Real.exp (-(p * t))) :
    ∃ C₀ q : ℝ, 0 ≤ C₀ ∧ 0 < q ∧
      (∀ t : ℝ, 1 ≤ t → ‖P.f t‖ ≤ C₀ * Real.exp (-(q * t))) ∧
      (∀ t : ℝ, 0 < t → t ≤ 1 → ‖P.f t‖ ≤ C₀ * t ^ (-(1 : ℝ) / 2) * Real.exp (-(q / t))) := by
  set A : ℝ := ‖P.ε‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  set C₀ : ℝ := max C (A * C * Real.exp ((P.k - 1 / 2) ^ 2 / (p / 2))) with hC₀def
  have hC₀ : 0 ≤ C₀ := le_trans hC (le_max_left _ _)
  refine ⟨C₀, p / 2, hC₀, by linarith, ?_, ?_⟩
  · intro t ht
    have hmono : Real.exp (-(p * t)) ≤ Real.exp (-(p / 2 * t)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    calc ‖P.f t‖ ≤ C * Real.exp (-(p * t)) := hf t ht
      _ ≤ C₀ * Real.exp (-(p / 2 * t)) :=
          mul_le_mul (le_max_left _ _) hmono (Real.exp_pos _).le hC₀
  · intro t ht0 ht1
    have hu0 : (0 : ℝ) < 1 / t := by positivity
    have hu1 : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
    have hFE := P.h_feq (1 / t) hu0
    rw [one_div_one_div] at hFE
    rw [hFE, norm_smul, norm_mul]
    have hrpow : ‖(((1 / t) ^ P.k : ℝ) : ℂ)‖ = (1 / t) ^ P.k := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
    rw [hrpow]
    have habs := head_bound_absorb (A := A) (C := C) (p := p) (k := P.k) (t := t)
      hA0 hC hp hk ht0 ht1
    have hstep : A * (1 / t) ^ P.k * ‖P.g (1 / t)‖
        ≤ A * (1 / t) ^ P.k * (C * Real.exp (-(p / t))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hgb := hg (1 / t) hu1
      rwa [show p * (1 / t) = p / t by ring] at hgb
    refine le_trans hstep (le_trans habs ?_)
    have hmax : A * C * Real.exp ((P.k - 1 / 2) ^ 2 / (p / 2)) ≤ C₀ := le_max_right _ _
    have hnn : 0 ≤ t ^ (-(1 : ℝ) / 2) * Real.exp (-(p / 2 / t)) := by positivity
    nlinarith [hnn, hmax]

end FEPair

end RHTower
