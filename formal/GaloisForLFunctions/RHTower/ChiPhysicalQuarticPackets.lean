import GaloisForLFunctions.RHTower.ChiDegreeFourCoherentPackets
import GaloisForLFunctions.RHTower.ChiPhysicalStationaryKernel

/-!
# Signed physical fourth-grade packets

The complete actual chi-four kernel inherits the coherent integer root phase,
with exact common Fresnel orientation and the entire source remainder. Full
nonnegative tensor packets retain a positive mass after rotation. In the
original coordinates their real physical mass is negative at large scales.
No cutoff transition, complementary physical term or coefficient is removed.
These packet signs do not settle the complete mixed-grade self-target form.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
open RHTower
namespace GaloisForLFunctions.RHTower

private theorem quartic_root_mem_box {N H p q r s : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (hp : p ∈ Icc N (N + H)) (hq : q ∈ Icc N (N + H))
    (hr : r ∈ Icc N (N + H)) (hs : s ∈ Icc N (N + H)) :
    chiDegreeFourRoot p q r s ∈ Icc N (N + H) := by
  have hpair {x y : ℝ} (hx : x ∈ Icc N (N + H)) (hy : y ∈ Icc N (N + H)) :
      Real.sqrt (x * y) ∈ Icc N (N + H) := by
    constructor
    · apply Real.le_sqrt_of_sq_le
      simpa only [pow_two] using mul_le_mul hx.1 hy.1 hN.le (hN.le.trans hx.1)
    · apply (Real.sqrt_le_left (by positivity : 0 ≤ N + H)).mpr
      simpa only [pow_two] using mul_le_mul hx.2 hy.2 (hN.le.trans hy.1) (by positivity : 0 ≤ N + H)
  exact hpair (hpair hp hq) (hpair hr hs)

/-- Physical height centered on a common quartic integer packet. -/
def physicalDegreeFourScale (N : ℝ) : ℝ := (4 * Real.pi / 3) * N

/-- Both full source remainders, uniformly over the quartic packet. -/
def physicalDegreeFourEntryBudget (N Cm Ce : ℝ) : ℝ :=
  Cm / (4 * Real.sqrt (8 * Real.pi * N)) +
    (6 / Real.sqrt (4 / (100 * physicalDegreeFourScale N))) *
      (208 / physicalDegreeFourScale N) * Ce

/-- Literal complete chi-four kernel with the four source logarithmic frequencies. -/
def physicalDegreeFourKernel (N : ℝ) (p q r s : ℕ) : ℂ :=
  ∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
    (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
      (zetaChi (linePt t) ^ (4 : ℤ) *
        Complex.exp (((((Real.log p + Real.log q + Real.log r + Real.log s) * t : ℝ) : ℂ) * I)))

private theorem quartic_window_plateau {N G H : ℝ} (hN : 0 < N) (hH : H ≤ N / 6)
    (hG : G ∈ Icc N (N + H)) :
    bagPhysicalHeightWindow (2 * Real.pi * G / physicalDegreeFourScale N) = 1 ∧
      2 * Real.pi * G / physicalDegreeFourScale N ∈ Icc (1 / 2 : ℝ) 4 := by
  have he : 2 * Real.pi * G / physicalDegreeFourScale N = (3 / 2) * (G / N) := by
    unfold physicalDegreeFourScale
    field_simp [Real.pi_ne_zero]
    ring
  have hlo : (3 / 2 : ℝ) ≤ (3 / 2) * (G / N) := by
    have hh : (1 : ℝ) ≤ G / N := (le_div_iff₀ hN).mpr (by simpa using hG.1)
    linarith only [hh]
  have hhi : (3 / 2 : ℝ) * (G / N) ≤ 7 / 4 := by
    have hh : G / N ≤ 7 / 6 := (div_le_iff₀ hN).mpr (by linarith only [hG.2, hH])
    linarith only [hh]
  rw [he]
  constructor
  · apply bagPhysicalHeightWindow.one_of_mem_closedBall
    change dist ((3 / 2) * (G / N)) (3 / 2) ≤ 1 / 4
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith only [hhi]
  · exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

/-- Exact grade-four Fresnel orientation and amplitude on the source plateau. -/
theorem physicalChiStationaryMain_four_packet_eq {N H G : ℝ}
    (hN : 0 < N) (hH : H ≤ N / 6) (hG : G ∈ Icc N (N + H)) :
    physicalChiStationaryMain (physicalDegreeFourScale N) (2 * Real.pi * G) 4 =
      bourgainOscillation (3 * Real.pi / 4) *
        ((Real.pi * Real.sqrt G : ℝ) : ℂ) * bourgainOscillation (8 * Real.pi * G) := by
  have hG0 := hN.trans_le hG.1
  have ha0 : 0 < 2 * Real.pi * G := by positivity
  have hamp : (2 * Real.pi * G) * Real.sqrt (2 * Real.pi / (4 * (2 * Real.pi * G))) =
      Real.pi * Real.sqrt G := by
    calc
      _ = Real.sqrt ((2 * Real.pi * G) ^ 2 * (2 * Real.pi / (4 * (2 * Real.pi * G)))) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha0.le]
      _ = Real.sqrt (Real.pi ^ 2 * G) := by
        congr 1
        field_simp
        ring
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq Real.pi_pos.le]
  have hphase : bourgainOscillation (Real.pi / 4) ^ (4 : ℤ) *
      Complex.exp (I * (((4 * (2 * Real.pi * G) - Real.pi / 4 : ℝ) : ℂ))) =
      bourgainOscillation (3 * Real.pi / 4) * bourgainOscillation (8 * Real.pi * G) := by
    simp only [bourgainOscillation, zpow_ofNat, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold physicalChiStationaryMain
  norm_num only [Int.cast_ofNat]
  rw [(quartic_window_plateau hN hH hG).1, Complex.ofReal_one, mul_one]
  have hampC := congrArg (fun x : ℝ => (x : ℂ)) hamp
  push_cast at hampC
  calc
    _ = (bourgainOscillation (Real.pi / 4) ^ (4 : ℤ) *
        Complex.exp (I * (((4 * (2 * Real.pi * G) - Real.pi / 4 : ℝ) : ℂ)))) *
        (((2 * Real.pi * G : ℝ) : ℂ) * (Real.sqrt (2 * Real.pi / (4 * (2 * Real.pi * G))) : ℂ)) := by ring
    _ = _ := by
      rw [hphase]
      push_cast
      rw [hampC]
      ring

/-- The complete physical quartic kernel has its literal root-phase main and
both full remainders, with constants supplied by the actual chi source. -/
theorem exists_physicalDegreeFourKernel_entry_error :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ N H : ℝ, 0 < N → 0 ≤ H → H ≤ N / 6 →
      4 ≤ physicalDegreeFourScale N → ∀ p q r s : ℕ,
      (p : ℝ) ∈ Icc N (N + H) → (q : ℝ) ∈ Icc N (N + H) →
      (r : ℝ) ∈ Icc N (N + H) → (s : ℝ) ∈ Icc N (N + H) →
      ‖physicalDegreeFourKernel N p q r s -
        bourgainOscillation (3 * Real.pi / 4) *
          ((Real.pi * Real.sqrt (chiDegreeFourRoot p q r s) : ℝ) : ℂ) *
            bourgainOscillation (8 * Real.pi * chiDegreeFourRoot p q r s)‖ ≤
        physicalDegreeFourEntryBudget N Cm Ce := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_complete_physical_chi_positiveGrade_kernel
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro N H hN hH hHN hT p q r s hp hq hr hs
  let G := chiDegreeFourRoot p q r s
  have hG : G ∈ Icc N (N + H) := quartic_root_mem_box hN hH hp hq hr hs
  have hG0 : 0 < G := hN.trans_le hG.1
  have ha : 0 < 2 * Real.pi * G := by positivity
  have hlog : 4 * Real.log ((2 * Real.pi * G) / (2 * Real.pi)) =
      Real.log p + Real.log q + Real.log r + Real.log s := by
    rw [mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    exact four_mul_log_chiDegreeFourRoot (hN.trans_le hp.1) (hN.trans_le hq.1)
      (hN.trans_le hr.1) (hN.trans_le hs.1)
  have hk := hb (physicalDegreeFourScale N) (2 * Real.pi * G) hT ha
    (quartic_window_plateau hN hHN hG).2 4 (by norm_num)
  norm_num only [Int.cast_ofNat] at hk
  rw [hlog, physicalChiStationaryMain_four_packet_eq hN hHN hG] at hk
  have hfirst : (2 * Real.pi * G) * Cm /
      (4 * (2 * Real.pi * G) * Real.sqrt (4 * (2 * Real.pi * G))) ≤
      Cm / (4 * Real.sqrt (8 * Real.pi * N)) := by
    have he : (2 * Real.pi * G) * Cm /
        (4 * (2 * Real.pi * G) * Real.sqrt (4 * (2 * Real.pi * G))) =
        Cm / (4 * Real.sqrt (8 * Real.pi * G)) := by
      rw [show 4 * (2 * Real.pi * G) = 8 * Real.pi * G by ring]
      field_simp
      ring
    rw [he]
    apply div_le_div_of_nonneg_left hCm.le (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hG.1 (by positivity))
  exact hk.trans (by
    dsimp only [physicalDegreeFourEntryBudget]
    exact add_le_add hfirst le_rfl)

/-- Common phase alignment survives in the literal physical chi-four kernel.
Every source remainder is subtracted before asserting a directional lower bound. -/
theorem exists_physicalDegreeFourKernel_oriented_lower :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ N H : ℝ, 0 < N → 0 ≤ H → H ≤ N / 6 →
      4 ≤ physicalDegreeFourScale N → 2 * Real.pi * H ^ 2 / N ≤ 1 →
      ∀ p q r s : ℕ,
      (p : ℝ) ∈ Icc N (N + H) → (q : ℝ) ∈ Icc N (N + H) →
      (r : ℝ) ∈ Icc N (N + H) → (s : ℝ) ∈ Icc N (N + H) →
      Real.pi * Real.sqrt N * (1 - 2 * Real.pi * H ^ 2 / N) -
        physicalDegreeFourEntryBudget N Cm Ce ≤
          (bourgainOscillation (-(3 * Real.pi / 4)) * physicalDegreeFourKernel N p q r s).re := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_physicalDegreeFourKernel_entry_error
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro N H hN hH hHN hT heps p q r s hp hq hr hs
  let G := chiDegreeFourRoot p q r s
  let B := Real.pi * Real.sqrt G
  let U := bourgainOscillation (-(3 * Real.pi / 4))
  let V := bourgainOscillation (3 * Real.pi / 4)
  let P := bourgainOscillation (8 * Real.pi * G)
  have hUV : U * V = 1 := by
    dsimp only [U, V, bourgainOscillation]
    rw [← Complex.exp_add]
    have he : I * ((-(3 * Real.pi / 4) : ℝ) : ℂ) + I * ((3 * Real.pi / 4 : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [he, Complex.exp_zero]
  have hmain : U * (V * (B : ℂ) * P) = (B : ℂ) * P := by
    rw [← mul_assoc, ← mul_assoc, hUV, one_mul]
  have hk := hb N H hN hH hHN hT p q r s hp hq hr hs
  have hrot : ‖U * physicalDegreeFourKernel N p q r s - (B : ℂ) * P‖ ≤
      physicalDegreeFourEntryBudget N Cm Ce := by
    calc
      _ = ‖U * (physicalDegreeFourKernel N p q r s - V * (B : ℂ) * P)‖ := by
        rw [mul_sub, hmain]
      _ = ‖physicalDegreeFourKernel N p q r s - V * (B : ℂ) * P‖ := by
        rw [norm_mul, show ‖U‖ = 1 from norm_bourgainOscillation _, one_mul]
      _ ≤ _ := hk
  have hd := (Complex.abs_re_le_norm (U * physicalDegreeFourKernel N p q r s - (B : ℂ) * P)).trans hrot
  have hd' := (abs_le.mp hd).1
  have hBP : ((B : ℂ) * P).re = B * P.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.sub_re, hBP] at hd'
  have hp' := norm_chiDegreeFourRoot_phase_sub_one_le hN hH p q r s hp hq hr hs
  have hrp := (Complex.abs_re_le_norm (P - 1)).trans hp'
  have hrp' := (abs_le.mp hrp).1
  simp only [Complex.sub_re, Complex.one_re] at hrp'
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBp := mul_le_mul_of_nonneg_left hrp' hB
  have hG := quartic_root_mem_box hN hH hp hq hr hs
  have hBN : Real.pi * Real.sqrt N ≤ B :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hG.1) Real.pi_pos.le
  have hBN' := mul_le_mul_of_nonneg_right hBN (sub_nonneg.mpr heps)
  change _ ≤ (U * physicalDegreeFourKernel N p q r s).re
  nlinarith only [hd', hBp, hBN']

/-- Full fourfold source-frequency packet; arbitrary nonnegative tensor weights
can retain literal masks or correlations within the common box. -/
def physicalDegreeFourPacket (S : Finset ℕ) (w : ℕ → ℕ → ℕ → ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S,
    (w p q r s : ℂ) * Complex.exp
      (((((Real.log p + Real.log q + Real.log r + Real.log s) * t : ℝ) : ℂ) * I))

/-- Exact full physical packet expansion, preserving every term and height. -/
theorem integral_physicalDegreeFourPacket_eq (N : ℝ) (S : Finset ℕ)
    (w : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
      (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
        zetaChi (linePt t) ^ (4 : ℤ) * physicalDegreeFourPacket S w t) =
      ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S,
        (w p q r s : ℂ) * physicalDegreeFourKernel N p q r s := by
  let f : ℕ → ℕ → ℕ → ℕ → ℝ → ℂ := fun p q r s t => (w p q r s : ℂ) *
    ((bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
      (zetaChi (linePt t) ^ (4 : ℤ) * Complex.exp
        (((((Real.log p + Real.log q + Real.log r + Real.log s) * t : ℝ) : ℂ) * I))))
  have hc (p q r s : ℕ) : Continuous (f p q r s) :=
    continuous_const.mul ((Complex.continuous_ofReal.comp
      (bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const _))).mul
      (continuous_zetaChiCriticalGradeIntegrand 4 _))
  calc
    _ = ∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
        ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S, f p q r s t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [physicalDegreeFourPacket, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [f]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun p _ =>
        (continuous_finsetSum _ (fun q _ => continuous_finsetSum _ (fun r _ =>
          continuous_finsetSum _ (fun s _ => hc p q r s)))).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro p _
      rw [intervalIntegral.integral_finsetSum (fun q _ =>
        (continuous_finsetSum _ (fun r _ => continuous_finsetSum _ (fun s _ => hc p q r s))).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro q _
      rw [intervalIntegral.integral_finsetSum (fun r _ =>
        (continuous_finsetSum _ (fun s _ => hc p q r s)).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro r _
      rw [intervalIntegral.integral_finsetSum (fun s _ => (hc p q r s).intervalIntegrable _ _)]
      simp only [f, intervalIntegral.integral_const_mul, physicalDegreeFourKernel]

/-- A complete physical chi-four packet retains its full nonnegative coefficient
mass in one fixed direction, after paying both actual source remainders. -/
theorem exists_physicalDegreeFourPacket_oriented_lower :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ N H : ℝ, 0 < N → 0 ≤ H → H ≤ N / 6 →
      4 ≤ physicalDegreeFourScale N → 2 * Real.pi * H ^ 2 / N ≤ 1 →
      ∀ S : Finset ℕ, (∀ p ∈ S, (p : ℝ) ∈ Icc N (N + H)) →
      ∀ w : ℕ → ℕ → ℕ → ℕ → ℝ,
      (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, ∀ s ∈ S, 0 ≤ w p q r s) →
      (Real.pi * Real.sqrt N * (1 - 2 * Real.pi * H ^ 2 / N) - physicalDegreeFourEntryBudget N Cm Ce) *
        (∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S, w p q r s) ≤
        (bourgainOscillation (-(3 * Real.pi / 4)) *
          (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
            (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
              zetaChi (linePt t) ^ (4 : ℤ) * physicalDegreeFourPacket S w t)).re := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_physicalDegreeFourKernel_oriented_lower
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro N H hN hH hHN hT heps S hS w hw
  rw [integral_physicalDegreeFourPacket_eq]
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro s hs
  have hh := mul_le_mul_of_nonneg_right
    (hb N H hN hH hHN hT heps p q r s (hS p hp) (hS q hq) (hS r hr) (hS s hs))
    (hw p hp q hq r hr s hs)
  have he : (bourgainOscillation (-(3 * Real.pi / 4)) *
      ((w p q r s : ℂ) * physicalDegreeFourKernel N p q r s)).re =
      (bourgainOscillation (-(3 * Real.pi / 4)) * physicalDegreeFourKernel N p q r s).re * w p q r s := by
    rw [show bourgainOscillation (-(3 * Real.pi / 4)) *
        ((w p q r s : ℂ) * physicalDegreeFourKernel N p q r s) =
        (bourgainOscillation (-(3 * Real.pi / 4)) * physicalDegreeFourKernel N p q r s) *
          (w p q r s : ℂ) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [he]
  exact hh

private theorem physicalDegreeFourEntryBudget_le {N Cm Ce : ℝ}
    (hN : 1 ≤ N) (hCm : 0 ≤ Cm) (hCe : 0 ≤ Ce) :
    physicalDegreeFourEntryBudget N Cm Ce ≤ Cm + 6240 * Ce := by
  have hT : 4 ≤ physicalDegreeFourScale N := by
    have hh := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 4 * Real.pi / 3)
    dsimp only [physicalDegreeFourScale]
    nlinarith only [hh, Real.pi_gt_three]
  have hT0 : 0 < physicalDegreeFourScale N := by linarith only [hT]
  have hrT : 0 < Real.sqrt (physicalDegreeFourScale N) := Real.sqrt_pos.mpr hT0
  have hrT1 : 1 ≤ Real.sqrt (physicalDegreeFourScale N) :=
    Real.le_sqrt_of_sq_le (by linarith only [hT])
  have he : (6 / Real.sqrt (4 / (100 * physicalDegreeFourScale N))) *
      (208 / physicalDegreeFourScale N) = 6240 / Real.sqrt (physicalDegreeFourScale N) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
    norm_num only
    calc
      _ = 6240 * (Real.sqrt (physicalDegreeFourScale N) / physicalDegreeFourScale N) := by
        field_simp
        ring
      _ = _ := by rw [Real.sqrt_div_self']; ring
  have hchi : (6 / Real.sqrt (4 / (100 * physicalDegreeFourScale N))) *
      (208 / physicalDegreeFourScale N) ≤ 6240 := by
    rw [he]
    apply (div_le_iff₀ hrT).mpr
    linarith only [hrT1]
  have hrN : 1 ≤ Real.sqrt (8 * Real.pi * N) := by
    apply Real.le_sqrt_of_sq_le
    have hh := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 8 * Real.pi)
    nlinarith only [hh, Real.pi_gt_three]
  have hfirst : Cm / (4 * Real.sqrt (8 * Real.pi * N)) ≤ Cm := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt (8 * Real.pi * N))).mpr
    have hh := mul_nonneg hCm (show 0 ≤ 4 * Real.sqrt (8 * Real.pi * N) - 1 by linarith only [hrN])
    nlinarith only [hh]
  exact add_le_add hfirst (mul_le_mul_of_nonneg_right hchi hCe)

/-- At every sufficiently large physical scale, every coherent nonnegative
quartic packet carries a positive fixed-direction mass in the actual chi integral.
The threshold and all error estimates come from the source, without an assumed
stationary formula or an omitted complementary physical term. -/
theorem exists_physicalDegreeFourPacket_positive :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → 0 ≤ H → H ≤ N / 6 →
      2 * Real.pi * H ^ 2 / N ≤ 1 / 2 →
      ∀ S : Finset ℕ, (∀ p ∈ S, (p : ℝ) ∈ Icc N (N + H)) →
      ∀ w : ℕ → ℕ → ℕ → ℕ → ℝ,
      (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, ∀ s ∈ S, 0 ≤ w p q r s) →
      (Real.pi * Real.sqrt N / 4) * (∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S, w p q r s) ≤
        (bourgainOscillation (-(3 * Real.pi / 4)) *
          (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
            (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
              zetaChi (linePt t) ^ (4 : ℤ) * physicalDegreeFourPacket S w t)).re := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_physicalDegreeFourPacket_oriented_lower
  let B := Cm + 6240 * Ce
  refine ⟨1 + (4 * B / Real.pi) ^ 2, by positivity, ?_⟩
  intro N H hN hH hHN heps S hS w hw
  have hN1 : 1 ≤ N := by nlinarith only [hN, sq_nonneg (4 * B / Real.pi)]
  have hN0 : 0 < N := by linarith only [hN1]
  have hT : 4 ≤ physicalDegreeFourScale N := by
    have hh := mul_le_mul_of_nonneg_left hN1 (by positivity : 0 ≤ 4 * Real.pi / 3)
    dsimp only [physicalDegreeFourScale]
    nlinarith only [hh, Real.pi_gt_three]
  have hr : 4 * B / Real.pi ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (by linarith only [hN])
  have hB : B ≤ Real.pi * Real.sqrt N / 4 := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hr
    nlinarith only [hh]
  have hE := physicalDegreeFourEntryBudget_le hN1 hCm.le hCe.le
  have hmain : Real.pi * Real.sqrt N / 2 ≤
      Real.pi * Real.sqrt N * (1 - 2 * Real.pi * H ^ 2 / N) := by
    have hh := mul_le_mul_of_nonneg_left heps (by positivity : 0 ≤ Real.pi * Real.sqrt N)
    nlinarith only [hh]
  have hmargin : Real.pi * Real.sqrt N / 4 ≤
      Real.pi * Real.sqrt N * (1 - 2 * Real.pi * H ^ 2 / N) - physicalDegreeFourEntryBudget N Cm Ce := by
    change physicalDegreeFourEntryBudget N Cm Ce ≤ B at hE
    linarith only [hB, hE, hmain]
  have hmass : 0 ≤ ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S, w p q r s :=
    Finset.sum_nonneg fun p hp => Finset.sum_nonneg fun q hq =>
      Finset.sum_nonneg fun r hr => Finset.sum_nonneg fun s hs => hw p hp q hq r hr s hs
  exact (mul_le_mul_of_nonneg_right hmargin hmass).trans
    (hb N H hN0 hH hHN hT (by linarith only [heps]) S hS w hw)

private theorem quartic_orientation_re :
    (bourgainOscillation (3 * Real.pi / 4)).re ≤ -(1 / 2 : ℝ) := by
  have he : (bourgainOscillation (3 * Real.pi / 4)).re = Real.cos (3 * Real.pi / 4) := by
    simp only [bourgainOscillation, Complex.exp_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, sub_zero, zero_add, Real.exp_zero]
  rw [he, show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_four]
  have hh : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  linarith only [hh]

/-- The common quartic orientation is negative in the original real direction.
The actual physical kernel retains this sign, with its entire source error. -/
theorem exists_physicalDegreeFourKernel_real_upper :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ N H : ℝ, 0 < N → 0 ≤ H → H ≤ N / 6 →
      4 ≤ physicalDegreeFourScale N → 2 * Real.pi * H ^ 2 / N ≤ 1 / 4 →
      ∀ p q r s : ℕ,
      (p : ℝ) ∈ Icc N (N + H) → (q : ℝ) ∈ Icc N (N + H) →
      (r : ℝ) ∈ Icc N (N + H) → (s : ℝ) ∈ Icc N (N + H) →
      (physicalDegreeFourKernel N p q r s).re ≤
        -(Real.pi * Real.sqrt N / 4) + physicalDegreeFourEntryBudget N Cm Ce := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_physicalDegreeFourKernel_entry_error
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro N H hN hH hHN hT heps p q r s hp hq hr hs
  let G := chiDegreeFourRoot p q r s
  let B := Real.pi * Real.sqrt G
  let U := bourgainOscillation (3 * Real.pi / 4)
  let P := bourgainOscillation (8 * Real.pi * G)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hk := hb N H hN hH hHN hT p q r s hp hq hr hs
  have herr : ‖physicalDegreeFourKernel N p q r s - U * (B : ℂ)‖ ≤
      physicalDegreeFourEntryBudget N Cm Ce + B * (2 * Real.pi * H ^ 2 / N) := by
    calc
      _ ≤ ‖physicalDegreeFourKernel N p q r s - U * (B : ℂ) * P‖ +
          ‖U * (B : ℂ) * P - U * (B : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ physicalDegreeFourEntryBudget N Cm Ce + B * (2 * Real.pi * H ^ 2 / N) := by
        apply add_le_add hk
        rw [show U * (B : ℂ) * P - U * (B : ℂ) = U * (B : ℂ) * (P - 1) by ring,
          norm_mul, norm_mul, show ‖U‖ = 1 from norm_bourgainOscillation _,
          one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
        exact mul_le_mul_of_nonneg_left
          (norm_chiDegreeFourRoot_phase_sub_one_le hN hH p q r s hp hq hr hs) hB
  have hh := (abs_le.mp ((Complex.abs_re_le_norm
    (physicalDegreeFourKernel N p q r s - U * (B : ℂ))).trans herr)).2
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hh
  have hU := mul_le_mul_of_nonneg_right quartic_orientation_re hB
  have hphase := mul_le_mul_of_nonneg_left heps hB
  have hG := quartic_root_mem_box hN hH hp hq hr hs
  have hBN : Real.pi * Real.sqrt N ≤ B :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hG.1) Real.pi_pos.le
  change U.re * B ≤ -(1 / 2 : ℝ) * B at hU
  nlinarith only [hh, hU, hphase, hBN]

/-- Complete coherent nonnegative quartic packets have negative real physical
mass at every sufficiently large scale. This is a signed source obstruction to
treating all positive chi grades as positive terms of a target minorant. -/
theorem exists_physicalDegreeFourPacket_negative_real :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → 0 ≤ H → H ≤ N / 6 →
      2 * Real.pi * H ^ 2 / N ≤ 1 / 4 →
      ∀ S : Finset ℕ, (∀ p ∈ S, (p : ℝ) ∈ Icc N (N + H)) →
      ∀ w : ℕ → ℕ → ℕ → ℕ → ℝ,
      (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, ∀ s ∈ S, 0 ≤ w p q r s) →
      (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
        (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
          zetaChi (linePt t) ^ (4 : ℤ) * physicalDegreeFourPacket S w t).re ≤
        -(Real.pi * Real.sqrt N / 8) *
          (∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S, w p q r s) := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_physicalDegreeFourKernel_real_upper
  let B := Cm + 6240 * Ce
  refine ⟨1 + (8 * B / Real.pi) ^ 2, by positivity, ?_⟩
  intro N H hN hH hHN heps S hS w hw
  have hN1 : 1 ≤ N := by nlinarith only [hN, sq_nonneg (8 * B / Real.pi)]
  have hN0 : 0 < N := by linarith only [hN1]
  have hT : 4 ≤ physicalDegreeFourScale N := by
    have hh := mul_le_mul_of_nonneg_left hN1 (by positivity : 0 ≤ 4 * Real.pi / 3)
    dsimp only [physicalDegreeFourScale]
    nlinarith only [hh, Real.pi_gt_three]
  have hr : 8 * B / Real.pi ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (by linarith only [hN])
  have hB : B ≤ Real.pi * Real.sqrt N / 8 := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hr
    nlinarith only [hh]
  have hE := physicalDegreeFourEntryBudget_le hN1 hCm.le hCe.le
  change physicalDegreeFourEntryBudget N Cm Ce ≤ B at hE
  rw [integral_physicalDegreeFourPacket_eq]
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro s hs
  have hk := hb N H hN0 hH hHN hT heps p q r s (hS p hp) (hS q hq) (hS r hr) (hS s hs)
  have hk' : (physicalDegreeFourKernel N p q r s).re ≤ -(Real.pi * Real.sqrt N / 8) := by
    linarith only [hk, hE, hB]
  have hh := mul_le_mul_of_nonneg_right hk' (hw p hp q hq r hr s hs)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, mul_comm (w p q r s)] using hh

end GaloisForLFunctions.RHTower
