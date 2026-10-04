import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMain

/-!
# Coherent physical adjacent cubic packets

The exact prime-gap phase keeps every integer triple in a narrow common box
close to the positive real direction. The actual grade-one chi kernel retains
this mass after both complete physical remainders. Arbitrary nonnegative tensor
weights may keep the literal noncontraction mask. No joint cancellation estimate
for the full Gaussian family is assumed or asserted here.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

/-- Physical height placing the common cubic saddle in the actual plateau. -/
def physicalCubicPacketScale (N : ℝ) : ℝ := (4 * Real.pi / 3) * N

/-- Complete grade-one kernel of the adjacent cubic, with two positive and one negative frequency. -/
def physicalCubicPacketKernel (N : ℝ) (p q r : ℕ) : ℂ :=
  ∫ t in physicalCubicPacketScale N..2 * physicalCubicPacketScale N,
    (bagPhysicalHeightWindow (t / physicalCubicPacketScale N) : ℂ) *
      (zetaChi (linePt t) * Complex.exp
        ((((Real.log p + Real.log q - Real.log r) * t : ℝ) : ℂ) * I))

private theorem cubic_packet_saddle_box {N H p q r : ℝ}
    (hN : 0 < N) (hH : 0 ≤ H) (hHN : H ≤ N / 32)
    (hp : p ∈ Icc N (N + H)) (hq : q ∈ Icc N (N + H))
    (hr : r ∈ Icc N (N + H)) :
    p * q / r ∈ Icc (5 * N / 6) (7 * N / 6) := by
  have hr0 : 0 < r := hN.trans_le hr.1
  have hl := mul_le_mul hp.1 hq.1 hN.le (hN.le.trans hp.1)
  have hu := mul_le_mul hp.2 hq.2 (hN.le.trans hq.1) (by positivity : 0 ≤ N + H)
  have hh := mul_le_mul hHN hHN hH (by positivity : 0 ≤ N / 32)
  constructor
  · apply (le_div_iff₀ hr0).mpr
    have hnr := mul_le_mul_of_nonneg_left hr.2 hN.le
    have hnH := mul_le_mul_of_nonneg_left hHN hN.le
    nlinarith only [hl, hnr, hnH, sq_nonneg N]
  · apply (div_le_iff₀ hr0).mpr
    have hnr := mul_le_mul_of_nonneg_left hr.1 hN.le
    have hnH := mul_le_mul_of_nonneg_left hHN hN.le
    nlinarith only [hu, hnr, hnH, hh, sq_nonneg N]

private theorem cubic_packet_plateau {N G : ℝ} (hN : 0 < N)
    (hG : G ∈ Icc (5*N/6) (7*N/6)) :
    bagPhysicalHeightWindow (2*Real.pi*G / physicalCubicPacketScale N) = 1 ∧
      2*Real.pi*G / physicalCubicPacketScale N ∈ Icc (1/2:ℝ) 4 := by
  have he : 2*Real.pi*G / physicalCubicPacketScale N = (3/2)*(G/N) := by
    unfold physicalCubicPacketScale
    field_simp [Real.pi_ne_zero]
    ring
  have hl : (5/4:ℝ) ≤ (3/2)*(G/N) := by
    have hh : (5/6:ℝ) ≤ G/N := (le_div_iff₀ hN).mpr (by linarith only [hG.1])
    linarith only [hh]
  have hu : (3/2)*(G/N) ≤ (7/4:ℝ) := by
    have hh : G/N ≤ (7/6:ℝ) := (div_le_iff₀ hN).mpr (by linarith only [hG.2])
    linarith only [hh]
  rw [he]
  constructor
  · apply bagPhysicalHeightWindow.one_of_mem_closedBall
    change dist ((3/2)*(G/N)) (3/2) ≤ 1/4
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith only [hl, hu]
  · exact ⟨by linarith only [hl], by linarith only [hu]⟩

private theorem cubic_packet_main {N G : ℝ} (hN : 0 < N)
    (hG : G ∈ Icc (5*N/6) (7*N/6)) :
    physicalChiStationaryMain (physicalCubicPacketScale N) (2*Real.pi*G) 1 =
      ((2*Real.pi*Real.sqrt G : ℝ):ℂ) * bourgainOscillation (2*Real.pi*G) := by
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hG.1
  have ha : 0 < 2*Real.pi*G := by positivity
  have hamp : (2*Real.pi*G)*Real.sqrt (2*Real.pi/(2*Real.pi*G)) = 2*Real.pi*Real.sqrt G := by
    calc
      _ = Real.sqrt ((2*Real.pi*G)^2*(2*Real.pi/(2*Real.pi*G))) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]
      _ = Real.sqrt ((2*Real.pi)^2*G) := by congr 1; field_simp
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 2*Real.pi)]
  have hphase : bourgainOscillation (Real.pi/4) *
      Complex.exp (I*((2*Real.pi*G-Real.pi/4:ℝ):ℂ)) = bourgainOscillation (2*Real.pi*G) := by
    unfold bourgainOscillation
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold physicalChiStationaryMain
  simp only [zpow_one, Int.cast_one, one_mul, (cubic_packet_plateau hN hG).1,
    Complex.ofReal_one, mul_one]
  calc
    _ = (((2*Real.pi*G:ℝ):ℂ)*(Real.sqrt (2*Real.pi/(2*Real.pi*G)):ℂ)) *
        (bourgainOscillation (Real.pi/4)*Complex.exp (I*((2*Real.pi*G-Real.pi/4:ℝ):ℂ))) := by ring
    _ = _ := by rw [← Complex.ofReal_mul, hamp, hphase]

/-- Every cubic integer triple in a coherent box has its original phase close to one. -/
theorem norm_physicalCubicPacket_phase_sub_one_le {N H : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (p q r : ℕ) (hp : (p:ℝ) ∈ Icc N (N+H)) (hq : (q:ℝ) ∈ Icc N (N+H))
    (hr : (r:ℝ) ∈ Icc N (N+H)) :
    ‖bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))-1‖ ≤ 2*Real.pi*H^2/N := by
  have hr0 : (0:ℝ) < r := hN.trans_le hr.1
  have hrNat : 0 < r := by exact_mod_cast hr0
  have hpabs : |(p:ℝ)-r| ≤ H := abs_le.mpr ⟨by linarith [hp.1, hr.2], by linarith [hp.2, hr.1]⟩
  have hqabs : |(q:ℝ)-r| ≤ H := abs_le.mpr ⟨by linarith [hq.1, hr.2], by linarith [hq.2, hr.1]⟩
  rw [primeGaussianCubic_phase_recenter p q hrNat]
  calc
    _ = ‖bourgainOscillation (2*Real.pi*(((p:ℝ)-r)*((q:ℝ)-r)/r))-bourgainOscillation 0‖ := by
      simp only [bourgainOscillation, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    _ ≤ |2*Real.pi*(((p:ℝ)-r)*((q:ℝ)-r)/r)| := by
      simpa only [sub_zero] using norm_bourgainOscillation_sub_le (2*Real.pi*(((p:ℝ)-r)*((q:ℝ)-r)/r)) 0
    _ ≤ 2*Real.pi*H^2/N := by
      rw [← mul_div_assoc]
      simp only [abs_div, abs_mul, abs_of_pos hr0, abs_of_pos Real.pi_pos,
        abs_of_pos (by norm_num : (0:ℝ)<2)]
      apply (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul hpabs hqabs (abs_nonneg _) hH) (by positivity)) hr0.le).trans
      simpa only [pow_two] using div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*Real.pi*(H*H)) hN hr.1

/-- Both complete physical errors are uniform on a coherent cubic packet. -/
theorem exists_physicalCubicPacketKernel_error :
    ∃ C : ℝ, 0 < C ∧ ∀ N H : ℝ, 1 ≤ N → 0 ≤ H → H ≤ N/32 →
      ∀ p q r : ℕ, (p:ℝ) ∈ Icc N (N+H) → (q:ℝ) ∈ Icc N (N+H) →
      (r:ℝ) ∈ Icc N (N+H) →
      ‖physicalCubicPacketKernel N p q r -
        ((2*Real.pi*Real.sqrt ((p:ℝ)*q/r):ℝ):ℂ)*bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))‖ ≤ C/Real.sqrt N := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_complete_physical_chi_positiveGrade_kernel
  refine ⟨Cm+3120*Ce, by positivity, ?_⟩
  intro N H hN hH hHN p q r hp hq hr
  have hN0 : 0 < N := by linarith only [hN]
  have hG := cubic_packet_saddle_box hN0 hH hHN hp hq hr
  have hG0 : 0 < (p:ℝ)*q/r := lt_of_lt_of_le (by positivity) hG.1
  have ha : 0 < 2*Real.pi*((p:ℝ)*q/r) := by positivity
  have hTN : N ≤ physicalCubicPacketScale N := by
    unfold physicalCubicPacketScale
    nlinarith only [Real.pi_gt_three, hN0]
  have hT : 4 ≤ physicalCubicPacketScale N := by
    unfold physicalCubicPacketScale
    nlinarith only [Real.pi_gt_three, hN]
  have haN : N ≤ 2*Real.pi*((p:ℝ)*q/r) := by
    have hh := mul_le_mul_of_nonneg_left hG.1 (by positivity : 0 ≤ 2*Real.pi)
    have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hN0.le
    nlinarith only [hh, hpi, hN0]
  have hlog : Real.log ((2*Real.pi*((p:ℝ)*q/r))/(2*Real.pi)) = Real.log p+Real.log q-Real.log r := by
    rw [mul_div_cancel_left₀ _ (by positivity : 2*Real.pi ≠ 0),
      Real.log_div (mul_pos (hN0.trans_le hp.1) (hN0.trans_le hq.1)).ne' (hN0.trans_le hr.1).ne',
      Real.log_mul (hN0.trans_le hp.1).ne' (hN0.trans_le hq.1).ne']
  have hk := hb _ _ hT ha (cubic_packet_plateau hN0 hG).2 1 (by norm_num)
  simp only [Int.cast_one, zpow_one, one_mul, abs_one, mul_one, hlog] at hk
  rw [cubic_packet_main hN0 hG, physicalChiGradeOne_second_error (by linarith only [hT])] at hk
  have hfirst : (2*Real.pi*((p:ℝ)*q/r))*Cm/
      ((2*Real.pi*((p:ℝ)*q/r))*Real.sqrt (2*Real.pi*((p:ℝ)*q/r))) ≤ Cm/Real.sqrt N := by
    rw [mul_div_mul_left Cm _ ha.ne']
    exact div_le_div_of_nonneg_left hCm.le (by positivity) (Real.sqrt_le_sqrt haN)
  have hsecond : (3120*Ce)/Real.sqrt (physicalCubicPacketScale N) ≤ (3120*Ce)/Real.sqrt N :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (Real.sqrt_le_sqrt hTN)
  exact hk.trans (by simpa only [add_div] using add_le_add hfirst hsecond)

/-- Uniform positive real mass of the literal complete cubic kernel, at all large scales. -/
theorem exists_physicalCubicPacketKernel_positive :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → 0 ≤ H → H ≤ N/32 →
      2*Real.pi*H^2/N ≤ 1/4 → ∀ p q r : ℕ,
      (p:ℝ) ∈ Icc N (N+H) → (q:ℝ) ∈ Icc N (N+H) → (r:ℝ) ∈ Icc N (N+H) →
      Real.pi*Real.sqrt N/4 ≤ (physicalCubicPacketKernel N p q r).re := by
  obtain ⟨C, hC, hb⟩ := exists_physicalCubicPacketKernel_error
  refine ⟨1+(4*C/Real.pi)^2, by positivity, ?_⟩
  intro N H hN hH hHN heps p q r hp hq hr
  have hN1 : 1 ≤ N := by nlinarith only [hN, sq_nonneg (4*C/Real.pi)]
  have hN0 : 0 < N := by linarith only [hN1]
  have hroot : 4*C/Real.pi ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by linarith only [hN])
  have hCsmall : C ≤ Real.pi*Real.sqrt N/4 := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hroot
    nlinarith only [hh]
  have herror : C/Real.sqrt N ≤ C := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hN0)).mpr
    have hs : 1 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by simpa using hN1)
    nlinarith only [hs, hC]
  have hG := cubic_packet_saddle_box hN0 hH hHN hp hq hr
  have hG0 : 0 < (p:ℝ)*q/r := lt_of_lt_of_le (by positivity) hG.1
  have hrad : Real.sqrt N/2 ≤ Real.sqrt ((p:ℝ)*q/r) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [Real.sq_sqrt hN0.le, hG.1, hN0.le]
  have hphase := (Complex.abs_re_le_norm
    (bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))-1)).trans
      ((norm_physicalCubicPacket_phase_sub_one_le hN0 hH p q r hp hq hr).trans heps)
  have hphaseL := (abs_le.mp hphase).1
  simp only [Complex.sub_re, Complex.one_re] at hphaseL
  have herr := (Complex.abs_re_le_norm
    (physicalCubicPacketKernel N p q r-
      ((2*Real.pi*Real.sqrt ((p:ℝ)*q/r):ℝ):ℂ)*bourgainOscillation (2*Real.pi*((p:ℝ)*q/r)))).trans
      (hb N H hN1 hH hHN p q r hp hq hr)
  have herrL := (abs_le.mp herr).1
  rw [Complex.sub_re, Complex.re_ofReal_mul] at herrL
  have hm := mul_le_mul_of_nonneg_left hphaseL
    (by positivity : 0 ≤ 2*Real.pi*Real.sqrt ((p:ℝ)*q/r))
  have hrm := mul_le_mul_of_nonneg_left hrad Real.pi_pos.le
  nlinarith only [hm, hrm, herrL, herror, hCsmall,
    mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg N)]

/-- Full adjacent cubic tensor; weights may retain arbitrary masks or correlations. -/
def physicalCubicPacket (S : Finset ℕ) (w : ℕ → ℕ → ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S,
    (w p q r:ℂ)*Complex.exp ((((Real.log p+Real.log q-Real.log r)*t:ℝ):ℂ)*I)

/-- Exact expansion into complete physical entries, at one shared height. -/
theorem integral_physicalCubicPacket_eq (N : ℝ) (S : Finset ℕ) (w : ℕ → ℕ → ℕ → ℝ) :
    (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
      (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
        zetaChi (linePt t)*physicalCubicPacket S w t) =
      ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, (w p q r:ℂ)*physicalCubicPacketKernel N p q r := by
  let f : ℕ → ℕ → ℕ → ℝ → ℂ := fun p q r t => (w p q r:ℂ)*
    ((bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
      (zetaChi (linePt t)*Complex.exp ((((Real.log p+Real.log q-Real.log r)*t:ℝ):ℂ)*I)))
  have hc (p q r : ℕ) : Continuous (f p q r) := by
    have hh := continuous_zetaChiCriticalGradeIntegrand (1:ℤ) (Real.log p+Real.log q-Real.log r)
    simp only [zpow_one] at hh
    exact continuous_const.mul ((Complex.continuous_ofReal.comp
      (bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const _))).mul hh)
  calc
    _ = ∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
        ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, f p q r t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [physicalCubicPacket, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [f]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun p _ =>
        (continuous_finsetSum _ (fun q _ => continuous_finsetSum _ (fun r _ => hc p q r))).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro p _
      rw [intervalIntegral.integral_finsetSum (fun q _ =>
        (continuous_finsetSum _ (fun r _ => hc p q r)).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro q _
      rw [intervalIntegral.integral_finsetSum (fun r _ => (hc p q r).intervalIntegrable _ _)]
      simp only [f, intervalIntegral.integral_const_mul, physicalCubicPacketKernel]

/-- Every nonnegative correlated cubic packet has positive original real mass.
The threshold comes from both actual physical remainders, not a model premise. -/
theorem exists_physicalCubicPacket_positive :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → 0 ≤ H → H ≤ N/32 →
      2*Real.pi*H^2/N ≤ 1/4 → ∀ S : Finset ℕ,
      (∀ p ∈ S, (p:ℝ) ∈ Icc N (N+H)) → ∀ w : ℕ → ℕ → ℕ → ℝ,
      (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, 0 ≤ w p q r) →
      (Real.pi*Real.sqrt N/4)*(∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, w p q r) ≤
        (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
          (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
            zetaChi (linePt t)*physicalCubicPacket S w t).re := by
  obtain ⟨N₀, hN₀, hb⟩ := exists_physicalCubicPacketKernel_positive
  refine ⟨N₀, hN₀, ?_⟩
  intro N H hN hH hHN heps S hS w hw
  rw [integral_physicalCubicPacket_eq]
  simp only [Finset.mul_sum, Complex.re_sum, Complex.re_ofReal_mul]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (hb N H hN hH hHN heps p q r (hS p hp) (hS q hq) (hS r hr)) (hw p hp q hq r hr)

end RHTower
