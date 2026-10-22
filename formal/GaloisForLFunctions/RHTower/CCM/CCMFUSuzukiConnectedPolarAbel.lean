import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiConnectedPrimeAbel
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszVolterraLaplace

/-!
# Connected Suzuki polar channel in the Abel half-plane

Damp the literal connected polar density into a linearly bounded causal source.
The existing Volterra-Laplace identity then proves its Abel transform exactly
on the safe Euler half-plane. No prime-polar sign is inferred.
-/

open Complex Filter Set Topology MeasureTheory
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

def ccmSuzukiConnectedPolarDensity (ω h : ℝ) : ℝ :=
  ccmGuinandWeilThirdGradePolarDensity h *
    shiftedEulerLogConnectedThirdMultiplier ω h

def ccmSuzukiConnectedPolarDampedSource (b ω h : ℝ) : ℝ :=
  if b < h then Real.exp (-(1 + ω) * h) * ccmSuzukiConnectedPolarDensity ω h else 0

def ccmSuzukiConnectedPolarRateWindow (b ω H : ℝ) : ℝ :=
  ∫ h in Set.Ioc b H, ccmSuzukiConnectedPolarDensity ω h

theorem measurable_ccmSuzukiConnectedPolarDampedSource (b ω : ℝ) :
    Measurable (ccmSuzukiConnectedPolarDampedSource b ω) := by
  unfold ccmSuzukiConnectedPolarDampedSource
  apply Measurable.ite measurableSet_Ioi
  · unfold ccmSuzukiConnectedPolarDensity
    unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
    unfold shiftedEulerLogConnectedThirdMultiplier
    fun_prop
  · exact measurable_const

theorem ccmSuzukiConnectedPolarDensity_nonneg
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    0 ≤ ccmSuzukiConnectedPolarDensity ω h := by
  exact mul_nonneg
    (ccmGuinandWeilThirdGradePolarDensity_nonneg hh)
    (shiftedEulerLogConnectedThirdMultiplier_nonneg hω hh)

theorem ccmSuzukiConnectedPolarDensity_le
    {b ω h : ℝ} (hb : 0 < b) (hω : 0 < ω) (hbh : b ≤ h) :
    ccmSuzukiConnectedPolarDensity ω h ≤
      (64 / b ^ (3 : ℕ)) * Real.exp ((ω + 1 / 2) * h) := by
  have hh : 0 < h := hb.trans_le hbh
  have hm0 := shiftedEulerLogConnectedThirdMultiplier_nonneg hω hh
  have hmle := shiftedEulerLogConnectedThirdMultiplier_le_cosh hω hh
  have harg : 0 ≤ ω * h := (mul_pos hω hh).le
  have hexp : Real.exp (-(ω * h)) ≤ Real.exp (ω * h) :=
    Real.exp_le_exp.mpr (by linarith)
  have hm : shiftedEulerLogConnectedThirdMultiplier ω h ≤ Real.exp (ω * h) := by
    calc
      _ ≤ Real.cosh (ω * h) := hmle
      _ ≤ Real.exp (ω * h) := by rw [Real.cosh_eq]; linarith
  calc
    ccmSuzukiConnectedPolarDensity ω h ≤
        ((64 / b ^ (3 : ℕ)) * Real.exp (h / 2)) *
          shiftedEulerLogConnectedThirdMultiplier ω h := by
      exact mul_le_mul_of_nonneg_right
        (ccmGuinandWeilThirdGradePolarDensity_le hb hbh) hm0
    _ ≤ ((64 / b ^ (3 : ℕ)) * Real.exp (h / 2)) *
        Real.exp (ω * h) := by
      exact mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (64 / b ^ (3 : ℕ)) * Real.exp ((ω + 1 / 2) * h) := by
      rw [show (ω + 1 / 2) * h = h / 2 + ω * h by ring,
        Real.exp_add]
      ring

theorem ccmSuzukiConnectedPolarDampedSource_linear_bound
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω)
    {h : ℝ} (hh : 0 < h) :
    |ccmSuzukiConnectedPolarDampedSource b ω h| ≤
      (64 / b ^ (3 : ℕ)) * (1 + h) := by
  by_cases hbh : b < h
  · have hden0 := ccmSuzukiConnectedPolarDensity_nonneg hω (hb.trans hbh)
    have hden := ccmSuzukiConnectedPolarDensity_le hb hω hbh.le
    have hC : 0 ≤ 64 / b ^ (3 : ℕ) := by positivity
    have hhalf : Real.exp (-h / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      linarith
    calc
      |ccmSuzukiConnectedPolarDampedSource b ω h| =
          Real.exp (-(1 + ω) * h) * ccmSuzukiConnectedPolarDensity ω h := by
        rw [ccmSuzukiConnectedPolarDampedSource, if_pos hbh]
        exact abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hden0)
      _ ≤ Real.exp (-(1 + ω) * h) *
          ((64 / b ^ (3 : ℕ)) * Real.exp ((ω + 1 / 2) * h)) := by
        exact mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = (64 / b ^ (3 : ℕ)) * Real.exp (-h / 2) := by
        rw [mul_comm, mul_assoc, ← Real.exp_add]
        congr 1
        ring
      _ ≤ 64 / b ^ (3 : ℕ) := by
        simpa using mul_le_mul_of_nonneg_left hhalf hC
      _ ≤ (64 / b ^ (3 : ℕ)) * (1 + h) := by
        nlinarith
  · simp [ccmSuzukiConnectedPolarDampedSource, hbh]
    positivity

theorem ccmSuzukiConnectedPolarDampedSource_volterra
    {b ω H : ℝ} (hb : 0 < b) :
    (∫ h in Set.Ioc (0 : ℝ) H,
        Real.exp (-((1 + ω) * (H - h))) *
          ccmSuzukiConnectedPolarDampedSource b ω h) =
      Real.exp (-(1 + ω) * H) * ccmSuzukiConnectedPolarRateWindow b ω H := by
  have hpoint (h : ℝ) :
      Real.exp (-((1 + ω) * (H - h))) *
          ccmSuzukiConnectedPolarDampedSource b ω h =
        Real.exp (-(1 + ω) * H) *
          Set.indicator (Set.Ioi b) (ccmSuzukiConnectedPolarDensity ω) h := by
    by_cases hbh : b < h
    · rw [ccmSuzukiConnectedPolarDampedSource, if_pos hbh,
        Set.indicator_of_mem (show h ∈ Set.Ioi b from hbh)]
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring
    · rw [ccmSuzukiConnectedPolarDampedSource, if_neg hbh,
        Set.indicator_of_notMem (show h ∉ Set.Ioi b from hbh)]
      ring
  calc
    (∫ h in Set.Ioc (0 : ℝ) H,
        Real.exp (-((1 + ω) * (H - h))) *
          ccmSuzukiConnectedPolarDampedSource b ω h) =
      ∫ h in Set.Ioc (0 : ℝ) H,
        Real.exp (-(1 + ω) * H) *
          Set.indicator (Set.Ioi b) (ccmSuzukiConnectedPolarDensity ω) h := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro h _
      exact hpoint h
    _ = Real.exp (-(1 + ω) * H) *
        ∫ h in Set.Ioc (0 : ℝ) H,
          Set.indicator (Set.Ioi b) (ccmSuzukiConnectedPolarDensity ω) h := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.exp (-(1 + ω) * H) *
        ∫ h in Set.Ioc (0 : ℝ) H ∩ Set.Ioi b,
          ccmSuzukiConnectedPolarDensity ω h := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = _ := by
      unfold ccmSuzukiConnectedPolarRateWindow
      have hset : Set.Ioc (0 : ℝ) H ∩ Set.Ioi b = Set.Ioc b H := by
        ext h
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · intro hh
          exact ⟨hh.2, hh.1.2⟩
        · intro hh
          exact ⟨⟨hb.trans hh.1, hh.2⟩, hh.1⟩
      rw [hset]

private theorem integral_Ioi_zeroBelow_ccmSuzukiConnected
    {b : ℝ} (hb : 0 < b) {f : ℝ → ℂ}
    (hf : ∀ h : ℝ, h ≤ b → f h = 0) :
    (∫ h in Set.Ioi (0 : ℝ), f h) = ∫ h in Set.Ioi b, f h := by
  calc
    _ = ∫ h in Set.Ioi (0 : ℝ), (Set.Ioi b).indicator f h := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro h hh
      by_cases hbh : b < h
      · rw [Set.indicator_of_mem (show h ∈ Set.Ioi b from hbh)]
      · rw [Set.indicator_of_notMem (show h ∉ Set.Ioi b from hbh)]
        exact hf h (le_of_not_gt hbh)
    _ = ∫ h in Set.Ioi (0 : ℝ) ∩ Set.Ioi b, f h := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = _ := by
      have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioi b = Set.Ioi b := by
        ext h
        simp only [Set.mem_inter_iff, Set.mem_Ioi]
        exact ⟨fun hh => hh.2, fun hh => ⟨hb.trans hh, hh⟩⟩
      rw [hset]

theorem ccmSuzukiConnectedPolarRateWindow_zeroBelow
    {b ω H : ℝ} (hH : H ≤ b) :
    ccmSuzukiConnectedPolarRateWindow b ω H = 0 := by
  have hset : Set.Ioc b H = ∅ := by
    ext h
    simp only [Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
    intro hh
    linarith
  simp [ccmSuzukiConnectedPolarRateWindow, hset]

theorem ccmSuzukiConnectedPolarRateWindow_abel_eq_density
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω)
    {u : ℂ} (hu : 1 + ω < u.re) :
    u * ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) * (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ) =
      ∫ h : ℝ in Set.Ioi b,
        Complex.exp (-u * (h : ℂ)) * (ccmSuzukiConnectedPolarDensity ω h : ℂ) := by
  let r : ℝ := 1 + ω
  let z : ℂ := u - (r : ℂ)
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hz : 0 < z.re := by dsimp [z, r]; linarith
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
    linarith
  have hvol := integral_Ioi_expVolterra_laplace
    (b := r) hr (z := z) hz
    (φ := ccmSuzukiConnectedPolarDampedSource b ω)
    (C := 64 / b ^ (3 : ℕ))
    (measurable_ccmSuzukiConnectedPolarDampedSource b ω)
    (fun h hh => ccmSuzukiConnectedPolarDampedSource_linear_bound hb hω hh)
  have hLpoint (H : ℝ) :
      Complex.exp (-(z * (H : ℂ))) *
        ((∫ h in Set.Ioc (0 : ℝ) H,
          Real.exp (-(r * (H - h))) * ccmSuzukiConnectedPolarDampedSource b ω h : ℝ) : ℂ) =
        Complex.exp (-(u * (H : ℂ))) * (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ) := by
    rw [show (∫ h in Set.Ioc (0 : ℝ) H,
        Real.exp (-(r * (H - h))) * ccmSuzukiConnectedPolarDampedSource b ω h : ℝ) =
        Real.exp (-(r * H)) * ccmSuzukiConnectedPolarRateWindow b ω H by
          simpa only [r, neg_mul] using
            ccmSuzukiConnectedPolarDampedSource_volterra (ω := ω) (H := H) hb]
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    dsimp [z]
    ring
  have hRpoint (h : ℝ) :
      Complex.exp (-(z * (h : ℂ))) * (ccmSuzukiConnectedPolarDampedSource b ω h : ℂ) =
        (Set.Ioi b).indicator
          (fun h : ℝ => Complex.exp (-(u * (h : ℂ))) *
            (ccmSuzukiConnectedPolarDensity ω h : ℂ)) h := by
    by_cases hbh : b < h
    · rw [Set.indicator_of_mem (show h ∈ Set.Ioi b from hbh)]
      simp only [ccmSuzukiConnectedPolarDampedSource, if_pos hbh]
      push_cast
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      dsimp [z, r]
      push_cast
      ring
    · rw [Set.indicator_of_notMem (show h ∉ Set.Ioi b from hbh)]
      simp [ccmSuzukiConnectedPolarDampedSource, hbh]
  have hL : (∫ H in Set.Ioi (0 : ℝ),
      Complex.exp (-(z * (H : ℂ))) *
        ((∫ h in Set.Ioc (0 : ℝ) H,
          Real.exp (-(r * (H - h))) * ccmSuzukiConnectedPolarDampedSource b ω h : ℝ) : ℂ)) =
      ∫ H in Set.Ioi b,
        Complex.exp (-(u * (H : ℂ))) *
          (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ) := by
    calc
      _ = ∫ H in Set.Ioi (0 : ℝ),
          Complex.exp (-(u * (H : ℂ))) *
            (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro H _
        exact hLpoint H
      _ = _ := integral_Ioi_zeroBelow_ccmSuzukiConnected hb (fun H hH => by
        rw [ccmSuzukiConnectedPolarRateWindow_zeroBelow hH]
        simp)
  have hR : (∫ h in Set.Ioi (0 : ℝ),
      Complex.exp (-(z * (h : ℂ))) * (ccmSuzukiConnectedPolarDampedSource b ω h : ℂ)) =
      ∫ h in Set.Ioi b,
        Complex.exp (-(u * (h : ℂ))) *
          (ccmSuzukiConnectedPolarDensity ω h : ℂ) := by
    calc
      _ = ∫ h in Set.Ioi (0 : ℝ),
          (Set.Ioi b).indicator
            (fun h : ℝ => Complex.exp (-(u * (h : ℂ))) *
              (ccmSuzukiConnectedPolarDensity ω h : ℂ)) h := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro h _
        exact hRpoint h
      _ = ∫ h in Set.Ioi (0 : ℝ) ∩ Set.Ioi b,
          Complex.exp (-(u * (h : ℂ))) *
            (ccmSuzukiConnectedPolarDensity ω h : ℂ) := by
        rw [setIntegral_indicator measurableSet_Ioi]
      _ = _ := by
        have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioi b = Set.Ioi b := by
          ext h
          simp only [Set.mem_inter_iff, Set.mem_Ioi]
          exact ⟨fun hh => hh.2, fun hh => ⟨hb.trans hh, hh⟩⟩
        rw [hset]
  rw [hL, hR] at hvol
  have hzsum : z + (r : ℂ) = u := by dsimp [z]; ring
  rw [hzsum] at hvol
  simp only [neg_mul] at hvol ⊢
  rw [hvol]
  simp [hu0]

end

end RHTower
