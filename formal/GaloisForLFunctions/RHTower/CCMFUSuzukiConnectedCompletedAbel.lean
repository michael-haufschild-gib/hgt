import GaloisForLFunctions.RHTower.CCMFUSuzukiConnectedPolarAbel
import GaloisForLFunctions.RHTower.CCMFUSuzukiClockVolterraBridge

/-!
# Completed connected Suzuki source in the Abel half-plane

The actual finite prime-minus-polar cumulative source equals the difference of the
two clocked channels. Its Abel transform equals the literal prime Dirichlet series
minus the clocked polar Laplace integral on the safe Euler half-plane. The sign
between channels is retained; neither term is bounded separately on the target
half-plane, and this module proves no RH-strength window bound.
-/

open Complex Filter Set Topology MeasureTheory
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

theorem measurable_ccmSuzukiConnectedPrimeRateWindow (b ω : ℝ) :
    Measurable (ccmSuzukiConnectedPrimeRateWindow b ω) := by
  let A : ℕ → ℂ := fun m =>
    ∑ k ∈ Finset.Icc 1 m, ccmSuzukiConnectedPrimeDirichletCoeff b ω k
  have hA : Measurable A := measurable_of_countable A
  have hfloor : Measurable (fun H : ℝ => ⌊Real.exp H⌋₊) :=
    Real.measurable_exp.nat_floor
  change Measurable (fun H : ℝ => A ⌊Real.exp H⌋₊)
  exact hA.comp hfloor

theorem norm_ccmSuzukiConnectedPrimeRateWindow_le
    {b ω H : ℝ} (hb : 0 < b) (hω : 0 < ω) :
    ‖ccmSuzukiConnectedPrimeRateWindow b ω H‖ ≤
      (32 / b ^ (2 : ℕ)) * Real.exp ((ω + 1) * H) := by
  let N : ℕ := ⌊Real.exp H⌋₊
  let C : ℝ := 32 / b ^ (2 : ℕ)
  have hN : (N : ℝ) ≤ Real.exp H := Nat.floor_le (Real.exp_pos H).le
  have hcard : ((Finset.Icc 1 N).card : ℝ) ≤ Real.exp H := by
    calc
      ((Finset.Icc 1 N).card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (by simp [Nat.card_Icc] : (Finset.Icc 1 N).card ≤ N)
      _ ≤ Real.exp H := hN
  have hpow : (Real.exp H) ^ ω = Real.exp (ω * H) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos H), Real.log_exp]
    congr 1
    ring
  calc
    ‖ccmSuzukiConnectedPrimeRateWindow b ω H‖ ≤
      ∑ k ∈ Finset.Icc 1 N, ‖ccmSuzukiConnectedPrimeDirichletCoeff b ω k‖ := by
      unfold ccmSuzukiConnectedPrimeRateWindow
      exact norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 N, C * Real.exp (ω * H) := by
      apply Finset.sum_le_sum
      intro k hk
      have hke : (k : ℝ) ≤ Real.exp H := by
        exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans hN
      have hkp : (k : ℝ) ^ ω ≤ Real.exp (ω * H) := by
        rw [← hpow]
        exact Real.rpow_le_rpow (Nat.cast_nonneg k) hke hω.le
      exact (norm_ccmSuzukiConnectedPrimeDirichletCoeff_le_rpow hb hω k).trans
        (mul_le_mul_of_nonneg_left hkp (by positivity))
    _ = ((Finset.Icc 1 N).card : ℝ) * (C * Real.exp (ω * H)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp H * (C * Real.exp (ω * H)) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (32 / b ^ (2 : ℕ)) * Real.exp ((ω + 1) * H) := by
      dsimp only [C]
      rw [show (ω + 1) * H = H + ω * H by ring, Real.exp_add]
      ring

theorem integrableOn_ccmSuzukiConnectedPrimeRateWindow
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω)
    {u : ℂ} (hu : ω + 1 < u.re) :
    IntegrableOn
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        ccmSuzukiConnectedPrimeRateWindow b ω H)
      (Set.Ioi b) := by
  let δ : ℝ := u.re - (ω + 1)
  let C : ℝ := 32 / b ^ (2 : ℕ)
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hbase : IntegrableOn (fun H : ℝ => C * Real.exp (-δ * H))
      (Set.Ioi b) := by
    have he := integrableOn_exp_mul_Ioi (a := -δ) (by linarith) b
    simpa only [MeasureTheory.IntegrableOn, neg_mul] using he.const_mul C
  apply hbase.mono'
  · apply Measurable.aestronglyMeasurable
    exact (by fun_prop : Measurable (fun H : ℝ =>
      Complex.exp (-u * (H : ℂ)))).mul
        (measurable_ccmSuzukiConnectedPrimeRateWindow b ω)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    rw [norm_mul, Complex.norm_exp]
    have hre : (-u * (H : ℂ)).re = -u.re * H := by simp [mul_re]
    rw [hre]
    calc
      Real.exp (-u.re * H) * ‖ccmSuzukiConnectedPrimeRateWindow b ω H‖ ≤
        Real.exp (-u.re * H) * (C * Real.exp ((ω + 1) * H)) := by
        exact mul_le_mul_of_nonneg_left
          (norm_ccmSuzukiConnectedPrimeRateWindow_le hb hω)
          (Real.exp_nonneg _)
      _ = C * Real.exp (-δ * H) := by
        rw [mul_comm, mul_assoc, ← Real.exp_add]
        congr 1
        dsimp only [δ]
        ring

theorem integrableOn_ccmSuzukiConnectedPolarRateWindow
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω)
    {u : ℂ} (hu : 1 + ω < u.re) :
    IntegrableOn
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ))
      (Set.Ioi b) := by
  let r : ℝ := 1 + ω
  let z : ℂ := u - (r : ℂ)
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hz : 0 < z.re := by dsimp [z, r]; linarith
  have hbase := integrableOn_Ioi_cexp_mul_expVolterra
    (b := r) hr (z := z) hz
    (φ := ccmSuzukiConnectedPolarDampedSource b ω)
    (C := 64 / b ^ (3 : ℕ))
    (measurable_ccmSuzukiConnectedPolarDampedSource b ω)
    (fun h hh => ccmSuzukiConnectedPolarDampedSource_linear_bound hb hω hh)
  have hpoint (H : ℝ) :
      Complex.exp (-(z * (H : ℂ))) *
        ((∫ h in Set.Ioc (0 : ℝ) H,
          Real.exp (-(r * (H - h))) *
            ccmSuzukiConnectedPolarDampedSource b ω h : ℝ) : ℂ) =
        Complex.exp (-u * (H : ℂ)) *
          (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ) := by
    rw [show (∫ h in Set.Ioc (0 : ℝ) H,
        Real.exp (-(r * (H - h))) *
          ccmSuzukiConnectedPolarDampedSource b ω h : ℝ) =
        Real.exp (-(r * H)) * ccmSuzukiConnectedPolarRateWindow b ω H by
          simpa only [r, neg_mul] using
            ccmSuzukiConnectedPolarDampedSource_volterra (ω := ω) (H := H) hb]
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    dsimp [z]
    ring
  have hbase' : IntegrableOn
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ))
      (Set.Ioi (0 : ℝ)) := by
    exact hbase.congr_fun (fun H _ => hpoint H) measurableSet_Ioi
  exact hbase'.mono_set (Set.Ioi_subset_Ioi hb.le)

theorem ccmSuzukiConnectedPolarRateWindow_eq_literal
    {b H : ℝ} (hbH : b ≤ H) (ω : ℝ) :
    ccmSuzukiConnectedPolarRateWindow b ω H =
      ∫ h in b..H,
        ccmSuzukiConnectedThirdGradeWeight ω h * (2 * Real.cosh (h / 2)) := by
  rw [ccmSuzukiConnectedPolarRateWindow,
    ← intervalIntegral.integral_of_le hbH]
  apply intervalIntegral.integral_congr
  intro h hh
  unfold ccmSuzukiConnectedPolarDensity
    ccmGuinandWeilThirdGradePolarDensity
    ccmSuzukiConnectedThirdGradeWeight
  ring

theorem ccmSuzukiConnectedThirdGradeCumulative_eq_prime_sub_polar
    {b H : ℝ} (hb : 0 < b) (hbH : b < H) (ω : ℝ) :
    (ccmSuzukiConnectedThirdGradeCumulative b ω H : ℂ) =
      ccmSuzukiConnectedPrimeRateWindow b ω H -
        (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ) := by
  rw [ccmSuzukiConnectedPrimeRateWindow_eq_literalPrime hb (hb.trans hbH) ω,
    ccmSuzukiConnectedPolarRateWindow_eq_literal hbH.le ω]
  unfold ccmSuzukiConnectedThirdGradeCumulative
    ccmGuinandWeilPrimePolarWeightedWindow
  simp only [Complex.ofReal_sub, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hbk : b < Real.log k <;> simp [hbk]

theorem ccmSuzukiConnectedThirdGradeCumulative_abel_eq_source
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω)
    {u : ℂ} (hu : 1 + ω < u.re) :
    u * ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmSuzukiConnectedThirdGradeCumulative b ω H : ℂ) =
      LSeries (ccmSuzukiConnectedPrimeDirichletCoeff b ω) u -
        ∫ h : ℝ in Set.Ioi b,
          Complex.exp (-u * (h : ℂ)) *
            (ccmSuzukiConnectedPolarDensity ω h : ℂ) := by
  have hP := integrableOn_ccmSuzukiConnectedPrimeRateWindow hb hω
    (by linarith : ω + 1 < u.re)
  have hR := integrableOn_ccmSuzukiConnectedPolarRateWindow hb hω hu
  have hpoint : ∀ H ∈ Set.Ioi b,
      Complex.exp (-u * (H : ℂ)) *
        (ccmSuzukiConnectedThirdGradeCumulative b ω H : ℂ) =
        Complex.exp (-u * (H : ℂ)) *
          ccmSuzukiConnectedPrimeRateWindow b ω H -
        Complex.exp (-u * (H : ℂ)) *
          (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ) := by
    intro H hH
    rw [ccmSuzukiConnectedThirdGradeCumulative_eq_prime_sub_polar hb hH ω]
    ring
  have hint : (∫ H : ℝ in Set.Ioi b,
      Complex.exp (-u * (H : ℂ)) *
        (ccmSuzukiConnectedThirdGradeCumulative b ω H : ℂ)) =
      (∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          ccmSuzukiConnectedPrimeRateWindow b ω H) -
      (∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmSuzukiConnectedPolarRateWindow b ω H : ℂ)) := by
    rw [← MeasureTheory.integral_sub hP hR]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro H hH
    exact hpoint H hH
  rw [hint, mul_sub]
  have hprime := LSeries_ccmSuzukiConnectedPrimeDirichletCoeff_eq_abel
    hb hω (by linarith : ω + 1 < u.re)
  have hpolar := ccmSuzukiConnectedPolarRateWindow_abel_eq_density hb hω hu
  rw [← hprime, hpolar]

end

end RHTower
