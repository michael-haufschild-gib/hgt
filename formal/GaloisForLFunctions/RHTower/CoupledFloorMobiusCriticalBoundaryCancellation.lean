import GaloisForLFunctions.RHTower.CoupledFloorMobiusShiftIncidence
import GaloisForLFunctions.RHTower.PolynomialFockLocalBregman

/-!
# Critical-boundary cancellation for the coupled floor--Möbius incidence

The common upper input in `CoupledFloorMobiusShiftIncidence` leaves `L²(0,∞)` as its damping
parameter tends to zero.  The *combined* lower-minus-upper arithmetic incidence nevertheless has a
genuine critical boundary value.  We prove this by upgrading the corpus natural-argument estimate
for Suzuki's coupled error to real arguments, obtaining exponential decay after the logarithmic
change of variables, and then applying dominated convergence to the exact damping identity.

The closed capstone records all three facts together:

* the uncancelled upper mode has divergent squared norm;
* the critical combined incidence is square-integrable;
* the regularized combined incidences converge strongly in `L²` to it.

This discharges the analytic critical-carrier premise in route CFI.  It does not assume or prove the
remaining graph-debt/source-order scalar needed by the four-unit RH endpoint.
-/

open Finset ArithmeticFunction Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

/-! ## A real-argument envelope for the coupled error -/

/-- The natural-argument corpus envelope survives interpolation across each unit floor cell. -/
theorem abs_suzukiCoupledErrorReal_le {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      |suzukiCoupledErrorReal ω X| ≤ C * X ^ (1 - ω) := by
  obtain ⟨C, hC, hnat⟩ := abs_suzukiCoupledError_le hω0 hω1
  let r : ℝ := suzukiEulerDensityConstant ω
  refine ⟨C + |r|, by positivity, ?_⟩
  intro X hX
  let N : ℕ := ⌊X⌋₊
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hN1 : 1 ≤ N := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hN0
      have hlt : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
      simp [N, hN0] at hlt
      exact (not_lt_of_ge hX) hlt)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNX : (N : ℝ) ≤ X := by
    simpa [N] using Nat.floor_le hX0.le
  have hgap : |(N : ℝ) - X| ≤ 1 := by
    have hlt : X < (N : ℝ) + 1 := by simpa [N] using Nat.lt_floor_add_one X
    rw [abs_of_nonpos (sub_nonpos.mpr hNX)]
    linarith
  have hsummatory : suzukiShiftedSummatoryReal ω X =
      suzukiShiftedSummatoryReal ω (N : ℝ) := by
    simp only [suzukiShiftedSummatoryReal]
    rw [Nat.floor_natCast]
  have hnat' : |suzukiCoupledErrorReal ω (N : ℝ)| ≤ C * (N : ℝ) ^ (1 - ω) := by
    simpa [suzukiCoupledErrorReal_natCast] using hnat N hN1
  have hβ : (1 : ℝ) ≤ 1 + ω := by linarith
  have hlip : |(N : ℝ) ^ (1 + ω) - X ^ (1 + ω)| ≤
      (1 + ω) * X ^ ω * |(N : ℝ) - X| := by
    simpa using abs_rpow_sub_rpow_le_of_le hNpos hX0 hNX (le_refl X) hβ
  have hpowmono : (N : ℝ) ^ (1 - ω) ≤ X ^ (1 - ω) := by
    exact Real.rpow_le_rpow hNpos.le hNX (by linarith)
  have hXpow : X ^ ω ≤ X ^ (1 - ω) := by
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hmain : |suzukiMainTermReal ω (N : ℝ) - suzukiMainTermReal ω X| ≤
      |r| * X ^ (1 - ω) := by
    have hden : 0 < 1 + ω := by linarith
    rw [suzukiMainTermReal, suzukiMainTermReal]
    change |r * (N : ℝ) ^ (1 + ω) / (1 + ω) - r * X ^ (1 + ω) / (1 + ω)| ≤ _
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hden]
    have hstep : |(N : ℝ) ^ (1 + ω) - X ^ (1 + ω)| ≤
        (1 + ω) * X ^ ω := by
      calc
        _ ≤ (1 + ω) * X ^ ω * |(N : ℝ) - X| := hlip
        _ ≤ (1 + ω) * X ^ ω * 1 := by gcongr
        _ = (1 + ω) * X ^ ω := by ring
    have hnonneg : 0 ≤ |r| := abs_nonneg r
    calc
      |r| * |(N : ℝ) ^ (1 + ω) - X ^ (1 + ω)| / (1 + ω)
          ≤ |r| * ((1 + ω) * X ^ ω) / (1 + ω) := by gcongr
      _ = |r| * X ^ ω := by field_simp
      _ ≤ |r| * X ^ (1 - ω) := mul_le_mul_of_nonneg_left hXpow hnonneg
  have herrsplit : suzukiCoupledErrorReal ω X =
      suzukiCoupledErrorReal ω (N : ℝ) +
        (suzukiMainTermReal ω (N : ℝ) - suzukiMainTermReal ω X) := by
    rw [suzukiCoupledErrorReal, suzukiCoupledErrorReal, hsummatory]
    ring
  rw [herrsplit]
  calc
    |suzukiCoupledErrorReal ω (N : ℝ) +
        (suzukiMainTermReal ω (N : ℝ) - suzukiMainTermReal ω X)|
        ≤ |suzukiCoupledErrorReal ω (N : ℝ)| +
          |suzukiMainTermReal ω (N : ℝ) - suzukiMainTermReal ω X| := abs_add_le _ _
    _ ≤ C * (N : ℝ) ^ (1 - ω) + |r| * X ^ (1 - ω) := add_le_add hnat' hmain
    _ ≤ C * X ^ (1 - ω) + |r| * X ^ (1 - ω) := by gcongr
    _ = (C + |r|) * X ^ (1 - ω) := by ring

/-! ## Measurability of the critical carrier -/

theorem measurable_suzukiShiftedSummatoryReal (ω : ℝ) :
    Measurable (suzukiShiftedSummatoryReal ω) := by
  exact (measurable_from_top (f := fun N : ℕ =>
    ∑ n ∈ Finset.Icc 1 N, suzukiShiftedCoefficient ω n)).comp Nat.measurable_floor

theorem measurable_suzukiMainTermReal (ω : ℝ) :
    Measurable (suzukiMainTermReal ω) := by
  unfold suzukiMainTermReal
  fun_prop

theorem measurable_suzukiCoupledErrorReal (ω : ℝ) :
    Measurable (suzukiCoupledErrorReal ω) := by
  exact (measurable_suzukiShiftedSummatoryReal ω).sub (measurable_suzukiMainTermReal ω)

theorem measurable_coupledErrorVector (ω δ : ℝ) :
    Measurable (coupledErrorVector ω δ) := by
  unfold coupledErrorVector
  exact (Real.measurable_exp.comp (measurable_id.const_mul _).neg).mul
    ((measurable_suzukiCoupledErrorReal ω).comp Real.measurable_exp)

/-! ## Critical `L²` cancellation -/

/-- The combined critical incidence decays like `exp (-2ωt)`. -/
theorem abs_coupledErrorVector_zero_le {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      |coupledErrorVector ω 0 t| ≤ C * Real.exp (-(2 * ω * t)) := by
  obtain ⟨C, hC, hreal⟩ := abs_suzukiCoupledErrorReal_le hω0 hω1
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hexp1 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
  have hE := hreal (Real.exp t) hexp1
  have hfac : 0 < Real.exp (-((1 + ω + 0) * t)) := Real.exp_pos _
  rw [coupledErrorVector, abs_mul, abs_of_pos hfac]
  calc
    Real.exp (-((1 + ω + 0) * t)) * |suzukiCoupledErrorReal ω (Real.exp t)|
        ≤ Real.exp (-((1 + ω + 0) * t)) *
            (C * Real.exp t ^ (1 - ω)) := mul_le_mul_of_nonneg_left hE hfac.le
    _ = C * Real.exp (-(2 * ω * t)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
      rw [show Real.exp (-((1 + ω + 0) * t)) * (C * Real.exp (t * (1 - ω))) =
        C * (Real.exp (-((1 + ω + 0) * t)) * Real.exp (t * (1 - ω))) by ring,
        ← Real.exp_add]
      congr 1
      ring

/-- The full lower-minus-upper incidence remains square-integrable at the singular boundary. -/
theorem integrableOn_coupledErrorVector_zero_sq {ω : ℝ}
    (hω0 : 0 < ω) (hω1 : ω < 1 / 2) :
    IntegrableOn (fun t => coupledErrorVector ω 0 t ^ 2) (Set.Ioi (0 : ℝ)) volume := by
  obtain ⟨C, hC, hbound⟩ := abs_coupledErrorVector_zero_le hω0 hω1
  have hmaj : IntegrableOn (fun t : ℝ => C ^ 2 * Real.exp (-(4 * ω) * t))
      (Set.Ioi (0 : ℝ)) volume :=
    (exp_neg_integrableOn_Ioi (0 : ℝ) (b := 4 * ω) (by positivity)).const_mul (C ^ 2)
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((measurable_coupledErrorVector ω 0).pow_const 2).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    have hb := hbound t ht0
    have hsq : coupledErrorVector ω 0 t ^ 2 = |coupledErrorVector ω 0 t| ^ 2 := by
      rw [sq_abs]
    have hexpsq : Real.exp (-(2 * ω * t)) ^ 2 = Real.exp (-(4 * ω) * t) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hsq]
    nlinarith [hb, abs_nonneg (coupledErrorVector ω 0 t), Real.exp_pos (-(2 * ω * t)),
      hexpsq.le, hexpsq.ge]

/-- Every regularized carrier is exact scalar damping of the critical combined carrier. -/
theorem coupledErrorVector_eq_damping_mul_zero (ω δ t : ℝ) :
    coupledErrorVector ω δ t = Real.exp (-(δ * t)) * coupledErrorVector ω 0 t := by
  unfold coupledErrorVector
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  ring

/-- The regularized combined incidences converge strongly in `L²` to the critical carrier. -/
theorem tendsto_integral_coupledErrorVector_sqDistance_zero {ω : ℝ}
    (hω0 : 0 < ω) (hω1 : ω < 1 / 2) :
    Tendsto (fun δ : ℝ => ∫ t in Set.Ioi (0 : ℝ),
        (coupledErrorVector ω δ t - coupledErrorVector ω 0 t) ^ 2)
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
  have hdom := integrableOn_coupledErrorVector_zero_sq hω0 hω1
  have hdc := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (fun t => coupledErrorVector ω 0 t ^ 2)
    (F := fun δ t => (coupledErrorVector ω δ t - coupledErrorVector ω 0 t) ^ 2)
    (f := fun _ => 0)
    (Filter.Eventually.of_forall fun δ =>
      (((measurable_coupledErrorVector ω δ).sub
        (measurable_coupledErrorVector ω 0)).pow_const 2).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hδ0 : 0 ≤ δ := Set.mem_Ici.mp hδ
      have ht0 : 0 ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
      have hdt : 0 ≤ δ * t := mul_nonneg hδ0 ht0
      have hexppos : 0 < Real.exp (-(δ * t)) := Real.exp_pos _
      have hexple : Real.exp (-(δ * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hcoef : |Real.exp (-(δ * t)) - 1| ≤ 1 := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hcoefsq : (Real.exp (-(δ * t)) - 1) ^ 2 ≤ 1 := by
        have hcoef0 := abs_nonneg (Real.exp (-(δ * t)) - 1)
        rw [← sq_abs]
        nlinarith
      rw [coupledErrorVector_eq_damping_mul_zero]
      rw [show Real.exp (-(δ * t)) * coupledErrorVector ω 0 t -
          coupledErrorVector ω 0 t =
          (Real.exp (-(δ * t)) - 1) * coupledErrorVector ω 0 t by ring,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      simpa using mul_le_mul_of_nonneg_right hcoefsq
        (sq_nonneg (coupledErrorVector ω 0 t)))
    hdom
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hcont : ContinuousAt (fun δ : ℝ =>
          (coupledErrorVector ω δ t - coupledErrorVector ω 0 t) ^ 2) 0 := by
        unfold coupledErrorVector
        fun_prop
      have hle : nhdsWithin (0 : ℝ) (Set.Ici 0) ≤ nhds 0 := by
        rw [nhdsWithin]
        exact inf_le_left
      simpa using hcont.tendsto.mono_left hle)
  simpa only [integral_zero] using hdc

/-! ## Closed CFI boundary-cancellation certificate -/

/-- **CFI critical-boundary singular cancellation.**  This premise-free theorem distinguishes the
divergent common upper input from the square-integrable arithmetic lower-minus-upper incidence and
certifies strong convergence of the regularized incidence to its critical boundary value. -/
theorem coupledFloorMobiusCriticalBoundary_singularCancellation :
    Tendsto (fun δ : ℝ => ∫ t in Set.Ioi (0 : ℝ), dampingMode δ t ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) atTop ∧
      ∀ ω ∈ Set.Ioo (0 : ℝ) (1 / 2),
        (∀ t ∈ Set.Ici (0 : ℝ),
          coupledErrorVector ω 0 t =
            ∑' d : ℕ, (incidenceLower ω 0 t d - incidenceUpper ω 0 t d)) ∧
        IntegrableOn (fun t => coupledErrorVector ω 0 t ^ 2) (Set.Ioi (0 : ℝ)) volume ∧
        Tendsto (fun δ : ℝ => ∫ t in Set.Ioi (0 : ℝ),
            (coupledErrorVector ω δ t - coupledErrorVector ω 0 t) ^ 2)
          (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
  refine ⟨tendsto_integral_dampingMode_sq, ?_⟩
  intro ω hω
  have hω0 : 0 < ω := hω.1
  have hω1 : ω < 1 / 2 := hω.2
  refine ⟨?_, integrableOn_coupledErrorVector_zero_sq hω0 hω1,
    tendsto_integral_coupledErrorVector_sqDistance_zero hω0 hω1⟩
  intro t ht
  exact coupledErrorVector_eq_tsum_zero hω0 (Set.mem_Ici.mp ht)

end

end RHTower
