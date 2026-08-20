import GaloisForLFunctions.RHTower.PrimeEndpointJet
import Mathlib

/-!
# The higher-order Mertens theorem with an exponential rate

The limits of `PrimeHigherMertens` are upgraded to the de la Vallée Poussin rate

`|∑_{p ≤ x} (log p)^k/p - (log x)^k/k - C_k| ≤ B (log x)^{k-1} exp (-c √log x)`.

Two devices do the work: the packaged prime-number-theorem envelope
`exists_pntErrorEnvelope`, and the tail estimate
`∫_{Ioi x} (log t)^m e^{-c √log t}/t ≤ e^{-(c/2)√log x} ∫_{Ioi 2} (log t)^m e^{-(c/2)√log t}/t`,
obtained by splitting the exponential in half.

The consequence used by the endpoint-jet theorem is the monomial defect estimate: for every
algebraic order `M`,

`|D_x(u^{k}) - C_{k}/(log x)^{k}| = O(L^{-M-1})`,

so the monomial part of the boundary defect is exactly a jet coefficient to all algebraic orders.
-/

set_option maxHeartbeats 1600000

open Filter Topology Set MeasureTheory Asymptotics

namespace RHTower

noncomputable section

/-! ## Tail bound for the logarithmic de la Vallée Poussin weight -/

theorem setIntegral_Ioi_logPow_pntErrorWeight_le {c : ℝ} (hc : 0 < c) (m : ℕ) {x : ℝ}
    (hx : 2 ≤ x) :
    ∫ t in Ioi x, (Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t
      ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log x)) *
        ∫ t in Ioi (2 : ℝ), (Real.log t) ^ m * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) / t := by
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have hsub : Ioi x ⊆ Ioi (2 : ℝ) := Ioi_subset_Ioi hx
  have hbase2 : IntegrableOn
      (fun t : ℝ => (Real.log t) ^ m * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) / t)
      (Ioi (2 : ℝ)) := integrableOn_logPow_pntErrorWeight hc2 m
  have hbase1 : IntegrableOn
      (fun t : ℝ => (Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t)
      (Ioi x) := (integrableOn_logPow_pntErrorWeight hc m).mono_set hsub
  have hstep : ∫ t in Ioi x, (Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t
      ≤ ∫ t in Ioi x, Real.exp (-(c / 2) * Real.sqrt (Real.log x)) *
          ((Real.log t) ^ m * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) / t) := by
    refine setIntegral_mono_on hbase1 ((hbase2.mono_set hsub).const_mul _) measurableSet_Ioi ?_
    intro t ht
    have htx : x < t := ht
    have ht2 : (2 : ℝ) < t := lt_of_le_of_lt hx htx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have htpos : (0 : ℝ) < t := by linarith
    have hsqrt : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log t) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) htx.le)
    have hexp : Real.exp (-c * Real.sqrt (Real.log t))
        ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log x)) *
          Real.exp (-(c / 2) * Real.sqrt (Real.log t)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hlogpow : (0 : ℝ) ≤ (Real.log t) ^ m := pow_nonneg hlogt.le m
    have hgoal : (Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t
        ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log x)) *
          ((Real.log t) ^ m * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) / t) := by
      rw [div_le_iff₀ htpos]
      have hrw : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) *
          ((Real.log t) ^ m * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) / t) * t
          = (Real.log t) ^ m * (Real.exp (-(c / 2) * Real.sqrt (Real.log x)) *
            Real.exp (-(c / 2) * Real.sqrt (Real.log t))) := by
        field_simp
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hexp hlogpow
    exact hgoal
  refine hstep.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine setIntegral_mono_set hbase2 ?_ (LE.le.eventuallyLE hsub)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : (2 : ℝ) < t := ht
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have htpos : (0 : ℝ) < t := by linarith
  positivity

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory Asymptotics

/-! ## A packaged prime-number-theorem envelope -/

theorem exists_pntErrorEnvelope :
    ∃ D c T : ℝ, 0 < c ∧ 0 ≤ D ∧ 4 ≤ T ∧
      (∀ t : ℝ, T ≤ t → |Chebyshev.theta t - t| ≤ D * t * Real.exp (-c * Real.sqrt (Real.log t)))
      ∧ (∀ t : ℝ, T ≤ t → |thetaError t| ≤ D * Real.exp (-c * Real.sqrt (Real.log t))) := by
  obtain ⟨c, hc0, hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hC.and (Filter.eventually_ge_atTop (4 : ℝ)))
  have hT4 : (4 : ℝ) ≤ T := (hT T le_rfl).2
  refine ⟨|C|, c, T, hc0, abs_nonneg C, hT4, ?_, ?_⟩
  · intro t htT
    have ht4 : (4 : ℝ) ≤ t := le_trans hT4 htT
    have htpos : (0 : ℝ) < t := by linarith
    have h1 : ‖(Chebyshev.theta - id : ℝ → ℝ) t‖
        ≤ C * ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖ := (hT t htT).1
    have h2 : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖
        = t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h3 : ‖(Chebyshev.theta - id : ℝ → ℝ) t‖ = |Chebyshev.theta t - t| := by
      simp [Real.norm_eq_abs]
    rw [h2, h3] at h1
    calc |Chebyshev.theta t - t| ≤ C * (t * Real.exp (-c * Real.sqrt (Real.log t))) := h1
      _ ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = |C| * t * Real.exp (-c * Real.sqrt (Real.log t)) := by ring
  · intro t htT
    have ht4 : (4 : ℝ) ≤ t := le_trans hT4 htT
    have htpos : (0 : ℝ) < t := by linarith
    have hnum : |Chebyshev.theta t - t| ≤ |C| * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      have h1 : ‖(Chebyshev.theta - id : ℝ → ℝ) t‖
          ≤ C * ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖ := (hT t htT).1
      have h2 : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖
          = t * Real.exp (-c * Real.sqrt (Real.log t)) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h3 : ‖(Chebyshev.theta - id : ℝ → ℝ) t‖ = |Chebyshev.theta t - t| := by
        simp [Real.norm_eq_abs]
      rw [h2, h3] at h1
      calc |Chebyshev.theta t - t| ≤ C * (t * Real.exp (-c * Real.sqrt (Real.log t))) := h1
        _ ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ = |C| * t * Real.exp (-c * Real.sqrt (Real.log t)) := by ring
    have hdiv : thetaError t = (Chebyshev.theta t - t) / t := by
      rw [thetaError]
      field_simp
    rw [hdiv, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
    calc |Chebyshev.theta t - t| ≤ |C| * t * Real.exp (-c * Real.sqrt (Real.log t)) := hnum
      _ = |C| * Real.exp (-c * Real.sqrt (Real.log t)) * t := by ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory Asymptotics

/-! ## The higher-order Mertens theorem with an exponential rate -/

theorem exists_primeLogPowSum_sub_bound (m : ℕ) :
    ∃ B c X₀ : ℝ, 0 < c ∧ 0 ≤ B ∧ 4 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      |primeLogPowSum (m + 1) x - (Real.log x) ^ (m + 1) / ((m : ℝ) + 1)
          - mertensLogPowConstantFull m|
        ≤ B * (Real.log x) ^ m * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨D, c, T, hc0, hD, hT4, hthetaB, herrB⟩ := exists_pntErrorEnvelope
  set J1 : ℝ := ∫ t in Ioi (2 : ℝ),
    (Real.log t) ^ (m - 1) * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) / t with hJ1
  set J2 : ℝ := ∫ t in Ioi (2 : ℝ),
    (Real.log t) ^ m * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) / t with hJ2
  have hJnn : ∀ (k : ℕ), (0 : ℝ) ≤ ∫ t in Ioi (2 : ℝ),
      (Real.log t) ^ k * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) / t := by
    intro k
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht2 : (2 : ℝ) < t := ht
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have htpos : (0 : ℝ) < t := by linarith
    positivity
  have hJ1nn : (0 : ℝ) ≤ J1 := by rw [hJ1]; exact hJnn (m - 1)
  have hJ2nn : (0 : ℝ) ≤ J2 := by rw [hJ2]; exact hJnn m
  refine ⟨D + D * ((m : ℝ) * J1 + J2), c / 2, T, by linarith, ?_, hT4, ?_⟩
  · have h1 : (0 : ℝ) ≤ D * ((m : ℝ) * J1 + J2) := by positivity
    linarith
  intro x hxT
  have hx4 : (4 : ℝ) ≤ x := le_trans hT4 hxT
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx1 : 1 ≤ Real.log x := by
    have he : Real.exp 1 ≤ x := by nlinarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) he
  -- the exact identity
  have hIoc : IntegrableOn (logPowThetaErrorIntegrand m) (Ioc (2 : ℝ) x) :=
    (integrableOn_logPowThetaErrorIntegrand_Icc m x).mono_set Ioc_subset_Icc_self
  have hIoi : IntegrableOn (logPowThetaErrorIntegrand m) (Ioi x) :=
    (integrableOn_logPowThetaErrorIntegrand m).mono_set (Ioi_subset_Ioi hx2)
  have hsplit : (∫ t in Ioi (2 : ℝ), logPowThetaErrorIntegrand m t)
      = (∫ t in Ioc (2 : ℝ) x, logPowThetaErrorIntegrand m t)
        + ∫ t in Ioi x, logPowThetaErrorIntegrand m t := by
    rw [← Ioc_union_Ioi_eq_Ioi hx2]
    refine setIntegral_union ?_ measurableSet_Ioi hIoc hIoi
    rw [Set.disjoint_left]
    intro a ha ha'
    exact absurd ha.2 (not_le.mpr ha')
  have hid : primeLogPowSum (m + 1) x - (Real.log x) ^ (m + 1) / ((m : ℝ) + 1)
      - mertensLogPowConstantFull m
      = logPowDivId m x * (Chebyshev.theta x - x)
        + ∫ t in Ioi x, logPowThetaErrorIntegrand m t := by
    rw [primeLogPowSum_eq_add (m + 1) hx2, mertensLogPowConstantFull, mertensLogPowConstant,
      hsplit]
    have hstep := primeLogPowSumIoc_sub_eq m hx2
    linarith [hstep]
  rw [hid]
  -- the boundary term
  have hb1 : |logPowDivId m x * (Chebyshev.theta x - x)|
      ≤ D * (Real.log x) ^ m * Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [logPowDivId, abs_mul, abs_div, abs_of_nonneg (pow_nonneg hlogx.le m),
      abs_of_pos hxpos]
    have hstep : (Real.log x) ^ m / x * |Chebyshev.theta x - x|
        ≤ (Real.log x) ^ m / x * (D * x * Real.exp (-c * Real.sqrt (Real.log x))) := by
      gcongr
      exact hthetaB x hxT
    refine hstep.trans_eq ?_
    field_simp
  -- the tail term
  have hb2 : |∫ t in Ioi x, logPowThetaErrorIntegrand m t|
      ≤ D * ((m : ℝ) * J1 + J2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    have hptb : ∀ t ∈ Ioi x, ‖logPowThetaErrorIntegrand m t‖
        ≤ D * ((m : ℝ) * ((Real.log t) ^ (m - 1) *
            Real.exp (-c * Real.sqrt (Real.log t)) / t))
          + D * ((Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t) := by
      intro t ht
      have htx : x < t := ht
      have htT : T ≤ t := le_of_lt (lt_of_le_of_lt hxT htx)
      have ht2 : (2 : ℝ) < t := by linarith
      have htpos : (0 : ℝ) < t := by linarith
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
      have hA : (0 : ℝ) ≤ (m : ℝ) * (Real.log t) ^ (m - 1) :=
        mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hlogt.le _)
      have hB : (0 : ℝ) ≤ (Real.log t) ^ m := pow_nonneg hlogt.le _
      have hfac : |derivLogPowDivId m t * t|
          ≤ ((m : ℝ) * (Real.log t) ^ (m - 1) + (Real.log t) ^ m) / t := by
        have hval : derivLogPowDivId m t * t
            = ((m : ℝ) * (Real.log t) ^ (m - 1) - (Real.log t) ^ m) / t := by
          rw [derivLogPowDivId]
          field_simp
        rw [hval, abs_div, abs_of_pos htpos]
        have hnum : |(m : ℝ) * (Real.log t) ^ (m - 1) - (Real.log t) ^ m|
            ≤ (m : ℝ) * (Real.log t) ^ (m - 1) + (Real.log t) ^ m := by
          rw [abs_le]
          constructor <;> linarith
        exact div_le_div_of_nonneg_right hnum htpos.le
      rw [Real.norm_eq_abs, logPowThetaErrorIntegrand, abs_mul]
      calc |derivLogPowDivId m t * t| * |thetaError t|
          ≤ (((m : ℝ) * (Real.log t) ^ (m - 1) + (Real.log t) ^ m) / t)
              * (D * Real.exp (-c * Real.sqrt (Real.log t))) :=
            mul_le_mul hfac (herrB t htT) (abs_nonneg _) (by positivity)
        _ = D * ((m : ℝ) * ((Real.log t) ^ (m - 1) *
              Real.exp (-c * Real.sqrt (Real.log t)) / t))
            + D * ((Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t) := by
            field_simp
    have hgint : IntegrableOn (fun t : ℝ =>
        D * ((m : ℝ) * ((Real.log t) ^ (m - 1) * Real.exp (-c * Real.sqrt (Real.log t)) / t))
          + D * ((Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t)) (Ioi x) := by
      refine Integrable.add ?_ ?_
      · exact (((integrableOn_logPow_pntErrorWeight hc0 (m - 1)).mono_set
          (Ioi_subset_Ioi hx2)).const_mul _).const_mul D
      · exact ((integrableOn_logPow_pntErrorWeight hc0 m).mono_set
          (Ioi_subset_Ioi hx2)).const_mul D
    have hnorm : ‖∫ t in Ioi x, logPowThetaErrorIntegrand m t‖
        ≤ ∫ t in Ioi x,
            (D * ((m : ℝ) * ((Real.log t) ^ (m - 1) *
              Real.exp (-c * Real.sqrt (Real.log t)) / t))
              + D * ((Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t)) := by
      refine MeasureTheory.norm_integral_le_of_norm_le hgint ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hptb t ht
    rw [Real.norm_eq_abs] at hnorm
    refine hnorm.trans ?_
    rw [integral_add
      (((integrableOn_logPow_pntErrorWeight hc0 (m - 1)).mono_set
        (Ioi_subset_Ioi hx2)).const_mul _ |>.const_mul D)
      (((integrableOn_logPow_pntErrorWeight hc0 m).mono_set (Ioi_subset_Ioi hx2)).const_mul D),
      integral_const_mul, integral_const_mul, integral_const_mul]
    have ht1 := setIntegral_Ioi_logPow_pntErrorWeight_le hc0 (m - 1) hx2
    have ht2 := setIntegral_Ioi_logPow_pntErrorWeight_le hc0 m hx2
    rw [← hJ1] at ht1
    rw [← hJ2] at ht2
    have hstep : D * ((m : ℝ) * (∫ t in Ioi x,
          (Real.log t) ^ (m - 1) * Real.exp (-c * Real.sqrt (Real.log t)) / t))
        + D * (∫ t in Ioi x, (Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t)
        ≤ D * ((m : ℝ) * (Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * J1))
          + D * (Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * J2) := by
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h1 := mul_le_mul_of_nonneg_left ht1 hm
      nlinarith [hD, h1, ht2]
    refine hstep.trans_eq ?_
    ring
  -- combine
  have hexp : Real.exp (-c * Real.sqrt (Real.log x))
      ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    refine Real.exp_le_exp.mpr ?_
    have hs : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
    nlinarith
  have hpow1 : (1 : ℝ) ≤ (Real.log x) ^ m := one_le_pow₀ hlogx1
  have htri : |logPowDivId m x * (Chebyshev.theta x - x)
      + ∫ t in Ioi x, logPowThetaErrorIntegrand m t|
      ≤ |logPowDivId m x * (Chebyshev.theta x - x)|
        + |∫ t in Ioi x, logPowThetaErrorIntegrand m t| := abs_add_le _ _
  refine htri.trans ?_
  have hbb1 : |logPowDivId m x * (Chebyshev.theta x - x)|
      ≤ D * (Real.log x) ^ m * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    refine hb1.trans ?_
    gcongr
  have hbb2 : |∫ t in Ioi x, logPowThetaErrorIntegrand m t|
      ≤ D * ((m : ℝ) * J1 + J2) * (Real.log x) ^ m
        * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    refine hb2.trans ?_
    have hcoef : (0 : ℝ) ≤ D * ((m : ℝ) * J1 + J2) :=
      mul_nonneg hD (by
        have hm : (0 : ℝ) ≤ (m : ℝ) * J1 := mul_nonneg (Nat.cast_nonneg m) hJ1nn
        linarith)
    have hexp0 : (0 : ℝ) < Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := Real.exp_pos _
    calc D * ((m : ℝ) * J1 + J2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x))
        = D * ((m : ℝ) * J1 + J2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * 1 := by ring
      _ ≤ D * ((m : ℝ) * J1 + J2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x))
            * (Real.log x) ^ m :=
          mul_le_mul_of_nonneg_left hpow1 (mul_nonneg hcoef hexp0.le)
      _ = D * ((m : ℝ) * J1 + J2) * (Real.log x) ^ m
            * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by ring
  refine (add_le_add hbb1 hbb2).trans_eq ?_
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory Asymptotics

/-! ## The monomial endpoint defect -/

theorem primeBoundaryDefect_pow_eq (m : ℕ) {x : ℝ} (hx : 4 ≤ x) :
    primeBoundaryDefect (fun u : ℝ => u ^ (m + 1)) x
      = primeLogPowSum (m + 1) x / (Real.log x) ^ (m + 1) - 1 / ((m : ℝ) + 1) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogpow : ((Real.log x) ^ (m + 1)) ≠ 0 := by positivity
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
      (if n.Prime then (Real.log n / Real.log x) ^ (m + 1) / n else 0))
      = primeLogPowSum (m + 1) x / (Real.log x) ^ (m + 1) := by
    rw [primeLogPowSum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [primeLogPowWeight]
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp, div_pow]
      field_simp
    · rw [if_neg hp, if_neg hp, zero_div]
  have hint : (∫ u in (0 : ℝ)..1, u ^ (m + 1) / u) = 1 / ((m : ℝ) + 1) := by
    have hae : (fun u : ℝ => u ^ (m + 1) / u) =ᶠ[ae volume] fun u : ℝ => u ^ m := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
      have hu0 : u ≠ 0 := hu
      field_simp
      ring
    rw [intervalIntegral.integral_congr_ae (hae.mono (fun u hu _ => hu)), integral_pow]
    field_simp
    rw [one_pow, zero_pow (by omega)]
    ring
  rw [primeBoundaryDefect, hsum, hint]

/-- **`(10)`: the monomial endpoint defect.**  For every algebraic order `M`, the normalized
prime-harmonic defect at the monomial `u^{m+1}` equals `C_{m+1}/L^{m+1}` up to `O(L^{-M-1})`. -/
theorem exists_abs_primeBoundaryDefect_pow_le (m M : ℕ) :
    ∃ B X₀ : ℝ, 0 ≤ B ∧ 4 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      |primeBoundaryDefect (fun u : ℝ => u ^ (m + 1)) x
          - mertensLogPowConstantFull m / (Real.log x) ^ (m + 1)|
        ≤ B / (Real.log x) ^ (M + 1) := by
  obtain ⟨B, c, X₀, hc0, hB, hX₀, hbound⟩ := exists_primeLogPowSum_sub_bound m
  obtain ⟨K, hKnn, hKbound⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y →
      Real.exp (-c * Real.sqrt y) ≤ K / y ^ (M + 1) := by
    have hcpow : (0 : ℝ) < c ^ (2 * (M + 1)) := pow_pos hc0 _
    have hfac : (0 : ℝ) < (((2 * (M + 1)).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    refine ⟨(((2 * (M + 1)).factorial : ℕ) : ℝ) / c ^ (2 * (M + 1)),
      le_of_lt (div_pos hfac hcpow), ?_⟩
    intro y hy
    have h := exp_neg_sqrt_le_pow hc0 (M + 1) hy
    rwa [div_div]
  refine ⟨B * K, X₀, mul_nonneg hB hKnn, hX₀, ?_⟩
  intro x hx
  have hx4 : (4 : ℝ) ≤ x := le_trans hX₀ hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx1 : 1 ≤ Real.log x := by
    have he : Real.exp 1 ≤ x := by nlinarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) he
  have hval : primeBoundaryDefect (fun u : ℝ => u ^ (m + 1)) x
      - mertensLogPowConstantFull m / (Real.log x) ^ (m + 1)
      = (primeLogPowSum (m + 1) x - (Real.log x) ^ (m + 1) / ((m : ℝ) + 1)
          - mertensLogPowConstantFull m) / (Real.log x) ^ (m + 1) := by
    rw [primeBoundaryDefect_pow_eq m hx4]
    field_simp
  rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (Real.log x) ^ (m + 1))]
  have hnum := hbound x hx
  have hexpK : Real.exp (-c * Real.sqrt (Real.log x)) ≤ K / (Real.log x) ^ (M + 1) :=
    hKbound _ hlogx
  have hstep : |primeLogPowSum (m + 1) x - (Real.log x) ^ (m + 1) / ((m : ℝ) + 1)
      - mertensLogPowConstantFull m| / (Real.log x) ^ (m + 1)
      ≤ (B * (Real.log x) ^ m * Real.exp (-c * Real.sqrt (Real.log x)))
        / (Real.log x) ^ (m + 1) := by
    gcongr
  refine hstep.trans ?_
  have heq : (B * (Real.log x) ^ m * Real.exp (-c * Real.sqrt (Real.log x)))
      / (Real.log x) ^ (m + 1) = B * Real.exp (-c * Real.sqrt (Real.log x)) / Real.log x := by
    field_simp
    ring
  rw [heq]
  have hstep2 : B * Real.exp (-c * Real.sqrt (Real.log x)) / Real.log x
      ≤ B * (K / (Real.log x) ^ (M + 1)) / Real.log x := by
    gcongr
  refine hstep2.trans ?_
  have hgoal : B * (K / (Real.log x) ^ (M + 1)) / Real.log x
      = B * K / ((Real.log x) ^ (M + 1) * Real.log x) := by
    field_simp
  rw [hgoal]
  refine div_le_div_of_nonneg_left (mul_nonneg hB hKnn) (pow_pos hlogx (M + 1)) ?_
  calc (Real.log x) ^ (M + 1) = (Real.log x) ^ (M + 1) * 1 := (mul_one _).symm
    _ ≤ (Real.log x) ^ (M + 1) * Real.log x := by gcongr

end

end RHTower
