import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheJetsOfTheFlatTailHaveLogarithmicMoments
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorSymbolSplitsAtTheZeros
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.HTGeometry.DigammaMittagLeffler
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel

/-!
# The row of the flat tail has the Mellin transform of the zeros

In the coordinate `t = n/N` the row of the flat tail is

`ϱ(t) = 1/t − ψ(1/t) − ½ log(1 − t²) − log 2π`   (`rowProfile`),

the right side of von Mangoldt's formula for `ψ` at `1/t`. This file computes its Mellin
transform: for `ε > 0`, with `s = 1 + ε`,

`∫_0^1 t^ε ϱ(t) dt = Σ_ρ 1/(ρ (s − ρ))`   (`mellin_rowProfile`),

the sum over the zeros of `ξ` with multiplicity.

* `∫_0^1 t^ε ψ(1/t) dt = Σ_k Λ(k) k^{−s}/s = −ζ′(s)/(s ζ(s))`: each prime power `k` contributes
  on `t ≤ 1/k` (`hasSum_integral_rpow_mul_psi`).
* `∫_0^1 t^ε (−log(1 − t²)) dt = Σ_m 1/((m+1)(s + 2m + 2)) = (ψ_Γ(s/2 + 1) + γ)/s`: the series of
  the logarithm, then the series of the digamma function
  (`hasSum_integral_rpow_mul_neg_log`).
* `ξ′/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ ψ_Γ(s/2) + ζ′/ζ(s)` and `ξ′/ξ(0) = −(1 + (γ − log 4π)/2)`
  give `s ∫_0^1 t^ε ϱ = ξ′/ξ(s) − ξ′/ξ(0)`, and Hadamard's partial fractions give the sum.
-/

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower (XiZeroCopy xi)

/-! ### The row in the coordinate of the tail -/

/-- The row of the flat tail in the coordinate of the tail:
`ϱ(t) = 1/t − ψ(1/t) − ½ log(1 − t²) − log 2π`. -/
def rowProfile (t : ℝ) : ℝ := primeRemainder t + archRow t

theorem measurable_rowProfile : Measurable rowProfile :=
  measurable_primeRemainder.add measurable_archRow

/-- The moment `μ_j = ∫_0^1 log^j(1/t) ϱ(t) dt`. -/
def rowMoment (j : ℕ) : ℝ := ∫ t in Set.Ioc 0 1, logPow j t * rowProfile t

theorem rowMoment_eq (j : ℕ) : rowMoment j = primeMoment j + archMoment j := by
  rw [rowMoment, primeMoment, archMoment,
    ← integral_add (integrableOn_logPow_mul_primeRemainder j) (integrableOn_logPow_mul_archRow j)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [rowProfile]
  ring

/-- A weight dominated by a logarithmic profile is integrable against the row. -/
theorem integrableOn_mul_rowProfile {w : ℝ → ℝ} (hw : Measurable w) (j : ℕ) {c : ℝ}
    (hb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |w t| ≤ c * logPow j t) :
    IntegrableOn (fun t => w t * rowProfile t) (Set.Ioc 0 1) := by
  have h1 := (integrableOn_logPow_mul_primeRemainder j).abs
  have h2 := (integrableOn_logPow_mul_archRow j).abs
  refine Integrable.mono' ((h1.add h2).const_mul c)
    (hw.mul measurable_rowProfile).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
  have hL := logPow_nonneg j ht
  have hc := hb t ht
  have key : |w t| * |primeRemainder t + archRow t| ≤
      c * (|logPow j t * primeRemainder t| + |logPow j t * archRow t|) := by
    calc |w t| * |primeRemainder t + archRow t|
        ≤ (c * logPow j t) * (|primeRemainder t| + |archRow t|) :=
          mul_le_mul hc (abs_add_le _ _) (abs_nonneg _) ((abs_nonneg _).trans hc)
      _ = c * (|logPow j t * primeRemainder t| + |logPow j t * archRow t|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hL]
          ring
  rw [Real.norm_eq_abs, abs_mul, rowProfile]
  exact key

theorem integrableOn_primeRemainder : IntegrableOn primeRemainder (Set.Ioc 0 1) :=
  (integrableOn_logPow_mul_primeRemainder 0).congr_fun
    (fun t _ => by simp [logPow]) measurableSet_Ioc

theorem integrableOn_archRow : IntegrableOn archRow (Set.Ioc 0 1) :=
  (integrableOn_logPow_mul_archRow 0).congr_fun
    (fun t _ => by simp [logPow]) measurableSet_Ioc

/-! ### Powers of the coordinate -/

theorem integral_Ioc_rpow {r : ℝ} (hr : -1 < r) {c : ℝ} (hc : 0 ≤ c) :
    ∫ t in Set.Ioc (0 : ℝ) c, t ^ r = c ^ (r + 1) / (r + 1) := by
  rw [← intervalIntegral.integral_of_le hc, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith), sub_zero]

theorem measurable_rpow_const (ε : ℝ) : Measurable fun t : ℝ => t ^ ε :=
  measurable_id.pow_const ε

theorem abs_rpow_le_one {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    |t ^ ε| ≤ 1 := by
  rw [abs_of_nonneg (Real.rpow_nonneg ht.1.le ε)]
  exact Real.rpow_le_one ht.1.le ht.2 hε

/-- A function dominated by an integrable one stays integrable under a weight `t^ε`. -/
theorem integrableOn_rpow_mul {ε : ℝ} (hε : 0 ≤ ε) {f : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioc 0 1))
    (hm : Measurable f) : IntegrableOn (fun t => t ^ ε * f t) (Set.Ioc 0 1) := by
  refine Integrable.mono' hf.abs ((measurable_rpow_const ε).mul hm).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_rpow_le_one hε ht)

theorem integrableOn_rpow_mul_inv {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => t ^ ε * (1 / t)) (Set.Ioc 0 1) := by
  have h : IntegrableOn (fun t : ℝ => t ^ (ε - 1)) (Set.Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioc
  show t ^ (ε - 1) = t ^ ε * (1 / t)
  rw [Real.rpow_sub_one ht.1.ne']
  ring

theorem integral_rpow_mul_inv {ε : ℝ} (hε : 0 < ε) :
    ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * (1 / t) = 1 / ε := by
  have h := integral_Ioc_rpow (r := ε - 1) (by linarith) zero_le_one
  rw [Real.one_rpow, sub_add_cancel] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  show t ^ ε * (1 / t) = t ^ (ε - 1)
  rw [Real.rpow_sub_one ht.1.ne']
  ring

/-! ### The prime powers -/

/-- **The Mellin transform of `ψ(1/t)`**: the prime power `k` contributes on `t ≤ 1/k`. -/
theorem hasSum_integral_rpow_mul_psi {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun k : ℕ => (Λ k : ℝ) * (k : ℝ) ^ (-(1 + ε)) / (1 + ε))
      (∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * Chebyshev.psi (1 / t)) := by
  have hcont : IntegrableOn (fun t : ℝ => t ^ ε) (Set.Ioc 0 1) :=
    (Real.continuous_rpow_const hε.le).integrableOn_Ioc
  have hFint : ∀ k : ℕ, Integrable
      (fun t => (Λ k : ℝ) * (Set.Iic (1 / (k : ℝ))).indicator (fun t => t ^ ε) t)
      (volume.restrict (Set.Ioc 0 1)) := fun k =>
    (hcont.indicator measurableSet_Iic).const_mul _
  have hFval : ∀ k : ℕ, ∫ t in Set.Ioc (0 : ℝ) 1,
      (Λ k : ℝ) * (Set.Iic (1 / (k : ℝ))).indicator (fun t => t ^ ε) t =
      (Λ k : ℝ) * (k : ℝ) ^ (-(1 + ε)) / (1 + ε) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hc0 : (0 : ℝ) ≤ 1 / k := by positivity
      have hc1 : 1 / (k : ℝ) ≤ 1 := by
        rw [div_le_one hk0]
        exact_mod_cast hk
      have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iic (1 / (k : ℝ)) = Set.Ioc 0 (1 / (k : ℝ)) := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨⟨h1, h3.trans hc1⟩, h3⟩
      have e : (1 / (k : ℝ)) ^ (ε + 1) = (k : ℝ) ^ (-(1 + ε)) := by
        rw [one_div, Real.inv_rpow hk0.le, Real.rpow_neg hk0.le, add_comm]
      rw [integral_const_mul, setIntegral_indicator measurableSet_Iic, hset,
        integral_Ioc_rpow (by linarith) hc0, e]
      ring
  have hnorm : ∀ k : ℕ, ∫ t in Set.Ioc (0 : ℝ) 1,
      ‖(Λ k : ℝ) * (Set.Iic (1 / (k : ℝ))).indicator (fun t => t ^ ε) t‖ =
      (Λ k : ℝ) * (k : ℝ) ^ (-(1 + ε)) / (1 + ε) := by
    intro k
    rw [← hFval k]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    show ‖(Λ k : ℝ) * (Set.Iic (1 / (k : ℝ))).indicator (fun t => t ^ ε) t‖ = _
    -- on `(0, 1]` the cut power is nonnegative
    have hind : 0 ≤ (Set.Iic (1 / (k : ℝ))).indicator (fun t => t ^ ε) t := by
      rw [Set.indicator_apply]
      split_ifs
      · exact Real.rpow_nonneg ht.1.le ε
      · exact le_rfl
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hind)]
  have hsummable : Summable fun k : ℕ => ∫ t in Set.Ioc (0 : ℝ) 1,
      ‖(Λ k : ℝ) * (Set.Iic (1 / (k : ℝ))).indicator (fun t => t ^ ε) t‖ := by
    simp only [hnorm]
    exact (RHTower.summable_vonMangoldt_rpow (by linarith : 1 < 1 + ε)).div_const _
  have hsum := hasSum_integral_of_summable_integral_norm hFint hsummable
  simp only [hFval] at hsum
  have hval : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * Chebyshev.psi (1 / t) =
      ∫ t in Set.Ioc (0 : ℝ) 1,
        ∑' k : ℕ, (Λ k : ℝ) * (Set.Iic (1 / (k : ℝ))).indicator (fun t => t ^ ε) t := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    -- pointwise, the sum over the prime powers is `t^ε ψ(1/t)`
    have hx0 : 0 ≤ 1 / t := by
      have := ht.1
      positivity
    show t ^ ε * Chebyshev.psi (1 / t) =
      ∑' k : ℕ, (Λ k : ℝ) * (Set.Iic (1 / (k : ℝ))).indicator (fun t => t ^ ε) t
    rw [Chebyshev.psi_eq_sum_Icc, Finset.mul_sum, tsum_eq_sum (s := Finset.Icc 0 ⌊1 / t⌋₊)]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp
      · have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
        have hle : t ≤ 1 / (k : ℝ) :=
          (le_one_div ht.1 hk0').mpr ((Nat.le_floor_iff hx0).mp (Finset.mem_Icc.mp hk).2)
        rw [Set.indicator_of_mem (Set.mem_Iic.mpr hle)]
        exact mul_comm _ _
    · intro k hk
      have hk' : ⌊1 / t⌋₊ < k := by
        by_contra h
        exact hk (Finset.mem_Icc.mpr ⟨Nat.zero_le _, not_lt.mp h⟩)
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk')
      have hnle : ¬ t ≤ 1 / (k : ℝ) := fun h =>
        (not_le.mpr hk') ((Nat.le_floor_iff hx0).mpr ((le_one_div ht.1 hk0).mp h))
      rw [Set.indicator_of_notMem (by simpa using hnle), mul_zero]
  rw [hval]
  exact hsum

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
