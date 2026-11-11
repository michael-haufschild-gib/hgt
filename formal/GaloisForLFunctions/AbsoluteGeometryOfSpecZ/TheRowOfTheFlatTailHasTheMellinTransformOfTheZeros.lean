import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheJetsOfTheFlatTailHaveLogarithmicMoments
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorSymbolSplitsAtTheZeros
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.HTGeometry.DigammaMittagLeffler
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.RHTower.LagExplicitFormula

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

/-- The real von Mangoldt series is `−ζ′/ζ` on the real line. -/
theorem ofReal_tsum_vonMangoldt_rpow {σ : ℝ} (hσ : 1 < σ) :
    ((∑' k : ℕ, (Λ k : ℝ) * (k : ℝ) ^ (-σ) : ℝ) : ℂ) =
      -deriv riemannZeta σ / riemannZeta σ := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries,
    Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [LSeries.term_of_ne_zero hk.ne', Complex.ofReal_mul, Complex.ofReal_cpow hk0,
      Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, div_eq_mul_inv]

/-! ### The series of the logarithm -/

/-- **The Mellin transform of `−log(1 − t²)`** through the series of the logarithm. -/
theorem hasSum_integral_rpow_mul_neg_log {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun m : ℕ => 1 / (((m : ℝ) + 1) * (ε + 2 * ((m : ℝ) + 1) + 1)))
      (∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * -Real.log (1 - t ^ 2)) := by
  have hGcont : ∀ m : ℕ, Continuous fun t : ℝ => t ^ ε * ((t ^ 2) ^ (m + 1) / ((m : ℝ) + 1)) :=
    fun m => (Real.continuous_rpow_const hε.le).mul (by fun_prop)
  have hGint : ∀ m : ℕ, Integrable (fun t : ℝ => t ^ ε * ((t ^ 2) ^ (m + 1) / ((m : ℝ) + 1)))
      (volume.restrict (Set.Ioo 0 1)) := fun m =>
    ((hGcont m).integrableOn_Ioc (a := 0) (b := 1)).mono_set Set.Ioo_subset_Ioc_self
  have hGval : ∀ m : ℕ,
      ∫ t in Set.Ioo (0 : ℝ) 1, t ^ ε * ((t ^ 2) ^ (m + 1) / ((m : ℝ) + 1)) =
        1 / (((m : ℝ) + 1) * (ε + 2 * ((m : ℝ) + 1) + 1)) := by
    intro m
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hd : (0 : ℝ) < ε + 2 * ((m : ℝ) + 1) + 1 := by positivity
    have hr : (-1 : ℝ) < ε + ((2 * (m + 1) : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((2 * (m + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h := integral_Ioc_rpow hr zero_le_one
    rw [Real.one_rpow] at h
    have hcongr : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * ((t ^ 2) ^ (m + 1) / ((m : ℝ) + 1)) =
        ∫ t in Set.Ioc (0 : ℝ) 1, (1 / ((m : ℝ) + 1)) * t ^ (ε + ((2 * (m + 1) : ℕ) : ℝ)) :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by
        show t ^ ε * ((t ^ 2) ^ (m + 1) / ((m : ℝ) + 1)) =
          (1 / ((m : ℝ) + 1)) * t ^ (ε + ((2 * (m + 1) : ℕ) : ℝ))
        rw [Real.rpow_add ht.1, Real.rpow_natCast, ← pow_mul]
        ring
    rw [← integral_Ioc_eq_integral_Ioo, hcongr, integral_const_mul, h]
    push_cast
    field_simp
  have hnorm : ∀ m : ℕ,
      ∫ t in Set.Ioo (0 : ℝ) 1, ‖t ^ ε * ((t ^ 2) ^ (m + 1) / ((m : ℝ) + 1))‖ =
        1 / (((m : ℝ) + 1) * (ε + 2 * ((m : ℝ) + 1) + 1)) := by
    intro m
    rw [← hGval m]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    show ‖t ^ ε * ((t ^ 2) ^ (m + 1) / ((m : ℝ) + 1))‖ = _
    have ht0 : 0 ≤ t ^ ε := Real.rpow_nonneg ht.1.le ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsummable : Summable fun m : ℕ => 1 / (((m : ℝ) + 1) * (ε + 2 * ((m : ℝ) + 1) + 1)) := by
    have hbase : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
      have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using h
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hbase
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul, sq]
    exact mul_le_mul_of_nonneg_left (by linarith) hm.le
  have hsum := hasSum_integral_of_summable_integral_norm hGint
    (by simp only [hnorm]; exact hsummable)
  simp only [hGval] at hsum
  have hval : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * -Real.log (1 - t ^ 2) =
      ∫ t in Set.Ioo (0 : ℝ) 1,
        ∑' m : ℕ, t ^ ε * ((t ^ 2) ^ (m + 1) / ((m : ℝ) + 1)) := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hlt : |t ^ 2| < 1 := by
      rw [abs_of_nonneg (sq_nonneg t)]
      nlinarith [ht.1, ht.2]
    exact (((Real.hasSum_pow_div_log_of_abs_lt_one hlt).mul_left (t ^ ε)).tsum_eq).symm
  rw [hval]
  exact hsum

/-- The Mellin transform of `−log(1 − t²)` is the digamma function. -/
theorem ofReal_integral_rpow_mul_neg_log {ε : ℝ} (hε : 0 < ε) :
    (1 + (ε : ℂ)) * ((∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * -Real.log (1 - t ^ 2) : ℝ) : ℂ) =
      Complex.digamma ((1 + (ε : ℂ)) / 2 + 1) + Real.eulerMascheroniConstant := by
  have hz : 0 < ((1 + (ε : ℂ)) / 2 + 1).re := by
    simp
    linarith
  have h1 := RHTower.hasSum_digammaSeries hz
  have h2 := (Complex.ofRealCLM.hasSum (hasSum_integral_rpow_mul_neg_log hε)).mul_left
    (1 + (ε : ℂ))
  have e : (fun m : ℕ => 1 / ((m : ℂ) + 1) - 1 / ((1 + (ε : ℂ)) / 2 + 1 + m)) =
      fun m : ℕ => (1 + (ε : ℂ)) *
        Complex.ofRealCLM (1 / (((m : ℝ) + 1) * (ε + 2 * ((m : ℝ) + 1) + 1))) := by
    funext m
    have hm : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    have hd : (ε : ℂ) + 2 * ((m : ℂ) + 1) + 1 ≠ 0 := by
      have h : ((ε + 2 * ((m : ℝ) + 1) + 1 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by positivity)
      push_cast at h
      exact h
    have hz' : (1 + (ε : ℂ)) / 2 + 1 + m ≠ 0 := by
      have h : (((1 + ε) / 2 + 1 + m : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by positivity)
      push_cast at h
      exact h
    rw [Complex.ofRealCLM_apply]
    push_cast
    field_simp
    ring
  rw [e] at h1
  exact h2.unique h1

/-! ### The Mellin transform of the row -/

/-- **The Mellin transform of the row of the flat tail is the sum over the zeros**:
`∫_0^1 t^ε ϱ(t) dt = Σ_ρ 1/(ρ (1 + ε − ρ))` for `ε > 0`. -/
theorem mellin_rowProfile {ε : ℝ} (hε : 0 < ε) :
    ((∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * rowProfile t : ℝ) : ℂ) =
      ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 + (ε : ℂ) - (q.1 : ℂ))) := by
  obtain ⟨Lr, hLr⟩ : ∃ x : ℝ, x = ∑' k : ℕ, (Λ k : ℝ) * (k : ℝ) ^ (-(1 + ε)) := ⟨_, rfl⟩
  obtain ⟨Ir, hIr⟩ : ∃ x : ℝ, x = ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * -Real.log (1 - t ^ 2) :=
    ⟨_, rfl⟩
  -- the prime part
  have hpr : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * primeRemainder t = 1 / ε - Lr / (1 + ε) := by
    have hψint : IntegrableOn (fun t : ℝ => t ^ ε * Chebyshev.psi (1 / t)) (Set.Ioc 0 1) := by
      have h := (integrableOn_rpow_mul_inv hε).sub
        (integrableOn_rpow_mul hε.le integrableOn_primeRemainder measurable_primeRemainder)
      refine h.congr_fun (fun t _ => ?_) measurableSet_Ioc
      simp only [Pi.sub_apply, primeRemainder]
      ring
    have hsplit : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * primeRemainder t =
        (∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * (1 / t)) -
          ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * Chebyshev.psi (1 / t) := by
      rw [← integral_sub (integrableOn_rpow_mul_inv hε) hψint]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [primeRemainder]
      ring
    rw [hsplit, integral_rpow_mul_inv hε, ← (hasSum_integral_rpow_mul_psi hε).tsum_eq,
      tsum_div_const, hLr]
  -- the archimedean part
  have har : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * archRow t =
      1 / 2 * Ir - Real.log (2 * Real.pi) / (1 + ε) := by
    have hlogint : IntegrableOn (fun t : ℝ => t ^ ε * -Real.log (1 - t ^ 2)) (Set.Ioc 0 1) := by
      have h0 : IntegrableOn (fun t : ℝ => -Real.log (1 - t ^ 2)) (Set.Ioc 0 1) := by
        have h := (integrableOn_archRow.add
          (integrableOn_const (C := Real.log (2 * Real.pi)) (by simp))).const_mul 2
        refine h.congr_fun (fun t _ => ?_) measurableSet_Ioc
        simp only [Pi.add_apply, archRow]
        ring
      exact integrableOn_rpow_mul hε.le h0
        (Real.measurable_log.comp (measurable_const.sub (measurable_id.pow_const 2))).neg
    have hpow : IntegrableOn (fun t : ℝ => t ^ ε) (Set.Ioc 0 1) :=
      (Real.continuous_rpow_const hε.le).integrableOn_Ioc
    have hval : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε = 1 / (1 + ε) := by
      rw [integral_Ioc_rpow (by linarith) zero_le_one, Real.one_rpow, add_comm]
    have hsplit : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * archRow t =
        1 / 2 * (∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * -Real.log (1 - t ^ 2)) -
          Real.log (2 * Real.pi) * ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_sub (hlogint.const_mul _) (hpow.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [archRow]
      ring
    rw [hsplit, hval, hIr]
    ring
  have hreal : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * rowProfile t =
      1 / ε - Lr / (1 + ε) + (1 / 2 * Ir - Real.log (2 * Real.pi) / (1 + ε)) := by
    rw [← hpr, ← har, ← integral_add
      (integrableOn_rpow_mul hε.le integrableOn_primeRemainder measurable_primeRemainder)
      (integrableOn_rpow_mul hε.le integrableOn_archRow measurable_archRow)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [rowProfile]
    ring
  -- the point `s = 1 + ε`
  have hsre : (1 + (ε : ℂ)).re = 1 + ε := by simp
  have hs1 : 1 < (1 + (ε : ℂ)).re := by rw [hsre]; linarith
  have hs0 : 0 < (1 + (ε : ℂ)).re := by rw [hsre]; linarith
  have hεne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hsne : (1 + (ε : ℂ)) ≠ 0 := fun h => by
    rw [h] at hs0
    simp at hs0
  have hsne1 : (1 + (ε : ℂ)) ≠ 1 := fun h => hεne (by linear_combination h)
  have hxi : xi (1 + (ε : ℂ)) ≠ 0 := RHTower.xi_ne_zero_of_one_lt_re hs1
  have hζ : riemannZeta (1 + (ε : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  -- Hadamard's partial fractions
  have hH := RHTower.XiAtlasFinitePart.logDeriv_xi_sub_eq hxi
  have hterm : ∀ q : XiZeroCopy, (RHTower.XiAtlasFinitePart.xiZero q)⁻¹ -
      (RHTower.XiAtlasFinitePart.xiZero q - (1 + (ε : ℂ)))⁻¹ =
      (1 + (ε : ℂ)) * (1 / ((q.1 : ℂ) * (1 + (ε : ℂ) - (q.1 : ℂ)))) := by
    intro q
    have hρ : (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_ne_zero q
    have hsρ : (1 + (ε : ℂ)) - (q.1 : ℂ) ≠ 0 := by
      intro h
      have hq : (q.1 : ℂ) = 1 + (ε : ℂ) := (sub_eq_zero.mp h).symm
      have hz := RHTower.xi_xiZeroCopy_eq_zero q
      rw [hq] at hz
      exact hxi hz
    have hρs : (q.1 : ℂ) - (1 + (ε : ℂ)) ≠ 0 := fun h => hsρ (by linear_combination -h)
    show ((q.1 : ℂ))⁻¹ - ((q.1 : ℂ) - (1 + (ε : ℂ)))⁻¹ = _
    field_simp
    ring
  rw [tsum_congr hterm, tsum_mul_left] at hH
  have hsum : ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 + (ε : ℂ) - (q.1 : ℂ))) =
      (logDeriv xi (1 + (ε : ℂ)) - logDeriv xi 0) / (1 + (ε : ℂ)) := by
    rw [hH]
    field_simp
  -- the logarithmic derivative of `ξ` at `s` and at `0`
  have hadd := GaloisForLFunctions.ArithmeticCorrespondencePositivity.logDeriv_xi_eq_add
    hs0 hsne1 hζ
  have hΓ := RHTower.logDeriv_Gammaℝ_eq hs0
  have hdig := Complex.digamma_apply_add_one ((1 + (ε : ℂ)) / 2) (fun m h => by
    have h' := congrArg Complex.re h
    simp at h'
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  have hζ' : logDeriv riemannZeta (1 + (ε : ℂ)) =
      deriv riemannZeta (1 + (ε : ℂ)) / riemannZeta (1 + (ε : ℂ)) := logDeriv_apply _ _
  have h4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have hlog4 : Complex.log (4 * (Real.pi : ℂ)) =
      ((2 * Real.log 2 + Real.log Real.pi : ℝ) : ℂ) := by
    rw [← h4, Complex.ofReal_log (by positivity)]
    push_cast
    ring
  have h0 : logDeriv xi 0 =
      -((Real.eulerMascheroniConstant - ((2 * Real.log 2 + Real.log Real.pi : ℝ) : ℂ)) / 2 + 1) := by
    rw [RHTower.XiAtlasFinitePart.logDeriv_xi_zero, completedRiemannZeta₀_zero, hlog4]
  have hlog2 : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  -- the prime and gamma sides as complex numbers
  have hcast : ((1 + ε : ℝ) : ℂ) = 1 + (ε : ℂ) := by
    push_cast
    ring
  have hLc : (Lr : ℂ) = -deriv riemannZeta (1 + (ε : ℂ)) / riemannZeta (1 + (ε : ℂ)) := by
    have h := ofReal_tsum_vonMangoldt_rpow (by linarith : 1 < 1 + ε)
    rw [hcast, ← hLr] at h
    exact h
  have hIc : (Ir : ℂ) = (Complex.digamma ((1 + (ε : ℂ)) / 2) + ((1 + (ε : ℂ)) / 2)⁻¹ +
      Real.eulerMascheroniConstant) / (1 + (ε : ℂ)) := by
    have h := ofReal_integral_rpow_mul_neg_log hε
    rw [← hIr, hdig] at h
    rw [← h]
    field_simp
  rw [hreal, hsum, hadd, hΓ, hζ', h0, hlog2]
  push_cast
  rw [hIc, hLc]
  field_simp
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
