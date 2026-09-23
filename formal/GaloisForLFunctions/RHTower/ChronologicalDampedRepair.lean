import GaloisForLFunctions.RHTower.ChronologicalLambertRepair
import GaloisForLFunctions.RHTower.ChronologicalFermiRepair

/-!
# Bounded arithmetic coefficients from damped chronological repair

The damped fixed point is q/(1+εq). Its exact formal Lambert inverse is
μ convolved with the geometric source (-ε)^(d-1), bounded by 1/(1-ε)
for 0≤ε<1 and uniformly by two for 0≤ε≤1/2. The rational response
has full squared L² error at most ε²/4.

The finite arithmetic heat residual is a geometric mixture of raw Möbius
heat errors at the exact cutoffs N/d, plus an explicit exponential term.
This identity exposes the remaining truncation problem. It does not prove
convergence of these finite residuals or the Riemann hypothesis.
-/

noncomputable section
open Finset Set MeasureTheory Filter
open scoped Topology
namespace RHTower

def chronologicalDampedSeries (ε : ℝ) : PowerSeries ℝ :=
  PowerSeries.X * PowerSeries.mk (fun n => (-ε)^n)

theorem chronologicalDampedSeries_equation (ε : ℝ) :
    (1 + PowerSeries.C ε * PowerSeries.X) * chronologicalDampedSeries ε = PowerSeries.X := by
  have hi : (1 + PowerSeries.C ε * PowerSeries.X) *
      PowerSeries.mk (fun n => (-ε)^n) = 1 := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [add_mul]
    | succ n =>
      simp [add_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, pow_succ]
      ring
  unfold chronologicalDampedSeries
  calc
    _ = PowerSeries.X * ((1 + PowerSeries.C ε * PowerSeries.X) *
        PowerSeries.mk (fun n => (-ε)^n)) := by ring
    _ = _ := by rw [hi, mul_one]

def chronologicalDampedSource (ε : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => PowerSeries.coeff n (chronologicalDampedSeries ε), by simp [chronologicalDampedSeries]⟩

def chronologicalDampedArithmetic (ε : ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * chronologicalDampedSource ε

theorem chronologicalDampedSource_apply (ε : ℝ) (n : ℕ) (hn : 0 < n) :
    chronologicalDampedSource ε n = (-ε)^(n-1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp [chronologicalDampedSource, chronologicalDampedSeries, PowerSeries.coeff_succ_X_mul]

theorem chronologicalDampedArithmetic_reconstruct (ε : ℝ) :
    chronologicalLambertSeries (chronologicalDampedArithmetic ε) = chronologicalDampedSeries ε := by
  apply PowerSeries.ext
  intro n
  simp only [chronologicalLambertSeries, PowerSeries.coeff_mk]
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * chronologicalDampedArithmetic ε =
      chronologicalDampedSource ε := by
    rw [chronologicalDampedArithmetic, ← mul_assoc,
      ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  rw [he]
  rfl

theorem chronologicalDampedArithmetic_formula (ε : ℝ) (n : ℕ) :
    chronologicalDampedArithmetic ε n =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n/d) : ℝ) * (-ε)^(d-1) := by
  rw [chronologicalDampedArithmetic, ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.intCoe_apply]
  rw [Nat.sum_divisorsAntidiagonal' (fun a b =>
      (ArithmeticFunction.moebius a : ℝ) * chronologicalDampedSource ε b)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [chronologicalDampedSource_apply ε d (Nat.pos_of_mem_divisors hd)]

theorem chronologicalDampedArithmetic_bound (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    |chronologicalDampedArithmetic ε n| ≤ 1 / (1-ε) := by
  rw [chronologicalDampedArithmetic_formula]
  have hg := hasSum_geometric_of_lt_one hε0 hε1
  calc
    _ ≤ ∑ d ∈ n.divisors, |(ArithmeticFunction.moebius (n/d) : ℝ) * (-ε)^(d-1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, ε^(d-1) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hε0]
      have hb : |(ArithmeticFunction.moebius (n/d) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n/d)
      exact mul_le_of_le_one_left (pow_nonneg hε0 _) hb
    _ = ∑ j ∈ n.divisors.image (fun d => d-1), ε^j := by
      rw [Finset.sum_image]
      intro a ha b hb he
      change a-1=b-1 at he
      have ha0 := Nat.pos_of_mem_divisors ha
      have hb0 := Nat.pos_of_mem_divisors hb
      omega
    _ ≤ ∑' j : ℕ, ε^j := hg.summable.sum_le_tsum _ (fun j _ => pow_nonneg hε0 j)
    _ = _ := by simpa only [one_div] using hg.tsum_eq

theorem chronologicalDampedArithmetic_uniform_bound (ε : ℝ) (hε0 : 0 ≤ ε) (hεh : ε ≤ 1/2) :
    ∀ n, |chronologicalDampedArithmetic ε n| ≤ 2 := by
  intro n
  have hh := chronologicalDampedArithmetic_bound ε hε0 (by linarith) n
  have hi : 1/(1-ε) ≤ (2:ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 1-ε)).mpr
    linarith
  exact hh.trans hi

def chronologicalDampedResponse (ε t : ℝ) : ℝ :=
  Real.exp (-t) / (1 + ε * Real.exp (-t))

theorem chronologicalDampedResponse_fixed (ε t : ℝ) (hε : 0 ≤ ε) :
    chronologicalDampedResponse ε t = chronologicalFermi t *
      (1 + (1-ε) * chronologicalDampedResponse ε t) := by
  unfold chronologicalDampedResponse chronologicalFermi
  rw [Real.exp_neg]
  field_simp
  ring

theorem chronologicalDampedResponse_error (ε t : ℝ) (hε : 0 ≤ ε) :
    Real.exp (-t) - chronologicalDampedResponse ε t =
      ε * Real.exp (-2*t) / (1 + ε * Real.exp (-t)) := by
  have hd : 1 + ε * Real.exp (-t) ≠ 0 := by positivity
  unfold chronologicalDampedResponse
  have he : Real.exp (-2*t) = Real.exp (-t)^(2 : ℕ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp
  ring

theorem chronologicalDampedResponse_error_sq_le (ε t : ℝ) (hε : 0 ≤ ε) :
    (Real.exp (-t) - chronologicalDampedResponse ε t)^(2 : ℕ) ≤ ε^(2 : ℕ) * Real.exp (-4*t) := by
  rw [chronologicalDampedResponse_error ε t hε]
  have hd : 1 ≤ 1 + ε * Real.exp (-t) := by
    have hh : 0 ≤ ε * Real.exp (-t) := by positivity
    linarith
  have he : 0 ≤ ε * Real.exp (-2*t) := by positivity
  have hh := div_le_self he hd
  have hp := sq_le_sq₀ (by positivity : 0 ≤ ε * Real.exp (-2*t) / (1 + ε * Real.exp (-t))) he |>.mpr hh
  have hex : Real.exp (-2*t)^(2 : ℕ) = Real.exp (-4*t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, hex] using hp

theorem chronologicalDampedResponse_continuous (ε : ℝ) (hε : 0 ≤ ε) :
    Continuous (chronologicalDampedResponse ε) := by
  apply (Real.continuous_exp.comp continuous_neg).div
    (continuous_const.add (continuous_const.mul (Real.continuous_exp.comp continuous_neg)))
  intro t
  change 1 + ε * Real.exp (-t) ≠ 0
  positivity

def chronologicalDampedResponseEnergy (ε : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), (Real.exp (-t) - chronologicalDampedResponse ε t)^(2 : ℕ)

theorem chronologicalDampedResponse_error_integrable (ε : ℝ) (hε : 0 ≤ ε) :
    IntegrableOn (fun t => (Real.exp (-t) - chronologicalDampedResponse ε t)^(2 : ℕ)) (Ioi 0) := by
  have hb := (integrableOn_exp_mul_Ioi (a := (-4:ℝ)) (by linarith) 0).const_mul (ε^(2 : ℕ))
  apply hb.mono' ((Real.continuous_exp.comp continuous_neg).sub
    (chronologicalDampedResponse_continuous ε hε) |>.pow 2 |>.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact chronologicalDampedResponse_error_sq_le ε t hε

theorem chronologicalDampedResponseEnergy_bound (ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ chronologicalDampedResponseEnergy ε ∧ chronologicalDampedResponseEnergy ε ≤ ε^(2 : ℕ)/4 := by
  constructor
  · exact integral_nonneg (fun t => sq_nonneg _)
  · have hh := integral_mono (chronologicalDampedResponse_error_integrable ε hε)
      ((integrableOn_exp_mul_Ioi (a := (-4:ℝ)) (by linarith) 0).const_mul (ε^(2 : ℕ)))
      (chronologicalDampedResponse_error_sq_le ε · hε)
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : (-4:ℝ)<0) 0] at hh
    simpa only [chronologicalDampedResponseEnergy, mul_zero, Real.exp_zero, neg_div_neg_eq,
      div_eq_mul_inv, inv_neg, neg_mul_neg, one_mul] using hh

theorem chronologicalDampedResponseEnergy_tendsto {ε : ℕ → ℝ} (hε : ∀ N, 0 ≤ ε N)
    (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun N => chronologicalDampedResponseEnergy (ε N)) atTop (𝓝 0) := by
  have hh := (ht.pow 2).div_const 4
  simp only [zero_pow (by omega : 2 ≠ 0), zero_div] at hh
  exact squeeze_zero (fun N => (chronologicalDampedResponseEnergy_bound (ε N) (hε N)).1)
    (fun N => (chronologicalDampedResponseEnergy_bound (ε N) (hε N)).2) hh

private theorem chronologicalDivisorWindow_sum (F : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ d ∈ Finset.Ioc 0 N, ∑ k ∈ Finset.Ioc 0 (N/d), F d k := by
  have he : (∑ n ∈ Finset.Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2) =
      ∑ x ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N with x.1*x.2 ≤ N, F x.1 x.2 := by
    trans ∑ n ∈ Finset.Ioc 0 N, ∑ x ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N with x.1*x.2 = n, F x.1 x.2
    · refine sum_congr rfl fun n hn => ?_
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (Finset.mem_Ioc.mp hn).1.ne' (Finset.mem_Ioc.mp hn).2]
    · simp_rw [sum_filter]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => by simp_all
  rw [he, sum_filter, sum_product]
  apply sum_congr rfl
  intro d hd
  simp only [sum_ite, not_le, sum_const_zero, add_zero]
  congr 1
  ext k
  simp only [mem_filter, Finset.mem_Ioc, and_assoc, and_congr_right_iff]
  intro hk
  have hdpos := (Finset.mem_Ioc.mp hd).1
  constructor
  · intro h
    exact (Nat.le_div_iff_mul_le hdpos).mpr (by simpa [Nat.mul_comm] using h.2)
  · intro h
    have hp := (Nat.le_div_iff_mul_le hdpos).mp h
    refine ⟨h.trans (Nat.div_le_self _ _), ?_⟩
    simpa [Nat.mul_comm] using hp

theorem chronologicalDampedArithmetic_finite_transform (ε : ℝ) (N : ℕ) (Φ : ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc 0 N, chronologicalDampedArithmetic ε n * Φ n =
      ∑ d ∈ Finset.Ioc 0 N, (-ε)^(d-1) *
        ∑ k ∈ Finset.Ioc 0 (N/d), (ArithmeticFunction.moebius k : ℝ) * Φ (d*k) := by
  have he : (∑ n ∈ Finset.Ioc 0 N, chronologicalDampedArithmetic ε n * Φ n) =
      ∑ n ∈ Finset.Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal,
        chronologicalDampedSource ε x.1 * (ArithmeticFunction.moebius x.2 : ℝ) * Φ (x.1*x.2) := by
    apply sum_congr rfl
    intro n hn
    rw [chronologicalDampedArithmetic, mul_comm (ArithmeticFunction.moebius : ArithmeticFunction ℝ),
      ArithmeticFunction.mul_apply, sum_mul]
    apply sum_congr rfl
    intro x hx
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    rfl
  rw [he, chronologicalDivisorWindow_sum (fun a b =>
    chronologicalDampedSource ε a * (ArithmeticFunction.moebius b : ℝ) * Φ (a*b))]
  apply sum_congr rfl
  intro d hd
  rw [chronologicalDampedSource_apply ε d (Finset.mem_Ioc.mp hd).1, mul_sum]
  apply sum_congr rfl
  intro k hk
  ring

def chronologicalRawHeatError (N : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t) + ∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
    GaloisForLFunctions.HTGeometry.ChronologicalTensor.fusionBoseDefect ((k:ℝ)*t)

def chronologicalDampedHeatError (ε : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t) + ∑ k ∈ Finset.Ioc 0 N, chronologicalDampedArithmetic ε k *
    GaloisForLFunctions.HTGeometry.ChronologicalTensor.fusionBoseDefect ((k:ℝ)*t)

theorem chronologicalDampedHeatError_exact_remainder (ε : ℝ) (N : ℕ) (t : ℝ) :
    chronologicalDampedHeatError ε N t =
      Real.exp (-t) - ∑ d ∈ Finset.Ioc 0 N, (-ε)^(d-1) * Real.exp (-((d:ℝ)*t)) +
        ∑ d ∈ Finset.Ioc 0 N, (-ε)^(d-1) * chronologicalRawHeatError (N/d) ((d:ℝ)*t) := by
  have he := chronologicalDampedArithmetic_finite_transform ε N
    (fun n => GaloisForLFunctions.HTGeometry.ChronologicalTensor.fusionBoseDefect ((n:ℝ)*t))
  unfold chronologicalDampedHeatError
  rw [he]
  simp only [chronologicalRawHeatError, mul_add, sum_add_distrib]
  have hs : (∑ d ∈ Finset.Ioc 0 N, (-ε)^(d-1) *
      ∑ k ∈ Finset.Ioc 0 (N/d), (ArithmeticFunction.moebius k : ℝ) *
        GaloisForLFunctions.HTGeometry.ChronologicalTensor.fusionBoseDefect ((↑(d*k):ℝ)*t)) =
      ∑ d ∈ Finset.Ioc 0 N, (-ε)^(d-1) *
        ∑ k ∈ Finset.Ioc 0 (N/d), (ArithmeticFunction.moebius k : ℝ) *
          GaloisForLFunctions.HTGeometry.ChronologicalTensor.fusionBoseDefect ((k:ℝ)*((d:ℝ)*t)) := by
    simp only [Nat.cast_mul, mul_assoc, mul_comm]
  rw [hs]
  ring

end RHTower
