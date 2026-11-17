import GaloisForLFunctions.HilbertMetric.Bergman.DiskAreaSurjectivity
import GaloisForLFunctions.HilbertMetric.Bergman.DiskReproducingKernel

/-!
# Sharp finite Taylor interpolation in the Bergman disk

A finite collection of Taylor coefficients determines a unique polynomial
of least area. Orthogonal decomposition gives the full excess norm and
its exact equality case on the entire holomorphic L² class. The same
coordinates give every sharp central derivative norm, attained by its
normalized monomial, including vanishing of all lower derivatives.
-/

open Complex MeasureTheory Metric
open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.Bergman
open HTGeometry
noncomputable section

/-- The polynomial with the prescribed finite collection of Taylor coefficients. -/
def finiteJetInterpolant (S : Finset ℕ) (v : ℕ → ℂ) : Disk :=
  ∑ n ∈ S, lp.single 2 n (v n / (Real.sqrt ((n : ℝ) + 1) : ℂ))

@[simp] theorem finiteJetInterpolant_apply (S : Finset ℕ) (v : ℕ → ℂ) (n : ℕ) :
    finiteJetInterpolant S v n =
      if n ∈ S then v n / (Real.sqrt ((n : ℝ) + 1) : ℂ) else 0 := by
  classical
  simp only [finiteJetInterpolant, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  simp

private theorem sqrt_index_ne_zero (n : ℕ) : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'

/-- Prescribed Taylor coefficients are recovered exactly; all others vanish. -/
theorem finiteJetInterpolant_coeff (S : Finset ℕ) (v : ℕ → ℂ) (n : ℕ) :
    diskCoeff (diskFun (finiteJetInterpolant S v)) n = if n ∈ S then v n else 0 := by
  classical
  rw [diskCoeff_diskFun, coefficient, finiteJetInterpolant_apply]
  split_ifs
  · exact mul_div_cancel₀ _ (sqrt_index_ne_zero n)
  · exact mul_zero _

/-- The coefficient model gives the literal interpolating polynomial on the whole plane. -/
theorem diskFun_finiteJetInterpolant (S : Finset ℕ) (v : ℕ → ℂ) (z : ℂ) :
    diskFun (finiteJetInterpolant S v) z = ∑ n ∈ S, v n * z ^ n := by
  classical
  have hc (n : ℕ) : coefficient (finiteJetInterpolant S v) n = if n ∈ S then v n else 0 := by
    rw [← diskCoeff_diskFun, finiteJetInterpolant_coeff]
  rw [diskFun, tsum_eq_sum (s := S) (fun n hn => by rw [hc, if_neg hn, zero_mul])]
  exact Finset.sum_congr rfl fun n hn => by rw [hc, if_pos hn]

/-- The exact squared norm is the weighted sum of the prescribed Taylor data. -/
theorem finiteJetInterpolant_norm_sq (S : Finset ℕ) (v : ℕ → ℂ) :
    ‖finiteJetInterpolant S v‖ ^ 2 = ∑ n ∈ S, ‖v n‖ ^ 2 / ((n : ℝ) + 1) := by
  classical
  rw [hardyDisk_norm_sq, tsum_eq_sum (s := S) (fun n hn => by
    rw [finiteJetInterpolant_apply, if_neg hn, norm_zero, zero_pow two_ne_zero])]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteJetInterpolant_apply, if_pos hn, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]

private theorem finiteJetInterpolant_orthogonal (S : Finset ℕ) (a : Disk) :
    inner ℂ (finiteJetInterpolant S (coefficient a))
      (a - finiteJetInterpolant S (coefficient a)) = 0 := by
  classical
  rw [lp.inner_eq_tsum]
  calc
    _ = ∑' _n : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      rw [RCLike.inner_apply, lp.coeFn_sub, Pi.sub_apply, finiteJetInterpolant_apply]
      by_cases hn : n ∈ S
      · have hc : coefficient a n / (Real.sqrt ((n : ℝ) + 1) : ℂ) = a n := by
          unfold coefficient
          field_simp [sqrt_index_ne_zero n]
        simp only [if_pos hn, hc, sub_self, zero_mul]
      · simp only [if_neg hn, map_zero, mul_zero]
    _ = 0 := by simp

/-- Finite Taylor interpolation splits off an orthogonal remainder with exactly the excess norm. -/
theorem finiteJet_pythagorean (S : Finset ℕ) (a : Disk) :
    ‖a‖ ^ 2 = (∑ n ∈ S, ‖coefficient a n‖ ^ 2 / ((n : ℝ) + 1)) +
      ‖a - finiteJetInterpolant S (coefficient a)‖ ^ 2 := by
  have he : finiteJetInterpolant S (coefficient a) +
      (a - finiteJetInterpolant S (coefficient a)) = a := by abel
  have h := norm_add_sq (𝕜 := ℂ) (finiteJetInterpolant S (coefficient a))
    (a - finiteJetInterpolant S (coefficient a))
  simpa only [he, finiteJetInterpolant_orthogonal, map_zero, mul_zero, add_zero,
    finiteJetInterpolant_norm_sq] using h

/-- Equality in the finite Taylor bound characterizes the unique interpolating polynomial. -/
theorem finiteJet_norm_eq_iff (S : Finset ℕ) (a : Disk) :
    ‖a‖ ^ 2 = ∑ n ∈ S, ‖coefficient a n‖ ^ 2 / ((n : ℝ) + 1) ↔
      a = finiteJetInterpolant S (coefficient a) := by
  rw [finiteJet_pythagorean S a]
  constructor
  · intro h
    have hz : ‖a - finiteJetInterpolant S (coefficient a)‖ = 0 := by
      nlinarith only [h, norm_nonneg (a - finiteJetInterpolant S (coefficient a))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro h
    rw [sub_eq_zero.mpr h, norm_zero, zero_pow two_ne_zero, add_zero]

/-- The complete holomorphic L² class has the same sharp finite Taylor interpolation bound. -/
theorem holomorphic_finiteJet_area_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball (0 : ℂ) 1)) (S : Finset ℕ) :
    Real.pi * (∑ n ∈ S, ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1)) ≤
      ∫ z in ball (0 : ℂ) 1, ‖f z‖ ^ 2 := by
  obtain ⟨a, _, ha, hn⟩ := exists_disk_coordinates hf hi
  have hc : coefficient a = diskCoeff f := by
    funext n
    rw [coefficient, ha n, normalizedTaylor]
    field_simp [sqrt_index_ne_zero n]
  rw [← hn, ← hc]
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  rw [finiteJet_pythagorean S a]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality determines the unique polynomial, including when the prescribed indices have gaps. -/
theorem holomorphic_finiteJet_area_eq_iff {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball (0 : ℂ) 1)) (S : Finset ℕ) :
    (∫ z in ball (0 : ℂ) 1, ‖f z‖ ^ 2) =
        Real.pi * (∑ n ∈ S, ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1)) ↔
      ∀ z : ℂ, ‖z‖ < 1 → f z = ∑ n ∈ S, diskCoeff f n * z ^ n := by
  obtain ⟨a, ha, ht, hn⟩ := exists_disk_coordinates hf hi
  have hc : coefficient a = diskCoeff f := by
    funext n
    rw [coefficient, ht n, normalizedTaylor]
    field_simp [sqrt_index_ne_zero n]
  have he : (∫ z in ball (0 : ℂ) 1, ‖f z‖ ^ 2) =
      Real.pi * (∑ n ∈ S, ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1)) ↔
        a = finiteJetInterpolant S (diskCoeff f) := by
    rw [← hn, ← hc]
    constructor
    · intro h
      exact (finiteJet_norm_eq_iff S a).mp (mul_left_cancel₀ Real.pi_ne_zero h)
    · intro h
      exact congrArg (fun r : ℝ => Real.pi * r) ((finiteJet_norm_eq_iff S a).mpr h)
  rw [he]
  constructor
  · intro h z hz
    rw [← ha z hz, h, diskFun_finiteJetInterpolant]
  · intro h
    apply (diskFun_eqOn_iff _ _).mp
    intro z hz
    rw [ha z hz, h z hz, diskFun_finiteJetInterpolant]

/-- All central derivatives are the normalized Bergman coordinates with their exact factorial factor. -/
theorem iteratedDeriv_diskFun_zero (a : Disk) (n : ℕ) :
    iteratedDeriv n (diskFun a) 0 =
      (n.factorial : ℂ) * (Real.sqrt ((n : ℝ) + 1) : ℂ) * a n := by
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h := diskCoeff_diskFun a n
  rw [diskCoeff, coefficient] at h
  field_simp [hf] at h
  rw [h]

/-- The sharp central derivative norm is attained by the normalized monomial of the same degree. -/
theorem central_higher_jet_isGreatest (n : ℕ) :
    IsGreatest {r : ℝ | ∃ a : Disk, ‖a‖ ≤ 1 ∧
      (∀ k < n, iteratedDeriv k (diskFun a) 0 = 0) ∧
      ‖iteratedDeriv n (diskFun a) 0‖ = r}
      ((n.factorial : ℝ) * Real.sqrt ((n : ℝ) + 1)) := by
  constructor
  · refine ⟨lp.single 2 n (1 : ℂ), ?_, ?_, ?_⟩
    · rw [lp.norm_single (by norm_num), norm_one]
    · intro k hk
      rw [iteratedDeriv_diskFun_zero]
      simp [lp.single_apply, Nat.ne_of_lt hk]
    · rw [iteratedDeriv_diskFun_zero]
      simp [lp.single_apply, Real.sqrt_nonneg]
  · rintro r ⟨a, ha, _, rfl⟩
    rw [iteratedDeriv_diskFun_zero, norm_mul, norm_mul, Complex.norm_natCast,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (by positivity) ((hardyDisk_norm_coord_le a n).trans ha)

#print axioms central_higher_jet_isGreatest

#print axioms holomorphic_finiteJet_area_bound
#print axioms holomorphic_finiteJet_area_eq_iff
#print axioms finiteJetInterpolant_coeff
#print axioms diskFun_finiteJetInterpolant
#print axioms finiteJet_pythagorean
#print axioms finiteJet_norm_eq_iff
end
end GaloisForLFunctions.HilbertMetric.Bergman
