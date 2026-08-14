import GaloisForLFunctions.HTGeometry.GevreyJetMonomial
import GaloisForLFunctions.HTGeometry.EulerADETruncation

/-!
# Ingredients of the nonlinear Maillet estimate

Four facts separate the linear coefficient recursion from the nonlinear one.

* The convergent series form a subsemiring, so the coefficients of the Taylor family of an
  analytic differential polynomial are again convergent.
* The shift factor of the recursion is dominated by the indicial power for every integral Gevrey
  exponent above the Newton drop, not only for the drop itself.
* A geometric series survives multiplication by a polynomial weight, which is what the weighted
  norms cost.
* Replacing the perturbation by a truncation of it leaves the coefficient of the defect at the
  truncation level unchanged, because every monomial of the defect carries at least two factors of
  the perturbation and each of them vanishes to high order.
-/

open PowerSeries MvPolynomial
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The convergent series as a subsemiring -/

/-- The convergent power series, as a subsemiring of the formal ones. -/
def convergentSubsemiring : Subsemiring (PowerSeries ℂ) where
  carrier := {F | IsGevreySeries 0 F}
  zero_mem' := isGevreySeries_zero 0
  one_mem' := isGevreySeries_one 0
  add_mem' := fun hF hG => IsGevreySeries.add hF hG
  mul_mem' := fun hF hG => IsGevreySeries.mul le_rfl hF hG

theorem mem_convergentSubsemiring {F : PowerSeries ℂ} :
    F ∈ convergentSubsemiring ↔ IsGevreySeries 0 F := Iff.rfl

/-! ### The shift factor at an integral exponent -/

/-- **The shift factor of the recursion is dominated by the indicial power** for every integral
exponent above the Newton drop. -/
theorem shiftFactor_nat_le {m d r : ℕ} (hr : m ≤ d + r) {n k : ℕ} (hk : k < n) :
    ((k : ℝ) + 1) ^ m * (((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r) ≤ ((n : ℝ) + 1) ^ d := by
  have hn : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le k) hk
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hfacn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfack : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hratio : ((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r ≤ (1 / (n : ℝ)) ^ r := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (by positivity) (factorial_ratio_le hk) r
  have hpoly : ((k : ℝ) + 1) ^ m ≤ (n : ℝ) ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have : (k : ℕ) + 1 ≤ n := hk
    exact_mod_cast this
  have hnr : (0 : ℝ) < (n : ℝ) ^ r := by positivity
  have hstep : ((k : ℝ) + 1) ^ m * (((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r)
      ≤ (n : ℝ) ^ m * (1 / (n : ℝ)) ^ r :=
    mul_le_mul hpoly hratio (by positivity) (by positivity)
  have hval : (n : ℝ) ^ m * (1 / (n : ℝ)) ^ r ≤ ((n : ℝ) + 1) ^ d := by
    have hmr : (n : ℝ) ^ m ≤ (n : ℝ) ^ (d + r) := pow_le_pow_right₀ hn1 hr
    have hsplit : (n : ℝ) ^ (d + r) * (1 / (n : ℝ)) ^ r = (n : ℝ) ^ d := by
      rw [pow_add, one_div, inv_pow]
      field_simp
    calc (n : ℝ) ^ m * (1 / (n : ℝ)) ^ r ≤ (n : ℝ) ^ (d + r) * (1 / (n : ℝ)) ^ r :=
          mul_le_mul_of_nonneg_right hmr (by positivity)
      _ = (n : ℝ) ^ d := hsplit
      _ ≤ ((n : ℝ) + 1) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
  linarith

/-! ### A geometric sum with a polynomial weight -/

theorem polyGeom_shift_sum_le {a : ℕ} {Ca q : ℝ} (hCa : ∀ μ : ℕ, ((μ : ℝ) + 1) ^ a ≤ Ca * 2 ^ μ)
    (hCa0 : 0 ≤ Ca) (hq0 : 0 ≤ q) (hq : 2 * q < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((((n - k : ℕ) : ℝ)) + 1) ^ a * q ^ (n - k)
      ≤ Ca * ((2 * q) / (1 - 2 * q)) := by
  have hstep : ∀ k ∈ Finset.range n,
      ((((n - k : ℕ) : ℝ)) + 1) ^ a * q ^ (n - k) ≤ Ca * (2 * q) ^ (n - k) := by
    intro k _
    have h1 := hCa (n - k)
    have h2 : (0 : ℝ) ≤ q ^ (n - k) := pow_nonneg hq0 _
    calc ((((n - k : ℕ) : ℝ)) + 1) ^ a * q ^ (n - k) ≤ (Ca * 2 ^ (n - k)) * q ^ (n - k) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = Ca * (2 * q) ^ (n - k) := by rw [mul_pow]; ring
  have hq2 : (0 : ℝ) ≤ 2 * q := by linarith
  calc ∑ k ∈ Finset.range n, ((((n - k : ℕ) : ℝ)) + 1) ^ a * q ^ (n - k)
      ≤ ∑ k ∈ Finset.range n, Ca * (2 * q) ^ (n - k) := Finset.sum_le_sum hstep
    _ = Ca * ∑ k ∈ Finset.range n, (2 * q) ^ (n - k) := by rw [Finset.mul_sum]
    _ ≤ Ca * ((2 * q) / (1 - 2 * q)) :=
        mul_le_mul_of_nonneg_left (geom_shift_sum_le hq2 hq n) hCa0

/-! ### Truncations -/

theorem gevreyWeightBound_truncSeries {a r N' : ℕ} {A ε : ℝ} (hA : 0 < A) (hε : 0 ≤ ε)
    {H : PowerSeries ℂ}
    (h : ∀ k ≤ N', ‖PowerSeries.coeff k H‖ * ((k : ℝ) + 1) ^ a ≤ ε * A ^ k * ((k ! : ℝ)) ^ r) :
    GevreyWeightBound a ε A r (truncSeries N' H) := by
  intro n
  rw [coeff_truncSeries]
  by_cases hn : n ≤ N'
  · rw [if_pos hn]
    exact h n hn
  · rw [if_neg hn, norm_zero, zero_mul]
    positivity

theorem X_pow_dvd_truncSeries {M N' : ℕ} {H : PowerSeries ℂ}
    (hH : (PowerSeries.X : PowerSeries ℂ) ^ M ∣ H) :
    (PowerSeries.X : PowerSeries ℂ) ^ M ∣ truncSeries N' H := by
  rw [PowerSeries.X_pow_dvd_iff] at hH ⊢
  intro n hn
  rw [coeff_truncSeries]
  by_cases h : n ≤ N'
  · rw [if_pos h]
    exact hH n hn
  · rw [if_neg h]

theorem eulerOp_iterate_sub (j : ℕ) (F G : PowerSeries ℂ) :
    GaloisForLFunctions.HTGeometry.eulerOp^[j] (F - G)
      = GaloisForLFunctions.HTGeometry.eulerOp^[j] F
        - GaloisForLFunctions.HTGeometry.eulerOp^[j] G := by
  have h := eulerOp_iterate_add j (F - G) G
  rw [sub_add_cancel] at h
  rw [h]
  ring

/-! ### The defect only sees the perturbation below the current level -/

/-- **Replacing the perturbation by a truncation does not move the defect at the truncation
level.**  Every monomial of the defect carries at least two factors of the perturbation, and both
vanish to the order of the truncation. -/
theorem coeff_taylorDefect_eq_of_sub_dvd {m n M : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) (Y H H' : PowerSeries ℂ) (hM : 1 ≤ M)
    (hH : (PowerSeries.X : PowerSeries ℂ) ^ M ∣ H)
    (hH' : (PowerSeries.X : PowerSeries ℂ) ^ M ∣ H')
    (hdiff : (PowerSeries.X : PowerSeries ℂ) ^ n ∣ (H - H')) :
    PowerSeries.coeff n (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)
      = PowerSeries.coeff n (taylorDefect (eulerJetVector Y) (eulerJetVector H') P) := by
  classical
  obtain ⟨T, hTs, _, hTsum⟩ :=
    hasTaylorDefectFamily (A := PowerSeries ℂ) (⊤ : Subsemiring (PowerSeries ℂ)) P
      (fun _ => Subsemiring.mem_top _)
  have hu : ∀ j : Fin (m + 1),
      (PowerSeries.X : PowerSeries ℂ) ^ M ∣ eulerJetVector (m := m) H j :=
    fun j => X_pow_dvd_eulerOp_iterate (j : ℕ) hH
  have hv : ∀ j : Fin (m + 1),
      (PowerSeries.X : PowerSeries ℂ) ^ M ∣ eulerJetVector (m := m) H' j :=
    fun j => X_pow_dvd_eulerOp_iterate (j : ℕ) hH'
  have huv : ∀ j : Fin (m + 1), (PowerSeries.X : PowerSeries ℂ) ^ n ∣
      (eulerJetVector (m := m) H j - eulerJetVector (m := m) H' j) := by
    intro j
    rw [eulerJetVector, eulerJetVector, ← eulerOp_iterate_sub]
    exact X_pow_dvd_eulerOp_iterate (j : ℕ) hdiff
  have hdvd : (PowerSeries.X : PowerSeries ℂ) ^ (n + M) ∣
      (taylorDefect (eulerJetVector Y) (eulerJetVector H) P
        - taylorDefect (eulerJetVector Y) (eulerJetVector H') P) := by
    rw [hTsum (eulerJetVector Y) (eulerJetVector H),
      hTsum (eulerJetVector Y) (eulerJetVector H'), Finsupp.sum, Finsupp.sum,
      ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun α hα => ?_
    have hα2 : 2 ≤ jetDegree α := hTs α hα
    have hsub : aeval (eulerJetVector Y) (T α)
          * jetMonomial (eulerJetVector (m := m) H) α
        - aeval (eulerJetVector Y) (T α) * jetMonomial (eulerJetVector (m := m) H') α
        = aeval (eulerJetVector Y) (T α)
          * (jetMonomial (eulerJetVector (m := m) H) α
            - jetMonomial (eulerJetVector (m := m) H') α) := by ring
    rw [hsub]
    exact Dvd.dvd.mul_left (X_pow_dvd_jetMonomial_sub_of_two_le hv hu huv α hα2) _
  have hzero : PowerSeries.coeff n
      (taylorDefect (eulerJetVector Y) (eulerJetVector H) P
        - taylorDefect (eulerJetVector Y) (eulerJetVector H') P) = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp hdvd) n (by omega)
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-! ### The recursion at a positive leading shift -/

/-- **The coefficient recursion when the operator has no term below shift `v`.**  The `n`-th
coefficient of the argument is isolated at level `n + v`. -/
theorem shiftPolynomial_shift_mul_coeff {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (v : ℕ)
    (hv : ∀ μ, μ < v → shiftPolynomial B μ = 0) (F : PowerSeries ℂ) (n : ℕ) :
    (shiftPolynomial B v).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n F
      = PowerSeries.coeff (n + v) (eulerLinearOp B F)
        - ∑ k ∈ Finset.range n,
            (shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F := by
  classical
  have h := coeff_eulerLinearOp_range B F (n + v)
  have hsplit : ∑ k ∈ Finset.range (n + v + 1),
        (shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F
      = ∑ k ∈ Finset.range (n + 1),
        (shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F :=
    (Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr (by
        have hx' := Finset.mem_range.mp hx
        omega))
      (fun k hk hk' => by
        have h1 : k < n + v + 1 := Finset.mem_range.mp hk
        have h2 : ¬ (k < n + 1) := fun h => hk' (Finset.mem_range.mpr h)
        rw [hv (n + v - k) (by omega), Polynomial.eval_zero, zero_mul])).symm
  rw [hsplit, Finset.sum_range_succ] at h
  have hidx : n + v - n = v := by omega
  rw [hidx] at h
  linear_combination -h

end GaloisForLFunctions.HTGeometry
