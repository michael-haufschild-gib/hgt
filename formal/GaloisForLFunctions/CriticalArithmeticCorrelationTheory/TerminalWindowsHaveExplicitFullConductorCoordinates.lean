import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.HorizonKernelEuclideanIdentities

/-!
# Explicit full-conductor coordinates of terminal data

Data vanishing on the lower half of a finite horizon have a direct
divisor-coordinate expansion. Above half the horizon each coordinate
reads just one datum. Thus the coefficients at horizon-sized conductors
are explicit, rather than supplied only by a spanning theorem.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory

/-- The divisor coordinate of a finite terminal datum. -/
def terminalDivisorCoordinate (f : ℕ → ℝ) (N m : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, if m ∣ d then f d / (d : ℝ) else 0

private theorem twice_le_of_proper_divisor {d n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (hdn : d ∣ n) (hne : n ≠ d) : 2 * d ≤ n := by
  obtain ⟨k, rfl⟩ := hdn
  have hk : 2 ≤ k := by
    by_contra hh
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl
    · simp only [mul_zero, lt_self_iff_false] at hn
    · simp only [mul_one, ne_eq, not_true_eq_false] at hne
  simpa only [mul_comm d 2] using Nat.mul_le_mul_left d hk

private theorem divisors_eq_terminal_filter {d N : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    d.divisors = (Icc 1 N).filter (fun m => m ∣ d) := by
  ext m
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · intro hm
    exact ⟨⟨Nat.pos_of_dvd_of_pos hm.1 hd, (Nat.le_of_dvd hd hm.1).trans hdN⟩, hm.1⟩
  · intro hm
    exact ⟨hm.2, hd.ne'⟩

/-- Exchanging the conductor and divisor sums recovers the finite divisibility transform. -/
theorem sum_terminalDivisorCoordinate_mul_ramanujan (f : ℕ → ℝ) (N n : ℕ) :
    (∑ m ∈ Icc 1 N, terminalDivisorCoordinate f N m * ramanujanLagCoefficient m n) =
      ∑ d ∈ Icc 1 N, if d ∣ n then f d else 0 := by
  simp_rw [terminalDivisorCoordinate, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  calc
    _ = f d / (d : ℝ) * (∑ m ∈ d.divisors, ramanujanLagCoefficient m n) := by
      rw [divisors_eq_terminal_filter hd0 (mem_Icc.mp hd).2, sum_filter, mul_sum]
      apply sum_congr rfl
      intro m _
      by_cases hmd : m ∣ d
      · simp only [if_pos hmd]
      · simp only [if_neg hmd, zero_mul, mul_zero]
    _ = _ := by
      rw [BezoutValuationIncidence.sum_divisors_ramanujanLagCoefficient]
      by_cases hdn : d ∣ n
      · rw [if_pos hdn, if_pos hdn, div_mul_cancel₀ _ hdR]
      · rw [if_neg hdn, if_neg hdn, mul_zero]

/-- Every proper divisor lies in the zero part of a terminal datum. -/
theorem terminalDivisorCoordinate_reconstructs
    {f : ℕ → ℝ} {N : ℕ} (hlow : ∀ d, 2 * d ≤ N → f d = 0)
    {n : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ m ∈ Icc 1 N, terminalDivisorCoordinate f N m * ramanujanLagCoefficient m n) = f n := by
  rw [sum_terminalDivisorCoordinate_mul_ramanujan]
  rw [sum_eq_single n]
  · simp only [dvd_refl, if_true]
  · intro d hd hdn
    by_cases hdiv : d ∣ n
    · rw [if_pos hdiv, hlow d
        ((twice_le_of_proper_divisor (mem_Icc.mp hd).1 (mem_Icc.mp hn).1 hdiv hdn.symm).trans
          (mem_Icc.mp hn).2)]
    · exact if_neg hdiv
  · exact fun h => False.elim (h hn)

/-- A conductor above half the horizon has just its own nonzero multiple in the coordinate. -/
theorem terminalDivisorCoordinate_above_half (f : ℕ → ℝ) {N m : ℕ}
    (hm : m ∈ Icc 1 N) (hhalf : N < 2 * m) :
    terminalDivisorCoordinate f N m = f m / (m : ℝ) := by
  unfold terminalDivisorCoordinate
  rw [sum_eq_single m]
  · simp only [dvd_refl, if_true]
  · intro d hd hdm
    apply if_neg
    intro hmd
    have htwice := twice_le_of_proper_divisor (mem_Icc.mp hm).1 (mem_Icc.mp hd).1 hmd hdm
    exact hhalf.not_ge (htwice.trans (mem_Icc.mp hd).2)
  · exact fun h => False.elim (h hm)

/-- The same explicit coordinates in the logarithmically normalized horizon basis. -/
def terminalNormalizedConductorCoordinate (f : ℕ → ℝ) (N m : ℕ) : ℝ :=
  Real.sqrt (Real.log N) * Real.sqrt (m.totient : ℝ) * terminalDivisorCoordinate f N m

/-- The explicit coefficients reconstruct the actual Euclidean horizon vector. -/
theorem sum_terminalNormalizedConductorCoordinate_smul
    {f : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : ∀ d, 2 * d ≤ N → f d = 0) :
    (∑ m ∈ Icc 1 N, terminalNormalizedConductorCoordinate f N m •
      normalizedRamanujanHorizonVector m N) =
        horizonProfileVector (fun n => f n / Real.sqrt n) N := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsL : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  ext n
  have hn0 : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp n.property).1
  have hsn : Real.sqrt (n : ℕ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
    (∑ m ∈ Icc 1 N, terminalNormalizedConductorCoordinate f N m •
      normalizedRamanujanHorizonVector m N) = f n / Real.sqrt (n : ℕ)
  rw [map_sum]
  calc
    _ = ∑ m ∈ Icc 1 N,
        terminalDivisorCoordinate f N m * ramanujanLagCoefficient m n / Real.sqrt (n : ℕ) := by
      apply sum_congr rfl
      intro m hm
      have hφ : (0 : ℝ) < m.totient := by
        exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hm).1
      have hsφ : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφ).ne'
      change terminalNormalizedConductorCoordinate f N m *
        ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) = _
      rw [terminalNormalizedConductorCoordinate, ramanujanPoleProfile,
        normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hm).1]
      field_simp [hsL, hsφ, hsn]
      <;> ring
    _ = f n / Real.sqrt (n : ℕ) := by
      rw [← sum_div, terminalDivisorCoordinate_reconstructs hlow n.property]

/-- The normalized coefficient square above half the horizon has its literal totient weight. -/
theorem terminalNormalizedConductorCoordinate_sq_above_half (f : ℕ → ℝ) {N m : ℕ}
    (hm : m ∈ Icc 1 N) (hhalf : N < 2 * m) :
    terminalNormalizedConductorCoordinate f N m ^ 2 =
      Real.log N * (m.totient : ℝ) * f m ^ 2 / (m : ℝ) ^ 2 := by
  rw [terminalNormalizedConductorCoordinate, terminalDivisorCoordinate_above_half f hm hhalf]
  simp only [mul_pow, div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N),
    Real.sq_sqrt (Nat.cast_nonneg m.totient)]
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.terminalDivisorCoordinate_reconstructs
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.terminalDivisorCoordinate_above_half
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_terminalNormalizedConductorCoordinate_smul
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.terminalNormalizedConductorCoordinate_sq_above_half
