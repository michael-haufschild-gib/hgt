import GaloisForLFunctions.HTGeometry.NonnegThetaCuspGrowth
import GaloisForLFunctions.HTGeometry.ShiftLatticeVerification
import Mathlib.NumberTheory.Divisors

/-!
# Unconditional instances of the cusp radius law

A non-negative coefficient family whose values are at least one on the positive
integers has a divergent Dirichlet series at every real parameter at or below
one, so the cusp criterion applies and the radius law holds outright.

Evaluating the base point at the cusp gap itself turns the law into the
local--global identity: the growth functional of the shift-lattice coefficients
at height `Δ` is exactly `1/(2πΔ)`, where `Δ` is the distance from the origin to
the shift spectrum.  Two families are recorded: the constant family in degree one
and conductor one, with gap one and constant `1/(2π)`; and the divisor function in
degree two and conductor one, with gap two and constant `1/(4π)`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section Divergence

/-- **A family bounded below by one has a divergent Dirichlet series at and below
one.**  Term-by-term comparison with the harmonic-type series. -/
theorem not_summable_of_one_le {r : ℕ → ℝ} (hr : ∀ n : ℕ, 1 ≤ n → 1 ≤ r n)
    {σ : ℝ} (hσ : σ ≤ 1) : ¬ Summable fun n : ℕ => r n * (n : ℝ) ^ (-σ) := by
  intro hsum
  have hbase : ¬ Summable fun n : ℕ => (n : ℝ) ^ (-σ) := by
    simp only [Real.summable_nat_rpow, not_lt]
    linarith
  refine hbase ?_
  have hshift := (summable_nat_add_iff 1).mpr hsum
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_ hshift
  intro n
  have h1 : (1 : ℝ) ≤ r (n + 1) := hr (n + 1) (by omega)
  have h2 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith

end Divergence

section CuspGap

variable {r : ℕ → ℝ}

/-- **The local--global identity at the cusp gap, unconditionally.**  For a
non-negative coefficient family whose Dirichlet series diverges at `σ`, the
growth functional of the shift-lattice coefficients based at height `Δ` is
exactly `1/(2πΔ)`, with `Δ` the distance from the origin to the shift
spectrum. -/
theorem hadamardLimsup_at_cuspGap (hr : ∀ n, 0 ≤ r n) {C B : ℝ}
    (hb : ∀ n, ‖realCoeff r n‖ ≤ C * (n : ℝ) ^ B) {σ d q : ℝ}
    (hd : 0 < d) (hq : 0 < q) (h1 : r 1 ≠ 0)
    (hns : ¬ Summable fun n : ℕ => r n * (n : ℝ) ^ (-σ)) :
    hadamardLimsup (shiftLatticeCoeff (realCoeff r) d (σ : ℂ)
        (((Metric.infDist 0 (shiftSpectrum (realCoeff r) d q) : ℝ) : ℂ)
          * Complex.I))
      = ENNReal.ofReal (1 / (2 * Real.pi *
          Metric.infDist 0 (shiftSpectrum (realCoeff r) d q))) := by
  have hgap : Metric.infDist 0 (shiftSpectrum (realCoeff r) d q)
      = d * q ^ (-(1 / d)) :=
    infDist_zero_shiftSpectrum (Complex.ofReal_ne_zero.mpr h1) hd hq
  have hpos : 0 < Metric.infDist 0 (shiftSpectrum (realCoeff r) d q) := by
    rw [hgap]; positivity
  exact hadamardLimsup_nonnegShiftLattice hr hb hd hns hpos

/-- **Radius of convergence exactly the cusp gap, unconditionally.** -/
theorem radius_at_cuspGap (hr : ∀ n, 0 ≤ r n) {C B : ℝ}
    (hb : ∀ n, ‖realCoeff r n‖ ≤ C * (n : ℝ) ^ B) {σ d q : ℝ}
    (hd : 0 < d) (hq : 0 < q) (h1 : r 1 ≠ 0)
    (hns : ¬ Summable fun n : ℕ => r n * (n : ℝ) ^ (-σ)) :
    (FormalMultilinearSeries.ofScalars ℂ (fun k =>
        shiftFactor ^ k
          * shiftLatticeCoeff (realCoeff r) d (σ : ℂ)
              (((Metric.infDist 0 (shiftSpectrum (realCoeff r) d q) : ℝ) : ℂ)
                * Complex.I) k)).radius
      = ENNReal.ofReal (Metric.infDist 0 (shiftSpectrum (realCoeff r) d q)) := by
  have hgap : Metric.infDist 0 (shiftSpectrum (realCoeff r) d q)
      = d * q ^ (-(1 / d)) :=
    infDist_zero_shiftSpectrum (Complex.ofReal_ne_zero.mpr h1) hd hq
  have hpos : 0 < Metric.infDist 0 (shiftSpectrum (realCoeff r) d q) := by
    rw [hgap]; positivity
  exact radius_nonnegShiftLattice hr hb hd hns hpos

end CuspGap

section ConstantFamily

/-- The constant real family. -/
def constCoeff : ℕ → ℝ := fun _ => 1

@[simp] theorem constCoeff_apply (n : ℕ) : constCoeff n = 1 := rfl

theorem realCoeff_constCoeff : realCoeff constCoeff = oneCoeff := by
  funext n
  rw [realCoeff_apply, constCoeff_apply, Complex.ofReal_one, oneCoeff]

theorem constCoeff_bound (n : ℕ) :
    ‖realCoeff constCoeff n‖ ≤ 1 * (n : ℝ) ^ (0 : ℝ) := by
  rw [realCoeff_constCoeff]
  exact oneCoeff_bound n

/-- **Degree one, conductor one: the cusp gap is one.** -/
theorem infDist_shiftSpectrum_constCoeff :
    Metric.infDist 0 (shiftSpectrum (realCoeff constCoeff) 1 1) = 1 := by
  refine infDist_zero_shiftSpectrum_zeta ?_
  rw [realCoeff_constCoeff, oneCoeff]
  exact one_ne_zero

/-- **The cusp radius law for the constant family, unconditionally.**  In degree
one and conductor one the gap is one and the growth constant is `1/(2π)`. -/
theorem hadamardLimsup_constCoeff_cusp {σ : ℝ} (hσ : σ ≤ 1) :
    hadamardLimsup (shiftLatticeCoeff (realCoeff constCoeff) 1 (σ : ℂ)
        ((1 : ℂ) * Complex.I))
      = ENNReal.ofReal (1 / (2 * Real.pi)) := by
  have h := hadamardLimsup_at_cuspGap (r := constCoeff) (fun n => zero_le_one)
    constCoeff_bound (d := 1) (q := 1) (σ := σ) one_pos one_pos one_ne_zero
    (not_summable_of_one_le (fun n _ => le_rfl) hσ)
  rw [infDist_shiftSpectrum_constCoeff, Complex.ofReal_one, mul_one] at h
  exact h

end ConstantFamily

section DivisorFamily

/-- The divisor-counting family, the coefficients of `ζ²`. -/
def divisorCoeff : ℕ → ℝ := fun n => ((n.divisors.card : ℕ) : ℝ)

@[simp] theorem divisorCoeff_apply (n : ℕ) :
    divisorCoeff n = ((n.divisors.card : ℕ) : ℝ) := rfl

theorem divisorCoeff_nonneg (n : ℕ) : 0 ≤ divisorCoeff n := Nat.cast_nonneg _

/-- Every divisor of `n` lies between one and `n`. -/
theorem divisors_subset_Icc (n : ℕ) : n.divisors ⊆ Finset.Icc 1 n := by
  intro m hm
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hm, Nat.divisor_le hm⟩

theorem card_divisors_le (n : ℕ) : n.divisors.card ≤ n := by
  have h := Finset.card_le_card (divisors_subset_Icc n)
  simpa using h

theorem divisorCoeff_bound (n : ℕ) :
    ‖realCoeff divisorCoeff n‖ ≤ 1 * (n : ℝ) ^ (1 : ℝ) := by
  rw [realCoeff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (divisorCoeff_nonneg n), Real.rpow_one, one_mul,
    divisorCoeff_apply]
  exact_mod_cast card_divisors_le n

/-- Every positive integer has at least one divisor. -/
theorem one_le_divisorCoeff {n : ℕ} (hn : 1 ≤ n) : 1 ≤ divisorCoeff n := by
  rw [divisorCoeff_apply]
  have hne : n ≠ 0 := by omega
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hne
  have hcard : 1 ≤ n.divisors.card := Finset.card_pos.mpr ⟨n, hmem⟩
  exact_mod_cast hcard

theorem divisorCoeff_one_ne_zero : divisorCoeff 1 ≠ 0 := by
  have := one_le_divisorCoeff (n := 1) le_rfl
  linarith

/-- **Degree two, conductor one: the cusp gap is two.** -/
theorem infDist_shiftSpectrum_divisorCoeff :
    Metric.infDist 0 (shiftSpectrum (realCoeff divisorCoeff) 2 1) = 2 :=
  infDist_zero_shiftSpectrum_degree_two
    (Complex.ofReal_ne_zero.mpr divisorCoeff_one_ne_zero)

/-- **The cusp radius law in degree two, unconditionally.**  For the divisor
function — the coefficients of `ζ²`, degree two and conductor one — the gap is
two and the growth constant is `1/(4π)`, matching `cusp_constant_degree_two`. -/
theorem hadamardLimsup_divisorCoeff_cusp {σ : ℝ} (hσ : σ ≤ 1) :
    hadamardLimsup (shiftLatticeCoeff (realCoeff divisorCoeff) 2 (σ : ℂ)
        ((2 : ℂ) * Complex.I))
      = ENNReal.ofReal (1 / (4 * Real.pi)) := by
  have h := hadamardLimsup_at_cuspGap (r := divisorCoeff) divisorCoeff_nonneg
    divisorCoeff_bound (d := 2) (q := 1) (σ := σ) (by norm_num) one_pos
    divisorCoeff_one_ne_zero
    (not_summable_of_one_le (fun n hn => one_le_divisorCoeff hn) hσ)
  rw [infDist_shiftSpectrum_divisorCoeff,
    show (((2 : ℝ)) : ℂ) = (2 : ℂ) from by norm_num] at h
  rw [h]
  congr 1
  ring

/-- **Radius of convergence exactly two, unconditionally, in degree two.** -/
theorem radius_divisorCoeff_cusp {σ : ℝ} (hσ : σ ≤ 1) :
    (FormalMultilinearSeries.ofScalars ℂ (fun k =>
        shiftFactor ^ k
          * shiftLatticeCoeff (realCoeff divisorCoeff) 2 (σ : ℂ)
              ((2 : ℂ) * Complex.I) k)).radius
      = ENNReal.ofReal 2 := by
  have h := radius_at_cuspGap (r := divisorCoeff) divisorCoeff_nonneg
    divisorCoeff_bound (d := 2) (q := 1) (σ := σ) (by norm_num) one_pos
    divisorCoeff_one_ne_zero
    (not_summable_of_one_le (fun n hn => one_le_divisorCoeff hn) hσ)
  rw [infDist_shiftSpectrum_divisorCoeff,
    show (((2 : ℝ)) : ℂ) = (2 : ℂ) from by norm_num] at h
  exact h

end DivisorFamily

end GaloisForLFunctions.HTGeometry
