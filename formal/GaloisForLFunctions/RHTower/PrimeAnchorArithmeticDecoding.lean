import GaloisForLFunctions.RHTower.FinitePrimeAnchorDecoder
import GaloisForLFunctions.BiScaleUncertainty.PrimeAnchorHorizonBounds
import Mathlib.NumberTheory.PrimeCounting

/-!
# Arithmetic anchors with complete finite decoding costs

Prime horizons give literal Möbius and Barban–Vehov anchors. Their signs and
cutoff conditions follow from the source definitions. The decoding cost keeps
the prime factor, taper loss and full graph inversion weights explicit.
-/

open Finset RHTower.Sieve RHTower.CHMDDoobGraph
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius

namespace RHTower.FinitePrimeAnchorDecoder
noncomputable section
set_option autoImplicit false

/-- Every natural parameter selects a prime horizon without a primality premise. -/
def primeHorizon (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem primeHorizon_mem_tail (n : ℕ) :
    primeHorizon n ∈ sievePrimeTail (primeHorizon n) := by
  have hp := Nat.prime_nth_prime n
  have hp2 : 2 ≤ primeHorizon n := hp.two_le
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp2, le_rfl⟩, hp, by omega⟩

theorem moebius_anchor (n : ℕ) :
    selbergMultiplesCoord (primeHorizon n) (fun d => (μ d : ℝ)) (primeHorizon n) =
      -(1 : ℝ) / primeHorizon n := by
  simpa only [mul_one] using
    selbergMultiplesCoord_moebius_mul_primeTail (primeHorizon_mem_tail n) (fun _ => 1)

theorem moebius_anchor_ne_zero (n : ℕ) :
    selbergMultiplesCoord (primeHorizon n) (fun d => (μ d : ℝ)) (primeHorizon n) ≠ 0 := by
  have hp : (primeHorizon n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.prime_nth_prime n).ne_zero
  simp [moebius_anchor, hp]

/-- A positive integral gap between prime horizon and taper cutoff supplies a live BV anchor. -/
theorem barbanVehov_anchor_at_gap (n m : ℕ) :
    selbergMultiplesCoord (primeHorizon n)
      (barbanVehovWeight (primeHorizon n + m + 1)) (primeHorizon n) =
      -Real.log (((primeHorizon n + m + 1 : ℕ) : ℝ) / primeHorizon n) /
        primeHorizon n :=
  barbanVehov_anchor (primeHorizon_mem_tail n) _ (by omega)

theorem barbanVehov_anchor_neg_at_gap (n m : ℕ) :
    selbergMultiplesCoord (primeHorizon n)
      (barbanVehovWeight (primeHorizon n + m + 1)) (primeHorizon n) < 0 :=
  barbanVehov_anchor_neg (primeHorizon_mem_tail n) _ (by omega)

/-- The exact arithmetic boundary for loss of every mixed observation. -/
theorem barbanVehov_record_zero_iff (n X : ℕ) :
    (∀ q ∈ Icc 1 (primeHorizon n),
      mixed (primeHorizon n) (primeHorizon n) (barbanVehovWeight X) q = 0) ↔
      X ≤ primeHorizon n :=
  barbanVehov_mixed_zero_iff (primeHorizon_mem_tail n) X

theorem inversionCost_scale (N k : ℕ) (t : ℝ) (r : ℕ → ℝ) :
    inversionCost N k (fun q => t * r q) = t * inversionCost N k r := by
  unfold inversionCost
  rw [mul_sum]
  apply sum_congr rfl
  intro d _
  have hs : (∑ m ∈ Icc 1 (N / d), |(μ m : ℝ)| * (t * r (d * m))) =
      t * ∑ m ∈ Icc 1 (N / d), |(μ m : ℝ)| * r (d * m) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    ring
  rw [hs]
  ring

theorem normalized_inversion_cost (N k : ℕ) (a : ℝ) (e : ℕ → ℝ) :
    inversionCost N k (fun q => |e q / a|) =
      |a|⁻¹ * inversionCost N k (fun q => |e q|) := by
  calc
    _ = inversionCost N k (fun q => |a|⁻¹ * |e q|) := by
      congr 1
      funext q
      rw [abs_div]
      ring
    _ = _ := inversionCost_scale N k _ _

/-- Observation noise priced by the reciprocal of the actual Möbius anchor. -/
def moebiusNoiseRadius (n k : ℕ) (z : ℕ → ℝ) : ℝ :=
  (primeHorizon n : ℝ) * inversionCost (primeHorizon n) k
    (fun q => |z q - mixed (primeHorizon n) (primeHorizon n) (fun d => (μ d : ℝ)) q|)

/-- The BV taper loss remains visible even when its cutoff approaches the anchor. -/
def barbanVehovNoiseRadius (n m k : ℕ) (z : ℕ → ℝ) : ℝ :=
  (primeHorizon n : ℝ) /
      |Real.log (((primeHorizon n + m + 1 : ℕ) : ℝ) / primeHorizon n)| *
    inversionCost (primeHorizon n) k
      (fun q => |z q - mixed (primeHorizon n) (primeHorizon n)
        (barbanVehovWeight (primeHorizon n + m + 1)) q|)

theorem moebius_graph_error_eq (n k : ℕ) (z : ℕ → ℝ) :
    graphError (primeHorizon n) k
      (selbergMultiplesCoord (primeHorizon n) (fun d => (μ d : ℝ)) (primeHorizon n))
      (fun d => (μ d : ℝ)) z = moebiusNoiseRadius n k z := by
  rw [graphError, div_self (moebius_anchor_ne_zero n)]
  simp only [sub_self, abs_zero, zero_mul, zero_add]
  rw [normalized_inversion_cost]
  have hg : |selbergMultiplesCoord (primeHorizon n)
      (fun d => (μ d : ℝ)) (primeHorizon n)|⁻¹ = (primeHorizon n : ℝ) := by
    rw [moebius_anchor]
    simp [abs_div, abs_of_nonneg (Nat.cast_nonneg (primeHorizon n) :
      (0 : ℝ) ≤ (primeHorizon n : ℝ))]
  rw [hg]
  rfl

theorem barbanVehov_graph_error_eq (n m k : ℕ) (z : ℕ → ℝ) :
    graphError (primeHorizon n) k
      (selbergMultiplesCoord (primeHorizon n)
        (barbanVehovWeight (primeHorizon n + m + 1)) (primeHorizon n))
      (barbanVehovWeight (primeHorizon n + m + 1)) z =
        barbanVehovNoiseRadius n m k z := by
  rw [graphError, div_self (barbanVehov_anchor_neg_at_gap n m).ne]
  simp only [sub_self, abs_zero, zero_mul, zero_add]
  rw [normalized_inversion_cost]
  have hg : |selbergMultiplesCoord (primeHorizon n)
      (barbanVehovWeight (primeHorizon n + m + 1)) (primeHorizon n)|⁻¹ =
      (primeHorizon n : ℝ) /
        |Real.log (((primeHorizon n + m + 1 : ℕ) : ℝ) / primeHorizon n)| := by
    rw [barbanVehov_anchor_at_gap]
    simp [abs_div, abs_of_nonneg (Nat.cast_nonneg (primeHorizon n) :
      (0 : ℝ) ≤ (primeHorizon n : ℝ))]
  rw [hg]
  rfl

theorem moebius_exact_decoding (n k : ℕ) :
    graph (primeHorizon n) k
      (selbergMultiplesCoord (primeHorizon n) (fun d => (μ d : ℝ)) (primeHorizon n))
      (mixed (primeHorizon n) (primeHorizon n) (fun d => (μ d : ℝ))) =
      synthesis (primeHorizon n) k (fun d => (μ d : ℝ)) := by
  unfold mixed
  simpa only [div_self (moebius_anchor_ne_zero n), one_smul] using
    exact_record (primeHorizon n) k
      (selbergMultiplesCoord (primeHorizon n) (fun d => (μ d : ℝ)) (primeHorizon n))
      (fun d => (μ d : ℝ))

theorem barbanVehov_exact_decoding (n m k : ℕ) :
    graph (primeHorizon n) k
      (selbergMultiplesCoord (primeHorizon n)
        (barbanVehovWeight (primeHorizon n + m + 1)) (primeHorizon n))
      (mixed (primeHorizon n) (primeHorizon n)
        (barbanVehovWeight (primeHorizon n + m + 1))) =
      synthesis (primeHorizon n) k (barbanVehovWeight (primeHorizon n + m + 1)) := by
  unfold mixed
  simpa only [div_self (barbanVehov_anchor_neg_at_gap n m).ne, one_smul] using
    exact_record (primeHorizon n) k
      (selbergMultiplesCoord (primeHorizon n)
        (barbanVehovWeight (primeHorizon n + m + 1)) (primeHorizon n))
      (barbanVehovWeight (primeHorizon n + m + 1))

/-- Full graph and signed-energy errors for arbitrary observations of the actual Möbius row. -/
theorem moebius_decoding_bounds (n k : ℕ) (z : ℕ → ℝ) :
    let p := primeHorizon n
    let c := fun d => (μ d : ℝ)
    let u := graph p k (selbergMultiplesCoord p c p) z
    let v := synthesis p k c
    ‖u - v‖ ≤ moebiusNoiseRadius n k z ∧
      |sourceEnergy u - sourceEnergy v| ≤
        moebiusNoiseRadius n k z ^ 2 + 2 * moebiusNoiseRadius n k z * ‖v‖ := by
  constructor
  · simpa only [moebius_graph_error_eq] using
      graph_error_le (primeHorizon n) k
        (selbergMultiplesCoord (primeHorizon n) (fun d => (μ d : ℝ)) (primeHorizon n))
        (fun d => (μ d : ℝ)) z
  · simpa only [energyError, moebius_graph_error_eq] using
      energy_error_le (primeHorizon n) k
        (selbergMultiplesCoord (primeHorizon n) (fun d => (μ d : ℝ)) (primeHorizon n))
        (fun d => (μ d : ℝ)) z

/-- The corresponding BV bounds retain the price of its actual taper. -/
theorem barbanVehov_decoding_bounds (n m k : ℕ) (z : ℕ → ℝ) :
    let p := primeHorizon n
    let c := barbanVehovWeight (p + m + 1)
    let u := graph p k (selbergMultiplesCoord p c p) z
    let v := synthesis p k c
    ‖u - v‖ ≤ barbanVehovNoiseRadius n m k z ∧
      |sourceEnergy u - sourceEnergy v| ≤
        barbanVehovNoiseRadius n m k z ^ 2 + 2 * barbanVehovNoiseRadius n m k z * ‖v‖ := by
  constructor
  · simpa only [barbanVehov_graph_error_eq] using
      graph_error_le (primeHorizon n) k
        (selbergMultiplesCoord (primeHorizon n)
          (barbanVehovWeight (primeHorizon n + m + 1)) (primeHorizon n))
        (barbanVehovWeight (primeHorizon n + m + 1)) z
  · simpa only [energyError, barbanVehov_graph_error_eq] using
      energy_error_le (primeHorizon n) k
        (selbergMultiplesCoord (primeHorizon n)
          (barbanVehovWeight (primeHorizon n + m + 1)) (primeHorizon n))
        (barbanVehovWeight (primeHorizon n + m + 1)) z

/-- A single fixed-cutoff constant prices reference norms for every prime horizon and BV gap. -/
theorem exists_arithmetic_decoder_budget (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      (∀ (n : ℕ) (z : ℕ → ℝ),
        let p := primeHorizon n
        let c := fun d => (μ d : ℝ)
        |sourceEnergy (graph p k (selbergMultiplesCoord p c p) z) -
            sourceEnergy (synthesis p k c)| ≤
          moebiusNoiseRadius n k z ^ 2 + 2 * moebiusNoiseRadius n k z *
            (B * Real.sqrt p * harmonicBudget p)) ∧
      (∀ (n m : ℕ) (z : ℕ → ℝ),
        let p := primeHorizon n
        let c := barbanVehovWeight (p + m + 1)
        |sourceEnergy (graph p k (selbergMultiplesCoord p c p) z) -
            sourceEnergy (synthesis p k c)| ≤
          barbanVehovNoiseRadius n m k z ^ 2 + 2 * barbanVehovNoiseRadius n m k z *
            (B * Real.sqrt p * Real.log (p + m + 1 : ℕ) * harmonicBudget p)) := by
  obtain ⟨B, hB, hbudget⟩ := exists_arithmetic_horizon_budget k
  refine ⟨B, hB, ?_, ?_⟩
  · intro n z
    have hb := moebius_decoding_bounds n k z
    have hL := (norm_nonneg _).trans hb.1
    refine hb.2.trans ?_
    gcongr
    exact (hbudget (primeHorizon n)).2.1
  · intro n m z
    have hb := barbanVehov_decoding_bounds n m k z
    have hL := (norm_nonneg _).trans hb.1
    refine hb.2.trans ?_
    gcongr
    exact (hbudget (primeHorizon n)).2.2 (primeHorizon n + m + 1) (by omega)

end
end RHTower.FinitePrimeAnchorDecoder
