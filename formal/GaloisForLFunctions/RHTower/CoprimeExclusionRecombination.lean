import GaloisForLFunctions.RHTower.MobiusCoprimeIncidence
import GaloisForLFunctions.HTGeometry.FiniteRowRecombination

/-!
# Removing coprimality exclusions before taking mean squares

The finite vector-valued form of Lemma 4.4 of *The Quasi-Riemann Hypothesis*
follows from the existing common-divisor Möbius kernel and finite recombination.
The exact identity retains all signs.  The energy bound first retains the
absolute Möbius mass, then gives the paper's coarser divisor-count cost.
-/

noncomputable section
open scoped BigOperators NNReal ArithmeticFunction.Moebius

namespace RHTower

variable {ι ρ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A coprimality-restricted column is an exact signed sum of divisor columns. -/
theorem sum_coprime_eq_moebius_divisor_columns (q : ℕ) (s : Finset ι)
    (n : ι → ℕ) (v : ι → E) :
    (∑ i ∈ s.filter (fun i => (q + 1).Coprime (n i)), v i) =
      ∑ d ∈ (q + 1).divisors, (μ d : ℂ) • ∑ i ∈ s.filter (fun i => d ∣ n i), v i := by
  classical
  have hcoeff (i : ι) :
      (∑ d ∈ (q + 1).divisors, if d ∣ n i then (μ d : ℂ) else 0) =
        if (q + 1).Coprime (n i) then 1 else 0 := by
    have hg : (q + 1).gcd (n i) ≠ 0 :=
      (Nat.gcd_pos_of_pos_left (n i) (Nat.succ_pos q)).ne'
    have hfilter : (q + 1).divisors.filter (fun d => d ∣ n i) =
        ((q + 1).gcd (n i)).divisors := by
      ext d
      simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hg]
    rw [← Finset.sum_filter, hfilter]
    have h := congrArg (fun z : ℤ => (z : ℂ))
      (mobiusCommonDivisorKernel_eq_coprimeIndicator (q + 1) (n i))
    simpa [mobiusCommonDivisorKernel] using h
  rw [Finset.sum_filter]
  calc
    (∑ i ∈ s, if (q + 1).Coprime (n i) then v i else 0) =
        ∑ i ∈ s, (if (q + 1).Coprime (n i) then (1 : ℂ) else 0) • v i := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = ∑ i ∈ s,
        (∑ d ∈ (q + 1).divisors, if d ∣ n i then (μ d : ℂ) else 0) • v i := by
      simp_rw [hcoeff]
    _ = _ := by
      simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.smul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

/-- Weighted exclusion removal retaining the actual absolute Möbius mass. -/
theorem sum_weight_coprime_energy_le_moebius_mass [Fintype ρ]
    (q : ℕ) (s : Finset ι) (w : ρ → ℝ≥0) (n : ρ → ι → ℕ) (v : ι → ρ → E) :
    (∑ r, (w r : ℝ) *
        ‖∑ i ∈ s.filter (fun i => (q + 1).Coprime (n r i)), v i r‖ ^ 2) ≤
      (∑ d ∈ (q + 1).divisors, ‖(μ d : ℂ)‖) *
        ∑ d ∈ (q + 1).divisors, ‖(μ d : ℂ)‖ *
          ∑ r, (w r : ℝ) * ‖∑ i ∈ s.filter (fun i => d ∣ n r i), v i r‖ ^ 2 := by
  simp_rw [sum_coprime_eq_moebius_divisor_columns]
  exact GaloisForLFunctions.HTGeometry.sum_weight_norm_sum_smul_sq_le_mass
    (q + 1).divisors w (fun d => (μ d : ℂ))
    (fun d r => ∑ i ∈ s.filter (fun i => d ∣ n r i), v i r)

/-- The divisor-count version of exclusion removal needs no individual column estimate. -/
theorem sum_weight_coprime_energy_le_divisor_count [Fintype ρ]
    (q : ℕ) (s : Finset ι) (w : ρ → ℝ≥0) (n : ρ → ι → ℕ) (v : ι → ρ → E) :
    (∑ r, (w r : ℝ) *
        ‖∑ i ∈ s.filter (fun i => (q + 1).Coprime (n r i)), v i r‖ ^ 2) ≤
      ((q + 1).divisors.card : ℝ) *
        ∑ d ∈ (q + 1).divisors,
          ∑ r, (w r : ℝ) * ‖∑ i ∈ s.filter (fun i => d ∣ n r i), v i r‖ ^ 2 := by
  have hmu (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have henergy (d : ℕ) : 0 ≤
      ∑ r, (w r : ℝ) * ‖∑ i ∈ s.filter (fun i => d ∣ n r i), v i r‖ ^ 2 :=
    Finset.sum_nonneg fun r _ => mul_nonneg (w r).coe_nonneg (sq_nonneg _)
  refine (sum_weight_coprime_energy_le_moebius_mass q s w n v).trans ?_
  apply mul_le_mul
  · calc
      (∑ d ∈ (q + 1).divisors, ‖(μ d : ℂ)‖) ≤
          ∑ _d ∈ (q + 1).divisors, (1 : ℝ) :=
        Finset.sum_le_sum fun d _ => hmu d
      _ = _ := by simp
  · apply Finset.sum_le_sum
    intro d _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmu d) (henergy d)
  · exact Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (henergy d)
  · positivity

end RHTower
