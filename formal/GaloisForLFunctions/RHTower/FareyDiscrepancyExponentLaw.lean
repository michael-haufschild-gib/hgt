import GaloisForLFunctions.RHTower.FareyDiscrepancyFranelCriterion
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.MobiusMertensAbsoluteMomentExponentLaw

/-!
# The exponent law for the Farey discrepancy

Let `Θ = sup {Re ρ : ζ(ρ) = 0, 0 < Re ρ < 1}`.  The Farey ℓ¹ discrepancy
`D_n = Σ_ν |f_ν - ν/L|` has exponent exactly `Θ`:

* `D_n = O(n^b)` for every `b > Θ`;
* if `D_n = O(n^b)` for some `b ≥ 0`, then `Θ ≤ b`.

Hence `Θ = inf {b ≥ 0 : D_n = O(n^b)}`, and `Θ = ½` is the Franel–Landau criterion.  The upper
half combines Littlewood's bound `M(N) = O(N^{Θ+ε})` with the sawtooth mean square; the lower half
combines Landau's inequality `|M(n)| ≤ 2π D_n` with the transport-cost exponent bound
`Σ_{k ≤ X} |M(k)| = O(X^{b+1}) ⇒ Θ ≤ b`.
-/

open Finset

open RHTower.Sieve (fareySet mem_fareySet)

namespace RHTower

noncomputable section

/-- The trivial Mertens bound `|M(N)| ≤ N + 1`. -/
theorem norm_mobiusMertensPartialSum_le_add_one (N : ℕ) :
    ‖mobiusMertensPartialSum N‖ ≤ (N : ℝ) + 1 := by
  unfold mobiusMertensPartialSum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ range (N + 1), ‖mobiusComplexCoefficient n‖ ≤ ∑ _n ∈ range (N + 1), (1 : ℝ) :=
        sum_le_sum fun n _ => by
          unfold mobiusComplexCoefficient
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = (N : ℝ) + 1 := by simp

/-- A power bound for the Farey discrepancy is a power bound for the Mertens function. -/
theorem norm_mobiusMertensPartialSum_le_of_fareyL1Discrepancy_le {C b : ℝ} (hb : 0 ≤ b)
    (h : ∀ n : ℕ, fareyL1Discrepancy n ≤ C * ((n : ℝ) + 1) ^ b) (N : ℕ) :
    ‖mobiusMertensPartialSum N‖ ≤ max (2 * Real.pi * C) 2 * ((N : ℝ) + 1) ^ b := by
  have hpow : 1 ≤ ((N : ℝ) + 1) ^ b :=
    Real.one_le_rpow (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]) hb
  rcases lt_or_ge N 2 with hN | hN
  · have hsmall : ‖mobiusMertensPartialSum N‖ ≤ 2 := by
      unfold mobiusMertensPartialSum mobiusComplexCoefficient
      interval_cases N
      · simp
      · simp [Finset.sum_range_succ]
    calc ‖mobiusMertensPartialSum N‖ ≤ 2 := hsmall
      _ ≤ 2 * ((N : ℝ) + 1) ^ b := by linarith
      _ ≤ max (2 * Real.pi * C) 2 * ((N : ℝ) + 1) ^ b :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · calc ‖mobiusMertensPartialSum N‖ ≤ 2 * Real.pi * fareyL1Discrepancy N :=
          norm_mobiusMertensPartialSum_le_fareyL1Discrepancy hN
      _ ≤ 2 * Real.pi * (C * ((N : ℝ) + 1) ^ b) :=
          mul_le_mul_of_nonneg_left (h N) (by positivity)
      _ = 2 * Real.pi * C * ((N : ℝ) + 1) ^ b := by ring
      _ ≤ max (2 * Real.pi * C) 2 * ((N : ℝ) + 1) ^ b :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Lower half of the exponent law.**  If `D_n ≤ C (n+1)^b` for all `n` with `b ≥ 0`, then every
zeta zero has real part at most `b`. -/
theorem zetaZeroAbscissa_le_of_fareyL1Discrepancy_le {C b : ℝ} (hb : 0 ≤ b)
    (h : ∀ n : ℕ, fareyL1Discrepancy n ≤ C * ((n : ℝ) + 1) ^ b) :
    zetaZeroAbscissa ≤ b := by
  set C' : ℝ := max (2 * Real.pi * C) 2 with hC'
  have hC'0 : 0 ≤ C' := le_trans (by norm_num) (le_max_right _ _)
  have hM := norm_mobiusMertensPartialSum_le_of_fareyL1Discrepancy_le hb h
  have hS : ∀ X : ℕ, ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖
      ≤ C' * ((X : ℝ) + 1) ^ (b + 1) := by
    intro X
    have hX : (0 : ℝ) < (X : ℝ) + 1 := by positivity
    calc ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖
        ≤ ∑ _k ∈ range (X + 1), C' * ((X : ℝ) + 1) ^ b := by
          refine sum_le_sum fun k hk => (hM k).trans ?_
          have hkX : (k : ℝ) ≤ X := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
          refine mul_le_mul_of_nonneg_left ?_ hC'0
          exact Real.rpow_le_rpow (by positivity) (by linarith) hb
      _ = C' * ((X : ℝ) + 1) ^ (b + 1) := by
          rw [sum_const, card_range, nsmul_eq_mul, Real.rpow_add hX, Real.rpow_one]
          push_cast
          ring
  have := zetaZeroAbscissa_le_of_sum_norm_mertens_le (by linarith) hS
  linarith

/-- **Upper half of the exponent law.**  `D_n = O(n^b)` for every `b` greater than the zeta zero
abscissa. -/
theorem exists_fareyL1Discrepancy_le_rpow_of_zetaZeroAbscissa_lt {b : ℝ}
    (hb : zetaZeroAbscissa < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, fareyL1Discrepancy n ≤ C * ((n : ℝ) + 1) ^ b := by
  set ε : ℝ := b - zetaZeroAbscissa with hε
  have hε0 : 0 < ε := by linarith
  have hΘ := half_le_zetaZeroAbscissa
  set a : ℝ := min (zetaZeroAbscissa + ε / 2) 1 with ha
  have ha1 : a ≤ 1 := min_le_right _ _
  have ha2 : a ≤ zetaZeroAbscissa + ε / 2 := min_le_left _ _
  have ha0 : 1 / 2 ≤ a := le_min (by linarith) (by norm_num)
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a := by
    rcases le_total (zetaZeroAbscissa + ε / 2) 1 with hle | hle
    · obtain ⟨C, hC0, hC⟩ := mobiusMertens_subpower_zetaZeroAbscissa (ε / 2) (by positivity)
      refine ⟨C, hC0, fun N => ?_⟩
      rw [ha, min_eq_left hle]
      exact hC N
    · refine ⟨1, zero_le_one, fun N => ?_⟩
      rw [ha, min_eq_right hle, Real.rpow_one, one_mul]
      exact norm_mobiusMertensPartialSum_le_add_one N
  obtain ⟨C', hC'0, hC'⟩ := fareyL1Discrepancy_le_of_mertens_rpow_bound ha0 ha1 hC0 hC
    (δ := ε / 2) (by positivity)
  refine ⟨C', hC'0, fun n => (hC' n).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)) hC'0
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **The Farey exponent law.**  The zeta zero abscissa is the exponent of the Farey ℓ¹
discrepancy: `Θ = inf {b ≥ 0 : D_n = O(n^b)}`. -/
theorem zetaZeroAbscissa_eq_sInf_fareyL1Discrepancy_exponents :
    zetaZeroAbscissa = sInf {b : ℝ | 0 ≤ b ∧ ∃ C : ℝ, ∀ n : ℕ,
      fareyL1Discrepancy n ≤ C * ((n : ℝ) + 1) ^ b} := by
  set S := {b : ℝ | 0 ≤ b ∧ ∃ C : ℝ, ∀ n : ℕ, fareyL1Discrepancy n ≤ C * ((n : ℝ) + 1) ^ b}
    with hS
  have hΘ := half_le_zetaZeroAbscissa
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa + ε ∈ S := by
    intro ε hε
    obtain ⟨C, _, hC⟩ := exists_fareyL1Discrepancy_le_rpow_of_zetaZeroAbscissa_lt
      (b := zetaZeroAbscissa + ε) (by linarith)
    exact ⟨by linarith, C, hC⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun b hb => hb.1⟩
  refine le_antisymm ?_ ?_
  · exact le_csInf hne fun b hb => by
      obtain ⟨hb0, C, hC⟩ := hb
      exact zetaZeroAbscissa_le_of_fareyL1Discrepancy_le hb0 hC
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le hbdd (hmem ε hε)

end

end RHTower
