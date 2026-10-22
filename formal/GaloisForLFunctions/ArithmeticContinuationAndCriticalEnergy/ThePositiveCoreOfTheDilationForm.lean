import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheQuotientIncidenceKernelIsIndefinite
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CompensationNeedsItsCrossTerms

/-!
# The positive core of the dilation form

At zero damping the source collapses to the constant one, and a constant row is *positively*
correlated with its own prime dilations: the dilation form of the constant row is

`Q_ε(1) = Σ_{n ≤ T} ψ_ε(n)/(n(n+1))`,  `ψ_ε(n) = Σ_{j ≤ n} Λ(j) j^{-ε} > 0`
(`rowDilationForm_one_eq`, `rowDilationForm_one_pos`).

So the dilation form has a positive core, and the complete decomposition of the form at the constant
row keeps every cross term:

`Q_ε(v) = Q_ε(1) + B_ε(1, v − 1) + B_ε(v − 1, 1) + Q_ε(v − 1)`
(`rowDilationForm_split_at_one`),

with `B_ε` the bilinear dilation pairing.  The two cross terms are *linear* functionals of the
residual `v − 1` with explicit weights — one pairs the residual's dilation against the constant, the
other pairs the residual against the explicit prime prefix `ψ_ε` — and only the last term is
quadratic in the residual.

Applied to the actual source this isolates the obstruction: the sign of the signed work is the sign
of a positive explicit core, plus two explicit linear functionals of `A_ε − 1`, plus the residual's
own dilation form (`signedDampingWork_split_at_one`).  Since the corpus's renormalisation neutrality
says admission is unchanged by subtracting the constant source, the quadratic residual term is the
only unpaid part — and it is the one that vanishes with the deviation from constancy.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The bilinear dilation pairing -/

/-- The bilinear form behind the dilation form. -/
def rowDilationPairing (ε : ℝ) (T : ℕ) (u v : ℕ → ℝ) : ℝ :=
  pronicPairing T u (fun n => ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j))

theorem rowDilationForm_eq_pairing (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    rowDilationForm ε T v = rowDilationPairing ε T v v := by
  simp only [rowDilationForm, rowDilationPairing, pronicPairing]

theorem rowDilationPairing_add_left (ε : ℝ) (T : ℕ) (u₁ u₂ v : ℕ → ℝ) :
    rowDilationPairing ε T (fun n => u₁ n + u₂ n) v =
      rowDilationPairing ε T u₁ v + rowDilationPairing ε T u₂ v := by
  simp only [rowDilationPairing, pronicPairing]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem rowDilationPairing_add_right (ε : ℝ) (T : ℕ) (u v₁ v₂ : ℕ → ℝ) :
    rowDilationPairing ε T u (fun n => v₁ n + v₂ n) =
      rowDilationPairing ε T u v₁ + rowDilationPairing ε T u v₂ := by
  simp only [rowDilationPairing, pronicPairing]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hsum : (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * (v₁ (n / j) + v₂ (n / j))) =
      (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v₁ (n / j)) +
        ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v₂ (n / j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  ring

/-! ## §2. The constant core -/

/-- The damped prime prefix `ψ_ε(n) = Σ_{j ≤ n} Λ(j) j^{-ε}`. -/
def dampedPrimePrefix (ε : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j

theorem dampedPrimePrefix_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ dampedPrimePrefix ε n := by
  refine Finset.sum_nonneg fun j _ => ?_
  rw [dampedPrimeWeight]
  have h1 : 0 ≤ ArithmeticFunction.vonMangoldt j := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : (0 : ℝ) ≤ (j : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg j) _
  exact mul_nonneg h1 h2

/-- The dilation form of the constant row is the pronic average of the damped prime prefix. -/
theorem rowDilationForm_one_eq (ε : ℝ) (T : ℕ) :
    rowDilationForm ε T (fun _ => 1) =
      ∑ n ∈ Icc 1 T, dampedPrimePrefix ε n / ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [rowDilationForm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dampedPrimePrefix]
  have hsum : (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * (1 : ℝ)) =
      ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  ring

/-- **The constant core is positive.**  Already the prime two contributes. -/
theorem rowDilationForm_one_pos (ε : ℝ) {T : ℕ} (hT : 2 ≤ T) :
    0 < rowDilationForm ε T (fun _ => 1) := by
  rw [rowDilationForm_one_eq]
  have hcell : ∀ n ∈ Icc 1 T, 0 ≤ dampedPrimePrefix ε n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    exact div_nonneg (dampedPrimePrefix_nonneg ε n) (by positivity)
  have htwo : (2 : ℕ) ∈ Icc 1 T := mem_Icc.mpr ⟨by omega, hT⟩
  have hpos : 0 < dampedPrimePrefix ε 2 / ((2 : ℝ) * ((2 : ℝ) + 1)) := by
    have hIcc : (Icc 1 2 : Finset ℕ) = {1, 2} := by
      ext n
      rw [mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hval : dampedPrimePrefix ε 2 = Real.log 2 * (2 : ℝ) ^ (-ε) := by
      rw [dampedPrimePrefix, hIcc, Finset.sum_insert (by simp), Finset.sum_singleton,
        dampedPrimeWeight, dampedPrimeWeight]
      rw [ArithmeticFunction.vonMangoldt_apply_one,
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    rw [hval]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hrpow : (0 : ℝ) < (2 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num) _
    exact div_pos (mul_pos hlog hrpow) (by norm_num)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hcell htwo)
  simpa using hpos

/-! ## §3. The decomposition at the constant row -/

/-- **The complete decomposition at the constant row**, with every cross term kept. -/
theorem rowDilationForm_split_at_one (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    rowDilationForm ε T v =
      rowDilationForm ε T (fun _ => 1) +
        rowDilationPairing ε T (fun _ => 1) (fun n => v n - 1) +
        rowDilationPairing ε T (fun n => v n - 1) (fun _ => 1) +
        rowDilationForm ε T (fun n => v n - 1) := by
  have hv : v = fun n => (1 : ℝ) + (v n - 1) := funext fun n => by ring
  rw [rowDilationForm_eq_pairing, hv, rowDilationPairing_add_left,
    rowDilationPairing_add_right, rowDilationPairing_add_right,
    rowDilationForm_eq_pairing, rowDilationForm_eq_pairing]
  ring

/-- **The signed work at the constant source.**  The positive core, two explicit linear functionals
of the deviation, the deviation's own dilation form, and the polar correction. -/
theorem signedDampingWork_split_at_one (ε : ℝ) (T : ℕ) :
    signedDampingWork ε T =
      (rowDilationForm ε T (fun _ => 1) +
        rowDilationPairing ε T (fun _ => 1)
            (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) +
        rowDilationPairing ε T
            (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) (fun _ => 1) +
        rowDilationForm ε T (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1)) +
      polarDilationCorrection ε T := by
  rw [signedDampingWork_eq_dilationForm_add_correction, dilationForm_eq_rowDilationForm,
    rowDilationForm_split_at_one]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
