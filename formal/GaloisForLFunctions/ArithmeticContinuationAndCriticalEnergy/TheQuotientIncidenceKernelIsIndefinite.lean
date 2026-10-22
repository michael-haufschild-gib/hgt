import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheTangentIsADilationAverageOfTheSource

/-!
# The quotient incidence kernel is indefinite

Grouping the prime dilations by the level they land on turns the dilation form into a bilinear form
with an explicit integer kernel,

`κ_ε(n, m) = Σ_{j ≤ n, ⌊n/j⌋ = m} Λ(j) j^{-ε}`,

supported on the hyperbolic incidence `m = ⌊n/j⌋` (`dilationForm_eq_kernel_form`).  Two elementary
facts about that kernel decide what a proof of the continuation sign can look like.

* **The diagonal vanishes.**  `⌊n/j⌋ = n` forces `j = 1`, and `Λ(1) = 0`, so `κ_ε(n, n) = 0`
  (`quotientIncidenceKernel_self`).  The form carries no diagonal mass at all; every contribution
  is a genuine incidence between two different levels.
* **Hence the form is indefinite.**  Already at horizon two the kernel has the single entry
  `κ_ε(2, 1) = (log 2) 2^{-ε} > 0`, so the form is a pure cross term and changes sign with the
  relative sign of the two cells (`exists_row_rowDilationForm_neg`).

So the numerical range of the prime dilation operator is *not* nonnegative on rows, and no
positivity property of the kernel can give the continuation sign.  The surviving route is the one
the dilation identity already states: the sign has to be proved for the **actual source** —
the centred damped Möbius prefix with its polar correction — and never for an arbitrary row.  That
is the exact analogue, on the damping side, of the corpus's rule that a bound must read the signs
of the coefficients.
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The dilation form of an arbitrary row and its kernel -/

/-- The pronic dilation form of an arbitrary row. -/
def rowDilationForm (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, v n * (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) /
    ((n : ℝ) * ((n : ℝ) + 1))

theorem dilationForm_eq_rowDilationForm (ε : ℝ) (T : ℕ) :
    dilationForm ε T = rowDilationForm ε T (pmPowerDampedCenteredDivisorPrefix ε) := rfl

/-- **The quotient incidence kernel**: the dilation weights grouped by the level they land on. -/
def quotientIncidenceKernel (ε : ℝ) (n m : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, if n / j = m then dampedPrimeWeight ε j else 0

/-- The dilation of a row is the kernel acting on it. -/
theorem sum_dilation_eq_kernel (ε : ℝ) {T n : ℕ} (hn : n ∈ Icc 1 T) (v : ℕ → ℝ) :
    (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) =
      ∑ m ∈ Icc 1 T, quotientIncidenceKernel ε n m * v m := by
  rw [mem_Icc] at hn
  have hswap : (∑ m ∈ Icc 1 T, quotientIncidenceKernel ε n m * v m) =
      ∑ j ∈ Icc 1 n, ∑ m ∈ Icc 1 T, (if n / j = m then dampedPrimeWeight ε j else 0) * v m := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => by rw [quotientIncidenceKernel, Finset.sum_mul]
  rw [hswap]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_Icc] at hj
  have hmem : n / j ∈ Icc 1 T := by
    rw [mem_Icc]
    exact ⟨(Nat.one_le_div_iff hj.1).mpr hj.2, le_trans (Nat.div_le_self n j) hn.2⟩
  have hterm : ∀ m ∈ Icc 1 T,
      (if n / j = m then dampedPrimeWeight ε j else 0) * v m =
        if n / j = m then dampedPrimeWeight ε j * v m else 0 := by
    intro m _
    by_cases h : n / j = m <;> simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq (Icc 1 T) (n / j)
    (fun m => dampedPrimeWeight ε j * v m), if_pos hmem]

/-- The dilation form in kernel coordinates. -/
theorem rowDilationForm_eq_kernel_form (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    rowDilationForm ε T v =
      ∑ n ∈ Icc 1 T, ∑ m ∈ Icc 1 T,
        quotientIncidenceKernel ε n m * v n * v m / ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [rowDilationForm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [sum_dilation_eq_kernel ε hn v, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem dilationForm_eq_kernel_form (ε : ℝ) (T : ℕ) :
    dilationForm ε T =
      ∑ n ∈ Icc 1 T, ∑ m ∈ Icc 1 T,
        quotientIncidenceKernel ε n m * pmPowerDampedCenteredDivisorPrefix ε n *
          pmPowerDampedCenteredDivisorPrefix ε m / ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [dilationForm_eq_rowDilationForm, rowDilationForm_eq_kernel_form]

/-! ## §2. The diagonal vanishes -/

/-- **Zero diagonal.**  A dilation can only return to its own level by the factor one, and
`Λ(1) = 0`. -/
theorem quotientIncidenceKernel_self (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    quotientIncidenceKernel ε n n = 0 := by
  rw [quotientIncidenceKernel]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [mem_Icc] at hj
  by_cases h1 : j = 1
  · subst h1
    simp [dampedPrimeWeight]
  · have hj2 : 2 ≤ j := by omega
    have hlt : n / j < n := Nat.div_lt_self hn (by omega)
    rw [if_neg (by omega : ¬ n / j = n)]

/-! ## §3. The form is indefinite, so positivity must come from the source -/

/-- The only entry of the kernel at horizon two: `κ_ε(2, 1) = (log 2) 2^{-ε}`. -/
theorem quotientIncidenceKernel_two_one (ε : ℝ) :
    quotientIncidenceKernel ε 2 1 = Real.log 2 * (2 : ℝ) ^ (-ε) := by
  have hIcc : (Icc 1 2 : Finset ℕ) = {1, 2} := by
    ext n
    rw [mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [quotientIncidenceKernel, hIcc]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  norm_num [dampedPrimeWeight, ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- **The dilation numerical range is indefinite.**  With zero diagonal and a positive
off-diagonal entry the form is a pure cross term: the row supported on the first two levels with
opposite signs makes it negative at every damping.  Hence no positivity of the kernel can supply
the continuation sign; it must be proved for the actual source. -/
theorem exists_row_rowDilationForm_neg (ε : ℝ) :
    ∃ v : ℕ → ℝ, rowDilationForm ε 2 v < 0 := by
  refine ⟨fun n => if n = 1 then 1 else if n = 2 then -1 else 0, ?_⟩
  have hIcc : (Icc 1 2 : Finset ℕ) = {1, 2} := by
    ext n
    rw [mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hIcc1 : (Icc 1 1 : Finset ℕ) = {1} := by
    ext n
    rw [mem_Icc, Finset.mem_singleton]
    omega
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrpow : 0 < (2 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num) _
  rw [rowDilationForm, hIcc, Finset.sum_insert (by simp), Finset.sum_singleton, hIcc1, hIcc]
  rw [Finset.sum_singleton, Finset.sum_insert (by simp), Finset.sum_singleton]
  norm_num [dampedPrimeWeight, ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hpos : 0 < Real.log 2 * (2 : ℝ) ^ (-ε) := mul_pos hlog hrpow
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
