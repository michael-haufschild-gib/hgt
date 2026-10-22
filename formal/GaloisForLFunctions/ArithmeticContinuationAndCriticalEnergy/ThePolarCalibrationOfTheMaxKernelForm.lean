import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheMaxKernelFormOfTheDampingAutocorrelation

/-!
# The polar calibration of the max-kernel form

In prime-pair coordinates the damping autocorrelation is a bilinear form in the increments
`Λ_η(j) − m(η)` of the centred damped Chebyshev function.  The pole subtraction contributes one
constant per prime-power cell, so three of the four resulting pieces are *explicit*: the weights of
the Nyman–Beurling kernel can be summed in closed form,

`Σ_{k ≤ T} 1/max(j,k) = 1 − 1/j + Σ_{j ≤ m ≤ T} 1/m`,  `Σ_{j,k ≤ T} 1/max(j,k) = 2T − Σ_{m ≤ T} 1/m`,

and what remains is one genuinely bilinear prime-pair sum:

`Σ_{j,k ≤ T} (Λ_η(j) − m(η))(Λ_ε(k) − m(ε))/max(j,k)
   = P_T(η, ε) − m(ε) R_T(η) − m(η) R_T(ε) + m(η) m(ε) (2T − Σ_{m ≤ T} 1/m)`,

with `P_T` the prime-pair form and `R_T(η) = Σ_{j ≤ T} Λ_η(j)(1 − 1/j + Σ_{j ≤ m ≤ T} 1/m)` a
single prime sum against a logarithmic weight (`maxKernelForm_increment_eq`).

This calibrates the obligation.  The explicit polar term grows linearly in the horizon, the
logarithmic row weight makes `R_T` grow linearly too, and the sign the continuation layer needs is
a statement about the sum of three linearly growing quantities being nonnegative up to one
boundary term — so the prime-pair sum must cancel the polar and row terms to *relative* precision
`1/T`.  Leading-order prime asymptotics are therefore not enough, and that is the exact price of
the sign criterion, stated before any estimate is attempted
(`riemannHypothesis_of_primePairMaxKernelForm_ge`).
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Closed forms for the kernel weights -/

/-- The row weight of the Nyman–Beurling kernel at depth `T`. -/
def maxKernelRowWeight (T j : ℕ) : ℝ := 1 - 1 / (j : ℝ) + ∑ m ∈ Icc j T, 1 / (m : ℝ)

/-- **The row weight in closed form.**  Below `j` the kernel is constant `1/j`, above it is `1/k`. -/
theorem sum_one_div_max_eq_rowWeight {j T : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T) :
    (∑ k ∈ Icc 1 T, 1 / ((max j k : ℕ) : ℝ)) = maxKernelRowWeight T j := by
  have h1 : Ioc 0 T = Icc 1 T := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have h2 : Ioc 0 (j - 1) = Icc 1 (j - 1) := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have h3 : Ioc (j - 1) T = Icc j T := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have hsplit := Finset.sum_Ioc_consecutive (fun k : ℕ => 1 / ((max j k : ℕ) : ℝ))
    (Nat.zero_le (j - 1)) (show j - 1 ≤ T by omega)
  rw [h1, h2, h3] at hsplit
  have hlow : ∑ k ∈ Icc 1 (j - 1), 1 / ((max j k : ℕ) : ℝ) = 1 - 1 / (j : ℝ) := by
    have hconst : ∀ k ∈ Icc 1 (j - 1), 1 / ((max j k : ℕ) : ℝ) = 1 / (j : ℝ) := by
      intro k hk
      rw [mem_Icc] at hk
      rw [max_eq_left (by omega : k ≤ j)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hcard : ((j - 1 + 1 - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      have he : (j - 1 + 1 - 1 : ℕ) = j - 1 := by omega
      rw [he, Nat.cast_sub hj]
      push_cast
      ring
    have hj0 : (j : ℝ) ≠ 0 := by
      have : (0 : ℝ) < j := by exact_mod_cast hj
      exact this.ne'
    rw [hcard]
    field_simp
  have hhigh : ∑ k ∈ Icc j T, 1 / ((max j k : ℕ) : ℝ) = ∑ m ∈ Icc j T, 1 / (m : ℝ) :=
    Finset.sum_congr rfl fun k hk => by rw [max_eq_right (mem_Icc.mp hk).1]
  rw [maxKernelRowWeight, ← hsplit, hlow, hhigh]

/-- **The total kernel mass in closed form**: `Σ_{j,k ≤ T} 1/max(j,k) = 2T − Σ_{m ≤ T} 1/m`, since
the level `max = M` carries `2M − 1` cells. -/
theorem sum_sum_one_div_max_eq (T : ℕ) :
    (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, 1 / ((max j k : ℕ) : ℝ)) =
      2 * (T : ℝ) - ∑ m ∈ Icc 1 T, 1 / (m : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hT1 : (1 : ℕ) ≤ T + 1 := by omega
    have hinner : ∀ j ∈ Icc 1 T, (∑ k ∈ Icc 1 (T + 1), 1 / ((max j k : ℕ) : ℝ)) =
        (∑ k ∈ Icc 1 T, 1 / ((max j k : ℕ) : ℝ)) + 1 / ((T : ℝ) + 1) := by
      intro j hj
      rw [mem_Icc] at hj
      rw [Finset.sum_Icc_succ_top hT1, max_eq_right (by omega : j ≤ T + 1)]
      push_cast
      ring
    have hlast : (∑ k ∈ Icc 1 (T + 1), 1 / ((max (T + 1) k : ℕ) : ℝ)) = 1 := by
      have hconst : ∀ k ∈ Icc 1 (T + 1), 1 / ((max (T + 1) k : ℕ) : ℝ) = 1 / ((T : ℝ) + 1) := by
        intro k hk
        rw [mem_Icc] at hk
        rw [max_eq_left hk.2]
        push_cast
        ring
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      have hne : ((T : ℝ) + 1) ≠ 0 := by positivity
      have hcard : ((T + 1 + 1 - 1 : ℕ) : ℝ) = (T : ℝ) + 1 := by push_cast; ring
      rw [hcard]
      field_simp
    rw [Finset.sum_Icc_succ_top hT1, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ih,
      Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hlast, Finset.sum_Icc_succ_top hT1]
    have hcard : ((T + 1 - 1 : ℕ) : ℝ) = (T : ℝ) := by push_cast; ring
    have hne : ((T : ℝ) + 1) ≠ 0 := by positivity
    rw [hcard]
    push_cast
    field_simp
    ring

/-! ## §2. The explicit decomposition of the prime-pair form -/

/-- The prime-pair form: the damped von Mangoldt weights at two dampings against the
Nyman–Beurling kernel. -/
def primePairMaxKernelForm (T : ℕ) (η ε : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
    dampedVonMangoldt η j * dampedVonMangoldt ε k / ((max j k : ℕ) : ℝ)

/-- The single prime sum against the kernel's row weight: a logarithmically weighted damped
Chebyshev sum. -/
def rowWeightedPrimeSum (T : ℕ) (η : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 T, dampedVonMangoldt η j * maxKernelRowWeight T j

/-- **The polar calibration.**  Three of the four pieces of the autocorrelation's prime-pair form
are explicit; only the prime-pair sum is not. -/
theorem maxKernelForm_increment_eq (T : ℕ) (η ε : ℝ) :
    (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, dampedChebyshevIncrement η j *
        dampedChebyshevIncrement ε k / ((max j k : ℕ) : ℝ)) =
      primePairMaxKernelForm T η ε - dampedReadout ε * rowWeightedPrimeSum T η -
        dampedReadout η * rowWeightedPrimeSum T ε +
        dampedReadout η * dampedReadout ε *
          (2 * (T : ℝ) - ∑ m ∈ Icc 1 T, 1 / (m : ℝ)) := by
  have hrow : ∀ j ∈ Icc 1 T, (∑ k ∈ Icc 1 T, 1 / ((max j k : ℕ) : ℝ)) = maxKernelRowWeight T j :=
    fun j hj => sum_one_div_max_eq_rowWeight (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
  have hB : (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
      dampedVonMangoldt η j / ((max j k : ℕ) : ℝ)) = rowWeightedPrimeSum T η := by
    rw [rowWeightedPrimeSum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hrow j hj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hC : (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
      dampedVonMangoldt ε k / ((max j k : ℕ) : ℝ)) = rowWeightedPrimeSum T ε := by
    rw [Finset.sum_comm, rowWeightedPrimeSum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← hrow k hk, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [max_comm]; ring
  have hsplit : (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, dampedChebyshevIncrement η j *
        dampedChebyshevIncrement ε k / ((max j k : ℕ) : ℝ)) =
      (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
        dampedVonMangoldt η j * dampedVonMangoldt ε k / ((max j k : ℕ) : ℝ)) -
        dampedReadout ε * (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
          dampedVonMangoldt η j / ((max j k : ℕ) : ℝ)) -
        dampedReadout η * (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
          dampedVonMangoldt ε k / ((max j k : ℕ) : ℝ)) +
        dampedReadout η * dampedReadout ε * (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
          1 / ((max j k : ℕ) : ℝ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold dampedChebyshevIncrement
    ring
  rw [hsplit, hB, hC, sum_sum_one_div_max_eq, primePairMaxKernelForm]

/-- **The explicit prime-pair criterion for the Riemann hypothesis.**  With the polar and
row-weight terms separated, a lower bound on the prime-pair sum alone — against the explicit
harmonic and polar terms and the horizon boundary term — gives RH. -/
theorem riemannHypothesis_of_primePairMaxKernelForm_ge
    (h : ∀ (T : ℕ) (η ε : ℝ), 0 < η → η ≤ ε → ε ≤ 1 / 2 →
      dampedReadout ε * rowWeightedPrimeSum T η + dampedReadout η * rowWeightedPrimeSum T ε +
          dampedChebyshevError η T * dampedChebyshevError ε T / ((T : ℝ) + 1) ≤
        primePairMaxKernelForm T η ε + dampedReadout η * dampedReadout ε *
          (2 * (T : ℝ) - ∑ m ∈ Icc 1 T, 1 / (m : ℝ))) :
    RiemannHypothesis :=
  riemannHypothesis_of_maxKernelForm_ge_boundary fun T η ε hη hηε hε => by
    rw [maxKernelForm_increment_eq]
    linarith [h T η ε hη hηε hε]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
