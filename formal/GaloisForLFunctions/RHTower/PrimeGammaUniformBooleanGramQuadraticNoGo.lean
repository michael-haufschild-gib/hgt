import GaloisForLFunctions.RHTower.PrimeGammaSignedEulerianCurvaturePluckerLift
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex
import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope

/-!
# Uniform Boolean Gram quadratic obstruction

The uniform Boolean metric makes the literal nested first-trace edges too concentrated.  Their
normalized second Gram coefficient is at most `13/98`, whereas completed theta-moment
log-convexity forces the Xi square-coordinate ratio to be at least `1/6`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section AbstractBooleanTail

variable {ι : Type*} [Fintype ι]

/-- Discounted squared mass of the noninitial Boolean edge columns. -/
def uniformBooleanTailTrace (w discount : ι → ℝ) : ℝ :=
  ∑ i, discount i * w i ^ (2 : ℕ)

/-- Tail trace ceiling forced by `discount ≤ 1/4`, edge weight `≤ 1/6`, and total tail mass
`≤ 1/2`. -/
theorem uniformBooleanTailTrace_le_one_div_fortyEight
    (w discount : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_le : ∀ i, w i ≤ 1 / 6)
    (hdiscount_le : ∀ i, discount i ≤ 1 / 4)
    (hsum : ∑ i, w i ≤ 1 / 2) :
    uniformBooleanTailTrace w discount ≤ 1 / 48 := by
  unfold uniformBooleanTailTrace
  calc
    (∑ i, discount i * w i ^ (2 : ℕ)) ≤ ∑ i, w i / 24 := by
      apply Finset.sum_le_sum
      intro i hi
      have hsq : w i ^ (2 : ℕ) ≤ (1 / 6) * w i := by
        nlinarith [mul_nonneg (hw_nonneg i) (sub_nonneg.mpr (hw_le i))]
      calc
        discount i * w i ^ (2 : ℕ) ≤ (1 / 4) * w i ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right (hdiscount_le i) (sq_nonneg _)
        _ ≤ (1 / 4) * ((1 / 6) * w i) :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = w i / 24 := by ring
    _ = (∑ i, w i) / 24 := by rw [Finset.sum_div]
    _ ≤ (1 / 2) / 24 := div_le_div_of_nonneg_right hsum (by norm_num)
    _ = 1 / 48 := by norm_num

/-- Trace ratio that equals the normalized quadratic coefficient of `det(I + u G)`. -/
def gramNormalizedQuadraticRatio (trace traceSq : ℝ) : ℝ :=
  (trace ^ (2 : ℕ) - traceSq) / (2 * trace ^ (2 : ℕ))

/-- The uniform Boolean trace ceiling and first-column square force the exact `13/98` quadratic
ceiling. -/
theorem gramNormalizedQuadraticRatio_le_thirteen_div_ninetyEight
    {trace traceSq : ℝ}
    (htrace_lower : 1 / 8 ≤ trace)
    (htrace_upper : trace ≤ 7 / 48)
    (htraceSq : 1 / 64 ≤ traceSq) :
    gramNormalizedQuadraticRatio trace traceSq ≤ 13 / 98 := by
  have htrace_pos : 0 < trace := lt_of_lt_of_le (by norm_num) htrace_lower
  have htrace_sq_upper : trace ^ (2 : ℕ) ≤ (7 / 48 : ℝ) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htrace_upper)
      (add_nonneg htrace_pos.le (by norm_num : 0 ≤ (7 / 48 : ℝ)))]
  unfold gramNormalizedQuadraticRatio
  rw [div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos htrace_pos))]
  nlinarith

/-- Squared-entry trace of a finite real Gram matrix.  For a symmetric matrix this is
`trace (G^(2 : ℕ))`. -/
def gramEntrySqSum {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  ∑ i, ∑ j, G i j ^ (2 : ℕ)

/-- The initial Boolean column of squared norm `1/8` forces squared-entry trace at least `1/64`. -/
theorem one_div_sixtyFour_le_gramEntrySqSum_of_zero_zero
    {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (h00 : G 0 0 = 1 / 8) :
    1 / 64 ≤ gramEntrySqSum G := by
  have hrow : G 0 0 ^ (2 : ℕ) ≤ ∑ j, G 0 j ^ (2 : ℕ) := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (G 0 j)) (Finset.mem_univ 0)
  have hall : (∑ j, G 0 j ^ (2 : ℕ)) ≤ ∑ i, ∑ j, G i j ^ (2 : ℕ) := by
    exact Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (G i j)) (Finset.mem_univ 0)
  unfold gramEntrySqSum
  rw [h00] at hrow
  norm_num at hrow
  exact hrow.trans hall

end AbstractBooleanTail

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Magnitude of the corrected first-trace edge along a prime enumeration. -/
def sieveFirstTraceWeight (e : ℕ ≃ Nat.Primes) (n : ℕ) : ℝ :=
  sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ)

theorem sieveFirstTraceWeight_nonneg (e : ℕ ≃ Nat.Primes) (n : ℕ) :
    0 ≤ sieveFirstTraceWeight e n := by
  exact div_nonneg (sieveDensity_pos _).le (by positivity)

/-- Increasing enumeration starts with the exact loss `1/2`. -/
theorem sieveFirstTraceWeight_zero
    (e : ℕ ≃ Nat.Primes) (hfirst : e 0 = ⟨2, Nat.prime_two⟩) :
    sieveFirstTraceWeight e 0 = 1 / 2 := by
  simp [sieveFirstTraceWeight, sievePrefix_zero, hfirst]

/-- Sieve density decreases along every prime enumeration. -/
theorem sieveDensity_sievePrefix_succ_le
    (e : ℕ ≃ Nat.Primes) (n : ℕ) :
    sieveDensity (sievePrefix e (n + 1)) ≤ sieveDensity (sievePrefix e n) := by
  rw [sievePrefix_succ, sieveDensity_insert (notMem_sievePrefix e n)]
  have hdensity := (sieveDensity_pos (sievePrefix e n)).le
  have hinv : 0 ≤ (((e n : ℕ) : ℝ))⁻¹ := by positivity
  nlinarith [mul_nonneg hdensity hinv]

theorem antitone_sieveDensity_sievePrefix (e : ℕ ≃ Nat.Primes) :
    Antitone (fun n => sieveDensity (sievePrefix e n)) :=
  antitone_nat_of_succ_le (sieveDensity_sievePrefix_succ_le e)

/-- Once the prime `2` is inserted, every later sieve density is at most `1/2`. -/
theorem sieveDensity_sievePrefix_le_half
    (e : ℕ ≃ Nat.Primes) (hfirst : e 0 = ⟨2, Nat.prime_two⟩)
    {n : ℕ} (hn : 1 ≤ n) :
    sieveDensity (sievePrefix e n) ≤ 1 / 2 := by
  calc
    sieveDensity (sievePrefix e n) ≤ sieveDensity (sievePrefix e 1) :=
      antitone_sieveDensity_sievePrefix e hn
    _ = 1 / 2 := by
      have hpref : sievePrefix e 1 = insert (e 0) (sievePrefix e 0) := by
        simpa using sievePrefix_succ e 0
      rw [hpref, sieveDensity_insert (notMem_sievePrefix e 0), sievePrefix_zero, hfirst]
      norm_num

/-- Every noninitial increasing-prime sieve loss is at most `1/6`. -/
theorem sieveFirstTraceWeight_le_one_div_six
    (e : ℕ ≃ Nat.Primes) (hfirst : e 0 = ⟨2, Nat.prime_two⟩)
    {n : ℕ} (hn : 1 ≤ n) :
    sieveFirstTraceWeight e n ≤ 1 / 6 := by
  have hfirst_val : (e 0 : ℕ) = 2 := congrArg Subtype.val hfirst
  have hpne : (e n : ℕ) ≠ 2 := by
    intro hp
    have heq : e n = e 0 := Subtype.ext (by omega)
    have hn0 := e.injective heq
    omega
  have hp3_nat : 3 ≤ (e n : ℕ) := by
    have hp2 := (e n).2.two_le
    omega
  have hp3 : (3 : ℝ) ≤ ((e n : ℕ) : ℝ) := by exact_mod_cast hp3_nat
  have hp_pos : (0 : ℝ) < ((e n : ℕ) : ℝ) := by positivity
  have hdensity := sieveDensity_sievePrefix_le_half e hfirst hn
  unfold sieveFirstTraceWeight
  rw [div_le_iff₀ hp_pos]
  nlinarith

/-- Every finite tail of the sieve losses has mass at most `1/2`. -/
theorem sum_sieveFirstTraceWeight_tail_le_half
    (e : ℕ ≃ Nat.Primes) (hfirst : e 0 = ⟨2, Nat.prime_two⟩) (N : ℕ) :
    ∑ n ∈ Finset.range N, sieveFirstTraceWeight e (n + 1) ≤ 1 / 2 := by
  have hsum := sum_sieveDensity_div_prime e (N + 1)
  change (∑ n ∈ Finset.range (N + 1), sieveFirstTraceWeight e n) =
    1 - sieveDensity (sievePrefix e (N + 1)) at hsum
  rw [Finset.sum_range_succ', sieveFirstTraceWeight_zero e hfirst] at hsum
  have hdensity := (sieveDensity_pos (sievePrefix e (N + 1))).le
  nlinarith

/-- Uniform probability that two sign configurations agree on `n + 2` prescribed faces. -/
def uniformBooleanTailDiscount (n : ℕ) : ℝ := (1 / 2) ^ (n + 2)

theorem uniformBooleanTailDiscount_nonneg (n : ℕ) :
    0 ≤ uniformBooleanTailDiscount n := by
  unfold uniformBooleanTailDiscount
  exact pow_nonneg (by norm_num) _

theorem uniformBooleanTailDiscount_le_one_div_four (n : ℕ) :
    uniformBooleanTailDiscount n ≤ 1 / 4 := by
  induction n with
  | zero => norm_num [uniformBooleanTailDiscount]
  | succ n ih =>
      rw [uniformBooleanTailDiscount,
        show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
      change uniformBooleanTailDiscount n * (1 / 2) ≤ 1 / 4
      have hnonneg := uniformBooleanTailDiscount_nonneg n
      nlinarith

/-- Uniform-Boolean squared trace of the noninitial literal sieve edges. -/
def sieveUniformBooleanTailTrace (e : ℕ ≃ Nat.Primes) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    uniformBooleanTailDiscount n * sieveFirstTraceWeight e (n + 1) ^ (2 : ℕ)

theorem sieveUniformBooleanTailTrace_le_one_div_fortyEight
    (e : ℕ ≃ Nat.Primes) (hfirst : e 0 = ⟨2, Nat.prime_two⟩) (N : ℕ) :
    sieveUniformBooleanTailTrace e N ≤ 1 / 48 := by
  let w : Fin N → ℝ := fun n => sieveFirstTraceWeight e (n + 1)
  let discount : Fin N → ℝ := fun n => uniformBooleanTailDiscount n
  have htail := uniformBooleanTailTrace_le_one_div_fortyEight w discount
    (fun n => sieveFirstTraceWeight_nonneg e (n + 1))
    (fun n => sieveFirstTraceWeight_le_one_div_six e hfirst (by omega))
    (fun n => uniformBooleanTailDiscount_le_one_div_four n)
    (by
      change (∑ n : Fin N, sieveFirstTraceWeight e (n + 1)) ≤ 1 / 2
      rw [Fin.sum_univ_eq_sum_range
        (fun n : ℕ => sieveFirstTraceWeight e (n + 1)) N]
      simpa using sum_sieveFirstTraceWeight_tail_le_half e hfirst N)
  unfold sieveUniformBooleanTailTrace
  rw [← Fin.sum_univ_eq_sum_range]
  simpa [uniformBooleanTailTrace, w, discount] using htail

/-- Total uniform-Boolean trace, including the initial prime-`2` column of squared norm `1/8`. -/
def sieveUniformBooleanTrace (e : ℕ ≃ Nat.Primes) (N : ℕ) : ℝ :=
  1 / 8 + sieveUniformBooleanTailTrace e N

theorem sieveUniformBooleanTrace_mem_Icc
    (e : ℕ ≃ Nat.Primes) (hfirst : e 0 = ⟨2, Nat.prime_two⟩) (N : ℕ) :
    sieveUniformBooleanTrace e N ∈ Set.Icc (1 / 8) (7 / 48) := by
  constructor
  · unfold sieveUniformBooleanTrace
    have htail : 0 ≤ sieveUniformBooleanTailTrace e N := by
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (uniformBooleanTailDiscount_nonneg n)
        (sq_nonneg (sieveFirstTraceWeight e (n + 1)))
    linarith
  · unfold sieveUniformBooleanTrace
    have htail := sieveUniformBooleanTailTrace_le_one_div_fortyEight e hfirst N
    linarith

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Scale-free quadratic ratio of the completed theta/Xi square-coordinate coefficients. -/
def thetaSquareCoordinateQuadraticRatio : ℝ :=
  thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 /
    (6 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ))

/-- Completed theta-moment log-convexity gives the exact `1/6` Xi quadratic floor. -/
theorem one_div_six_le_thetaSquareCoordinateQuadraticRatio :
    1 / 6 ≤ thetaSquareCoordinateQuadraticRatio := by
  have hmoment := thetaCuspRawEvenMoment_sq_le_adjacent 1 (by omega)
  norm_num at hmoment
  have hmpos : 0 < thetaCuspRawEvenMoment 1 := thetaCuspRawEvenMoment_pos 1
  have hden : 0 < 6 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) := by
    exact mul_pos (by norm_num) (sq_pos_of_pos hmpos)
  unfold thetaSquareCoordinateQuadraticRatio
  rw [le_div_iff₀ hden]
  nlinarith

/-- Exact rational separation between every uniform Boolean candidate and the theta source. -/
theorem thirteen_div_ninetyEight_lt_thetaSquareCoordinateQuadraticRatio :
    13 / 98 < thetaSquareCoordinateQuadraticRatio := by
  exact lt_of_lt_of_le (by norm_num) one_div_six_le_thetaSquareCoordinateQuadraticRatio

/-- No trace pair satisfying the uniform Boolean bounds can have the Xi quadratic ratio. -/
theorem uniformBooleanGramRatio_ne_thetaSquareCoordinateQuadraticRatio
    {trace traceSq : ℝ}
    (htrace_lower : 1 / 8 ≤ trace)
    (htrace_upper : trace ≤ 7 / 48)
    (htraceSq : 1 / 64 ≤ traceSq) :
    GaloisForLFunctions.HTGeometry.gramNormalizedQuadraticRatio trace traceSq ≠
      thetaSquareCoordinateQuadraticRatio := by
  have hle :=
    GaloisForLFunctions.HTGeometry.gramNormalizedQuadraticRatio_le_thirteen_div_ninetyEight
      htrace_lower htrace_upper htraceSq
  have hlt := thirteen_div_ninetyEight_lt_thetaSquareCoordinateQuadraticRatio
  linarith

end

end RHTower

