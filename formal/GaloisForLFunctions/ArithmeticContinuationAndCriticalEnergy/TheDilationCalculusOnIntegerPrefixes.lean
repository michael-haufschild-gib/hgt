import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationInversionLawOfTheSource

/-!
# The dilation calculus on integer prefixes

The prefix dilations `(D^f v)(n) = Σ_{j ≤ n} f(j) v(⌊n/j⌋)` compose *exactly*, integer parts and
all, because `⌊⌊n/j⌋/k⌋ = ⌊n/(jk)⌋`:

`D^f ∘ D^g = D^{f * g}`  (`prefixDilation_comp`),

so the dilations represent the Dirichlet ring on integer prefixes with no error term.  This is the
calculus that connects the two exact laws the source obeys.  The damped form of `Λ * 1 = log` is
`Λ_ε * ζ_ε = (log)_ε` (`sum_divisors_dampedPrime_mul_rpow`), and composing it with the inversion
law of the source produces a second exact linear law:

`Σ_{j ≤ n} (log j) j^{-ε} A_ε(⌊n/j⌋) = Ψ_ε(n) − m₀(ε) Σ_{j ≤ n} Λ(j) j^{-ε} Φ_ε(⌊n/j⌋)`
(`prefixDilation_dampedLog_centeredPrefix`),

with `Ψ_ε` the damped prime floor sum and `Φ_ε` the damped unit floor sum.  So the centred damped
Möbius source satisfies an explicit law against *every* dilation kernel obtained from the damped
unit row, and the signed work's own kernel `Λ_ε` differs from that row by one convolution.  The
laws are the structural input the indefiniteness of the quotient incidence kernel demands.
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The weighted hyperbola and the composition law -/

/-- **The weighted hyperbola rearrangement.** -/
theorem sum_Icc_divisor_convolution_mul_eq (f g w : ℕ → ℝ) (n : ℕ) :
    (∑ m ∈ Icc 1 n, (∑ j ∈ m.divisors, f j * g (m / j)) * w m) =
      ∑ j ∈ Icc 1 n, f j * ∑ k ∈ Icc 1 (n / j), g k * w (j * k) := by
  have hinner : ∀ m ∈ Icc 1 n, (∑ j ∈ m.divisors, f j * g (m / j)) * w m =
      ∑ j ∈ Icc 1 n, if j ∣ m then f j * g (m / j) * w m else 0 := by
    intro m hm
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    rw [mem_Icc] at hm
    ext j
    rw [Nat.mem_divisors, Finset.mem_filter, mem_Icc]
    constructor
    · rintro ⟨hjm, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hjm (by omega), (Nat.le_of_dvd (by omega) hjm).trans hm.2⟩,
        hjm⟩
    · rintro ⟨-, hjm⟩
      exact ⟨hjm, by omega⟩
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_Icc] at hj
  have hj0 : 0 < j := hj.1
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_nbij' (fun m => m / j) (fun k => j * k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, mem_Icc] at hm
    rw [mem_Icc]
    exact ⟨(Nat.one_le_div_iff hj0).mpr (Nat.le_of_dvd (by omega) hm.2),
      Nat.div_le_div_right hm.1.2⟩
  · intro k hk
    rw [mem_Icc] at hk
    rw [Finset.mem_filter, mem_Icc]
    refine ⟨⟨Nat.mul_pos hj0 hk.1, ?_⟩, Dvd.intro k rfl⟩
    have h := (Nat.le_div_iff_mul_le hj0).mp hk.2
    calc j * k = k * j := Nat.mul_comm j k
      _ ≤ n := h
  · intro m hm
    rw [Finset.mem_filter] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro k _
    exact Nat.mul_div_cancel_left k hj0
  · intro m hm
    rw [Finset.mem_filter] at hm
    rw [Nat.mul_div_cancel' hm.2]
    ring

/-- The prefix dilation operator `(D^f v)(n) = Σ_{j ≤ n} f(j) v(⌊n/j⌋)`. -/
def prefixDilation (f v : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, f j * v (n / j)

/-- **The dilation calculus.**  Prefix dilations compose by Dirichlet convolution, exactly: the
integer parts cause no error, because `⌊⌊n/j⌋/k⌋ = ⌊n/(jk)⌋`. -/
theorem prefixDilation_comp (f g v : ℕ → ℝ) (n : ℕ) :
    prefixDilation f (prefixDilation g v) n =
      prefixDilation (fun m => ∑ j ∈ m.divisors, f j * g (m / j)) v n := by
  rw [prefixDilation, prefixDilation,
    sum_Icc_divisor_convolution_mul_eq f g (fun m => v (n / m)) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prefixDilation, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.div_div_eq_div_mul]

/-! ## §2. The damped form of `Λ * 1 = log` -/

/-- `Λ_ε * ζ_ε = (log)_ε`: the damping twist of `Λ * 1 = log`. -/
theorem sum_divisors_dampedPrime_mul_rpow (ε : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (∑ j ∈ m.divisors, dampedPrimeWeight ε j * ((m / j : ℕ) : ℝ) ^ (-ε)) =
      Real.log m * (m : ℝ) ^ (-ε) := by
  have hm0 : m ≠ 0 := by omega
  have hmul : dampedTwist ε (Λ : ArithmeticFunction ℝ) *
      dampedTwist ε (↑ζ : ArithmeticFunction ℝ) =
      dampedTwist ε (ArithmeticFunction.log : ArithmeticFunction ℝ) := by
    rw [← dampedTwist_mul, ArithmeticFunction.vonMangoldt_mul_zeta]
  have hval : (dampedTwist ε (Λ : ArithmeticFunction ℝ) *
      dampedTwist ε (↑ζ : ArithmeticFunction ℝ)) m =
      dampedTwist ε (ArithmeticFunction.log : ArithmeticFunction ℝ) m := by rw [hmul]
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun a b => dampedTwist ε (Λ : ArithmeticFunction ℝ) a *
        dampedTwist ε (↑ζ : ArithmeticFunction ℝ) b),
    dampedTwist_apply, ArithmeticFunction.log_apply] at hval
  rw [← hval]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : (m / j) ≠ 0 := by
    have h1 := Nat.pos_of_mem_divisors hj
    have h2 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hj)
    have := (Nat.one_le_div_iff h1).mpr h2
    omega
  have hz : ((↑ζ : ArithmeticFunction ℝ) (m / j)) = 1 := by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hjd]
    norm_num
  rw [dampedPrimeWeight, dampedTwist_apply, dampedTwist_apply, hz]
  ring

/-! ## §3. The log-dilation law of the source -/

/-- **The log-dilation law.**  Composing the damped `Λ * 1 = log` relation with the inversion law
makes the logarithmic dilation average of the centred source explicit. -/
theorem prefixDilation_dampedLog_centeredPrefix (ε : ℝ) (n : ℕ) :
    prefixDilation (fun j => Real.log j * (j : ℝ) ^ (-ε))
        (pmPowerDampedCenteredDivisorPrefix ε) n =
      dampedPrimeFloorSum ε n -
        (pmPowerDampedDivisorDensity ε).re *
          ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * dampedUnitFloorSum ε (n / j) := by
  have hkernel : prefixDilation (fun j => Real.log j * (j : ℝ) ^ (-ε))
      (pmPowerDampedCenteredDivisorPrefix ε) n =
      prefixDilation (fun m => ∑ j ∈ m.divisors,
        dampedPrimeWeight ε j * ((m / j : ℕ) : ℝ) ^ (-ε))
        (pmPowerDampedCenteredDivisorPrefix ε) n := by
    rw [prefixDilation, prefixDilation]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [sum_divisors_dampedPrime_mul_rpow ε (mem_Icc.mp hm).1]
  rw [hkernel, ← prefixDilation_comp (dampedPrimeWeight ε) (fun k => (k : ℝ) ^ (-ε))
    (pmPowerDampedCenteredDivisorPrefix ε) n]
  have hinner : ∀ j ∈ Icc 1 n,
      dampedPrimeWeight ε j *
          prefixDilation (fun k => (k : ℝ) ^ (-ε)) (pmPowerDampedCenteredDivisorPrefix ε) (n / j) =
        dampedPrimeWeight ε j * ((n / j : ℕ) : ℝ) -
          (pmPowerDampedDivisorDensity ε).re *
            (dampedPrimeWeight ε j * dampedUnitFloorSum ε (n / j)) := by
    intro j _
    rw [prefixDilation, sum_rpow_mul_centeredPrefix_eq ε (n / j)]
    ring
  rw [prefixDilation, Finset.sum_congr rfl hinner, Finset.sum_sub_distrib, ← Finset.mul_sum,
    dampedPrimeFloorSum]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
