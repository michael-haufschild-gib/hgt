import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes
import GaloisForLFunctions.RHTower.TotientMulMoebius

/-!
# Arithmetic coefficient of a true integer lag

Möbius inversion of the CRT compatibility kernel gives the Ramanujan lag
coefficient. Its normalized value is the Möbius-to-totient ratio of the exact
quotient by the lag gcd. These classical identities support the subsequent
valuation visibility and recovery theorems for actual divisor-sieve signals.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- Möbius inverse of the integer CRT compatibility kernel at lag `h`. -/
def ramanujanLagCoefficient (q h : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, moebiusReal (q / d) * (if d ∣ h then (d : ℝ) else 0)

/-- The normalized multiplier of true translation compressed to divisor responses. -/
def sieveLagMultiplier (q h : ℕ) : ℝ :=
  ramanujanLagCoefficient q h / (q.totient : ℝ)

/-- Summing lag coefficients over divisors recovers exact CRT compatibility. -/
theorem sum_divisors_ramanujanLagCoefficient (g h : ℕ) :
    (∑ q ∈ g.divisors, ramanujanLagCoefficient q h) =
      if g ∣ h then (g : ℝ) else 0 := by
  by_cases hg : g = 0
  · subst g
    simp [ramanujanLagCoefficient]
  · apply (sum_eq_iff_sum_mul_moebius_eq.mpr ?_) g (Nat.pos_of_ne_zero hg)
    intro n _
    rw [Nat.sum_divisorsAntidiagonal' (fun a b =>
      ((μ a : ℤ) : ℝ) * (if b ∣ h then (b : ℝ) else 0))]
    rfl

private theorem lagCoefficient_gcd_sum (q h : ℕ) (hq : q ≠ 0) :
    ramanujanLagCoefficient q h =
      ∑ d ∈ (Nat.gcd q h).divisors, (d : ℝ) * moebiusReal (q / d) := by
  have hset : q.divisors.filter (fun d => d ∣ h) = (Nat.gcd q h).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdq, _⟩, hdh⟩
      exact ⟨⟨hdq, hdh⟩, Nat.gcd_ne_zero_left hq⟩
    · rintro ⟨⟨hdq, hdh⟩, _⟩
      exact ⟨⟨hdq, hq⟩, hdh⟩
  rw [ramanujanLagCoefficient, ← hset, sum_filter]
  apply sum_congr rfl
  intro d _
  split_ifs <;> ring

/-- Public gcd-divisor interface, including the zero modulus, for coefficient bridges. -/
theorem ramanujanLagCoefficient_eq_gcd_divisor_sum (q h : ℕ) :
    ramanujanLagCoefficient q h =
      ∑ d ∈ (Nat.gcd q h).divisors, (d : ℝ) * moebiusReal (q / d) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [ramanujanLagCoefficient, moebiusReal]
  · exact lagCoefficient_gcd_sum q h hq.ne'

private theorem lag_moebius_product (t e : ℕ) :
    moebiusReal (t * e) = if e.Coprime t then moebiusReal t * moebiusReal e else 0 := by
  by_cases hc : e.Coprime t
  · simp only [if_pos hc, moebiusReal,
      isMultiplicative_moebius.map_mul_of_coprime hc.symm, Int.cast_mul]
  · have hn : ¬Squarefree (t * e) :=
      fun hs => hc (Nat.coprime_of_squarefree_mul hs).symm
    simp [hc, moebiusReal, moebius_eq_zero_of_not_squarefree hn]

/-- Exact normalized Ramanujan quotient, including zero modulus and zero lag. -/
theorem sieveLagMultiplier_eq_moebius_totient_quotient (q h : ℕ) :
    sieveLagMultiplier q h =
      moebiusReal (q / Nat.gcd q h) / ((q / Nat.gcd q h).totient : ℝ) := by
  by_cases hq : q = 0
  · subst q
    simp [sieveLagMultiplier, ramanujanLagCoefficient, moebiusReal]
  let g := Nat.gcd q h
  let t := q / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left h (Nat.pos_of_ne_zero hq)
  have hgd : g ∣ q := Nat.gcd_dvd_left q h
  have ht : 0 < t := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hgd) hg
  have hqtg : q = t * g := (Nat.div_mul_cancel hgd).symm
  have hdiv (e : ℕ) (he : e ∈ g.divisors) : q / (g / e) = t * e := by
    have hed := Nat.dvd_of_mem_divisors he
    have hepos := Nat.pos_of_mem_divisors he
    apply Nat.div_eq_of_eq_mul_left (Nat.div_pos (Nat.le_of_dvd hg hed) hepos)
    calc
      q = t * g := hqtg
      _ = (t * e) * (g / e) := by
        conv_lhs => rw [← Nat.div_mul_cancel hed]
        ring
  have hsum : ramanujanLagCoefficient q h =
      moebiusReal t * (GaloisForLFunctions.RHTower.TotientMulMoebius.H t g : ℝ) := by
    rw [lagCoefficient_gcd_sum q h hq]
    change (∑ d ∈ g.divisors, (d : ℝ) * moebiusReal (q / d)) = _
    rw [← Nat.sum_div_divisors g (fun d => (d : ℝ) * moebiusReal (q / d))]
    simp only [GaloisForLFunctions.RHTower.TotientMulMoebius.H, Int.cast_sum,
      mul_sum, sum_filter]
    apply sum_congr rfl
    intro e he
    rw [hdiv e he, lag_moebius_product]
    split_ifs <;> simp only [moebiusReal, Int.cast_mul, Int.cast_natCast, mul_zero, Int.cast_zero]
    ring
  have htot := congrArg (fun z : ℤ => (z : ℝ))
    (GaloisForLFunctions.RHTower.TotientMulMoebius.totient_mul_eq t ht g)
  push_cast at htot
  rw [← hqtg] at htot
  have hφq : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  have hφt : (t.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr ht).ne'
  change ramanujanLagCoefficient q h / (q.totient : ℝ) = moebiusReal t / (t.totient : ℝ)
  rw [hsum]
  apply (div_eq_div_iff hφq hφt).mpr
  rw [htot]
  ring

/-- The unnormalized coefficient is the totient weight times the lag multiplier. -/
theorem ramanujanLagCoefficient_eq_totient_mul (q h : ℕ) :
    ramanujanLagCoefficient q h = (q.totient : ℝ) * sieveLagMultiplier q h := by
  by_cases hq : q = 0
  · simp [hq, ramanujanLagCoefficient]
  · have hφ : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
    unfold sieveLagMultiplier
    field_simp

end
end GaloisForLFunctions.BezoutValuationIncidence
