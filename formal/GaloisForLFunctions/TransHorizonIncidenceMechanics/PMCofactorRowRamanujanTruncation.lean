import GaloisForLFunctions.TransHorizonIncidenceMechanics.CofactorSquarefreeFermiSamplingAndPronicObservability
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimeBoundaryDissipationAndCofinalDefectSign
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanLogMass
import GaloisForLFunctions.RHTower.Sieve.PSeriesTailAboveCutoff
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# The PM cofactor row reproduces the damped divisor function

The Route PM cofactor row `c_Q(d) = Re(d Σ_{m ≤ Q/d} μ(m) w(dm))`, `w` the Ramanujan weights of
`c_ε(d) = μ(d) d^{-ε}`, is supported on `[1, Q]`. Hence its horizon-`Q` sieve response is its
complete divisor sum at **every** integer, and by the Ramanujan expansion it is the truncation
`s_Q(n) = Re Σ_{q ≤ Q} w(q) c_q(n)` of `τ_ε(n) = Σ_q w(q) c_q(n)`. With `‖w(q)‖ ≤ q^{-1-ε}` and
`|c_q(n)| ≤ Σ_{d | (n, q)} d`, the omitted modes cost at most

`|s_Q(n) - τ_ε(n)| ≤ (1+ε)/ε · τ(n) · Q^{-ε}`,

each divisor `d | n` contributing `d Σ_{q > Q, d | q} q^{-1-ε} ≤ (1+ε)/ε · Q^{-ε}`. Since
`τ(n) = n^{o(1)}`, the row's response agrees with `τ_ε` uniformly on every polynomial range
`n ≤ Q^r` as `Q → ∞`: far beyond its horizon the actual receiver row observes the complete
damped divisor function.
-/

open Finset Filter Topology ArithmeticFunction RHTower
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The cofactor row vanishes beyond its cutoff. -/
theorem pmCofactorRealWeight_eq_zero_of_gt (ε : ℝ) {Q d : ℕ} (h : Q < d) :
    pmCofactorRealWeight ε Q d = 0 := by
  unfold pmCofactorRealWeight pmPowerDampedRamanujanCofactor
  rw [Nat.div_eq_of_lt h]
  simp

/-- The cofactor row is bounded by one. -/
theorem abs_pmCofactorRealWeight_le_one {ε : ℝ} (hε : 0 < ε) (Q d : ℕ) :
    |pmCofactorRealWeight ε Q d| ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [pmCofactorRealWeight, pmPowerDampedRamanujanCofactor]
  · unfold pmCofactorRealWeight
    refine (Complex.abs_re_le_norm _).trans ((norm_pmPowerDampedRamanujanCofactor_le hε Q hd).trans ?_)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)

/-- **Ramanujan form of the row response.** For every `n ≥ 1`,
`s_Q(n) = Re Σ_{q ≤ Q} w(q) c_q(n)`. -/
theorem sieveSeq_pmCofactorRealWeight_eq (ε : ℝ) (Q : ℕ) {n : ℕ} (hn : 0 < n) :
    sieveSeq Q (pmCofactorRealWeight ε Q) n =
      (∑ q ∈ Icc 1 Q, pmPowerDampedRamanujanWeight ε q * d4BMRamanujanNaturalCoefficient n q).re := by
  rw [pmPowerDampedRamanujanCofactor_expansion ε Q hn, Complex.re_sum]
  unfold sieveSeq pmCofactorRealWeight
  rw [sum_filter]
  refine sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

/-- Ramanujan sums only see the common divisors: `|c_q(n)| ≤ Σ_{d | n, d | q} d`. -/
theorem norm_ramanujan_le_common_divisor_mass {n q : ℕ} (hn : 0 < n) (hq : 0 < q) :
    ‖d4BMRamanujanNaturalCoefficient n q‖ ≤
      ∑ d ∈ n.divisors, if d ∣ q then (d : ℝ) else 0 := by
  rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hq]
  calc
    _ ≤ ∑ d ∈ (n.gcd q).divisors, ‖(d : ℂ) * (moebius (q / d) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (n.gcd q).divisors, (d : ℝ) := by
      apply sum_le_sum
      intro d _
      rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
      have hmu : |(moebius (q / d) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q / d))
      simpa using mul_le_mul_of_nonneg_left hmu (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    _ = ∑ d ∈ n.divisors.filter (· ∣ q), (d : ℝ) := by
      congr 1
      ext d
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h1, hn.ne'⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left q hn).ne'⟩
    _ = _ := by rw [sum_filter]

/-- The multiples of `d` above `Q`: `d Σ_{Q < q < R, d | q} q^{-1-ε} ≤ (1+ε)/ε · Q^{-ε}`. -/
theorem multiples_rpow_tail_le {ε : ℝ} (hε : 0 < ε) {Q d : ℕ} (hQ : 1 ≤ Q) (hd : 0 < d)
    (R : ℕ) :
    (d : ℝ) * ∑ q ∈ (Ico (Q + 1) R).filter (d ∣ ·), (q : ℝ) ^ (-(1 + ε)) ≤
      (1 + ε) / ε * (Q : ℝ) ^ (-ε) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  -- reindex the multiples `q = d m`, `m ≥ ⌊Q/d⌋ + 1`
  have hsub : (Ico (Q + 1) R).filter (d ∣ ·) ⊆ (Icc (Q / d + 1) R).image (fun m => d * m) := by
    intro q hq
    obtain ⟨hqI, ⟨m, rfl⟩⟩ := mem_filter.mp hq
    obtain ⟨h1, h2⟩ := mem_Ico.mp hqI
    refine mem_image.mpr ⟨m, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra hc
      have : m ≤ Q / d := by omega
      have := (Nat.le_div_iff_mul_le hd).mp this
      nlinarith
    · nlinarith
  have hinj : Set.InjOn (fun m => d * m) (Icc (Q / d + 1) R : Set ℕ) :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h
  have h1 : ∑ q ∈ (Ico (Q + 1) R).filter (d ∣ ·), (q : ℝ) ^ (-(1 + ε)) ≤
      ∑ m ∈ Icc (Q / d + 1) R, ((d * m : ℕ) : ℝ) ^ (-(1 + ε)) := by
    rw [← sum_image hinj]
    exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : ∑ m ∈ Icc (Q / d + 1) R, ((d * m : ℕ) : ℝ) ^ (-(1 + ε)) =
      (d : ℝ) ^ (-(1 + ε)) * ∑ m ∈ Icc (Q / d + 1) R, (m : ℝ) ^ (-(1 + ε)) := by
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Nat.cast_mul, Real.mul_rpow hdR.le (Nat.cast_nonneg m)]
  have h3 := RHTower.Sieve.sum_rpow_neg_tail_le (c := 1 + ε) (by linarith) (R := Q / d + 1) (N := R) (by omega)
  rw [show (1 : ℝ) - (1 + ε) = -ε by ring, show (1 + ε - 1 : ℝ) = ε by ring] at h3
  -- `(⌊Q/d⌋ + 1)^{-ε} ≤ (Q/d)^{-ε}`
  have h4 : (((Q / d + 1 : ℕ) : ℝ)) ^ (-ε) ≤ ((Q : ℝ) / d) ^ (-ε) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    have := Nat.lt_div_mul_add (a := Q) hd
    rw [div_le_iff₀ hdR]
    push_cast
    have h' : (Q : ℝ) < ((Q / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
    linarith
  have h5 : ((Q : ℝ) / d) ^ (-ε) = (d : ℝ) ^ ε * (Q : ℝ) ^ (-ε) := by
    rw [Real.div_rpow hQR.le hdR.le, Real.rpow_neg hdR.le, div_inv_eq_mul, mul_comm]
  have h6 : (d : ℝ) * (d : ℝ) ^ (-(1 + ε)) * (d : ℝ) ^ ε = 1 := by
    rw [show -(1 + ε) = -1 + -ε by ring, Real.rpow_add hdR, Real.rpow_neg_one,
      Real.rpow_neg hdR.le]
    field_simp
  have hsum_le : ∑ q ∈ (Ico (Q + 1) R).filter (d ∣ ·), (q : ℝ) ^ (-(1 + ε)) ≤
      (d : ℝ) ^ (-(1 + ε)) * ((1 + ε) / ε * ((Q / d + 1 : ℕ) : ℝ) ^ (-ε)) := by
    calc _ ≤ ∑ m ∈ Icc (Q / d + 1) R, ((d * m : ℕ) : ℝ) ^ (-(1 + ε)) := h1
      _ = _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hdR.le _)
  calc (d : ℝ) * ∑ q ∈ (Ico (Q + 1) R).filter (d ∣ ·), (q : ℝ) ^ (-(1 + ε))
      ≤ (d : ℝ) * ((d : ℝ) ^ (-(1 + ε)) * ((1 + ε) / ε * ((Q / d + 1 : ℕ) : ℝ) ^ (-ε))) :=
        mul_le_mul_of_nonneg_left hsum_le hdR.le
    _ ≤ (d : ℝ) * ((d : ℝ) ^ (-(1 + ε)) * ((1 + ε) / ε * ((d : ℝ) ^ ε * (Q : ℝ) ^ (-ε)))) := by
        rw [← h5]
        gcongr
    _ = (1 + ε) / ε * (Q : ℝ) ^ (-ε) * ((d : ℝ) * (d : ℝ) ^ (-(1 + ε)) * (d : ℝ) ^ ε) := by ring
    _ = (1 + ε) / ε * (Q : ℝ) ^ (-ε) := by rw [h6, mul_one]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
