import GaloisForLFunctions.TransHorizonIncidenceMechanics.PMCofactorRowRamanujanTruncation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.GlobalRenormalizedDefectSignAtLargeHorizons

/-!
# The global defect sign of the PM cofactor row

The receiver row of the PM route is the cofactor row `c_Q` at cutoff `Q`. Its horizon-`Q`
response is the truncated Ramanujan expansion of `τ_ε(n) = ∏_{p | n} (1 - p^{-ε})`, which obeys
the **global unit envelope** `0 ≤ τ_ε(n) ≤ 1 = τ_ε(1)` and has the first jump
`τ_ε(1) - τ_ε(2) = 2^{-ε}`. On a polynomial range `M ≤ Q^r` the truncation costs at most
`η = 4^{-ε}/64` (uniform agreement), so the Dirichlet polarization gives

`2 D̃_Q(M) ≤ -(2^{-ε} - 2η)² + (1 + η)² - (1 - η)² < 0`:

no rough primes, no envelope ladder and no ratio-five boundary are needed, because the row
observes the complete damped divisor function, which never exceeds its initial value. Beyond
the polynomial range the long-window law applies with the terminal prime mode
`(p - 1) ρ_ε² / (p^{1+ε} - 1)²`, `ρ_ε = 1/ζ(1+ε)`. Hence, for every fixed damping `ε > 0`,
eventually in the cutoff, the renormalized defect of the actual receiver row is nonpositive at
every prefix.
-/

open Finset Filter Topology ArithmeticFunction RHTower
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- **Polynomial range.** For every `ε > 0` and `r`, eventually in the cutoff `Q`, the defect of
the cofactor row is nonpositive at every prefix `M ≤ Q^r`. -/
theorem eventually_pmCofactor_defect_nonpos_polynomial {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    ∀ᶠ Q : ℕ in atTop, ∀ M : ℕ, M ≤ Q ^ r →
      sieveRenormalizedPrefixDefect Q M (pmCofactorRealWeight ε Q) ≤ 0 := by
  set t : ℝ := (2 : ℝ) ^ (-ε)
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  set η : ℝ := t ^ 2 / 64
  have hη : 0 < η := by positivity
  filter_upwards [eventually_abs_sieveSeq_pmCofactor_sub_divisorCoeff_le hε r hη] with Q hQ M hM
  set c := pmCofactorRealWeight ε Q
  rcases Nat.eq_zero_or_pos M with rfl | hM1
  · have h := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary Q 0 c
    simp at h
    linarith
  have h1 := abs_le.mp (hQ 1 le_rfl (by omega))
  have h2 := abs_le.mp (hQ 2 (by omega) (by omega))
  have hM' := abs_le.mp (hQ (M + 1) (by omega) (by omega))
  have hτ1 : pmPowerDampedDivisorCoeff ε 1 = 1 := pmPowerDampedDivisorCoeff_one ε
  have hτ2 : pmPowerDampedDivisorCoeff ε 2 = 1 - t := pmPowerDampedDivisorCoeff_prime ε Nat.prime_two
  have hτM0 := pmPowerDampedDivisorCoeff_nonneg hε.le (M + 1)
  have hτM1 := pmPowerDampedDivisorCoeff_le_one hε.le (M + 1)
  rw [hτ1] at h1
  rw [hτ2] at h2
  have hid := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary Q M c
  -- the first jump is at least `t - 2η`
  have hjump : (t - 2 * η) ^ 2 ≤ (sieveSeq Q c (1 + 1) - sieveSeq Q c 1) ^ 2 := by
    have hpos : 0 ≤ t - 2 * η := by simp only [η]; nlinarith
    have : t - 2 * η ≤ sieveSeq Q c 1 - sieveSeq Q c (1 + 1) := by
      simp only [show (1 : ℕ) + 1 = 2 by rfl]; linarith [h1.1, h2.2]
    nlinarith
  have hE : (sieveSeq Q c (1 + 1) - sieveSeq Q c 1) ^ 2 ≤
      ∑ k ∈ Icc 1 M, (sieveSeq Q c (k + 1) - sieveSeq Q c k) ^ 2 :=
    single_le_sum (f := fun k => (sieveSeq Q c (k + 1) - sieveSeq Q c k) ^ 2)
      (fun _ _ => sq_nonneg _) (mem_Icc.mpr ⟨le_rfl, hM1⟩)
  have hend : sieveSeq Q c (M + 1) ^ 2 ≤ (1 + η) ^ 2 := by
    have hlo : -(1 + η) ≤ sieveSeq Q c (M + 1) := by linarith [hM'.1]
    have hhi : sieveSeq Q c (M + 1) ≤ 1 + η := by linarith [hM'.2]
    nlinarith
  have hstart : (1 - η) ^ 2 ≤ sieveSeq Q c 1 ^ 2 := by
    have : 0 ≤ 1 - η := by simp only [η]; nlinarith
    nlinarith [h1.1]
  have hfin : -(t - 2 * η) ^ 2 + ((1 + η) ^ 2 - (1 - η) ^ 2) < 0 := by
    simp only [η]; nlinarith
  linarith

/-- The terminal prime mode of the cofactor row: `φ(p) (c(p)/p)² ≥ ρ_ε²/(4 Q^(2k+1))` for every
prime `p ∈ (Q/2, Q]`, whenever `ε ≤ k`. -/
theorem pmCofactor_primeTail_mode_ge {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : ε ≤ k) {Q p : ℕ}
    (hp : p ∈ sievePrimeTail Q) :
    (pmPowerDampedDivisorDensity ε).re ^ 2 / (4 * (Q : ℝ) ^ (2 * k + 1)) ≤
      (p.totient : ℝ) * (pmCofactorRealWeight ε Q p / (p : ℝ)) ^ 2 := by
  obtain ⟨hpI, hpp, hhalf⟩ := mem_filter.mp hp
  obtain ⟨hp2, hpQ⟩ := mem_Icc.mp hpI
  set ρ := (pmPowerDampedDivisorDensity ε).re
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpQR : (p : ℝ) ≤ Q := by exact_mod_cast hpQ
  have hp1 : (1 : ℝ) ≤ p := by linarith
  -- `c(p) = p Re w(p) = -p ρ/(p^{1+ε} - 1)`
  have hQp : Q / p = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hden : pmPowerDampedRamanujanDenominator ε p = (p : ℝ) ^ (1 + ε) - 1 := by
    simp [pmPowerDampedRamanujanDenominator, hpp.primeFactors]
  have hcp : pmCofactorRealWeight ε Q p / (p : ℝ) = -ρ / ((p : ℝ) ^ (1 + ε) - 1) := by
    unfold pmCofactorRealWeight pmPowerDampedRamanujanCofactor
    rw [hQp, Icc_self, sum_singleton, mul_one, pmPowerDampedRamanujanWeight_eq_ofReal hε,
      moebius_apply_prime hpp]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, Complex.mul_re,
      Complex.natCast_re, Complex.ofReal_re, Complex.natCast_im, Complex.ofReal_im, mul_zero,
      sub_zero, hden]
    have hpos : 0 < (p : ℝ) := by linarith
    field_simp
    push_cast
    ring
  rw [hcp, Nat.totient_prime hpp, Nat.cast_sub (by omega), Nat.cast_one, div_pow, neg_sq]
  have hD : 0 < (p : ℝ) ^ (1 + ε) - 1 := by
    have : (p : ℝ) ≤ (p : ℝ) ^ (1 + ε) := by
      calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (p : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    linarith
  have hDle : (p : ℝ) ^ (1 + ε) - 1 ≤ (Q : ℝ) ^ (k + 1) := by
    have h1 : (p : ℝ) ^ (1 + ε) ≤ (p : ℝ) ^ ((k : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have h2 : (p : ℝ) ^ ((k : ℝ) + 1) ≤ (Q : ℝ) ^ ((k : ℝ) + 1) :=
      Real.rpow_le_rpow (by linarith) hpQR (by positivity)
    have e : (Q : ℝ) ^ ((k : ℝ) + 1) = (Q : ℝ) ^ (k + 1) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    linarith
  have hQ : (2 : ℝ) ≤ Q := by linarith
  have hp2Q : (Q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hhalf.le
  -- `(p - 1)/(p^{1+ε} - 1)² ≥ 1/(4 Q^(2k+1))`
  have hsq : ((p : ℝ) ^ (1 + ε) - 1) ^ 2 ≤ (Q : ℝ) ^ (2 * k + 2) := by
    have := pow_le_pow_left₀ hD.le hDle 2
    rwa [← pow_mul, show (k + 1) * 2 = 2 * k + 2 by ring] at this
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg _
  calc ρ ^ 2 / (4 * (Q : ℝ) ^ (2 * k + 1))
      ≤ ρ ^ 2 * ((p : ℝ) - 1) / (Q : ℝ) ^ (2 * k + 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hp2Q' : (Q : ℝ) ≤ 2 * (p : ℝ) - 1 := by
          have : Q ≤ 2 * p - 1 := by omega
          have h' : ((2 * p - 1 : ℕ) : ℝ) = 2 * (p : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [← h']; exact_mod_cast this
        have hp1' : (Q : ℝ) ≤ 4 * ((p : ℝ) - 1) := by linarith
        have : (Q : ℝ) ^ (2 * k + 2) = (Q : ℝ) ^ (2 * k + 1) * Q := by ring
        rw [this]
        have hA : 0 ≤ ρ ^ 2 * (Q : ℝ) ^ (2 * k + 1) := by positivity
        calc ρ ^ 2 * ((Q : ℝ) ^ (2 * k + 1) * Q) = ρ ^ 2 * (Q : ℝ) ^ (2 * k + 1) * Q := by ring
          _ ≤ ρ ^ 2 * (Q : ℝ) ^ (2 * k + 1) * (4 * ((p : ℝ) - 1)) :=
              mul_le_mul_of_nonneg_left hp1' hA
          _ = ρ ^ 2 * ((p : ℝ) - 1) * (4 * (Q : ℝ) ^ (2 * k + 1)) := by ring
    _ ≤ ((p : ℝ) - 1) * (ρ ^ 2 / ((p : ℝ) ^ (1 + ε) - 1) ^ 2) := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ ρ ^ 2 * ((p : ℝ) - 1) := mul_nonneg hρ2 (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left hsq this]

/-- **Global sign of the PM cofactor row.** For every damping `ε > 0`, eventually in the cutoff
`Q`, the renormalized defect of the actual receiver row is nonpositive at every prefix `M`. -/
theorem eventually_pmCofactor_renormalizedDefect_nonpos_all {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ M : ℕ,
      sieveRenormalizedPrefixDefect Q M (pmCofactorRealWeight ε Q) ≤ 0 := by
  set k : ℕ := ⌈ε⌉₊
  have hk : ε ≤ k := Nat.le_ceil ε
  set ρ := (pmPowerDampedDivisorDensity ε).re
  have hρ : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  -- the long-window threshold is eventually below `Q^(2k+6)`
  have hthr : ∀ᶠ Q : ℕ in atTop,
      11 * (Q : ℝ) ^ 5 + 16 * (Q : ℝ) ^ (2 * k + 3) / ρ ^ 2 ≤ (Q : ℝ) ^ (2 * k + 6) := by
    have hlim : Tendsto (fun Q : ℕ => (11 / (Q : ℝ) ^ (2 * k + 1) + 16 / ρ ^ 2 / (Q : ℝ) ^ 3))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun Q : ℕ => (Q : ℝ) ^ (2 * k + 1)) atTop atTop :=
        (tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun Q : ℕ => (Q : ℝ) ^ 3) atTop atTop :=
        (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds.div_atTop h1).add (tendsto_const_nhds.div_atTop h2)
    filter_upwards [hlim.eventually (eventually_le_nhds one_pos), eventually_ge_atTop 1]
      with Q hQ hQ1
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ1
    have e : 11 * (Q : ℝ) ^ 5 + 16 * (Q : ℝ) ^ (2 * k + 3) / ρ ^ 2 =
        (11 / (Q : ℝ) ^ (2 * k + 1) + 16 / ρ ^ 2 / (Q : ℝ) ^ 3) * (Q : ℝ) ^ (2 * k + 6) := by
      field_simp; ring
    rw [e]
    exact mul_le_of_le_one_left (by positivity) hQ
  filter_upwards [eventually_pmCofactor_defect_nonpos_polynomial hε (2 * k + 6), hthr,
    eventually_ge_atTop 2] with Q hpoly hQthr hQ2 M
  by_cases hM : M ≤ Q ^ (2 * k + 6)
  · exact hpoly M hM
  · push Not at hM
    obtain ⟨p, hp⟩ := exists_mem_sievePrimeTail hQ2
    have hMR : (Q : ℝ) ^ (2 * k + 6) ≤ M := by exact_mod_cast hM.le
    have hM5 : 11 * (Q : ℝ) ^ 5 ≤ M := by
      have : 0 ≤ 16 * (Q : ℝ) ^ (2 * k + 3) / ρ ^ 2 := by positivity
      linarith
    have h := two_mul_sieveRenormalizedPrefixDefect_le_terminal_mode (by omega)
      (abs_pmCofactorRealWeight_le_one hε Q) hp hM5
    have hmode := pmCofactor_primeTail_mode_ge hε hk hp
    have hgap0 : 0 ≤ (M : ℝ) - 11 * (Q : ℝ) ^ 5 := by linarith
    have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    have hlow : 4 * (Q : ℝ) ^ 2 ≤ ((M : ℝ) - 11 * (Q : ℝ) ^ 5) *
        (ρ ^ 2 / (4 * (Q : ℝ) ^ (2 * k + 1))) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have hge : 16 * (Q : ℝ) ^ (2 * k + 3) / ρ ^ 2 ≤ (M : ℝ) - 11 * (Q : ℝ) ^ 5 := by linarith
      rw [div_le_iff₀ (by positivity)] at hge
      have : 4 * (Q : ℝ) ^ 2 * (4 * (Q : ℝ) ^ (2 * k + 1)) = 16 * (Q : ℝ) ^ (2 * k + 3) := by ring
      nlinarith
    have := mul_le_mul_of_nonneg_left hmode hgap0
    linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
