import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedAmplitudeCellScheduled
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogEnergy
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

namespace RHTower.Sieve

open Filter

noncomputable section

/-- Uniform logarithmic exponent for divisor-bounded convolution powers of degree at most `L`. -/
def matomakiTeravainenCoefficientEnergyExponent (w L : ℕ) : ℕ :=
  2 ^ (2 * ((w + 1) * L)) - 1

/-- Every convolution degree at most `L` has logarithmic exponent bounded by the uniform one. -/
theorem matomakiTeravainen_coefficientEnergyExponent_le
    {w ell L : ℕ} (hell : ell ≤ L) :
    2 ^ (2 * ((w + 1) * ell)) - 1 ≤
      matomakiTeravainenCoefficientEnergyExponent w L := by
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (by omega)
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (w + 1) hell))

/-- A fixed degree cap turns every divisor-bounded raised coefficient energy into the exact
subpower budget required by the Matomäki--Teräväinen Huxley schedule. -/
theorem exists_matomakiTeravainen_coefficient_energy_schedule
    {eps C : ℝ} (heps : 0 < eps) (hC : 1 ≤ C)
    (w L : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ) (N A ell : ℕ) (a : Fin N → ℂ),
      T₀ ≤ T →
      1 ≤ N → N ≤ 2 * A →
      0 < ell → ell ≤ L →
      1 < (A : ℝ) →
      ((A ^ ell : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) →
      (∀ n : Fin N,
        ‖a n‖ ≤ C * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w)) →
      ∃ Q : ℝ, 1 ≤ Q ∧ Q ^ 3 ≤ T ^ (eps ^ 2) ∧
        ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
          Q * ((A ^ ell : ℕ) : ℝ) := by
  let K : ℕ := matomakiTeravainenCoefficientEnergyExponent w L
  let D : ℝ := C ^ (2 * L) * ((2 ^ L : ℕ) : ℝ)
  have hpow : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hQevent := eventually_const_mul_rpow_polylog_le_rpow
    (C := D ^ 3) (α := (0 : ℝ)) (β := eps ^ 2) (3 * K) hpow
  have hwidth : ∀ᶠ T : ℝ in atTop, ((2 ^ L : ℕ) : ℝ) ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop ((2 ^ L : ℕ) : ℝ)
  have hlarge : ∀ᶠ T : ℝ in atTop, (2 : ℝ) ≤ T := Filter.eventually_ge_atTop 2
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((2 ^ L : ℕ) : ℝ) ≤ T ^ eps ∧
      D ^ 3 * (1 + |Real.log T|) ^ (3 * K) ≤ T ^ (eps ^ 2) ∧
      2 ≤ T := by
    filter_upwards [hwidth, hQevent, hlarge] with T hw hq hT
    simpa only [Real.rpow_zero, mul_one] using And.intro hw (And.intro hq hT)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 T₁, le_max_left _ _, ?_⟩
  intro T N A ell a hT hN hNA hell hellL hA hAhi hpoint
  have hdata := hT₁ T (le_trans (le_max_right _ _) hT)
  have hT1 : (1 : ℝ) ≤ T := le_trans (by norm_num) hdata.2.2
  have hT0 : (0 : ℝ) < T := zero_lt_one.trans_le hT1
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have habsT : |Real.log T| = Real.log T := abs_of_nonneg hlogT0
  let Q : ℝ := D * (1 + |Real.log T|) ^ K
  refine ⟨Q, ?_, ?_, ?_⟩
  · have hCpow : (1 : ℝ) ≤ C ^ (2 * L) := one_le_pow₀ hC
    have htwo : (1 : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow L 2 (by omega)
    have hD : (1 : ℝ) ≤ D := by
      dsimp only [D]
      exact one_le_mul_of_one_le_of_one_le hCpow htwo
    have hlog : (1 : ℝ) ≤ 1 + |Real.log T| := by
      linarith [abs_nonneg (Real.log T)]
    dsimp only [Q]
    exact one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hlog)
  · dsimp only [Q]
    rw [mul_pow, ← pow_mul]
    simpa only [Nat.mul_comm] using hdata.2.1
  · have hraw := sum_normSq_convPow_le_fixed_polylog (ell := ell) (w := w)
      hN (zero_le_one.trans hC) a hpoint
    let e : ℕ := 2 ^ (2 * ((w + 1) * ell)) - 1
    have heK : e ≤ K := by
      dsimp only [e, K]
      exact matomakiTeravainen_coefficientEnergyExponent_le hellL
    have hCell : C ^ (2 * ell) ≤ C ^ (2 * L) :=
      pow_le_pow_right₀ hC (Nat.mul_le_mul_left 2 hellL)
    have hNpowNat : N ^ ell ≤ 2 ^ L * A ^ ell := by
      calc
        N ^ ell ≤ (2 * A) ^ ell := Nat.pow_le_pow_left hNA ell
        _ = 2 ^ ell * A ^ ell := by rw [mul_pow]
        _ ≤ 2 ^ L * A ^ ell :=
          Nat.mul_le_mul_right (A ^ ell) (Nat.pow_le_pow_right (by omega) hellL)
    have hNpow : (((N ^ ell : ℕ) : ℝ)) ≤
        ((2 ^ L : ℕ) : ℝ) * ((A ^ ell : ℕ) : ℝ) := by
      exact_mod_cast hNpowNat
    have hNpowT : (((N ^ ell : ℕ) : ℝ)) ≤ T := by
      calc
        (((N ^ ell : ℕ) : ℝ))
            ≤ ((2 ^ L : ℕ) : ℝ) * ((A ^ ell : ℕ) : ℝ) := hNpow
        _ ≤ T ^ eps * T ^ (1 - 2 * eps) :=
          mul_le_mul hdata.1 hAhi (by positivity) (by positivity)
        _ = T ^ (1 - eps) := by
          rw [← Real.rpow_add hT0]
          congr 1
          ring
        _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
        _ = T := by simp
    have hM1 : 1 ≤ N ^ ell := Nat.one_le_pow ell N hN
    have hMpos : (0 : ℝ) < ((N ^ ell : ℕ) : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
    have hlogM0 : 0 ≤ Real.log (((N ^ ell : ℕ) : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast hM1)
    have hlog : 1 + Real.log (((N ^ ell : ℕ) : ℝ)) ≤ 1 + |Real.log T| := by
      rw [habsT]
      simpa [add_comm] using add_le_add_left (Real.log_le_log hMpos hNpowT) 1
    have hlogOne : (1 : ℝ) ≤ 1 + Real.log (((N ^ ell : ℕ) : ℝ)) := by linarith
    have hlogPow :
        (1 + Real.log (((N ^ ell : ℕ) : ℝ))) ^ e ≤
          (1 + |Real.log T|) ^ K := by
      calc
        (1 + Real.log (((N ^ ell : ℕ) : ℝ))) ^ e
            ≤ (1 + |Real.log T|) ^ e :=
              pow_le_pow_left₀ (by linarith) hlog e
        _ ≤ (1 + |Real.log T|) ^ K :=
          pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log T)]) heK
    have hlen : (((N ^ ell : ℕ) : ℝ)) ≤
        ((2 ^ L : ℕ) : ℝ) * ((A ^ ell : ℕ) : ℝ) := hNpow
    calc
      ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2
          ≤ C ^ (2 * ell) *
              (((N ^ ell : ℕ) : ℝ) *
                (1 + Real.log (((N ^ ell : ℕ) : ℝ))) ^ e) := by
            simpa only [e] using hraw
      _ ≤ C ^ (2 * L) *
          ((((2 ^ L : ℕ) : ℝ) * ((A ^ ell : ℕ) : ℝ)) *
            (1 + |Real.log T|) ^ K) := by
          gcongr
      _ = Q * ((A ^ ell : ℕ) : ℝ) := by
          dsimp only [Q, D]
          ring

end

end RHTower.Sieve
