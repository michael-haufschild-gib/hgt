import GaloisForLFunctions.RHTower.WeilLagQuadraticInterpolation
import GaloisForLFunctions.RHTower.WeilLagFunctionPrimeGap

/-!
# The actual primes form a quadratic integer-lag mesh

The corpus's unconditional 71/100 short-gap supply yields the n^(3/4)
mesh geometry needed by natural-scale upper lag interpolation. A fixed prime
absorbs the bounded initial segment. The prime-lag RH boundary itself was
already proved by the separate prime-only Landau argument.
-/

open Real Set Filter

namespace RHTower

noncomputable section

private theorem prime_short_gap_square {p k q : ℕ} (hp : p.Prime)
    (hpk : p ≤ k) (hkq : k ≤ q)
    (hl : (k : ℝ) < p + (p : ℝ) ^ (71 / 100 : ℝ))
    (hu : (q : ℝ) ≤ k + (k : ℝ) ^ (71 / 100 : ℝ)) :
    ((q : ℝ) - p) ^ 2 ≤ 9 * ((p : ℝ) * Real.sqrt p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hpkR : (p : ℝ) ≤ k := by exact_mod_cast hpk
  have hkqR : (k : ℝ) ≤ q := by exact_mod_cast hkq
  have hpow : (p : ℝ) ^ (71 / 100 : ℝ) ≤ p := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (71 / 100 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using h
  have hk2p : (k : ℝ) ≤ 2 * p := by linarith
  have htwo : (2 : ℝ) ^ (71 / 100 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (71 / 100 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using h
  have hkpow : (k : ℝ) ^ (71 / 100 : ℝ) ≤ 2 * (p : ℝ) ^ (71 / 100 : ℝ) := by
    calc _ ≤ (2 * (p : ℝ)) ^ (71 / 100 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hk2p (by norm_num)
      _ = (2 : ℝ) ^ (71 / 100 : ℝ) * (p : ℝ) ^ (71 / 100 : ℝ) :=
        Real.mul_rpow (by norm_num) hp0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hp0.le _)
  have hgap : (q : ℝ) - p ≤ 3 * (p : ℝ) ^ (71 / 100 : ℝ) := by linarith
  have hgap0 : 0 ≤ (q : ℝ) - p := by linarith
  have hgapSq : ((q : ℝ) - p) ^ 2 ≤ 9 * ((p : ℝ) ^ (71 / 100 : ℝ)) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hgap)
      (show 0 ≤ 3 * (p : ℝ) ^ (71 / 100 : ℝ) + ((q : ℝ) - p) by positivity)
    nlinarith only [h]
  have hpower : ((p : ℝ) ^ (71 / 100 : ℝ)) ^ 2 ≤ (p : ℝ) * Real.sqrt p := by
    calc _ = ((p : ℝ) ^ (71 / 100 : ℝ)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = (p : ℝ) ^ ((71 / 100 : ℝ) * 2) := (Real.rpow_mul hp0.le _ _).symm
      _ ≤ (p : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
      _ = (p : ℝ) * Real.sqrt p := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hp0,
          Real.rpow_one, ← Real.sqrt_eq_rpow]
  exact hgapSq.trans (mul_le_mul_of_nonneg_left hpower (by norm_num))

/-- Actual primes satisfy the quantitative quadratic lag mesh law unconditionally. -/
theorem quadraticLagMesh_actual_primes : QuadraticLagMesh {p : ℕ | p.Prime} := by
  obtain ⟨X₀, hX₀, hbelow⟩ := exists_prime_short_gap
  obtain ⟨z₀, habove⟩ := Filter.eventually_atTop.mp
    Sieve.exists_eventually_routeT_prime_in_every_base_window
  let B : ℝ := max X₀ z₀
  obtain ⟨P, hPceil, hP⟩ := Nat.exists_infinite_primes (⌈B⌉₊ + 2)
  have hBP : B ≤ (P : ℝ) := by
    have hc : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
    have hn : (⌈B⌉₊ : ℝ) ≤ P := by exact_mod_cast (by omega : ⌈B⌉₊ ≤ P)
    exact hc.trans hn
  let C : ℝ := 9 + (P : ℝ) ^ 2
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, ?_⟩
  intro k hk
  by_cases hbig : B ≤ (k : ℝ)
  · obtain ⟨p, hp, hpk, hclose⟩ := hbelow k ((le_max_left X₀ z₀).trans hbig)
    rw [Nat.floor_natCast] at hclose
    obtain ⟨q, hq, hkq, hqu⟩ := habove k ((le_max_right X₀ z₀).trans hbig)
    rw [Sieve.routeTHoheiselEveryBaseExponent] at hqu
    have hpkN : p ≤ k := by exact_mod_cast hpk
    have hkqN : k ≤ q := by exact_mod_cast hkq.le
    refine ⟨p, hp, q, hq, hp.two_le, hpkN, hkqN, ?_⟩
    exact (prime_short_gap_square hp hpkN hkqN hclose hqu).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith only [sq_nonneg (P : ℝ)])
        (by positivity))
  · have hkP : k ≤ P := by
      have : (k : ℝ) ≤ P := (le_of_not_ge hbig).trans hBP
      exact_mod_cast this
    refine ⟨2, Nat.prime_two, P, hP, le_rfl, hk, hkP, ?_⟩
    have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP.two_le
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    have hsq : ((P : ℝ) - 2) ^ 2 ≤ (P : ℝ) ^ 2 := by nlinarith
    have hbase : (1 : ℝ) ≤ 2 * Real.sqrt 2 := by linarith
    calc _ ≤ (P : ℝ) ^ 2 := hsq
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C * (2 * Real.sqrt 2) := by nlinarith only [mul_nonneg hC (sub_nonneg.mpr hbase)]

end
end RHTower
