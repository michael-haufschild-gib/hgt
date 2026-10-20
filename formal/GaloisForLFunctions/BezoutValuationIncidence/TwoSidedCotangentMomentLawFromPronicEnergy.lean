import GaloisForLFunctions.BezoutValuationIncidence.PronicPositivityOfTheVasyuninPrimeKernel

/-!
# A two-sided law for the prime cotangent moment from the pronic energy

At a prime the energy-centered primitive is `F_p(M) = log p - (M mod p)`, and its pronic energy
splits at `M = p` into a head where `M mod p = M` and a tail of pronic mass `1/p`. Since
`(log p - r)² ≤ log² p + r²`,

`G^{ec}(p, p) ≤ log² p (1 - 1/p) + p + (log² p + (p - 1)²)/p = log² p + p + (p - 1)²/p`.

On the other hand `G^{ec}(p, p) = π V(1, p) + (p - 1) log p - log² p ≥ 0`. Together:

`log² p ≤ π V(1, p) + (p - 1) log p ≤ 2 log² p + p + (p - 1)²/p`.

With `Σ_{a<p} cot(πa/p) = 0`, `V(1, p) = (1/p) Σ_{a<p} a cot(πa/p)`, so the cotangent moment is
`-(p(p - 1)/π) log p + O(p²)` with explicit constants, obtained from pronic positivity and one
pronic tail estimate.
-/

open Finset ArithmeticFunction RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

theorem pmRamanujanEnergyCenteredPrimitive_prime {p : ℕ} (hp : p.Prime) (M : ℕ) :
    pmRamanujanEnergyCenteredPrimitive p M = Real.log p - ((M % p : ℕ) : ℝ) := by
  rw [pmRamanujanEnergyCenteredPrimitive, pmRamanujanPrimitive_prime hp, vonMangoldt_apply_prime hp]
  simp only [Complex.neg_re, Complex.natCast_re]
  ring

/-- The pronic mass of `[0, n]`: `Σ_{M ≤ n} 1/(M(M+1)) = 1 - 1/(n+1)`. -/
theorem sum_range_succ_pronic_mass (n : ℕ) :
    ∑ M ∈ range (n + 1), 1 / ((M : ℝ) * ((M : ℝ) + 1)) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- **Upper bound for the prime pronic energy.** -/
theorem pmRamanujanEnergyCenteredGram_prime_diag_le {p : ℕ} (hp : p.Prime) :
    pmRamanujanEnergyCenteredGram p p ≤ Real.log p ^ 2 + p + ((p : ℝ) - 1) ^ 2 / p := by
  set L := Real.log p
  set w : ℕ → ℝ := fun M => 1 / ((M : ℝ) * ((M : ℝ) + 1))
  set t : ℕ → ℝ := fun M => pmRamanujanEnergyCenteredPrimitive p M *
    pmRamanujanEnergyCenteredPrimitive p M / ((M : ℝ) * ((M : ℝ) + 1))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hw : HasSum w 1 := RHTower.hasSum_pm_reciprocal_weight
  have hw0 : ∀ M, 0 ≤ w M := fun M => by simp only [w]; positivity
  have hsum : Summable t := (hasSum_pmRamanujanEnergyCenteredGram hp.one_lt hp.one_lt).summable
  -- `(L - r)² ≤ L² + r²` for `r ≥ 0`
  have hpt : ∀ M, t M ≤ (L ^ 2 + ((M % p : ℕ) : ℝ) ^ 2) * w M := fun M => by
    have hr : (0 : ℝ) ≤ ((M % p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq : (L - ((M % p : ℕ) : ℝ)) * (L - ((M % p : ℕ) : ℝ)) ≤
        L ^ 2 + ((M % p : ℕ) : ℝ) ^ 2 := by nlinarith [mul_nonneg hL hr]
    simp only [t, w, pmRamanujanEnergyCenteredPrimitive_prime hp]
    rw [div_eq_mul_one_div _ ((M : ℝ) * ((M : ℝ) + 1))]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  -- head `M < p`: there `M mod p = M` and `M² w(M) ≤ 1`
  have hhead : ∑ M ∈ range p, t M ≤ L ^ 2 * (1 - 1 / p) + p := by
    have hmass : ∑ M ∈ range p, w M = 1 - 1 / p := by
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
      rw [hn, sum_range_succ_pronic_mass n]
      push_cast
      ring
    calc ∑ M ∈ range p, t M ≤ ∑ M ∈ range p, (L ^ 2 * w M + 1) := sum_le_sum fun M hM => by
          refine (hpt M).trans ?_
          rw [Nat.mod_eq_of_lt (mem_range.mp hM), add_mul]
          have h1 : ((M : ℕ) : ℝ) ^ 2 * w M ≤ 1 := by
            rcases Nat.eq_zero_or_pos M with rfl | hM0
            · simp [w]
            · have hM0' : (0 : ℝ) < M := by exact_mod_cast hM0
              simp only [w]
              rw [mul_one_div, div_le_one (by positivity)]
              nlinarith
          linarith
      _ = L ^ 2 * (1 - 1 / p) + p := by
          rw [sum_add_distrib, ← mul_sum, hmass, sum_const, card_range, nsmul_eq_mul, mul_one]
  -- tail `M ≥ p`: `M mod p ≤ p - 1` and the tail mass is `1/p`
  have htail : ∑' n, t (n + p) ≤ (L ^ 2 + ((p : ℝ) - 1) ^ 2) * (1 / p) := by
    have hwt : ∑' n, w (n + p) = 1 / p := by
      have h := hw.summable.sum_add_tsum_nat_add p
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
      rw [hw.tsum_eq] at h
      have hm := sum_range_succ_pronic_mass n
      rw [← hn] at hm
      have hpn : ((n : ℝ) + 1) = p := by rw [hn]; push_cast; ring
      rw [hpn] at hm
      simp only [w] at h ⊢
      linarith
    have hs1 : Summable (fun n => t (n + p)) := (summable_nat_add_iff p).mpr hsum
    have hs2 : Summable (fun n => (L ^ 2 + ((p : ℝ) - 1) ^ 2) * w (n + p)) :=
      ((summable_nat_add_iff p).mpr hw.summable).mul_left (L ^ 2 + ((p : ℝ) - 1) ^ 2)
    have hpt2 : ∀ n, t (n + p) ≤ (L ^ 2 + ((p : ℝ) - 1) ^ 2) * w (n + p) := fun n => by
      have hlt : ((n + p) % p : ℕ) + 1 ≤ p := Nat.mod_lt _ hp.pos
      have hc : (((n + p) % p : ℕ) : ℝ) ≤ (p : ℝ) - 1 := by
        have : ((((n + p) % p : ℕ) : ℝ)) + 1 ≤ p := by exact_mod_cast hlt
        linarith
      have h0 : (0 : ℝ) ≤ (((n + p) % p : ℕ) : ℝ) := Nat.cast_nonneg _
      have hsq : L ^ 2 + (((n + p) % p : ℕ) : ℝ) ^ 2 ≤ L ^ 2 + ((p : ℝ) - 1) ^ 2 := by nlinarith
      exact (hpt (n + p)).trans (mul_le_mul_of_nonneg_right hsq (hw0 _))
    calc ∑' n, t (n + p) ≤ ∑' n, (L ^ 2 + ((p : ℝ) - 1) ^ 2) * w (n + p) :=
          Summable.tsum_le_tsum hpt2 hs1 hs2
      _ = (L ^ 2 + ((p : ℝ) - 1) ^ 2) * (1 / p) := by rw [tsum_mul_left, hwt]
  have hG : pmRamanujanEnergyCenteredGram p p = ∑' M, t M := by
    have h := (hasSum_pmRamanujanEnergyCenteredGram hp.one_lt hp.one_lt).tsum_eq
    rw [pmRamanujanPrimitiveGram_eq_energyCentered hp.one_lt hp.one_lt, add_sub_cancel_left] at h
    exact h.symm
  rw [hG, ← hsum.sum_add_tsum_nat_add p]
  have : L ^ 2 * (1 - 1 / p) + p + (L ^ 2 + ((p : ℝ) - 1) ^ 2) * (1 / p) =
      L ^ 2 + p + ((p : ℝ) - 1) ^ 2 / p := by field_simp; ring
  linarith

/-- **Two-sided law for the Vasyunin sum `V(1, p)`.** -/
theorem vasyuninSum_one_prime_two_sided {p : ℕ} (hp : p.Prime) :
    Real.log p ^ 2 ≤ Real.pi * vasyuninSum 1 p + ((p : ℝ) - 1) * Real.log p ∧
      Real.pi * vasyuninSum 1 p + ((p : ℝ) - 1) * Real.log p ≤
        2 * Real.log p ^ 2 + p + ((p : ℝ) - 1) ^ 2 / p := by
  have hVpp : vasyuninSum p p = 0 := by
    unfold vasyuninSum
    refine sum_eq_zero fun a _ => ?_
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [show (p : ℝ) * a / p = ((a : ℤ) : ℝ) by field_simp; push_cast; ring,
      show sawtooth ((a : ℤ) : ℝ) = 0 by simp [sawtooth], mul_zero]
  -- `G^{ec}(p, p) = π V(1, p) + (p - 1) log p - log² p`
  have hdiag : pmRamanujanEnergyCenteredGram p p =
      Real.pi * vasyuninSum 1 p + ((p : ℝ) - 1) * Real.log p - Real.log p ^ 2 := by
    rw [pmRamanujanEnergyCenteredGram_prime_eq_vasyuninPrimeKernel hp hp, vasyuninPrimeKernel,
      hVpp, sieveCenteringDiscrepancy, Nat.totient_prime hp, vonMangoldt_apply_prime hp,
      Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  have hlow := vasyuninSum_one_prime_ge hp
  have hup := pmRamanujanEnergyCenteredGram_prime_diag_le hp
  constructor <;> linarith

/-- The cotangents over a full set of nonzero residues cancel in pairs. -/
theorem sum_Ico_cot_eq_zero (k : ℕ) : ∑ a ∈ Ico 1 k, Real.cot (Real.pi * ((a : ℝ) / k)) = 0 := by
  have hrefl : ∑ a ∈ Ico 1 k, Real.cot (Real.pi * ((a : ℝ) / k)) =
      ∑ a ∈ Ico 1 k, Real.cot (Real.pi * (((k - a : ℕ) : ℝ) / k)) := by
    refine sum_nbij' (fun a => k - a) (fun a => k - a) (fun a ha => ?_) (fun a ha => ?_)
      (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
    · simp only [mem_Ico] at ha ⊢; omega
    · simp only [mem_Ico] at ha ⊢; omega
    · simp only [mem_Ico] at ha; omega
    · simp only [mem_Ico] at ha; omega
    · simp only [mem_Ico] at ha
      rw [Nat.sub_sub_self ha.2.le]
  have hneg : ∀ a ∈ Ico 1 k, Real.cot (Real.pi * (((k - a : ℕ) : ℝ) / k)) =
      -Real.cot (Real.pi * ((a : ℝ) / k)) := by
    intro a ha
    have hk : (k : ℝ) ≠ 0 := by
      have := (mem_Ico.mp ha); exact_mod_cast (show k ≠ 0 by omega)
    rw [Nat.cast_sub (mem_Ico.mp ha).2.le,
      show Real.pi * (((k : ℝ) - a) / k) = Real.pi - Real.pi * ((a : ℝ) / k) by field_simp,
      Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]
  rw [sum_congr rfl hneg, sum_neg_distrib] at hrefl
  linarith

/-- `V(1, p) = (1/p) Σ_{a<p} a cot(πa/p)`. -/
theorem vasyuninSum_one_eq_moment {k : ℕ} (hk : 0 < k) :
    vasyuninSum 1 k = (∑ a ∈ Ico 1 k, (a : ℝ) * Real.cot (Real.pi * ((a : ℝ) / k))) / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hterm : ∀ a ∈ Ico 1 k, Real.cot (Real.pi * ((a : ℝ) / k)) * sawtooth ((1 : ℕ) * (a : ℝ) / k)
      = (a : ℝ) / k * Real.cot (Real.pi * ((a : ℝ) / k)) -
        1 / 2 * Real.cot (Real.pi * ((a : ℝ) / k)) := by
    intro a ha
    obtain ⟨h1, h2⟩ := mem_Ico.mp ha
    have hfr : Int.fract ((a : ℝ) / k) = (a : ℝ) / k :=
      Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one hkR).mpr (by exact_mod_cast h2)⟩
    have hne : (a : ℝ) / k ≠ 0 := (div_pos (by exact_mod_cast h1) hkR).ne'
    rw [Nat.cast_one, one_mul, sawtooth, hfr, if_neg hne]
    ring
  rw [vasyuninSum, sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, sum_Ico_cot_eq_zero, mul_zero,
    sub_zero, sum_div]
  exact sum_congr rfl fun a _ => by ring

/-- **The prime cotangent moment, two-sided.**
`(p/π)(log² p - (p-1) log p) ≤ Σ_{a<p} a cot(πa/p) ≤ (p/π)(2 log² p + p + (p-1)²/p - (p-1) log p)`. -/
theorem cotangent_moment_prime_two_sided {p : ℕ} (hp : p.Prime) :
    (p : ℝ) / Real.pi * (Real.log p ^ 2 - ((p : ℝ) - 1) * Real.log p) ≤
        ∑ a ∈ Ico 1 p, (a : ℝ) * Real.cot (Real.pi * ((a : ℝ) / p)) ∧
      ∑ a ∈ Ico 1 p, (a : ℝ) * Real.cot (Real.pi * ((a : ℝ) / p)) ≤
        (p : ℝ) / Real.pi * (2 * Real.log p ^ 2 + p + ((p : ℝ) - 1) ^ 2 / p -
          ((p : ℝ) - 1) * Real.log p) := by
  obtain ⟨h1, h2⟩ := vasyuninSum_one_prime_two_sided hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hV := vasyuninSum_one_eq_moment hp.pos
  set S := ∑ a ∈ Ico 1 p, (a : ℝ) * Real.cot (Real.pi * ((a : ℝ) / p))
  have hS : S = p * vasyuninSum 1 p := by rw [hV]; field_simp
  have hπ := Real.pi_pos
  constructor
  · rw [hS, div_mul_eq_mul_div, div_le_iff₀ hπ]
    nlinarith
  · rw [hS, div_mul_eq_mul_div, le_div_iff₀ hπ]
    nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
