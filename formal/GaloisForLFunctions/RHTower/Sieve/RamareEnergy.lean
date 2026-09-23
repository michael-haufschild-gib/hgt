import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare
import GaloisForLFunctions.RHTower.Sieve.RamareBilinearMeanSquare

/-!
# The Ramaré weight preserves the coefficient energy

Splitting a sum over its designated prime factors makes every integer appear in `ω_P(n)` of the
blocks, each time with weight `1/ω_P(n)`.  Squaring, the total energy of the blocks is

```text
∑_{p ∈ P} ∑_{m} |μ(m)/(ω_P(m)+1)|²  =  ∑_{n} ω_P(n)·(1/ω_P(n))²  ≤  ∑_{n ≤ M} 1  =  M ,
```

so the factorisation costs **nothing** in energy: the diagonal of the bilinear form is the diagonal
of the original polynomial.  Bounding the blocks one at a time instead charges `∑_p M/p = M·A`,
which exceeds the budget as soon as the harmonic mass `A` is large — and `A` must be large for the
rough term.  The two constraints are compatible only because the Ramaré weight is `1/ω_P`, not `1`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-- The cofactor coefficient is bounded by the reciprocal of the weight of its multiple. -/
theorem norm_ramareCofactorCoeff_sq_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {p m : ℕ} (hp : p.Prime) (hpP : p ∈ P) (hpm : ¬ p ∣ m) :
    ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ)
      ≤ (1 / ((primeFactorsIn P (p * m)).card : ℝ)) ^ (2 : ℕ) := by
  have hcard := card_primeFactorsIn_mul_prime hPprime hp hpP hpm
  have hden : (((primeFactorsIn P m).card : ℂ) + 1)
      = (((primeFactorsIn P (p * m)).card : ℕ) : ℂ) := by
    rw [hcard]
    push_cast
    ring
  have hnormden : ‖(((primeFactorsIn P m).card : ℂ) + 1)‖
      = ((primeFactorsIn P (p * m)).card : ℝ) := by
    rw [hden, Complex.norm_natCast]
  have hnum : ‖((μ m : ℤ) : ℂ)‖ ≤ 1 := by
    have hnorm : ‖((μ m : ℤ) : ℂ)‖ = |((μ m : ℤ) : ℝ)| := by
      rw [show (((μ m : ℤ)) : ℂ) = ((((μ m : ℤ) : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    exact abs_moebius_real_le_one m
  have hpos : (1 : ℝ) ≤ ((primeFactorsIn P (p * m)).card : ℝ) := by
    have := one_le_card_primeFactorsIn_mul hpP m
    exact_mod_cast this
  have hstep : ‖ramareCofactorCoeff P m‖ ≤ 1 / ((primeFactorsIn P (p * m)).card : ℝ) := by
    rw [ramareCofactorCoeff, norm_div, hnormden]
    exact div_le_div_of_nonneg_right hnum (by linarith)
  exact pow_le_pow_left₀ (norm_nonneg _) hstep 2

/-- The multiples of `p` produced by its cofactor block. -/
def ramareCofactorImage (M p : ℕ) : Finset ℕ :=
  ({m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}).image (fun m => p * m)

theorem ramareCofactorImage_subset (M p : ℕ) :
    ramareCofactorImage M p ⊆ Finset.Icc 1 M := by
  classical
  intro n hn
  rw [ramareCofactorImage, Finset.mem_image] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  rw [Finset.mem_filter, ramareCofactorSet, Finset.mem_image] at hm
  obtain ⟨⟨k, hk, hkm⟩, -⟩ := hm
  rw [Finset.mem_filter] at hk
  obtain ⟨hkI, hpk⟩ := hk
  have hkeq : p * (k / p) = k := Nat.mul_div_cancel' hpk
  rw [← hkm, hkeq]
  exact hkI

theorem dvd_of_mem_ramareCofactorImage {M p n : ℕ}
    (hn : n ∈ ramareCofactorImage M p) : p ∣ n := by
  classical
  rw [ramareCofactorImage, Finset.mem_image] at hn
  obtain ⟨m, -, rfl⟩ := hn
  exact Dvd.intro m rfl

/-- **The Ramaré blocks carry no more energy than the original polynomial.** -/
theorem sum_ramareCofactor_energy_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) :
    ∑ p ∈ P, ∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
        ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ)
      ≤ (M : ℝ) := by
  classical
  -- pass to the multiples
  have hblock : ∀ p ∈ P,
      ∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
          ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ)
        ≤ ∑ n ∈ ramareCofactorImage M p, (1 / ((primeFactorsIn P n).card : ℝ)) ^ (2 : ℕ) := by
    intro p hp
    have hpP := hPprime p hp
    have hinj : ∀ x ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
        ∀ y ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
        p * x = p * y → x = y := by
      intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hpP.pos hxy
    rw [ramareCofactorImage, Finset.sum_image hinj]
    refine Finset.sum_le_sum fun m hm => ?_
    have hpm : ¬ p ∣ m := (Finset.mem_filter.1 hm).2
    exact norm_ramareCofactorCoeff_sq_le hPprime hpP hp hpm
  refine le_trans (Finset.sum_le_sum hblock) ?_
  -- exchange the order of summation
  have hswap : ∑ p ∈ P, ∑ n ∈ ramareCofactorImage M p,
        (1 / ((primeFactorsIn P n).card : ℝ)) ^ (2 : ℕ)
      = ∑ n ∈ Finset.Icc 1 M, ∑ p ∈ P,
          (if n ∈ ramareCofactorImage M p then (1 / ((primeFactorsIn P n).card : ℝ)) ^ (2 : ℕ)
            else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun n _ => rfl
    ext n
    simp only [Finset.mem_filter]
    constructor
    · intro hn
      exact ⟨ramareCofactorImage_subset M p hn, hn⟩
    · rintro ⟨-, hn⟩
      exact hn
  rw [hswap]
  have hrow : ∀ n ∈ Finset.Icc 1 M,
      ∑ p ∈ P, (if n ∈ ramareCofactorImage M p then (1 / ((primeFactorsIn P n).card : ℝ)) ^ (2 : ℕ)
        else 0) ≤ 1 := by
    intro n _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    set k : ℕ := ({p ∈ P | n ∈ ramareCofactorImage M p}).card with hkdef
    have hsub : {p ∈ P | n ∈ ramareCofactorImage M p} ⊆ primeFactorsIn P n := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [mem_primeFactorsIn]
      exact ⟨hp.1, dvd_of_mem_ramareCofactorImage hp.2⟩
    have hkle : k ≤ (primeFactorsIn P n).card := Finset.card_le_card hsub
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0]
      norm_num
    · have hω : 1 ≤ (primeFactorsIn P n).card := le_trans hk0 hkle
      have hωR : (1 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := by exact_mod_cast hω
      have hkR : (k : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := by exact_mod_cast hkle
      have hval : (1 / ((primeFactorsIn P n).card : ℝ)) ^ (2 : ℕ)
          = 1 / (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn P n).card : ℝ)) := by
        rw [div_pow, one_pow, sq]
      rw [hval, mul_one_div, div_le_one (by nlinarith)]
      nlinarith [hkR, hωR]
  refine le_trans (Finset.sum_le_sum hrow) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
  norm_num

/-- Every cofactor of `p` in `[1, M]` is at most `⌊M/p⌋`. -/
theorem ramareCofactorSet_le (M : ℕ) {p m : ℕ}
    (hm : m ∈ ramareCofactorSet (Finset.Icc 1 M) p) : m ≤ M / p := by
  classical
  rw [ramareCofactorSet, Finset.mem_image] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  exact Nat.div_le_div_right hn.1.2

/-- The cofactor block of `p` has at most `⌊M/p⌋` elements. -/
theorem card_ramareCofactorSet_le (M : ℕ) (p : ℕ) :
    (ramareCofactorSet (Finset.Icc 1 M) p).card ≤ M / p := by
  classical
  refine le_trans (Finset.card_image_le) ?_
  rw [← card_Icc_filter_dvd M p]

/-- **The Ramaré `p`-diagonal of the mean square.**  The `1/ω_P` weight keeps the total energy at
`M`, so the diagonal coefficient is the mean value theorem's and the height-free part is carried by
`∑_{p ∈ P} p^{-2}`. -/
theorem sum_integral_normSq_ramareCofactorPoly_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    (M : ℕ) {W : ℝ} (hW : 1 ≤ W) :
    ∑ p ∈ P, (∫ w in Set.Icc (-W) W,
        ‖logPoly (ramareCofactorCoeff P)
          {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} w‖ ^ (2 : ℕ))
      ≤ 5 * Real.pi / 2 * W * (M : ℝ)
        + 5 * Real.exp 1 / 2 * (M : ℝ) ^ (2 : ℕ) * (∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * (p : ℝ))) := by
  classical
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  set E : ℕ → ℝ := fun p =>
    ∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
      ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ) with hEdef
  have hE0 : ∀ p, 0 ≤ E p := fun p => Finset.sum_nonneg fun m _ => by positivity
  -- the per-block mean value theorem, at the block's own length
  have hblock : ∀ p ∈ P, (∫ w in Set.Icc (-W) W,
      ‖logPoly (ramareCofactorCoeff P)
        {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} w‖ ^ (2 : ℕ))
      ≤ 5 * Real.pi / 2 * W * E p + 5 * Real.exp 1 / 2 * ((M / p : ℕ) : ℝ) * E p := by
    intro p hp
    have hppos := (hPprime p hp).pos
    have hs0 : (0 : ℕ) ∉ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} := by
      intro hcon
      have h0 : ¬ p ∣ (0 : ℕ) := (Finset.mem_filter.1 hcon).2
      exact h0 (dvd_zero p)
    have hsM : ∀ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}, m ≤ M / p :=
      fun m hm => ramareCofactorSet_le M (Finset.mem_filter.1 hm).1
    have h := integral_Icc_normSq_logPoly_le_energy (ramareCofactorCoeff P) hs0 hsM hW
    rw [hEdef]
    calc (∫ w in Set.Icc (-W) W,
          ‖logPoly (ramareCofactorCoeff P)
            {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} w‖ ^ (2 : ℕ))
        ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((M / p : ℕ) : ℝ))
            * (∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
                ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ)) := h
      _ = 5 * Real.pi / 2 * W
            * (∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
                ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ))
          + 5 * Real.exp 1 / 2 * ((M / p : ℕ) : ℝ)
            * (∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
                ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ)) := by ring
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · rw [← Finset.mul_sum]
    have henergy : ∑ p ∈ P, E p ≤ (M : ℝ) := sum_ramareCofactor_energy_le hPprime M
    refine mul_le_mul_of_nonneg_left henergy ?_
    have := Real.pi_pos
    positivity
  · have hEle : ∀ p ∈ P, E p ≤ ((M / p : ℕ) : ℝ) := by
      intro p hp
      have hcoeff : ∀ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
          ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ) ≤ 1 := by
        intro m hm
        have hpm : ¬ p ∣ m := (Finset.mem_filter.1 hm).2
        have hb := norm_ramareCofactorCoeff_sq_le hPprime (hPprime p hp) hp hpm
        have hpos : (1 : ℝ) ≤ ((primeFactorsIn P (p * m)).card : ℝ) := by
          have := one_le_card_primeFactorsIn_mul hp m
          exact_mod_cast this
        have : (1 / ((primeFactorsIn P (p * m)).card : ℝ)) ^ (2 : ℕ) ≤ 1 := by
          have h1 : 1 / ((primeFactorsIn P (p * m)).card : ℝ) ≤ 1 := by
            rw [div_le_one (by linarith)]
            exact hpos
          have h0 : (0 : ℝ) ≤ 1 / ((primeFactorsIn P (p * m)).card : ℝ) := by positivity
          nlinarith [h1, h0]
        linarith
      have hcard : ∑ m ∈ {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m},
          ‖ramareCofactorCoeff P m‖ ^ (2 : ℕ)
          ≤ (({m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}).card : ℝ) := by
        refine le_trans (Finset.sum_le_sum hcoeff) ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcle : ({m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}).card ≤ M / p :=
        le_trans (Finset.card_filter_le _ _) (card_ramareCofactorSet_le M p)
      have hcleR : (({m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}).card : ℝ)
          ≤ ((M / p : ℕ) : ℝ) := by exact_mod_cast hcle
      rw [hEdef]
      linarith
    have hstep : ∀ p ∈ P, 5 * Real.exp 1 / 2 * ((M / p : ℕ) : ℝ) * E p
        ≤ 5 * Real.exp 1 / 2 * (M : ℝ) ^ (2 : ℕ) * ((1 : ℝ) / ((p : ℝ) * (p : ℝ))) := by
      intro p hp
      have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hPprime p hp).pos
      have hdiv : ((M / p : ℕ) : ℝ) ≤ (M : ℝ) / (p : ℝ) := by
        have := (Nat.cast_div_le (α := ℝ) (m := M) (n := p))
        simpa using this
      have hd0 : (0 : ℝ) ≤ ((M / p : ℕ) : ℝ) := Nat.cast_nonneg _
      have hprod : ((M / p : ℕ) : ℝ) * E p ≤ ((M : ℝ) / (p : ℝ)) * ((M : ℝ) / (p : ℝ)) := by
        calc ((M / p : ℕ) : ℝ) * E p ≤ ((M / p : ℕ) : ℝ) * ((M / p : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (hEle p hp) hd0
          _ ≤ ((M : ℝ) / (p : ℝ)) * ((M : ℝ) / (p : ℝ)) := by nlinarith [hdiv, hd0]
      have hval : ((M : ℝ) / (p : ℝ)) * ((M : ℝ) / (p : ℝ))
          = (M : ℝ) ^ (2 : ℕ) * ((1 : ℝ) / ((p : ℝ) * (p : ℝ))) := by
        field_simp
      have hc0 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 := by positivity
      calc 5 * Real.exp 1 / 2 * ((M / p : ℕ) : ℝ) * E p
          = 5 * Real.exp 1 / 2 * (((M / p : ℕ) : ℝ) * E p) := by ring
        _ ≤ 5 * Real.exp 1 / 2 * (((M : ℝ) / (p : ℝ)) * ((M : ℝ) / (p : ℝ))) :=
            mul_le_mul_of_nonneg_left hprod hc0
        _ = 5 * Real.exp 1 / 2 * (M : ℝ) ^ (2 : ℕ) * ((1 : ℝ) / ((p : ℝ) * (p : ℝ))) := by
            rw [hval]; ring
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [← Finset.mul_sum]

/-- **The Ramaré `p`-diagonal is inside the Matomäki–Radziwiłł budget.**  Once the designated primes
satisfy `∑_{p ∈ P} p^{-2} ≤ 2ε/(5e)` — automatic for a prime range starting above `1/ε` — the
diagonal costs `10·W·M + ε·M²`: the mean value theorem's own diagonal, and a height-free part that
is `o(M²)`.  The whole residue of the factorisation is therefore the **prime off-diagonal**. -/
theorem sum_integral_normSq_ramareCofactorPoly_le_budget {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) {W ε : ℝ} (hW : 1 ≤ W) (hε : 0 < ε)
    (hsq : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * (p : ℝ)) ≤ 2 * ε / (5 * Real.exp 1)) :
    ∑ p ∈ P, (∫ w in Set.Icc (-W) W,
        ‖logPoly (ramareCofactorCoeff P)
          {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} w‖ ^ (2 : ℕ))
      ≤ 10 * W * (M : ℝ) + ε * (M : ℝ) ^ (2 : ℕ) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  refine le_trans (sum_integral_normSq_ramareCofactorPoly_le hPprime M hW) ?_
  have hfirst : 5 * Real.pi / 2 * W * (M : ℝ) ≤ 10 * W * (M : ℝ) := by
    have hWM : (0 : ℝ) ≤ W * (M : ℝ) := by positivity
    nlinarith [hpi, hWM]
  have hsecond : 5 * Real.exp 1 / 2 * (M : ℝ) ^ (2 : ℕ)
      * (∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * (p : ℝ))) ≤ ε * (M : ℝ) ^ (2 : ℕ) := by
    have hc0 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (M : ℝ) ^ (2 : ℕ) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hsq hc0) (le_of_eq ?_)
    field_simp
  linarith

end RHTower.Sieve

end
