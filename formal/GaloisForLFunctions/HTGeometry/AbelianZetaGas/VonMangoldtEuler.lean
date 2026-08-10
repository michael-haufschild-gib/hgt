import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModeMean

/-!
# The von Mangoldt Dirichlet series in Euler form

Summing the von Mangoldt coefficients over the prime powers rather than over the integers turns the
Dirichlet series into a sum over primes of local factors `log p · ∑_{a≥1} p^{−aσ}`.  Together with
`tsum_modeMean_sub_shift_prime` this identifies the local residue of the mode-mean ladder with the
local von Mangoldt factor, prime by prime.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

theorem vonMangoldt_primePow (p : Nat.Primes) (a : ℕ) :
    Λ ((p : ℕ) ^ (a + 1)) = Real.log ((p : ℕ) : ℝ) := by
  rw [vonMangoldt_apply_pow (Nat.succ_ne_zero a), vonMangoldt_apply_prime p.2]

theorem rpow_primePow (p : Nat.Primes) (a : ℕ) (σ : ℝ) :
    ((((p : ℕ) ^ (a + 1) : ℕ) : ℝ)) ^ (-σ) = ((p : ℕ) : ℝ) ^ (-(((a : ℝ) + 1) * σ)) := by
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Nat.cast_pow, ← Real.rpow_natCast (((p : ℕ) : ℝ)) (a + 1), ← Real.rpow_mul hp]
  congr 1
  push_cast
  ring

theorem support_vonMangoldt_rpow_subset (σ : ℝ) :
    (Function.support fun n : ℕ => Λ n * (n : ℝ) ^ (-σ)) ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hcon
  apply hn
  have hz : Λ n = 0 := vonMangoldt_eq_zero_iff.mpr hcon
  show Λ n * (n : ℝ) ^ (-σ) = 0
  rw [hz, zero_mul]

/-- **The Euler form of the von Mangoldt Dirichlet series.** -/
theorem tsum_vonMangoldt_eq_tsum_primes {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ))
      = ∑' p : Nat.Primes,
        Real.log ((p : ℕ) : ℝ) * ∑' a : ℕ, ((p : ℕ) : ℝ) ^ (-(((a : ℝ) + 1) * σ)) := by
  classical
  have hsum := summable_vonMangoldt_rpow hσ
  -- restrict to the prime powers
  have hrestrict : (∑' n : {n : ℕ // IsPrimePow n}, Λ (n : ℕ) * ((n : ℕ) : ℝ) ^ (-σ))
      = ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) :=
    tsum_subtype_eq_of_support_subset (support_vonMangoldt_rpow_subset σ)
  -- reindex the prime powers by (prime, exponent)
  have hterm : ∀ x : Nat.Primes × ℕ,
      Λ ((Nat.Primes.prodNatEquiv x : ℕ)) * (((Nat.Primes.prodNatEquiv x : ℕ)) : ℝ) ^ (-σ)
        = Real.log ((x.1 : ℕ) : ℝ) * ((x.1 : ℕ) : ℝ) ^ (-(((x.2 : ℝ) + 1) * σ)) := by
    rintro ⟨p, a⟩
    have hval : ((Nat.Primes.prodNatEquiv (p, a) : {n : ℕ // IsPrimePow n}) : ℕ)
        = (p : ℕ) ^ (a + 1) := rfl
    rw [hval, vonMangoldt_primePow p a, rpow_primePow p a σ]
  have hreindex : (∑' x : Nat.Primes × ℕ,
        Real.log ((x.1 : ℕ) : ℝ) * ((x.1 : ℕ) : ℝ) ^ (-(((x.2 : ℝ) + 1) * σ)))
      = ∑' n : {n : ℕ // IsPrimePow n}, Λ (n : ℕ) * ((n : ℕ) : ℝ) ^ (-σ) := by
    rw [← Nat.Primes.prodNatEquiv.tsum_eq
      (fun n : {n : ℕ // IsPrimePow n} => Λ (n : ℕ) * ((n : ℕ) : ℝ) ^ (-σ))]
    exact tsum_congr fun x => (hterm x).symm
  -- summability of the reindexed family
  have hsummableProd : Summable fun x : Nat.Primes × ℕ =>
      Real.log ((x.1 : ℕ) : ℝ) * ((x.1 : ℕ) : ℝ) ^ (-(((x.2 : ℝ) + 1) * σ)) := by
    have hsub : Summable fun n : {n : ℕ // IsPrimePow n} =>
        Λ (n : ℕ) * ((n : ℕ) : ℝ) ^ (-σ) := hsum.subtype _
    have hequiv := (Nat.Primes.prodNatEquiv.summable_iff
      (f := fun n : {n : ℕ // IsPrimePow n} => Λ (n : ℕ) * ((n : ℕ) : ℝ) ^ (-σ))).mpr hsub
    exact hequiv.congr fun x => hterm x
  rw [← hrestrict, ← hreindex, hsummableProd.tsum_prod]
  refine tsum_congr fun p => ?_
  rw [← tsum_mul_left]

/-! ## The mode-mean residue is the von Mangoldt mass -/

/-- **(GAS.12), arithmetic half.**  Summing the per-prime residues of the mode-mean ladder against
`log p` gives the von Mangoldt Dirichlet sum. -/
theorem tsum_primes_modeMean_residue (σ : EulerSigma) :
    (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ)
        * ((∑' j : ℕ, modeMean (eqgQ σ (p : ℕ)) j)
          - ∑' j : ℕ, modeMean (eqgQ σ (p : ℕ)) (j + 1)))
      = ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ.val) := by
  rw [tsum_vonMangoldt_eq_tsum_primes σ.one_lt]
  refine tsum_congr fun p => ?_
  rw [tsum_modeMean_sub_shift_prime σ p]

/-- **(GAS.12), arithmetic half in zeta form.**  That same sum is `−ζ′(σ)/ζ(σ)`. -/
theorem ofReal_tsum_primes_modeMean_residue (σ : EulerSigma) :
    ((∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ)
        * ((∑' j : ℕ, modeMean (eqgQ σ (p : ℕ)) j)
          - ∑' j : ℕ, modeMean (eqgQ σ (p : ℕ)) (j + 1)) : ℝ) : ℂ)
      = -deriv riemannZeta ((σ.val : ℝ) : ℂ) / riemannZeta ((σ.val : ℝ) : ℂ) := by
  rw [tsum_primes_modeMean_residue σ]
  exact ofReal_tsum_vonMangoldt_eq σ.one_lt

/-- **(GAS.12), residue form.**  The depth-one mode means, weighted by `log p`, sum to the von
Mangoldt Dirichlet mass. -/
theorem tsum_primes_modeMean_zero (σ : EulerSigma) :
    (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * modeMean (eqgQ σ (p : ℕ)) 0)
      = ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ.val) := by
  rw [← tsum_primes_modeMean_residue σ]
  refine tsum_congr fun p => ?_
  have hq0 : (0 : ℝ) ≤ eqgQ σ (p : ℕ) := (eqgQ_pos σ p.2.pos).le
  have hq1 : eqgQ σ (p : ℕ) < 1 := eqgQ_lt_one σ p.2.two_le
  rw [tsum_modeMean_sub_shift hq0 hq1]

/-- **(GAS.12), residue form in zeta terms.** -/
theorem ofReal_tsum_primes_modeMean_zero (σ : EulerSigma) :
    ((∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * modeMean (eqgQ σ (p : ℕ)) 0 : ℝ) : ℂ)
      = -deriv riemannZeta ((σ.val : ℝ) : ℂ) / riemannZeta ((σ.val : ℝ) : ℂ) := by
  rw [tsum_primes_modeMean_zero σ]
  exact ofReal_tsum_vonMangoldt_eq σ.one_lt

/-! ## Summability of the log-weighted prime ladder bounds -/

theorem summable_primes_vonMangoldt (σ : EulerSigma) :
    Summable fun p : Nat.Primes => Λ ((p : ℕ)) * (((p : ℕ) : ℝ)) ^ (-σ.val) :=
  (summable_vonMangoldt_rpow σ.one_lt).comp_injective Nat.Primes.coe_nat_injective

theorem div_one_sub_sq_le (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    q / (1 - q) ^ 2 ≤ 4 * q := by
  have hden : (1 : ℝ) / 2 ≤ 1 - q := by linarith
  have hsq : (1 : ℝ) / 4 ≤ (1 - q) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < (1 - q) ^ 2 := by nlinarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- **The log-weighted ladder bound is summable over the primes.**  This is the finiteness input the
Kullback–Leibler evaluation of Theorem 8.1 needs. -/
theorem summable_primes_log_mul_ladderBound (σ : EulerSigma) :
    Summable fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) * (eqgQ σ (p : ℕ) / (1 - eqgQ σ (p : ℕ)) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    ((summable_primes_vonMangoldt σ).mul_left 4)
  · have hq0 : (0 : ℝ) ≤ eqgQ σ (p : ℕ) := (eqgQ_pos σ p.2.pos).le
    have hq1 : eqgQ σ (p : ℕ) ≤ 1 / 2 := eqgQ_le_half σ p.2.two_le
    have hden : (0 : ℝ) < (1 - eqgQ σ (p : ℕ)) ^ 2 := by nlinarith
    have hlog : (0 : ℝ) ≤ Real.log ((p : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
    positivity
  · have hq0 : (0 : ℝ) ≤ eqgQ σ (p : ℕ) := (eqgQ_pos σ p.2.pos).le
    have hq1 : eqgQ σ (p : ℕ) ≤ 1 / 2 := eqgQ_le_half σ p.2.two_le
    have hlog : (0 : ℝ) ≤ Real.log ((p : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
    have hbound := div_one_sub_sq_le (eqgQ σ (p : ℕ)) hq0 hq1
    have hlam : Λ ((p : ℕ)) * (((p : ℕ) : ℝ)) ^ (-σ.val)
        = Real.log ((p : ℕ) : ℝ) * eqgQ σ (p : ℕ) := by
      rw [vonMangoldt_apply_prime p.2, eqgQ]
    rw [hlam]
    calc Real.log ((p : ℕ) : ℝ) * (eqgQ σ (p : ℕ) / (1 - eqgQ σ (p : ℕ)) ^ 2)
        ≤ Real.log ((p : ℕ) : ℝ) * (4 * eqgQ σ (p : ℕ)) :=
          mul_le_mul_of_nonneg_left hbound hlog
      _ = 4 * (Real.log ((p : ℕ) : ℝ) * eqgQ σ (p : ℕ)) := by ring

end

end GaloisForLFunctions.HTGeometry
