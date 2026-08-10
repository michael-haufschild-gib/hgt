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

end

end GaloisForLFunctions.HTGeometry
