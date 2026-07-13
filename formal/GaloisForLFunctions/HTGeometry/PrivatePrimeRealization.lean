import GaloisForLFunctions.HTGeometry.PrivatePrimeConfinement

/-!
# A concrete sequence with eventual private-prime exposure

Given a strictly increasing sequence of primes `pₙ` and an arbitrary integer sequence `aₙ`,
the rational sequence `bₙ = aₙ + 1/pₙ` has eventual private-prime exposure: `pₙ` divides the
reduced denominator of `bₙ` (`padicNorm (pₙ) (bₙ) = pₙ > 1`) and of no other `bₘ`
(`padicNorm (pₙ) (bₘ) ≤ 1`).  Hence the private-denominator criterion applies and `bₙ` has
bounded-relation confinement (`shifted_inv_prime_bounded_relation_confinement`), for every
prescribed integer part `aₙ` — the realization and approximation clause of the
bounded-relation magnitude law made unconditional.
-/

open Finset

namespace GaloisForLFunctions

/-- The `q`-adic norm of `1/q` is `q` for a prime `q`. -/
theorem padicNorm_inv_self {q : ℕ} (hq : q.Prime) : padicNorm q ((q : ℚ)⁻¹) = (q : ℚ) := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [IsAbsoluteValue.abv_inv (padicNorm q), padicNorm.padicNorm_p hq.one_lt, inv_inv]

/-- The `q`-adic norm of `1/r` is `1` for distinct primes `q ≠ r`. -/
theorem padicNorm_inv_coprime {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hne : q ≠ r) :
    padicNorm q ((r : ℚ)⁻¹) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [IsAbsoluteValue.abv_inv (padicNorm q)]
  have hval : padicNorm q (r : ℚ) = 1 := by
    have hnotdvd : ¬ (q : ℤ) ∣ (r : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hr).mp h)
    have h1 : padicNorm q ((r : ℤ) : ℚ) ≤ 1 := padicNorm.of_int _
    have h2 : ¬ padicNorm q ((r : ℤ) : ℚ) < 1 :=
      fun h => hnotdvd ((padicNorm.int_lt_one_iff _).mp h)
    have := le_antisymm h1 (not_lt.mp h2)
    simpa using this
  rw [hval, inv_one]

/-- **Private-prime exposure of a shifted inverse-prime sequence.**  For a strictly increasing
prime sequence `pₙ` and any integer sequence `aₙ`, the sequence `bₙ = aₙ + 1/pₙ` has
bounded-relation confinement: for every height `D` there is a threshold `M` past which every
height-`≤ D` integer relation `∑ dₘ bₘ = 0` is supported below `M`. -/
theorem shifted_inv_prime_bounded_relation_confinement {p : ℕ → ℕ} (hp : ∀ n, (p n).Prime)
    (hmono : StrictMono p) (a : ℕ → ℤ) (D : ℕ) :
    ∃ M : ℕ, ∀ d : ℕ →₀ ℤ, (∀ n, |d n| ≤ (D : ℤ)) →
      (∑ m ∈ d.support, (d m : ℚ) * ((a m : ℚ) + (p m : ℚ)⁻¹) = 0) →
      ∀ n ∈ d.support, n < M := by
  have htend : Filter.Tendsto p Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => hmono.le_apply) Filter.tendsto_id
  have hbn : ∀ n, 1 < padicNorm (p n) ((a n : ℚ) + (p n : ℚ)⁻¹) := by
    intro n
    haveI : Fact (p n).Prime := ⟨hp n⟩
    have hA : padicNorm (p n) ((a n : ℚ)) ≤ 1 := padicNorm.of_int _
    have hInv : padicNorm (p n) ((p n : ℚ)⁻¹) = (p n : ℚ) := padicNorm_inv_self (hp n)
    have hlt : (1 : ℚ) < (p n : ℚ) := by exact_mod_cast (hp n).one_lt
    have hne : padicNorm (p n) ((a n : ℚ)) ≠ padicNorm (p n) ((p n : ℚ)⁻¹) := by
      rw [hInv]; intro h; rw [h] at hA; linarith
    rw [padicNorm.add_eq_max_of_ne hne, hInv, max_eq_right (le_trans hA (le_of_lt hlt))]
    exact hlt
  have hbm : ∀ n m, m ≠ n → padicNorm (p n) ((a m : ℚ) + (p m : ℚ)⁻¹) ≤ 1 := by
    intro n m hmn
    haveI : Fact (p n).Prime := ⟨hp n⟩
    have hA : padicNorm (p n) ((a m : ℚ)) ≤ 1 := padicNorm.of_int _
    have hpne : p n ≠ p m := fun h => hmn (hmono.injective h).symm
    have hInv : padicNorm (p n) ((p m : ℚ)⁻¹) = 1 := padicNorm_inv_coprime (hp n) (hp m) hpne
    calc padicNorm (p n) ((a m : ℚ) + (p m : ℚ)⁻¹)
        ≤ max (padicNorm (p n) ((a m : ℚ))) (padicNorm (p n) ((p m : ℚ)⁻¹)) :=
          padicNorm.nonarchimedean
      _ ≤ 1 := by rw [hInv]; exact max_le hA le_rfl
  exact private_prime_bounded_relation_confinement hp htend hbn hbm D

end GaloisForLFunctions
