import GaloisForLFunctions.RHTower.Sieve.TwistedDiagonalReindex

/-!
# Twisted diagonal reindexing for arbitrary positive indices

The primitive diagonal theorem assumes coprime twist indices.  Every mollifier pair is reduced to
that case by cancelling `gcd h k`; the resulting diagonal is one scale sum along the reduced ray.
-/

open Finset

noncomputable section

namespace RHTower.Sieve

/-- Cancelling the common gcd does not change the twisted diagonal equation. -/
theorem twisted_diagonal_eq_reduced_iff
    {m n h k : ℕ} (hk : 1 ≤ k) :
    n * k = m * h ↔
      n * (k / Nat.gcd h k) = m * (h / Nat.gcd h k) := by
  let g := Nat.gcd h k
  have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hg : 0 < g := Nat.gcd_pos_of_pos_right h hk0
  have hgk : g * (k / g) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_right h k)
  have hgh : g * (h / g) = h := Nat.mul_div_cancel' (Nat.gcd_dvd_left h k)
  change n * k = m * h ↔ n * (k / g) = m * (h / g)
  constructor
  · intro heq
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * (n * (k / g)) = n * (g * (k / g)) := by ac_rfl
      _ = n * k := by rw [hgk]
      _ = m * h := heq
      _ = m * (g * (h / g)) := by rw [hgh]
      _ = g * (m * (h / g)) := by ac_rfl
  · intro heq
    calc
      n * k = n * (g * (k / g)) := by rw [hgk]
      _ = g * (n * (k / g)) := by ac_rfl
      _ = g * (m * (h / g)) := by rw [heq]
      _ = m * (g * (h / g)) := by ac_rfl
      _ = m * h := by rw [hgh]

/-- The diagonal for arbitrary positive `h,k` is the single scale sum along
their reduced coprime direction. -/
theorem twisted_diagonal_reindex_gcd
    {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M)
    (s : Finset ℕ) {h k : ℕ} (hk : 1 ≤ k)
    (D : Finset ℕ)
    (hD : ∀ d : ℕ, d ∈ D ↔
      ((k / Nat.gcd h k) * d ∈ s ∧ (h / Nat.gcd h k) * d ∈ s)) :
    ∑ m ∈ s, ∑ n ∈ s.filter (fun n => n * k = m * h), f m n =
      ∑ d ∈ D,
        f ((k / Nat.gcd h k) * d) ((h / Nat.gcd h k) * d) := by
  classical
  let g := Nat.gcd h k
  have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hg : 0 < g := Nat.gcd_pos_of_pos_right h hk0
  have hcop : Nat.Coprime (h / g) (k / g) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hkred : 1 ≤ k / g := by
    apply Nat.one_le_div_iff (by omega) |>.2
    exact Nat.gcd_le_right h (by omega)
  have hfilter : ∀ m : ℕ,
      s.filter (fun n => n * k = m * h) =
        s.filter (fun n => n * (k / g) = m * (h / g)) := by
    intro m
    apply Finset.filter_congr
    intro n hn
    exact twisted_diagonal_eq_reduced_iff hk
  simp_rw [hfilter]
  exact twisted_diagonal_reindex f s hkred hcop D hD

end RHTower.Sieve
