/-
The completability ladder of the central root tower reads the 2-adic digits of the central order.

Fix a symmetric nonvanishing unit `G` on the open critical strip and a central order `m`.  The
rung-`k` object of the central root ladder is the normal form `(s − 1/2)^{m/2^k} · G s`,
presented at the same unit: extracting `2^k`-th roots of the central factor divides the central
order, while root extraction of the unit itself is governed elsewhere by the equivariant anchor
mechanism and does not touch the fixed-point bit.  By the completion-parity dichotomy, the
rung-`k` object admits a continuous strip-nonvanishing completion exactly when `m / 2^k` is
even — which, given `2^k ∣ m`, says exactly `2^{k+1} ∣ m`.  The ladder of completability bits is
therefore the 2-adic divisibility chain of the central order: rung `k` completes iff the order
survives one more halving.  The entire ladder completes iff the central order is divisible by
every power of two, which for a finite order means `m = 0` — the carrier does not vanish at the
reflection's fixed point.  Total completability of the root ladder is thus equivalent to central
nonvanishing: the crease anchor carries the whole rung hierarchy as one 2-adic digit string.
-/
import GaloisForLFunctions.RHTower.CompletionParity

noncomputable section

namespace RHTower

/-- Given `2^k ∣ m`, evenness of the quotient `m / 2^k` is exactly one more dyadic divisibility:
`2^{k+1} ∣ m`. -/
theorem even_div_two_pow_iff {m k : ℕ} (hdvd : 2 ^ k ∣ m) :
    Even (m / 2 ^ k) ↔ 2 ^ (k + 1) ∣ m := by
  obtain ⟨q, rfl⟩ := hdvd
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [Nat.mul_div_cancel_left q hpos, even_iff_two_dvd, pow_succ]
  exact (mul_dvd_mul_iff_left hpos.ne').symm

/-- A natural number divisible by every power of two is zero: otherwise `2^m ∣ m` forces
`2^m ≤ m`, contradicting `m < 2^m`. -/
theorem eq_zero_of_forall_two_pow_dvd {m : ℕ} (h : ∀ k : ℕ, 2 ^ k ∣ m) : m = 0 := by
  by_contra hm
  have hle : 2 ^ m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (h m)
  have hlt : m < 2 ^ m := Nat.lt_two_pow_self
  omega

/-- **One rung of the completability ladder is one 2-adic digit.**  Given `2^k ∣ m`, the rung-`k`
central normal form `(s − 1/2)^{m/2^k} · G` admits a continuous strip-nonvanishing completion
exactly when `2^{k+1} ∣ m`: the completion-parity dichotomy reads evenness of `m / 2^k`, and
evenness of that quotient is the next dyadic divisibility of the central order. -/
theorem rung_completion_iff_next_dyadic {G : ℂ → ℂ}
    (hGne : ∀ s ∈ openStrip, G s ≠ 0) (hGsym : ∀ s ∈ openStrip, G (1 - s) = G s)
    {m k : ℕ} (hdvd : 2 ^ k ∣ m) :
    (∃ γ : ℂ → ℂ, ContinuousOn γ openStrip ∧ (∀ s ∈ openStrip, γ s ≠ 0) ∧
      ∀ s ∈ openStrip, γ (1 - s) * ((1 - s - 1/2) ^ (m / 2 ^ k) * G (1 - s))
        = γ s * ((s - 1/2) ^ (m / 2 ^ k) * G s)) ↔ 2 ^ (k + 1) ∣ m :=
  (completion_continuousOn_iff_even_center hGne hGsym (m / 2 ^ k)).trans
    (even_div_two_pow_iff hdvd)

/-- **Total completability of the central root ladder is central nonvanishing.**  Every rung of
the ladder admits a continuous completion exactly when the central order is zero: each completed
rung certifies one more dyadic divisibility of `m`, and a finite order divisible by every power
of two vanishes; conversely at `m = 0` every rung is the symmetric unit itself, completed by the
constant `1`.  The reflection's fixed point carries the entire rung hierarchy as the 2-adic
digit string of its order. -/
theorem completion_tower_iff_center_order_zero {G : ℂ → ℂ}
    (hGne : ∀ s ∈ openStrip, G s ≠ 0) (hGsym : ∀ s ∈ openStrip, G (1 - s) = G s) (m : ℕ) :
    (∀ k : ℕ, 2 ^ k ∣ m →
      ∃ γ : ℂ → ℂ, ContinuousOn γ openStrip ∧ (∀ s ∈ openStrip, γ s ≠ 0) ∧
        ∀ s ∈ openStrip, γ (1 - s) * ((1 - s - 1/2) ^ (m / 2 ^ k) * G (1 - s))
          = γ s * ((s - 1/2) ^ (m / 2 ^ k) * G s)) ↔ m = 0 := by
  constructor
  · intro hall
    refine eq_zero_of_forall_two_pow_dvd fun k => ?_
    induction k with
    | zero => exact one_dvd m
    | succ k ih =>
      exact (rung_completion_iff_next_dyadic hGne hGsym ih).mp (hall k ih)
  · rintro rfl k -
    exact (rung_completion_iff_next_dyadic hGne hGsym (dvd_zero _)).mpr (dvd_zero _)

end RHTower
