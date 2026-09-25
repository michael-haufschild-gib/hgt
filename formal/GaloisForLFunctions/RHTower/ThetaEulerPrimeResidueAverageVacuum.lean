import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime-residue forward averaging has only the vacuum in `ℓ²`

For every prime `p`, a zero-residue coefficient equal to the mean
of its `p`-cell block obeys a forward averaging law. If all such
laws hold and the coefficients are square summable, every index
above `1` vanishes. This is the analytic core of the all-prime
residue-channel span theorem in the accompanying paper card.
The identification with adjoints of the residue operators is not
asserted in this file.
-/

namespace RHTower

open Filter

private theorem forward_rigidity (f : ℕ → ℂ)
    (hfinite : ∀ ε : ℝ, 0 < ε → {n : ℕ | ε ≤ ‖f n‖}.Finite)
    (hforward : ∀ n : ℕ, 2 ≤ n → f n ≠ 0 →
      ∃ k : ℕ, n < k ∧ ‖f n‖ ≤ ‖f k‖) :
    ∀ n : ℕ, 2 ≤ n → f n = 0 := by
  intro n hn
  by_contra hne
  let ε : ℝ := ‖f n‖
  have hε : 0 < ε := norm_pos_iff.mpr hne
  let s : Set ℕ := {m | 2 ≤ m ∧ ε ≤ ‖f m‖}
  have hsfin : s.Finite :=
    (hfinite ε hε).subset (by intro m hm; exact hm.2)
  have hsne : s.Nonempty := ⟨n, hn, le_refl ε⟩
  obtain ⟨m, hm⟩ := hsfin.exists_maximal hsne
  have hmne : f m ≠ 0 := by
    intro h
    have := hm.prop.2
    simp [h, ε] at this
    exact hne this
  obtain ⟨k, hmk, hmag⟩ := hforward m hm.prop.1 hmne
  have hk : k ∈ s := ⟨le_trans hm.prop.1 (le_of_lt hmk), le_trans hm.prop.2 hmag⟩
  exact (hm.not_prop_of_gt hmk) hk

private theorem forward_of_average (f : ℕ → ℂ) (m p : ℕ) (hp : 2 ≤ p)
    (havg : ((p - 1 : ℕ) : ℂ) * f m =
      ∑ r ∈ Finset.Ico 1 p, f (m + r)) :
    ∃ k : ℕ, m < k ∧ ‖f m‖ ≤ ‖f k‖ := by
  by_contra h
  push Not at h
  have hsne : (Finset.Ico 1 p).Nonempty := by
    refine ⟨1, Finset.mem_Ico.mpr ?_⟩
    omega
  have hr : ∀ r ∈ Finset.Ico 1 p, ‖f (m + r)‖ < ‖f m‖ := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
    exact h (m + r) (by omega)
  have hsum := Finset.sum_lt_sum_of_nonempty hsne hr
  have htri : ‖∑ r ∈ Finset.Ico 1 p, f (m + r)‖ ≤
      ∑ r ∈ Finset.Ico 1 p, ‖f (m + r)‖ := norm_sum_le _ _
  have hnorm : ‖((p - 1 : ℕ) : ℂ) * f m‖ =
      ((p - 1 : ℕ) : ℝ) * ‖f m‖ := by simp
  have hconst : (∑ r ∈ Finset.Ico 1 p, ‖f m‖) =
      ((p - 1 : ℕ) : ℝ) * ‖f m‖ := by
    simp [Nat.card_Ico]
  rw [← havg, hnorm] at htri
  rw [hconst] at hsum
  exact (not_lt_of_ge htri) hsum

private theorem finite_superlevel_of_summable_norm_sq
    (f : ℕ → ℂ) (hs : Summable (fun n : ℕ => ‖f n‖ ^ 2))
    (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | ε ≤ ‖f n‖}.Finite := by
  have hsq : {n : ℕ | ε ^ 2 ≤ ‖f n‖ ^ 2}.Finite := by
    have hev := hs.tendsto_cofinite_zero.eventually_lt_const (sq_pos_of_pos hε)
    simpa only [not_lt] using Filter.eventually_cofinite.mp hev
  apply hsq.subset
  intro n hn
  exact pow_le_pow_left₀ (le_of_lt hε) hn _

/-- A square-summable forward-averaging sequence vanishes beyond the unit. -/
theorem highpass_forward_average_rigidity
    (f : ℕ → ℂ) (hs : Summable (fun n : ℕ => ‖f n‖ ^ 2))
    (havg : ∀ m : ℕ, 2 ≤ m → ∃ p : ℕ, 2 ≤ p ∧
      ((p - 1 : ℕ) : ℂ) * f m =
        ∑ r ∈ Finset.Ico 1 p, f (m + r)) :
    ∀ m : ℕ, 2 ≤ m → f m = 0 := by
  apply forward_rigidity f (finite_superlevel_of_summable_norm_sq f hs)
  intro m hm _
  obtain ⟨p, hp, hmean⟩ := havg m hm
  exact forward_of_average f m p hp hmean

/-- Prime-block averaging at every positive cofactor leaves no `ℓ²` tail. -/
theorem highpass_prime_average_vacuum
    (f : ℕ → ℂ) (hs : Summable (fun n : ℕ => ‖f n‖ ^ 2))
    (hprime : ∀ p n : ℕ, p.Prime → 0 < n →
      ((p - 1 : ℕ) : ℂ) * f (p * n) =
        ∑ r ∈ Finset.Ico 1 p, f (p * n + r)) :
    ∀ m : ℕ, 2 ≤ m → f m = 0 := by
  apply highpass_forward_average_rigidity f hs
  intro m hm
  have hm1 : m ≠ 1 := by omega
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hm1
  obtain ⟨n, hn⟩ := hdvd
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    simp at hn
    omega
  refine ⟨p, hp.two_le, ?_⟩
  simpa [hn] using hprime p n hp hnpos

/-- With the unused zero coordinate removed, only the unit coefficient survives. -/
theorem highpass_prime_average_supported_at_one
    (f : ℕ → ℂ) (hf0 : f 0 = 0)
    (hs : Summable (fun n : ℕ => ‖f n‖ ^ 2))
    (hprime : ∀ p n : ℕ, p.Prime → 0 < n →
      ((p - 1 : ℕ) : ℂ) * f (p * n) =
        ∑ r ∈ Finset.Ico 1 p, f (p * n + r)) :
    ∀ m : ℕ, m ≠ 1 → f m = 0 := by
  intro m hm
  by_cases h0 : m = 0
  · simpa [h0] using hf0
  · exact highpass_prime_average_vacuum f hs hprime m (by omega)

end RHTower
