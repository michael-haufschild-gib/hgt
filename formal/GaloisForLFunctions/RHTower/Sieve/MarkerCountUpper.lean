import GaloisForLFunctions.RHTower.Sieve.MertensWindowSharp

/-!
# The marker count from above

Each cell of the block loses one member to the floor of `H/p`, so the block bound carries a term
`−#P`.  Bounding `#P` by the length of the marker range wastes a factor of `log`, and that waste is
of the same order as the main term.  The markers are primes, so the sieve bounds them:

`#(bigPrimeSet M b) ≤ 2(b − M)/log Y + Y²·exp(4C)·(log M)⁴`.

With the marker count entering the criterion through this bound instead of `b`, the floor loss is
smaller than the main term by a factor of `log M`.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- A window of primes is the primes of the window. -/
theorem bigPrimeSet_eq_filter_Ioc (M b : ℕ) :
    bigPrimeSet M b = {p ∈ Finset.Ioc M b | p.Prime ∧ M < p} := by
  classical
  ext p
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨by omega, h2⟩, hp, by omega⟩
  · rintro ⟨⟨h1, h2⟩, hp, _⟩
    exact ⟨⟨by omega, h2⟩, hp⟩

/-- **The marker count from above.** -/
theorem card_bigPrimeSet_le_explicit {M b Y : ℕ} (hMb : M ≤ b) (hY : 1 ≤ Y) (hYM : Y ≤ M)
    (hM : 2 ≤ M) (hlog : 0 < Real.log Y) :
    (((bigPrimeSet M b).card : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - M) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log M) ^ (4 : ℝ)) := by
  rw [bigPrimeSet_eq_filter_Ioc M b]
  exact card_primes_Ioc_le_explicit M b M Y hMb hY hYM hM hlog

/-- **The matching criterion with the marker count as a parameter.** -/
theorem exists_hall_injection_recip_of_card {X H M Q z Y : ℕ} {S B : ℝ}
    (hM : 3 ≤ M) (hXH : X + H ≤ M * M)
    (hS : S ≤ ∑ p ∈ bigPrimeSet M (Q * M), 1 / (p : ℝ))
    (hB : (((bigPrimeSet M (Q * M)).card : ℕ) : ℝ) ≤ B)
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (H : ℝ) * S - B) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets (bigPrimeSet M (Q * M)) (windowCell X H))
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hppos : ∀ p ∈ bigPrimeSet M (Q * M), 0 < p := fun p hp =>
    (prime_of_mem_bigPrimeSet hp).pos
  refine exists_hall_injection_sum (X := X) (H := H) (bigPrimeSet M (Q * M)) (windowCell X H) _
    (fun p hp => prime_of_mem_bigPrimeSet hp)
    (fun p hp a ha => pos_of_mem_windowCell (hppos p hp) ha) ?_ ?_
    (fun p hp a ha => (mem_windowCell_iff (hppos p hp)).1 ha) ?_
  · intro p hp a ha r hr
    have hprod := ((mem_windowCell_iff (hppos p hp)).1 ha).2
    have hMp : M < p := lt_of_mem_bigPrimeSet hp
    have hMr : M < r := lt_of_mem_bigPrimeSet hr
    have haM : a ≤ M := by
      by_contra hcon
      have h1 : M + 1 ≤ a := by omega
      have h2 : M + 1 ≤ p := by omega
      have h3 : (M + 1) * (M + 1) ≤ a * p := Nat.mul_le_mul h1 h2
      have h4 : a * p ≤ M * M := le_trans hprod hXH
      nlinarith
    omega
  · have hlen : ((X + H : ℕ) : ℝ) - (X : ℝ) = (H : ℝ) := by push_cast; ring
    have hbt := card_primes_Ioc_le_explicit X (X + H) z Y (Nat.le_add_right X H) hY hYz hz hlog
    rw [hlen] at hbt
    refine le_trans hbt (le_trans hnum ?_)
    refine le_trans ?_ (sum_card_windowCell_ge (X := X) (H := H) (bigPrimeSet M (Q * M)))
    have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have hmul := mul_le_mul_of_nonneg_left hS hHnn
    linarith
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    exact hn.1

/-- **The matching criterion with every ingredient supplied.**  The reciprocal sum comes from the
sharp form of Mertens' second theorem and the marker count from the sieve; the sieve parameter `W`
for the marker count is independent of the parameter `Y` for the sources. -/
theorem exists_hall_injection_full {X H M Q z Y W : ℕ}
    (hM : 3 ≤ M) (hQ : 1 ≤ Q) (hXH : X + H ≤ M * M)
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hW : 1 ≤ W) (hWM : W ≤ M) (hlogW : 0 < Real.log W)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (H : ℝ) * (logLog ((Q * M : ℕ)) - logLog M
            - ((2 * mertensFirstConst + 1 / 2) / Real.log ((Q * M : ℕ))
              + (2 * mertensFirstConst + 1 / 2) / Real.log M))
          - (2 * (((Q * M : ℕ) : ℝ) - M) / Real.log W
              + ((W * W : ℕ) : ℝ)
                * (Real.exp (4 * mertensSecondUpperConst) * (Real.log M) ^ (4 : ℝ)))) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets (bigPrimeSet M (Q * M)) (windowCell X H))
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  have hMQM : M ≤ Q * M := Nat.le_mul_of_pos_left M (by omega)
  exact exists_hall_injection_recip_of_card hM hXH
    (sum_inv_bigPrimeSet_ge_sharp (by omega) hMQM)
    (card_bigPrimeSet_le_explicit hMQM hW hWM (by omega) hlogW)
    hY hYz hz hlog hnum

end RHTower.Sieve
