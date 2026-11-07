import GaloisForLFunctions.CountingHolography.TheBornRuleOfABlackHole

/-!
# Hecke supplies conservation, not the law

On a black hole `(q, t)` a place of degree `n` acts on every resonant state by `Xⁿ + Yⁿ = V_n`, the trace
of `πⁿ` (`ArithmeticScatteringHolography.hecke_rigidity`, `towerTrace_roots`). In the ring of probes
`πⁿ = a_n π + b_n`, and the two channel counts of level `n` are the counts of the probes `1 ∓ πⁿ`:

  `#ℤ[π]/(1 - πⁿ) = qⁿ + 1 - V_n`,  `#ℤ[π]/(1 + πⁿ) = qⁿ + 1 + V_n`  (`kreinSquare_one_add_pow`).

* **Every Hecke instance of the count law holds on every black hole**, true or fake
  (`conservation_at_every_level`): for `|t| ≤ q`,

    `K(1 + πⁿ) + K(1 - πⁿ) = 2 K(1) + 2 K(πⁿ)`,

  the conservation of channels at the place of degree `n`. It is the parallelogram law at the pair
  `(1, πⁿ)`, and it is all that the eigenvalues `V_n` can say about counts.
* **The fake keeps every one of them and breaks the law** (`hecke_conservation_without_law`): an
  overdamped black hole with three cusps and `q ≥ 9` has positive counts and conservation at every
  level, a count covariant under the delay, and violates the law at the probe `2 - π`.

So Hecke at a second place constrains a count exactly as it constrains flux: it supplies conservation
at the probes `1 ± πⁿ`, which every black hole obeys, and nothing about the probes with multiplicity,
where the law fails on the fakes.
-/

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

/-- The norm of `πⁿ` as a probe `b_n - (-a_n) π`. -/
theorem kreinSquare_pow (q t : ℤ) (n : ℕ) : kreinSquare q t (-powA q t n) (powB q t n) = q ^ n := by
  have h := norm_pow q t n
  unfold kreinSquare
  linear_combination h

/-- **The second channel count of level `n`**: the norm of `1 + πⁿ`. -/
theorem kreinSquare_one_add_pow (q t : ℤ) (n : ℕ) :
    kreinSquare q t (-powA q t n) (1 + powB q t n) = q ^ n + 1 + powV q t n := by
  have h := norm_pow q t n
  unfold kreinSquare powV
  linear_combination h

/-- The trace of the level `n` is bounded by the channels: `|V_n| < qⁿ + 1` for `|t| ≤ q`. -/
theorem abs_powV_lt {q t : ℤ} (hq : 2 ≤ q) (ht : |t| ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    |powV q t n| < q ^ n + 1 := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have ht' : |(t : ℝ)| ≤ q := by exact_mod_cast ht
  have h := abs_towerTrace_lt hq' ht' (by omega : 0 < n)
  rw [← powV_cast] at h
  have : ((|powV q t n| : ℤ) : ℝ) < ((q ^ n + 1 : ℤ) : ℝ) := by push_cast; exact h
  exact_mod_cast this

/-- **Conservation of channels at every level, on every black hole.** -/
theorem conservation_at_every_level {q t : ℤ} (hq : 2 ≤ q) (ht : |t| ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    (probeCount q t (-powA q t n) (1 + powB q t n) : ℤ) + probeCount q t (powA q t n) (1 - powB q t n) =
      2 * probeCount q t 0 1 + 2 * probeCount q t (-powA q t n) (powB q t n) := by
  have hV := abs_lt.mp (abs_powV_lt hq ht hn)
  have hpos : 0 ≤ q ^ n := pow_nonneg (by omega) n
  simp only [probeCount, kreinSquare_one_add_pow, kreinSquare_tower, kreinSquare_pow]
  rw [Int.natAbs_of_nonneg (by linarith), Int.natAbs_of_nonneg (by linarith), Int.natAbs_of_nonneg hpos]
  simp [kreinSquare]
  ring

/-- **Hecke conservation without the law.** An overdamped black hole with three cusps, `t = q - 2`,
`q ≥ 9`, has positive channel counts and conservation at every level and a delay-covariant count, and
its count violates the law. -/
theorem hecke_conservation_without_law {q : ℤ} (hq : 9 ≤ q) :
    4 * q < (q - 2) ^ 2 ∧
      (∀ n, 1 ≤ n → 0 < q ^ n + 1 - powV q (q - 2) n ∧ 0 < q ^ n + 1 + powV q (q - 2) n) ∧
      (∀ n, 1 ≤ n → (probeCount q (q - 2) (-powA q (q - 2) n) (1 + powB q (q - 2) n) : ℤ) +
        probeCount q (q - 2) (powA q (q - 2) n) (1 - powB q (q - 2) n) =
          2 * probeCount q (q - 2) 0 1 + 2 * probeCount q (q - 2) (-powA q (q - 2) n) (powB q (q - 2) n)) ∧
      IsCovariant q (q - 2) (probeCount q (q - 2)) ∧ ¬ CountLaw (probeCount q (q - 2)) := by
  have ht : |q - 2| ≤ q := by rw [abs_le]; constructor <;> omega
  refine ⟨by nlinarith, fun n hn => ?_, fun n hn => conservation_at_every_level (by omega) ht hn,
    probeCount_covariant (by omega) _, fun hlaw => ?_⟩
  · have := abs_lt.mp (abs_powV_lt (by omega) ht hn)
    constructor <;> linarith
  · have hf := fake_violates_second_probe hq
    simp only at hf
    have h := hlaw 1 1 0 1
    norm_num at h
    exact hf.2 h

end GaloisForLFunctions.CountingHolography

end
