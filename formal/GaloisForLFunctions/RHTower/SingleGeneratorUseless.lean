import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete
import GaloisForLFunctions.RHTower.BaezDuartePairingSeries
import GaloisForLFunctions.RHTower.BaezDuarteLeastSquares

/-!
# A single generator is quantitatively useless for large modulus

The closed forms of `QuarterGramEntry` and `HalfQuarterGram` are exact but only reach `m ∈ {1,2,4}`.  The
asymptotic question needs no closed form, and it has a clean answer: **a single Báez-Duarte generator becomes
useless as its modulus grows.**

The Gram diagonal is bounded below by its first `m − 1` terms, where `(n mod m) = n` and the summand is
`n/(m²(n+1)) ≥ 1/(2m²)`:

**`bdGram_self_lower` — `bdGram (1/m) (1/m) ≥ (m − 1)/(2m²)`.**

The pairing is exactly `(log m)/m` (`hasSum_pairing_discrete`), so the optimal single-generator gain is

`pairing²/gram ≤ ((log m)/m)² · 2m²/(m−1) = 2(log m)²/(m−1)`,

which tends to `0`.  Hence

**`bdDist_single_ge` — `d² ≥ 1 − 2(log m)²/(m − 1)` for the one-generator family `{1/m}`.**

So no single modulus, however large, gives a distance bounded away from `1` by more than `O((log m)²/m)`, and
the `m = 2` and `m = 4` bounds of the previous cards are not merely convenient small cases — the small moduli
are where the only appreciable single-generator gain lives.  Any route to `d_N → 0` must therefore be
*collective*: it needs the joint effect of many moduli, not a good choice of one.
-/

open Finset

noncomputable section

namespace RHTower

/-- **A lower bound on the Gram diagonal**, from the first `m − 1` terms of its series. -/
theorem bdGram_self_lower {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ) - 1) / (2 * (m : ℝ) ^ 2) ≤ bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hgram := hasSum_bdGram_discrete (m₁ := m) (m₂ := m) hm hm
  have hnonneg : ∀ n : ℕ, 0 ≤ (((n + 1) % m : ℕ) : ℝ) * (((n + 1) % m : ℕ) : ℝ)
      / ((m : ℝ) * (m : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have h1 : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) < ((n : ℝ) + 2) := by positivity
    positivity
  have hpartial := sum_le_hasSum (Finset.range (m - 1)) (fun i _ => hnonneg i) hgram
  refine le_trans ?_ hpartial
  have hterm : ∀ n ∈ Finset.range (m - 1),
      1 / (2 * (m : ℝ) ^ 2) ≤ (((n + 1) % m : ℕ) : ℝ) * (((n + 1) % m : ℕ) : ℝ)
        / ((m : ℝ) * (m : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hlt : n + 1 < m := by omega
    have hmod : (n + 1) % m = n + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod]
    have h1 : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) < ((n : ℝ) + 2) := by positivity
    have hc : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hstep : ((n : ℝ) + 2) ≤ 2 * ((n : ℝ) + 1) := by linarith
    have hmul : ((m : ℝ) * (m : ℝ) * ((n : ℝ) + 1)) * ((n : ℝ) + 2)
        ≤ ((m : ℝ) * (m : ℝ) * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    nlinarith [hmul]
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcard : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  rw [hcard]
  have hid : ((m : ℝ) - 1) * (1 / (2 * (m : ℝ) ^ 2)) = ((m : ℝ) - 1) / (2 * (m : ℝ) ^ 2) := by
    ring
  rw [hid]

/-- **The optimal single-generator gain is `O((log m)²/m)`.** -/
theorem bdDist_single_ge {m : ℕ} (hm : 2 ≤ m) :
    1 - 2 * Real.log (m : ℝ) ^ 2 / ((m : ℝ) - 1)
      ≤ bdDist (fun _ : Fin 1 => 1 / (m : ℝ)) ^ 2 := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm1R : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hglow := bdGram_self_lower hm1
  have hgpos : 0 < bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) := by
    refine lt_of_lt_of_le ?_ hglow
    have : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    positivity
  -- the exact single-generator value
  have hθ : ∀ _i : Fin 1, 0 < (1 / (m : ℝ)) ∧ (1 / (m : ℝ)) ≤ 1 := by
    intro _
    constructor
    · positivity
    · rw [div_le_one hm0]
      linarith
  have hlog : Real.log (1 / (m : ℝ)) = -Real.log (m : ℝ) := by
    rw [one_div, Real.log_inv]
  have hpair : (1 / (m : ℝ)) * Real.log (1 / (m : ℝ)) = -(Real.log (m : ℝ) / (m : ℝ)) := by
    rw [hlog]
    field_simp
  set g : ℝ := bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) with hg
  set L : ℝ := Real.log (m : ℝ) with hL
  have hc : ∀ i : Fin 1, ∑ j : Fin 1, bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) * (L / ((m : ℝ) * g))
      = -((1 / (m : ℝ)) * Real.log (1 / (m : ℝ))) := by
    intro i
    rw [Fin.sum_univ_one, hpair, ← hg]
    field_simp
  have hval := bdDist_sq_eq_of_realNormalEquations (fun _ : Fin 1 => 1 / (m : ℝ)) hθ
    (fun _ : Fin 1 => L / ((m : ℝ) * g)) (by
      intro i
      simpa using hc i)
  rw [hval]
  simp only [Fin.sum_univ_one]
  rw [hpair]
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact Real.log_nonneg (by linarith)
  have hkey : L ^ 2 / ((m : ℝ) * ((m : ℝ) * g)) ≤ 2 * L ^ 2 / ((m : ℝ) - 1) := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    have hglow' : ((m : ℝ) - 1) / (2 * (m : ℝ) ^ 2) ≤ g := hglow
    rw [div_le_iff₀ (by positivity)] at hglow'
    nlinarith [sq_nonneg L, hLnn, hm0, hglow']
  have hexp : L / ((m : ℝ) * g) * -(L / (m : ℝ)) = -(L ^ 2 / ((m : ℝ) * ((m : ℝ) * g))) := by
    field_simp
  rw [hexp]
  linarith [hkey]

end RHTower

end
