import GaloisForLFunctions.RHTower.SingleGeneratorUseless

/-!
# The Gram diagonal, sandwiched

`SingleGeneratorUseless` bounded the Gram diagonal below by `(m − 1)/(2m²)`.  The matching upper bound is just
as cheap: `(n mod m)² ≤ m·(n mod m)`, so the Gram series is dominated termwise by `1/m` times the pairing
series, whose value is `(log m)/m`:

**`bdGram_self_upper` — `bdGram (1/m) (1/m) ≤ (log m)/m`.**

Together:

`(m − 1)/(2m²) ≤ bdGram (1/m) (1/m) ≤ (log m)/m`,

so the diagonal is `1/m` up to a logarithm, and since the pairing is exactly `(log m)/m` the optimal
single-generator gain `pairing²/gram` is sandwiched:

**`single_gain_ge` — `(log m)/m ≤ pairing²/gram`**, i.e. `d² ≤ 1 − (log m)/m`, uniformly in `m`;
`bdDist_single_ge` (previous card) gives the matching `d² ≥ 1 − 2(log m)²/(m−1)`.

So every generator contributes something — the gain is at least `(log m)/m` — and none contributes much, the
gain being at most `2(log m)²/(m−1)`.  The two bounds differ only by a logarithm, so the single-generator
picture is now quantitatively closed.
-/

open Finset

noncomputable section

namespace RHTower

/-- **An upper bound on the Gram diagonal**, from `(n mod m)² ≤ m·(n mod m)`. -/
theorem bdGram_self_upper {m : ℕ} (hm : 1 ≤ m) :
    bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) ≤ Real.log (m : ℝ) / (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hgram := hasSum_bdGram_discrete (m₁ := m) (m₂ := m) hm hm
  have hpair := hasSum_pairing_discrete hm
  refine hasSum_le (fun n => ?_) hgram hpair
  have h1 : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  have h2 : (0 : ℝ) < ((n : ℝ) + 2) := by positivity
  have hmod : (((n + 1) % m : ℕ) : ℝ) ≤ (m : ℝ) := by
    have : ((n + 1) % m) ≤ m := le_of_lt (Nat.mod_lt _ hm)
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ (((n + 1) % m : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : (((n + 1) % m : ℕ) : ℝ) * (((n + 1) % m : ℕ) : ℝ)
      ≤ (m : ℝ) * (((n + 1) % m : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hmod hnn
  have hP : (0 : ℝ) < (m : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hkey hP.le]

/-- **The single-generator gain is at least `(log m)/m`.** -/
theorem single_gain_ge {m : ℕ} (hm : 2 ≤ m) :
    Real.log (m : ℝ) / (m : ℝ)
      ≤ (Real.log (m : ℝ) / (m : ℝ)) ^ 2 / bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm1R : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1R
  have hupper := bdGram_self_upper hm1
  have hglow := bdGram_self_lower hm1
  have hgpos : 0 < bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) := by
    refine lt_of_lt_of_le ?_ hglow
    have : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    positivity
  rw [le_div_iff₀ hgpos]
  have hL : 0 < Real.log (m : ℝ) / (m : ℝ) := by positivity
  calc Real.log (m : ℝ) / (m : ℝ) * bdGram (1 / (m : ℝ)) (1 / (m : ℝ))
      ≤ Real.log (m : ℝ) / (m : ℝ) * (Real.log (m : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper hL.le
    _ = (Real.log (m : ℝ) / (m : ℝ)) ^ 2 := by ring

end RHTower

end
