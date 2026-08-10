import GaloisForLFunctions.RHTower.GaussSampleTranslationL2

/-!
# The ratio-weighted moving-translation estimate

The iterated principal action applies the normalized diagonal to vectors that the previous stage
has already multiplied by the sampled ratio, so the relevant `ℓ²` defect carries an extra factor
`‖d_(i+j)‖²/‖d_i‖²`.  That factor is not uniformly bounded — it grows like `|i|^(1/(2m))` at the
reflected frequency — but the *weighted sum* still vanishes, and the reason is arithmetic in `m`:

`‖ρ‖⁴ ≤ 1 + ‖ρ‖^(2m)` holds exactly when `4 ≤ 2m`,

and `‖ρ‖^(2m) ≤ K |i| / |i+j|` is the corpus's uniform ratio bound.  So for `m ≥ 2` the
ratio-weighted defect has the same far-band shape as the unweighted one, and the same band-splitting
skeleton proves it vanishes.  For `m = 1` the far band contributes `O(1)` and the estimate is false;
that case is handled instead by the folded quadratic form.

The ratio is, however, bounded on the near band `2|j| ≤ i` for every `m`.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ## The ratio is bounded on the near band -/

/-- **Near-band ratio bound.**  Below half the frequency the sampled ratio is bounded by a
constant. -/
theorem norm_gaussSampleRatio_le_of_near {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (j : ℤ) (hj : 2 * j.natAbs ≤ I) :
    ‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖ ≤ 1 + 2 * K := by
  set R : ℝ := ‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖ with hR
  have hR0 : 0 ≤ R := by positivity
  rcases Nat.eq_zero_or_pos I with hI | hI
  · have hj0 : j = 0 := by omega
    have hzero : ‖gaussSampleValue k p (I : ℤ)‖ = 0 := by
      have : (I : ℤ) = 0 := by omega
      rw [this, gaussSampleValue_zero, norm_zero]
    have : R = 0 := by rw [hR, hzero, div_zero]
    rw [this]
    positivity
  have hbase := norm_gaussSampleRatio_pow_le hm k p hKb I j
  have hnat : (((I : ℤ) + j).natAbs : ℝ) ≥ (I : ℝ) / 2 := by
    have h2 : I ≤ ((I : ℤ) + j).natAbs * 2 := by omega
    have hcast := (Nat.cast_le (α := ℝ)).mpr h2
    push_cast at hcast
    linarith
  have hIpos : (0 : ℝ) < (I : ℝ) := by exact_mod_cast hI
  have hnpos : (0 : ℝ) < (((I : ℤ) + j).natAbs : ℝ) := by linarith
  have hupper : R ^ (2 * m) ≤ 2 * K := by
    refine hbase.trans ?_
    rw [div_le_iff₀ hnpos]
    nlinarith [hK.le, hnat, hIpos]
  rcases le_or_gt R 1 with h | h
  · nlinarith [hK.le]
  · have hpow : R ≤ R ^ (2 * m) := by
      calc R = R ^ 1 := (pow_one R).symm
        _ ≤ R ^ (2 * m) := pow_le_pow_right₀ h.le (by omega)
    linarith

/-- The sampled ratio is at most the defect plus one. -/
theorem norm_gaussSampleRatio_le {m : ℕ} (k : Fin m) (p : Nat.Primes) (i j : ℤ) :
    ‖gaussSampleValue k p (i + j)‖ / ‖gaussSampleValue k p i‖
      ≤ ‖gaussSampleRatioDefect k p j i‖ + 1 := by
  have h := norm_add_le (gaussSampleRatioDefect k p j i)
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
      ((gaussSamplePhase m p i : ℝ) : ℂ)))
  rw [gaussSampleRatioDefect, sub_add_cancel, norm_div,
    norm_gaussSampleRotation (m := m) p j i] at h
  exact h

/-! ## The ratio-weighted pointwise defect bound -/

/-- **Ratio-weighted pointwise defect bound**, valid from `m ≥ 2` on. -/
theorem norm_gaussSampleRatioDefect_sq_mul_ratio_sq_le {m : ℕ} (hm : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) {K : ℝ}
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (j : ℤ) :
    (‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖) ^ 2 *
        ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
      ≤ 4 + 4 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  set R : ℝ := ‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have htri : ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ≤ R + 1 := by
    rw [gaussSampleRatioDefect]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_gaussSampleRotation]
  have hsq : ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 ≤ 2 * R ^ 2 + 2 := by
    have hnn : (0 : ℝ) ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ := norm_nonneg _
    nlinarith [sq_nonneg (R - 1), htri, hnn]
  have hratio := norm_gaussSampleRatio_pow_le hm1 k p hKb I j
  have hpow2 : R ^ 2 ≤ 1 + R ^ (2 * m) := by
    rcases le_or_gt R 1 with h | h
    · have h1 : R ^ 2 ≤ 1 := pow_le_one₀ hR0 h
      have h2 : (0 : ℝ) ≤ R ^ (2 * m) := by positivity
      linarith
    · have h1 : R ^ 2 ≤ R ^ (2 * m) := pow_le_pow_right₀ h.le (by omega)
      linarith
  have hpow4 : R ^ 4 ≤ 1 + R ^ (2 * m) := by
    rcases le_or_gt R 1 with h | h
    · have h1 : R ^ 4 ≤ 1 := pow_le_one₀ hR0 h
      have h2 : (0 : ℝ) ≤ R ^ (2 * m) := by positivity
      linarith
    · have h1 : R ^ 4 ≤ R ^ (2 * m) := pow_le_pow_right₀ h.le (by omega)
      linarith
  have hnn : (0 : ℝ) ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 := by positivity
  have hkey : R ^ 2 * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 ≤ 2 * R ^ 4 + 2 * R ^ 2 := by
    nlinarith [hsq, sq_nonneg R]
  calc R ^ 2 * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 ≤ 2 * R ^ 4 + 2 * R ^ 2 := hkey
    _ ≤ 2 * (1 + R ^ (2 * m)) + 2 * (1 + R ^ (2 * m)) := by linarith
    _ ≤ 4 + 4 * (K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ)) := by linarith
    _ = 4 + 4 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) := by ring

/-! ## The ratio-weighted `ℓ²` estimate -/

/-- The ratio-weighted `ℓ²` moving-translation defect with the universal decay weight. -/
def gaussTranslationL2RatioDefectBound {m : ℕ} (k : Fin m) (p : Nat.Primes) (A : ℝ) (i : ℤ) :
    ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal
    (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
      ((‖gaussSampleValue k p (i + j)‖ / ‖gaussSampleValue k p i‖) ^ 2 *
        ‖gaussSampleRatioDefect k p j i‖ ^ 2))

/-- **The ratio-weighted moving-translation estimate**, from `m ≥ 2` on. -/
theorem tendsto_gaussTranslationL2RatioDefectBound {m : ℕ} (hm : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (A : ℝ) :
    Tendsto (fun I : ℕ => gaussTranslationL2RatioDefectBound k p A (I : ℤ)) atTop (nhds 0) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm1 k p
  refine GaloisForLFunctions.tendsto_tsum_zero_of_dominated
    (F := fun j I => ENNReal.ofReal
      (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
        ((‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖) ^ 2 *
          ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)))
    (G := fun j _ => ENNReal.ofReal ((4 + 8 * K) * A ^ 2) * GaloisForLFunctions.intQuadWeight j)
    (H := fun j I => if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (4 * K * A ^ 2 * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ))) else 0)
    ?_ ?_ ?_ ?_
  · -- every mode vanishes
    intro j
    have hdef := tendsto_gaussSampleRatioDefect_nat hm1 k p j
    have hnorm : Tendsto (fun I : ℕ => ‖gaussSampleRatioDefect k p j (I : ℤ)‖)
        atTop (nhds 0) := by simpa using hdef.norm
    have hmaj : Tendsto (fun I : ℕ =>
        (‖gaussSampleRatioDefect k p j (I : ℤ)‖ + 1) ^ 2 *
          ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2) atTop (nhds 0) := by
      have h1 : Tendsto (fun I : ℕ => (‖gaussSampleRatioDefect k p j (I : ℤ)‖ + 1) ^ 2)
          atTop (nhds 1) := by
        have h := (hnorm.add
          (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)))).pow 2
        simpa using h
      have h2 : Tendsto (fun I : ℕ => ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)
          atTop (nhds 0) := by simpa using hnorm.pow 2
      simpa using h1.mul h2
    have hR : Tendsto (fun I : ℕ =>
        (‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖) ^ 2 *
          ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2) atTop (nhds 0) := by
      refine squeeze_zero (fun I => by positivity) (fun I => ?_) hmaj
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (norm_gaussSampleRatio_le k p (I : ℤ) j) 2)
        (by positivity)
    have hmul := hR.const_mul (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2)
    rw [mul_zero] at hmul
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
    simpa [Function.comp_def] using hcont
  · -- the pointwise domination
    intro j I
    set a : ℕ := j.natAbs with ha
    set n : ℕ := ((I : ℤ) + j).natAbs with hn
    have hbound := norm_gaussSampleRatioDefect_sq_mul_ratio_sq_le hm k p hKb I j
    have hden : (0 : ℝ) < (1 + (a : ℝ)) ^ 2 := by positivity
    have hquad : GaloisForLFunctions.intQuadWeight j
        = ENNReal.ofReal (1 / (1 + (a : ℝ)) ^ 2) := by
      rw [GaloisForLFunctions.intQuadWeight, ha]
      congr 2
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have hGval : ENNReal.ofReal ((4 + 8 * K) * A ^ 2) *
        GaloisForLFunctions.intQuadWeight j
        = ENNReal.ofReal ((4 + 8 * K) * A ^ 2 / (1 + (a : ℝ)) ^ 2) := by
      rw [hquad, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hAsq : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have hstep : A ^ 2 / (1 + (a : ℝ)) ^ 2 *
        ((‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖) ^ 2 *
          ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)
        ≤ A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 4 * K * (I : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    by_cases hcase : I < 2 * a
    · by_cases hn0 : n = 0
      · rw [if_neg (by simp [hn0])]
        rw [add_zero, hGval]
        refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
        have hzero : ((n : ℕ) : ℝ) = 0 := by rw [hn0]; simp
        rw [hzero, div_zero, add_zero]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hden hden]
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 8 * K) hAsq) hden.le]
      · rw [if_pos ⟨hcase, hn0⟩, hGval, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
        have hnpos : (0 : ℝ) < (n : ℝ) := by
          have : 0 < n := Nat.pos_of_ne_zero hn0
          exact_mod_cast this
        have hexp : A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 4 * K * (I : ℝ) / (n : ℝ))
            = 4 * A ^ 2 / (1 + (a : ℝ)) ^ 2 +
              4 * K * A ^ 2 * (I : ℝ) / ((1 + (a : ℝ)) ^ 2 * (n : ℝ)) := by
          field_simp
        rw [hexp]
        have h1 : 4 * A ^ 2 / (1 + (a : ℝ)) ^ 2
            ≤ (4 + 8 * K) * A ^ 2 / (1 + (a : ℝ)) ^ 2 := by
          rw [div_le_div_iff₀ hden hden]
          nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 8 * K) hAsq) hden.le]
        linarith
    · rw [if_neg (by simp [hcase]), add_zero, hGval]
      refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
      have hIn : (I : ℝ) ≤ 2 * (n : ℝ) := by
        have : I ≤ 2 * n := by omega
        exact_mod_cast this
      have hratio : 4 * K * (I : ℝ) / (n : ℝ) ≤ 8 * K := by
        rcases Nat.eq_zero_or_pos n with h | h
        · have : ((n : ℕ) : ℝ) = 0 := by rw [h]; simp
          rw [this, div_zero]
          positivity
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
          rw [div_le_iff₀ hnpos]
          nlinarith [hK.le, hIn]
      have hle : A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 4 * K * (I : ℝ) / (n : ℝ))
          ≤ A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 8 * K) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      refine hle.trans (le_of_eq ?_)
      field_simp
  · -- uniformly small `G`-tails
    intro ε hε
    obtain ⟨S, hS⟩ := GaloisForLFunctions.exists_finset_tsum_compl_intQuadWeight_le
      (C := ENNReal.ofReal ((4 + 8 * K) * A ^ 2)) ENNReal.ofReal_ne_top hε
    exact ⟨S, fun _ => hS⟩
  · -- the far-band totals vanish
    have hc : (0 : ℝ) ≤ 4 * K * A ^ 2 := by positivity
    exact GaloisForLFunctions.tendsto_tsum_farBandRatio_zero hc

end

end RHTower
