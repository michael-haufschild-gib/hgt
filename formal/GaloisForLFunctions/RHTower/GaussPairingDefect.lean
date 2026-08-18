import GaloisForLFunctions.RHTower.GaussSampleTranslationL2
import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.HTGeometry.LatticeTailSums

/-!
# The `ℓ¹` moving-translation defect

The relative form of the iterated diagonal is read off a *pairing*, not a norm: the whole
deviation of `⟪e_n, G^r e_n⟫` from its model is `σ_n^r` times

`⟪a_δ^{r-1-i}, (R_n − M_n)(R_n^i 1)⟫`,

and the two-term split of `R_n − M_n` moves every normalized shifted block onto the *fixed* left
slot by adjointness.  What is then needed is an `ℓ¹` — not `ℓ²` — bound on
`Σ_j ‖X̂(j)‖ ‖Ŷ(j)‖ ‖defect_j‖`.

The elementary input is that the defect obeys a *linear* far-band bound

`‖defect_j(I)‖ ≤ 3 + K·I/|I+j|`,

obtained from the quadratic bound by `2D ≤ D² + 1`.  It has exactly the shape the corpus's
far-band tail estimate already consumes, so the `ℓ¹` estimate reuses the whole `ℓ²` skeleton.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-- **The linear form of the defect bound.** -/
theorem norm_gaussSampleRatioDefect_le_linear (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (j : ℤ) :
    ‖gaussSampleRatioDefect k p j (I : ℤ)‖
      ≤ 3 + K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) := by
  have hsq := norm_gaussSampleRatioDefect_sq_le hm k p hKb I j
  set D : ℝ := ‖gaussSampleRatioDefect k p j (I : ℤ)‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  set t : ℝ := K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) with ht
  have heq : 4 + 2 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) = 4 + 2 * t := by rw [ht]; ring
  have hsq' : D ^ 2 ≤ 4 + 2 * t := by rw [← heq]; exact hsq
  have hamgm : 2 * D ≤ D ^ 2 + 1 := by nlinarith [sq_nonneg (D - 1)]
  linarith

/-! ## The `ℓ¹` defect bound -/

/-- The `ℓ¹` moving-translation defect with weight `A/(1+|j|)^s`. -/
def gaussTranslationL1PowDefectBound {m : ℕ} (k : Fin m) (p : Nat.Primes) (A s : ℝ) (i : ℤ) :
    ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal
    (A / (1 + (j.natAbs : ℝ)) ^ s * ‖gaussSampleRatioDefect k p j i‖)

/-- **The `ℓ¹` moving-translation estimate.** -/
theorem tendsto_gaussTranslationL1PowDefectBound (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) {A : ℝ} (hA : 0 ≤ A) {s : ℝ} (hs : 1 < s) :
    Tendsto (fun I : ℕ => gaussTranslationL1PowDefectBound k p A s (I : ℤ)) atTop (nhds 0) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm k p
  refine GaloisForLFunctions.tendsto_tsum_zero_of_dominated
    (F := fun j I => ENNReal.ofReal
      (A / (1 + (j.natAbs : ℝ)) ^ s * ‖gaussSampleRatioDefect k p j (I : ℤ)‖))
    (G := fun j _ => ENNReal.ofReal ((3 + 2 * K) * A) * GaloisForLFunctions.intPowWeight s j)
    (H := fun j I => if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (K * A * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ s * (((I : ℤ) + j).natAbs : ℝ))) else 0)
    ?_ ?_ ?_ ?_
  · intro j
    have hdef := tendsto_gaussSampleRatioDefect_nat hm k p j
    have hnorm : Tendsto (fun I : ℕ => ‖gaussSampleRatioDefect k p j (I : ℤ)‖)
        atTop (nhds 0) := by simpa using hdef.norm
    have hmul := hnorm.const_mul (A / (1 + (j.natAbs : ℝ)) ^ s)
    rw [mul_zero] at hmul
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
    simpa [Function.comp_def] using hcont
  · intro j I
    set a : ℕ := j.natAbs with ha
    set n : ℕ := ((I : ℤ) + j).natAbs with hn
    have hbound := norm_gaussSampleRatioDefect_le_linear hm k p hKb I j
    have hden : (0 : ℝ) < (1 + (a : ℝ)) ^ s := Real.rpow_pos_of_pos (by positivity) s
    have hquad : GaloisForLFunctions.intPowWeight s j
        = ENNReal.ofReal (1 / (1 + (a : ℝ)) ^ s) := by
      rw [GaloisForLFunctions.intPowWeight, ha]
      congr 2
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have hGval : ENNReal.ofReal ((3 + 2 * K) * A) *
        GaloisForLFunctions.intPowWeight s j
        = ENNReal.ofReal ((3 + 2 * K) * A / (1 + (a : ℝ)) ^ s) := by
      rw [hquad, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hstep : A / (1 + (a : ℝ)) ^ s * ‖gaussSampleRatioDefect k p j (I : ℤ)‖
        ≤ A / (1 + (a : ℝ)) ^ s * (3 + K * (I : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    by_cases hcase : I < 2 * a
    · by_cases hn0 : n = 0
      · rw [if_neg (by simp [hn0]), add_zero, hGval]
        refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
        have hzero : ((n : ℕ) : ℝ) = 0 := by rw [hn0]; simp
        rw [hzero, div_zero, add_zero]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hden hden]
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * K) hA) hden.le]
      · rw [if_pos ⟨hcase, hn0⟩, hGval, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
        have hnpos : (0 : ℝ) < (n : ℝ) := by
          have : 0 < n := Nat.pos_of_ne_zero hn0
          exact_mod_cast this
        have hexp : A / (1 + (a : ℝ)) ^ s * (3 + K * (I : ℝ) / (n : ℝ))
            = 3 * A / (1 + (a : ℝ)) ^ s +
              K * A * (I : ℝ) / ((1 + (a : ℝ)) ^ s * (n : ℝ)) := by
          field_simp
        rw [hexp]
        have h1 : 3 * A / (1 + (a : ℝ)) ^ s ≤ (3 + 2 * K) * A / (1 + (a : ℝ)) ^ s := by
          rw [div_le_div_iff₀ hden hden]
          nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * K) hA) hden.le]
        linarith
    · rw [if_neg (by simp [hcase]), add_zero, hGval]
      refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
      have hIn : (I : ℝ) ≤ 2 * (n : ℝ) := by
        have : I ≤ 2 * n := by omega
        exact_mod_cast this
      have hratio : K * (I : ℝ) / (n : ℝ) ≤ 2 * K := by
        rcases Nat.eq_zero_or_pos n with h | h
        · have : ((n : ℕ) : ℝ) = 0 := by rw [h]; simp
          rw [this, div_zero]
          positivity
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
          rw [div_le_iff₀ hnpos]
          nlinarith [hK.le, hIn]
      have hle : A / (1 + (a : ℝ)) ^ s * (3 + K * (I : ℝ) / (n : ℝ))
          ≤ A / (1 + (a : ℝ)) ^ s * (3 + 2 * K) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      refine hle.trans (le_of_eq ?_)
      field_simp
  · intro ε hε
    obtain ⟨S, hS⟩ := GaloisForLFunctions.exists_finset_tsum_compl_intPowWeight_le hs
      (C := ENNReal.ofReal ((3 + 2 * K) * A)) ENNReal.ofReal_ne_top hε
    exact ⟨S, fun _ => hS⟩
  · have hc : (0 : ℝ) ≤ K * A := by positivity
    exact GaloisForLFunctions.tendsto_tsum_farBandPower_zero hc hs

/-! ## Reflection -/

theorem gaussTranslationL1PowDefectBound_neg (k : Fin m) (p : Nat.Primes) (A s : ℝ) (i : ℤ) :
    gaussTranslationL1PowDefectBound k p A s (-i) = gaussTranslationL1PowDefectBound k p A s i := by
  rw [gaussTranslationL1PowDefectBound, gaussTranslationL1PowDefectBound,
    ← (Equiv.neg ℤ).tsum_eq (fun j : ℤ => ENNReal.ofReal
      (A / (1 + (j.natAbs : ℝ)) ^ s * ‖gaussSampleRatioDefect k p j i‖))]
  refine tsum_congr fun j => ?_
  have hdef : gaussSampleRatioDefect k p j (-i)
      = starRingEnd ℂ (gaussSampleRatioDefect k p (-j) i) := by
    have h := gaussSampleRatioDefect_neg k p (-j) i
    rwa [neg_neg] at h
  rw [hdef, RCLike.norm_conj]
  simp [Equiv.neg]

theorem gaussTranslationL1PowDefectBound_natAbs (k : Fin m) (p : Nat.Primes) (A s : ℝ) (i : ℤ) :
    gaussTranslationL1PowDefectBound k p A s ((i.natAbs : ℤ))
      = gaussTranslationL1PowDefectBound k p A s i := by
  rcases Int.natAbs_eq i with h | h
  · rw [← h]
  · have hb := gaussTranslationL1PowDefectBound_neg k p A s ((i.natAbs : ℤ))
    rw [← h] at hb
    exact hb.symm

/-- **The `ℓ¹` estimate along any escaping frequency sequence.** -/
theorem tendsto_gaussTranslationL1PowDefectBound_comp (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) {A : ℝ} (hA : 0 ≤ A) {s : ℝ} (hs : 1 < s) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ => gaussTranslationL1PowDefectBound k p A s (ι n)) atTop (nhds 0) := by
  have hcomp := (tendsto_gaussTranslationL1PowDefectBound hm k p hA hs).comp hι
  refine hcomp.congr fun n => ?_
  simp only [Function.comp_apply]
  exact gaussTranslationL1PowDefectBound_natAbs k p A s (ι n)

/-! ## The band mass of the defect -/

/-- **The moving-translation defect has linear-times-logarithmic mass on the spike band.** -/
theorem tsum_band_defect_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) :
    ∑' l : ℤ, (if 2 * ((I : ℤ) + l).natAbs < I then
        ENNReal.ofReal (‖gaussSampleRatioDefect k p l (I : ℤ)‖) else 0)
      ≤ ENNReal.ofReal (6 * (I : ℝ) + 2 * K * (I : ℝ) * (1 + Real.log (I : ℝ))) := by
  classical
  set F : ℤ → ℝ≥0∞ := fun l => if 2 * ((I : ℤ) + l).natAbs < I then
    ENNReal.ofReal (‖gaussSampleRatioDefect k p l (I : ℤ)‖) else 0 with hF
  have hre : ∑' l : ℤ, F l = ∑' r : ℤ, F (r - (I : ℤ)) :=
    (Equiv.tsum_eq (Equiv.subRight ((I : ℤ))) F).symm
  have hpoint : ∀ r : ℤ, F (r - (I : ℤ))
      ≤ (if r.natAbs < I then (3 : ℝ≥0∞) else 0)
        + (if 0 < r.natAbs ∧ r.natAbs < I then
            ENNReal.ofReal (K * (I : ℝ)) * ENNReal.ofReal (1 / (r.natAbs : ℝ)) else 0) := by
    intro r
    have hidx : ((I : ℤ) + (r - (I : ℤ))) = r := by ring
    by_cases hsp : 2 * r.natAbs < I
    swap
    · have hz : F (r - (I : ℤ)) = 0 := by
        rw [hF]
        exact if_neg (by rw [hidx]; exact hsp)
      rw [hz]
      exact _root_.zero_le
    have hFval : F (r - (I : ℤ))
        = ENNReal.ofReal (‖gaussSampleRatioDefect k p (r - (I : ℤ)) (I : ℤ)‖) := by
      rw [hF]
      exact if_pos (by rw [hidx]; exact hsp)
    have hlt : r.natAbs < I := by omega
    have hbase := norm_gaussSampleRatioDefect_le_linear hm k p hKb I (r - (I : ℤ))
    rw [hidx] at hbase
    rcases Nat.eq_zero_or_pos r.natAbs with h0 | hpos
    · have hzero : ((r.natAbs : ℕ) : ℝ) = 0 := by rw [h0]; simp
      rw [hFval, if_pos hlt, if_neg (by omega)]
      refine le_trans (ENNReal.ofReal_le_ofReal hbase) ?_
      rw [hzero, div_zero, add_zero]
      rw [add_zero]
      exact le_of_eq (by norm_num)
    · rw [hFval, if_pos hlt, if_pos ⟨hpos, hlt⟩]
      refine le_trans (ENNReal.ofReal_le_ofReal hbase) ?_
      have hsplit : K * (I : ℝ) / ((r.natAbs : ℕ) : ℝ)
          = K * (I : ℝ) * (1 / ((r.natAbs : ℕ) : ℝ)) := by ring
      rw [hsplit, ENNReal.ofReal_add (by norm_num)
        (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine add_le_add ?_ le_rfl
      exact le_of_eq (by norm_num)
  refine le_trans (le_of_eq hre) (le_trans (ENNReal.tsum_le_tsum hpoint) ?_)
  rw [ENNReal.tsum_add]
  have hband : ∑' r : ℤ, (if r.natAbs < I then (3 : ℝ≥0∞) else 0)
      ≤ 3 * (2 * (I : ℝ≥0∞)) := by
    have hmove : ∀ r : ℤ, (if r.natAbs < I then (3 : ℝ≥0∞) else 0)
        = 3 * (if r.natAbs < I then (1 : ℝ≥0∞) else 0) := by
      intro r
      by_cases h : r.natAbs < I
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [tsum_congr hmove, ENNReal.tsum_mul_left]
    exact mul_le_mul_left' (tsum_int_band_one_le I) 3
  have hharm : ∑' r : ℤ, (if 0 < r.natAbs ∧ r.natAbs < I then
        ENNReal.ofReal (K * (I : ℝ)) * ENNReal.ofReal (1 / (r.natAbs : ℝ)) else 0)
      ≤ ENNReal.ofReal (K * (I : ℝ)) * ENNReal.ofReal (2 * (1 + Real.log (I : ℝ))) := by
    have hmove : ∀ r : ℤ, (if 0 < r.natAbs ∧ r.natAbs < I then
        ENNReal.ofReal (K * (I : ℝ)) * ENNReal.ofReal (1 / (r.natAbs : ℝ)) else 0)
        = ENNReal.ofReal (K * (I : ℝ)) *
          (if 0 < r.natAbs ∧ r.natAbs < I then ENNReal.ofReal (1 / (r.natAbs : ℝ)) else 0) := by
      intro r
      by_cases h : 0 < r.natAbs ∧ r.natAbs < I
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [tsum_congr hmove, ENNReal.tsum_mul_left]
    exact mul_le_mul_left' (tsum_int_punctured_band_inv_le I) _
  refine le_trans (add_le_add hband hharm) ?_
  have h1 : (3 : ℝ≥0∞) * (2 * (I : ℝ≥0∞)) = ENNReal.ofReal (6 * (I : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
    norm_num
    ring
  have hlogI : (0 : ℝ) ≤ Real.log (I : ℝ) := by
    rcases Nat.eq_zero_or_pos I with h | h
    · rw [h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have h2 : ENNReal.ofReal (K * (I : ℝ)) * ENNReal.ofReal (2 * (1 + Real.log (I : ℝ)))
      = ENNReal.ofReal (K * (I : ℝ) * (2 * (1 + Real.log (I : ℝ)))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-! ## The spike pairing bound -/

/-- **Pairing a spike against anything bounded on the band.**  Off the band the spike vanishes;
on the band its height is at most `H·I^c` and the defect has mass `O(I log I)`. -/
theorem tsum_spikeProfile_mul_defect_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {H c w : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ c) (hw : 0 ≤ w) (f : ℤ → ℝ) (hf0 : ∀ l, 0 ≤ f l)
    {I : ℕ} (hf : ∀ l : ℤ, 2 * ((I : ℤ) + l).natAbs < I → f l ≤ w) :
    ∑' l : ℤ, ENNReal.ofReal
        (spikeProfile H c I l * f l * ‖gaussSampleRatioDefect k p l (I : ℤ)‖)
      ≤ ENNReal.ofReal (H * (I : ℝ) ^ c * w *
          (6 * (I : ℝ) + 2 * K * (I : ℝ) * (1 + Real.log (I : ℝ)))) := by
  classical
  have hcoef : (0 : ℝ) ≤ H * (I : ℝ) ^ c * w := by
    have : (0 : ℝ) ≤ (I : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg I) c
    positivity
  have hpoint : ∀ l : ℤ,
      ENNReal.ofReal (spikeProfile H c I l * f l * ‖gaussSampleRatioDefect k p l (I : ℤ)‖)
        ≤ ENNReal.ofReal (H * (I : ℝ) ^ c * w) *
          (if 2 * ((I : ℤ) + l).natAbs < I then
            ENNReal.ofReal (‖gaussSampleRatioDefect k p l (I : ℤ)‖) else 0) := by
    intro l
    by_cases hband : 2 * (((I : ℤ) + l).natAbs : ℝ) < (I : ℝ)
    · have hbandN : 2 * ((I : ℤ) + l).natAbs < I := by exact_mod_cast hband
      have hspike : spikeProfile H c I l ≤ H * (I : ℝ) ^ c := by
        rw [spikeProfile, if_pos hband]
        refine mul_le_mul_of_nonneg_left ?_ hH
        refine Real.rpow_le_rpow (by positivity) ?_ hc
        exact div_le_self (Nat.cast_nonneg I) (by simp)
      have hmul : spikeProfile H c I l * f l * ‖gaussSampleRatioDefect k p l (I : ℤ)‖
          ≤ H * (I : ℝ) ^ c * w * ‖gaussSampleRatioDefect k p l (I : ℤ)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul hspike (hf l hbandN) (hf0 l)
          (mul_nonneg hH (Real.rpow_nonneg (Nat.cast_nonneg I) c))
      rw [if_pos hbandN, ← ENNReal.ofReal_mul hcoef]
      exact ENNReal.ofReal_le_ofReal hmul
    · have hzero : spikeProfile H c I l = 0 := by
        rw [spikeProfile, if_neg hband]
      rw [hzero, zero_mul, zero_mul, ENNReal.ofReal_zero]
      exact _root_.zero_le
  refine le_trans (ENNReal.tsum_le_tsum hpoint) ?_
  rw [ENNReal.tsum_mul_left]
  have hband := tsum_band_defect_le hm k p hK hKb I
  refine le_trans (mul_le_mul_left' hband _) ?_
  have hnn : (0 : ℝ) ≤ 6 * (I : ℝ) + 2 * K * (I : ℝ) * (1 + Real.log (I : ℝ)) := by
    have hlogI : (0 : ℝ) ≤ Real.log (I : ℝ) := by
      rcases Nat.eq_zero_or_pos I with h | h
      · rw [h]; simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    positivity
  rw [← ENNReal.ofReal_mul hcoef]

/-! ## The master pairing bound -/

/-- The linear-times-logarithmic band mass of the defect. -/
noncomputable def gaussBandDefectMass (K : ℝ) (I : ℕ) : ℝ :=
  6 * (I : ℝ) + 2 * K * (I : ℝ) * (1 + Real.log (I : ℝ))

theorem gaussBandDefectMass_nonneg {K : ℝ} (hK : 0 ≤ K) (I : ℕ) :
    0 ≤ gaussBandDefectMass K I := by
  have hlogI : (0 : ℝ) ≤ Real.log (I : ℝ) := by
    rcases Nat.eq_zero_or_pos I with h | h
    · rw [h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  rw [gaussBandDefectMass]
  positivity

/-- **The pairing of two two-piece profiles against the moving-translation defect.**  The bulk
part is the `ℓ¹` defect bound at the summed exponent; each of the three spike parts is a spike
height times the band mass. -/
theorem tsum_twoPiece_pairing_defect_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {AP θP HP cP AQ θQ HQ cQ : ℝ}
    (hAP : 0 ≤ AP) (hHP : 0 ≤ HP) (hAQ : 0 ≤ AQ) (hHQ : 0 ≤ HQ)
    (hcP : 0 ≤ cP) (hcQ : 0 ≤ cQ) (hθP : 0 ≤ θP) (hθQ : 0 ≤ θQ)
    {I : ℕ} {X Y : ℤ → ℂ}
    (hX : TwoPieceAmplitude AP θP HP cP I X)
    (hY : TwoPieceAmplitude AQ θQ HQ cQ I Y) :
    ∑' j : ℤ, ENNReal.ofReal (‖X j‖ * ‖Y j‖ * ‖gaussSampleRatioDefect k p j (I : ℤ)‖)
      ≤ gaussTranslationL1PowDefectBound k p (AP * AQ) (θP + θQ) (I : ℤ)
        + (ENNReal.ofReal (HP * (I : ℝ) ^ cP * (AQ / (1 + (I : ℝ) / 2) ^ θQ) *
              gaussBandDefectMass K I)
          + (ENNReal.ofReal (HQ * (I : ℝ) ^ cQ * (AP / (1 + (I : ℝ) / 2) ^ θP) *
              gaussBandDefectMass K I)
            + ENNReal.ofReal (HP * (I : ℝ) ^ cP * (HQ * (I : ℝ) ^ cQ) *
              gaussBandDefectMass K I))) := by
  classical
  set D : ℤ → ℝ := fun j => ‖gaussSampleRatioDefect k p j (I : ℤ)‖ with hD
  set bP : ℤ → ℝ := fun j => AP / (1 + (j.natAbs : ℝ)) ^ θP with hbP
  set bQ : ℤ → ℝ := fun j => AQ / (1 + (j.natAbs : ℝ)) ^ θQ with hbQ
  set sP : ℤ → ℝ := fun j => spikeProfile HP cP I j with hsP
  set sQ : ℤ → ℝ := fun j => spikeProfile HQ cQ I j with hsQ
  have hbP0 : ∀ j, 0 ≤ bP j := fun j => by rw [hbP]; positivity
  have hbQ0 : ∀ j, 0 ≤ bQ j := fun j => by rw [hbQ]; positivity
  have hsP0 : ∀ j, 0 ≤ sP j := fun j => spikeProfile_nonneg hHP I j
  have hsQ0 : ∀ j, 0 ≤ sQ j := fun j => spikeProfile_nonneg hHQ I j
  -- the four-term pointwise split
  have hpoint : ∀ j : ℤ, ENNReal.ofReal (‖X j‖ * ‖Y j‖ * D j)
      ≤ ENNReal.ofReal (AP * AQ / (1 + (j.natAbs : ℝ)) ^ (θP + θQ) * D j)
        + (ENNReal.ofReal (sP j * bQ j * D j)
          + (ENNReal.ofReal (sQ j * bP j * D j)
            + ENNReal.ofReal (sP j * sQ j * D j))) := by
    intro j
    have hxy : ‖X j‖ * ‖Y j‖ * D j
        ≤ bP j * bQ j * D j + (sP j * bQ j * D j + (sQ j * bP j * D j + sP j * sQ j * D j)) := by
      have h1 : ‖X j‖ ≤ bP j + sP j := hX j
      have h2 : ‖Y j‖ ≤ bQ j + sQ j := hY j
      have hprod : ‖X j‖ * ‖Y j‖ ≤ (bP j + sP j) * (bQ j + sQ j) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by linarith [hbP0 j, hsP0 j])
      have hD0 : 0 ≤ D j := norm_nonneg _
      nlinarith [hprod, hD0]
    have hsplit : bP j * bQ j = AP * AQ / (1 + (j.natAbs : ℝ)) ^ (θP + θQ) := by
      rw [hbP, hbQ, Real.rpow_add (by positivity)]
      field_simp
    rw [hsplit] at hxy
    have hD0 : 0 ≤ D j := norm_nonneg _
    have n1 : (0 : ℝ) ≤ AP * AQ / (1 + (j.natAbs : ℝ)) ^ (θP + θQ) * D j := by positivity
    have n2 : (0 : ℝ) ≤ sP j * bQ j * D j :=
      mul_nonneg (mul_nonneg (hsP0 j) (hbQ0 j)) hD0
    have n3 : (0 : ℝ) ≤ sQ j * bP j * D j :=
      mul_nonneg (mul_nonneg (hsQ0 j) (hbP0 j)) hD0
    have n4 : (0 : ℝ) ≤ sP j * sQ j * D j :=
      mul_nonneg (mul_nonneg (hsP0 j) (hsQ0 j)) hD0
    refine le_trans (ENNReal.ofReal_le_ofReal hxy) ?_
    rw [ENNReal.ofReal_add n1 (by linarith), ENNReal.ofReal_add n2 (by linarith),
      ENNReal.ofReal_add n3 n4]
  refine le_trans (ENNReal.tsum_le_tsum hpoint) ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
  refine add_le_add (le_of_eq rfl) (add_le_add ?_ (add_le_add ?_ ?_))
  · -- spike of `X` against the bulk of `Y`
    refine tsum_spikeProfile_mul_defect_le hm k p hK hKb hHP hcP (by positivity) bQ hbQ0 ?_
    intro l hband
    have hbandR : 2 * (((I : ℤ) + l).natAbs : ℝ) < (I : ℝ) := by exact_mod_cast hband
    have hfar : (I : ℝ) / 2 ≤ (l.natAbs : ℝ) := half_le_natAbs_of_mem_band hbandR
    rw [hbQ]
    refine div_le_div_of_nonneg_left hAQ (by positivity) ?_
    exact Real.rpow_le_rpow (by positivity) (by linarith) hθQ
  · -- spike of `Y` against the bulk of `X`
    refine tsum_spikeProfile_mul_defect_le hm k p hK hKb hHQ hcQ (by positivity) bP hbP0 ?_
    intro l hband
    have hbandR : 2 * (((I : ℤ) + l).natAbs : ℝ) < (I : ℝ) := by exact_mod_cast hband
    have hfar : (I : ℝ) / 2 ≤ (l.natAbs : ℝ) := half_le_natAbs_of_mem_band hbandR
    rw [hbP]
    refine div_le_div_of_nonneg_left hAP (by positivity) ?_
    exact Real.rpow_le_rpow (by positivity) (by linarith) hθP
  · -- the two spikes
    refine tsum_spikeProfile_mul_defect_le hm k p hK hKb hHP hcP
      (mul_nonneg hHQ (Real.rpow_nonneg (Nat.cast_nonneg I) cQ)) sQ hsQ0 ?_
    intro l hband
    have hbandR : 2 * (((I : ℤ) + l).natAbs : ℝ) < (I : ℝ) := by exact_mod_cast hband
    simp only [hsQ, spikeProfile, if_pos hbandR]
    refine mul_le_mul_of_nonneg_left ?_ hHQ
    refine Real.rpow_le_rpow (by positivity) ?_ hcQ
    exact div_le_self (Nat.cast_nonneg I) (by simp)

/-! ## The band mass is beaten by any strictly larger exponent -/

theorem tendsto_natCast_rpow_mul_bandMass_div_rpow {a b K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hab : a + 1 < b) :
    Tendsto (fun I : ℕ => (I : ℝ) ^ a * gaussBandDefectMass K I / (1 + (I : ℝ)) ^ b)
      atTop (nhds 0) := by
  have ht : 0 < b - a - 1 := by linarith
  have hbase := GaloisForLFunctions.tendsto_one_add_log_div_rpow_atTop_zero (t := b - a - 1) ht
  have hdom := hbase.const_mul (6 + 2 * K)
  rw [mul_zero] at hdom
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [eventually_ge_atTop 1] with I hI
    have hI1 : (1 : ℝ) ≤ (I : ℝ) := by exact_mod_cast hI
    have := gaussBandDefectMass_nonneg hK I
    positivity
  · filter_upwards [eventually_ge_atTop 1] with I hI
    have hI1 : (1 : ℝ) ≤ (I : ℝ) := by exact_mod_cast hI
    have hI0 : (0 : ℝ) < (I : ℝ) := by linarith
    have hlogI : (0 : ℝ) ≤ Real.log (I : ℝ) := Real.log_nonneg hI1
    have hb0 : (0 : ℝ) ≤ b := by linarith
    have hmass : gaussBandDefectMass K I ≤ (6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ))) := by
      rw [gaussBandDefectMass]
      nlinarith [mul_nonneg (le_of_lt hI0) hlogI, hK]
    have hposI : (0 : ℝ) < (I : ℝ) ^ a := Real.rpow_pos_of_pos hI0 a
    have hpow : (0 : ℝ) < (1 + (I : ℝ)) ^ b := Real.rpow_pos_of_pos (by linarith) b
    have hstep1 : (I : ℝ) ^ a * gaussBandDefectMass K I / (1 + (I : ℝ)) ^ b
        ≤ (I : ℝ) ^ a * ((6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ)))) / (1 + (I : ℝ)) ^ b := by
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hposI.le) hpow.le
    have hIb : (I : ℝ) ^ b ≤ (1 + (I : ℝ)) ^ b :=
      Real.rpow_le_rpow hI0.le (by linarith) hb0
    have hIbpos : (0 : ℝ) < (I : ℝ) ^ b := Real.rpow_pos_of_pos hI0 b
    have hnum : (0 : ℝ) ≤ (I : ℝ) ^ a * ((6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ)))) := by
      have h1 : (0 : ℝ) ≤ (6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ))) := by positivity
      exact mul_nonneg hposI.le h1
    have hstep2 : (I : ℝ) ^ a * ((6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ))))
          / (1 + (I : ℝ)) ^ b
        ≤ (I : ℝ) ^ a * ((6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ)))) / (I : ℝ) ^ b :=
      div_le_div_of_nonneg_left hnum hIbpos hIb
    have hsplit : (I : ℝ) ^ a * (I : ℝ) = (I : ℝ) ^ (a + 1) := by
      rw [Real.rpow_add hI0, Real.rpow_one]
    have hquot : (I : ℝ) ^ (a + 1) / (I : ℝ) ^ b = 1 / (I : ℝ) ^ (b - a - 1) := by
      rw [← Real.rpow_sub hI0, one_div, ← Real.rpow_neg hI0.le]
      congr 1
      ring
    have hid : (I : ℝ) ^ a * ((6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ)))) / (I : ℝ) ^ b
        = (6 + 2 * K) * ((1 + Real.log (I : ℝ)) / (I : ℝ) ^ (b - a - 1)) := by
      calc (I : ℝ) ^ a * ((6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ)))) / (I : ℝ) ^ b
          = (6 + 2 * K) * (1 + Real.log (I : ℝ)) * (((I : ℝ) ^ a * (I : ℝ)) / (I : ℝ) ^ b) := by
            ring
        _ = (6 + 2 * K) * (1 + Real.log (I : ℝ)) * ((I : ℝ) ^ (a + 1) / (I : ℝ) ^ b) := by
            rw [hsplit]
        _ = (6 + 2 * K) * (1 + Real.log (I : ℝ)) * (1 / (I : ℝ) ^ (b - a - 1)) := by rw [hquot]
        _ = (6 + 2 * K) * ((1 + Real.log (I : ℝ)) / (I : ℝ) ^ (b - a - 1)) := by ring
    calc (I : ℝ) ^ a * gaussBandDefectMass K I / (1 + (I : ℝ)) ^ b
        ≤ (I : ℝ) ^ a * ((6 + 2 * K) * ((I : ℝ) * (1 + Real.log (I : ℝ)))) / (I : ℝ) ^ b :=
          le_trans hstep1 hstep2
      _ = (6 + 2 * K) * ((1 + Real.log (I : ℝ)) / (I : ℝ) ^ (b - a - 1)) := hid

theorem tendsto_ofReal_zero_of_le_bandMass {K : ℝ} (hK : 0 ≤ K) {a b C : ℝ} (ha : 0 ≤ a)
    (hab : a + 1 < b) {f : ℕ → ℝ} (hf0 : ∀ I, 0 ≤ f I)
    (hf : ∀ᶠ I in atTop, f I ≤ C * ((I : ℝ) ^ a * gaussBandDefectMass K I / (1 + (I : ℝ)) ^ b)) :
    Tendsto (fun I : ℕ => ENNReal.ofReal (f I)) atTop (nhds 0) := by
  have hbase := (tendsto_natCast_rpow_mul_bandMass_div_rpow ha hK hab).const_mul C
  rw [mul_zero] at hbase
  have hreal : Tendsto f atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall (fun I => hf0 I)) hf hbase
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  simpa [Function.comp_def] using h

/-- A one-half shift in the denominator costs only a constant. -/
theorem inv_one_add_half_rpow_le {θ : ℝ} (hθ : 0 ≤ θ) (I : ℕ) :
    (1 : ℝ) / (1 + (I : ℝ) / 2) ^ θ ≤ 2 ^ θ / (1 + (I : ℝ)) ^ θ := by
  have h1 : (0 : ℝ) < 1 + (I : ℝ) / 2 := by positivity
  have h2 : (0 : ℝ) < 1 + (I : ℝ) := by positivity
  have hle : (1 : ℝ) + (I : ℝ) ≤ 2 * (1 + (I : ℝ) / 2) := by ring_nf; linarith
  have hpow : (1 + (I : ℝ)) ^ θ ≤ 2 ^ θ * (1 + (I : ℝ) / 2) ^ θ := by
    have := Real.rpow_le_rpow h2.le hle hθ
    rwa [Real.mul_rpow (by norm_num) h1.le] at this
  have hp1 : (0 : ℝ) < (1 + (I : ℝ) / 2) ^ θ := Real.rpow_pos_of_pos h1 θ
  have hp2 : (0 : ℝ) < (1 + (I : ℝ)) ^ θ := Real.rpow_pos_of_pos h2 θ
  rw [div_le_div_iff₀ hp1 hp2]
  linarith

/-! ## The pairing estimate -/

set_option maxHeartbeats 1000000 in
/-- **The pairing of two two-piece families against the moving-translation defect vanishes.** -/
theorem tendsto_tsum_twoPiece_pairing_defect_zero (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {AP θP BP σP cP AQ θQ BQ σQ cQ : ℝ}
    (hAP : 0 ≤ AP) (hBP : 0 ≤ BP) (hAQ : 0 ≤ AQ) (hBQ : 0 ≤ BQ)
    (hcP : 0 ≤ cP) (hcQ : 0 ≤ cQ) (hθP : 0 ≤ θP) (hθQ : 0 ≤ θQ)
    (h1 : 1 < θP + θQ) (h2 : cP + 1 < σP + θQ) (h3 : cQ + 1 < σQ + θP)
    (h4 : cP + cQ + 1 < σP + σQ)
    (X Y : ℕ → ℤ → ℂ)
    (hX : ∀ I : ℕ, 2 ≤ I → TwoPieceAmplitude AP θP (BP / (1 + (I : ℝ)) ^ σP) cP I (X I))
    (hY : ∀ I : ℕ, 2 ≤ I → TwoPieceAmplitude AQ θQ (BQ / (1 + (I : ℝ)) ^ σQ) cQ I (Y I)) :
    Tendsto (fun I : ℕ => ∑' j : ℤ, ENNReal.ofReal
        (‖X I j‖ * ‖Y I j‖ * ‖gaussSampleRatioDefect k p j (I : ℤ)‖)) atTop (nhds 0) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm k p
  have hHP : ∀ I : ℕ, (0 : ℝ) ≤ BP / (1 + (I : ℝ)) ^ σP := fun I => by positivity
  have hHQ : ∀ I : ℕ, (0 : ℝ) ≤ BQ / (1 + (I : ℝ)) ^ σQ := fun I => by positivity
  -- the bulk term
  have T1 : Tendsto (fun I : ℕ =>
      gaussTranslationL1PowDefectBound k p (AP * AQ) (θP + θQ) (I : ℤ)) atTop (nhds 0) :=
    tendsto_gaussTranslationL1PowDefectBound hm k p (mul_nonneg hAP hAQ) h1
  -- the spike-of-X term
  have T2 : Tendsto (fun I : ℕ => ENNReal.ofReal
      (BP / (1 + (I : ℝ)) ^ σP * (I : ℝ) ^ cP * (AQ / (1 + (I : ℝ) / 2) ^ θQ) *
        gaussBandDefectMass K I)) atTop (nhds 0) := by
    refine tendsto_ofReal_zero_of_le_bandMass (K := K) hK.le (a := cP) (b := σP + θQ)
      (C := BP * AQ * 2 ^ θQ) hcP (by linarith) (fun I => ?_) (Eventually.of_forall fun I => ?_)
    · have := gaussBandDefectMass_nonneg hK.le I
      have h5 : (0 : ℝ) ≤ (I : ℝ) ^ cP := Real.rpow_nonneg (Nat.cast_nonneg I) cP
      have h6 : (0 : ℝ) ≤ AQ / (1 + (I : ℝ) / 2) ^ θQ := by positivity
      have := hHP I
      positivity
    · have hmass := gaussBandDefectMass_nonneg hK.le I
      have hIc : (0 : ℝ) ≤ (I : ℝ) ^ cP := Real.rpow_nonneg (Nat.cast_nonneg I) cP
      have hhalf : AQ / (1 + (I : ℝ) / 2) ^ θQ ≤ AQ * (2 ^ θQ / (1 + (I : ℝ)) ^ θQ) := by
        have h := inv_one_add_half_rpow_le hθQ I
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left h hAQ
      have hsplit : (1 + (I : ℝ)) ^ (σP + θQ) = (1 + (I : ℝ)) ^ σP * (1 + (I : ℝ)) ^ θQ :=
        Real.rpow_add (by positivity) _ _
      have hnn : (0 : ℝ) ≤ BP / (1 + (I : ℝ)) ^ σP * (I : ℝ) ^ cP * gaussBandDefectMass K I := by
        have := hHP I
        positivity
      calc BP / (1 + (I : ℝ)) ^ σP * (I : ℝ) ^ cP * (AQ / (1 + (I : ℝ) / 2) ^ θQ) *
            gaussBandDefectMass K I
          = (BP / (1 + (I : ℝ)) ^ σP * (I : ℝ) ^ cP * gaussBandDefectMass K I) *
              (AQ / (1 + (I : ℝ) / 2) ^ θQ) := by ring
        _ ≤ (BP / (1 + (I : ℝ)) ^ σP * (I : ℝ) ^ cP * gaussBandDefectMass K I) *
              (AQ * (2 ^ θQ / (1 + (I : ℝ)) ^ θQ)) := mul_le_mul_of_nonneg_left hhalf hnn
        _ = BP * AQ * 2 ^ θQ *
              ((I : ℝ) ^ cP * gaussBandDefectMass K I / (1 + (I : ℝ)) ^ (σP + θQ)) := by
              rw [hsplit]
              field_simp
  -- the spike-of-Y term
  have T3 : Tendsto (fun I : ℕ => ENNReal.ofReal
      (BQ / (1 + (I : ℝ)) ^ σQ * (I : ℝ) ^ cQ * (AP / (1 + (I : ℝ) / 2) ^ θP) *
        gaussBandDefectMass K I)) atTop (nhds 0) := by
    refine tendsto_ofReal_zero_of_le_bandMass (K := K) hK.le (a := cQ) (b := σQ + θP)
      (C := BQ * AP * 2 ^ θP) hcQ (by linarith) (fun I => ?_) (Eventually.of_forall fun I => ?_)
    · have := gaussBandDefectMass_nonneg hK.le I
      have h5 : (0 : ℝ) ≤ (I : ℝ) ^ cQ := Real.rpow_nonneg (Nat.cast_nonneg I) cQ
      have h6 : (0 : ℝ) ≤ AP / (1 + (I : ℝ) / 2) ^ θP := by positivity
      have := hHQ I
      positivity
    · have hmass := gaussBandDefectMass_nonneg hK.le I
      have hIc : (0 : ℝ) ≤ (I : ℝ) ^ cQ := Real.rpow_nonneg (Nat.cast_nonneg I) cQ
      have hhalf : AP / (1 + (I : ℝ) / 2) ^ θP ≤ AP * (2 ^ θP / (1 + (I : ℝ)) ^ θP) := by
        have h := inv_one_add_half_rpow_le hθP I
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left h hAP
      have hsplit : (1 + (I : ℝ)) ^ (σQ + θP) = (1 + (I : ℝ)) ^ σQ * (1 + (I : ℝ)) ^ θP :=
        Real.rpow_add (by positivity) _ _
      have hnn : (0 : ℝ) ≤ BQ / (1 + (I : ℝ)) ^ σQ * (I : ℝ) ^ cQ * gaussBandDefectMass K I := by
        have := hHQ I
        positivity
      calc BQ / (1 + (I : ℝ)) ^ σQ * (I : ℝ) ^ cQ * (AP / (1 + (I : ℝ) / 2) ^ θP) *
            gaussBandDefectMass K I
          = (BQ / (1 + (I : ℝ)) ^ σQ * (I : ℝ) ^ cQ * gaussBandDefectMass K I) *
              (AP / (1 + (I : ℝ) / 2) ^ θP) := by ring
        _ ≤ (BQ / (1 + (I : ℝ)) ^ σQ * (I : ℝ) ^ cQ * gaussBandDefectMass K I) *
              (AP * (2 ^ θP / (1 + (I : ℝ)) ^ θP)) := mul_le_mul_of_nonneg_left hhalf hnn
        _ = BQ * AP * 2 ^ θP *
              ((I : ℝ) ^ cQ * gaussBandDefectMass K I / (1 + (I : ℝ)) ^ (σQ + θP)) := by
              rw [hsplit]
              field_simp
  -- the two-spike term
  have T4 : Tendsto (fun I : ℕ => ENNReal.ofReal
      (BP / (1 + (I : ℝ)) ^ σP * (I : ℝ) ^ cP *
        (BQ / (1 + (I : ℝ)) ^ σQ * (I : ℝ) ^ cQ) * gaussBandDefectMass K I))
      atTop (nhds 0) := by
    refine tendsto_ofReal_zero_of_le_bandMass (K := K) hK.le (a := cP + cQ) (b := σP + σQ)
      (C := BP * BQ) (by linarith) (by linarith) (fun I => ?_) ?_
    · have := gaussBandDefectMass_nonneg hK.le I
      have h5 : (0 : ℝ) ≤ (I : ℝ) ^ cP := Real.rpow_nonneg (Nat.cast_nonneg I) cP
      have h6 : (0 : ℝ) ≤ (I : ℝ) ^ cQ := Real.rpow_nonneg (Nat.cast_nonneg I) cQ
      have := hHP I
      have := hHQ I
      positivity
    · filter_upwards [eventually_ge_atTop 1] with I hI
      have hI1 : (1 : ℝ) ≤ (I : ℝ) := by exact_mod_cast hI
      have hI0 : (0 : ℝ) < (I : ℝ) := by linarith
      have hc : (I : ℝ) ^ cP * (I : ℝ) ^ cQ = (I : ℝ) ^ (cP + cQ) :=
        (Real.rpow_add hI0 _ _).symm
      have hs : (1 + (I : ℝ)) ^ (σP + σQ) = (1 + (I : ℝ)) ^ σP * (1 + (I : ℝ)) ^ σQ :=
        Real.rpow_add (by positivity) _ _
      rw [hs, ← hc]
      have hp1 : (0 : ℝ) < (1 + (I : ℝ)) ^ σP := Real.rpow_pos_of_pos (by positivity) σP
      have hp2 : (0 : ℝ) < (1 + (I : ℝ)) ^ σQ := Real.rpow_pos_of_pos (by positivity) σQ
      field_simp
      exact le_rfl
  -- assemble
  have hsum := T1.add (T2.add (T3.add T4))
  rw [add_zero, add_zero, add_zero] at hsum
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hsum ε hε, eventually_ge_atTop 2] with I hI hI2
  exact le_trans (tsum_twoPiece_pairing_defect_le hm k p hK hKb hAP (hHP I) hAQ (hHQ I)
    hcP hcQ hθP hθQ (hX I hI2) (hY I hI2)) hI

end

end RHTower
