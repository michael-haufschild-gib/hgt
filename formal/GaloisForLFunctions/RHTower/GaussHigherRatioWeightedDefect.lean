import GaloisForLFunctions.RHTower.GaussRatioWeightedDefect

/-!
# Higher ratio-weighted Gauss translation defects

At propagation depth `q`, normalized Gauss iteration inserts the sampled amplitude ratio to power
`2q` into the squared translation defect.  The conserved `2m`-power component law dominates this
weight exactly when `q+1 ≤ m`.  This module proves the resulting pointwise and summable hierarchy;
the existing ratio-square estimate is its first nontrivial case, while `q=2,m=3` supplies the new
arithmetic input for the first unresolved cubic propagation layer.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-- Higher-power ratio-weighted pointwise defect bound. -/
theorem norm_gaussSampleRatioDefect_sq_mul_ratio_pow_le
    {m q : ℕ} (hq : q + 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (j : ℤ) :
    (‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖) ^ (2 * q) *
        ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
      ≤ 4 + 4 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  set R : ℝ := ‖gaussSampleValue k p ((I : ℤ) + j)‖ /
    ‖gaussSampleValue k p (I : ℤ)‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have htri : ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ≤ R + 1 := by
    rw [gaussSampleRatioDefect]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_gaussSampleRotation]
  have hsq : ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 ≤ 2 * R ^ 2 + 2 := by
    have hnn : 0 ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ := norm_nonneg _
    nlinarith [sq_nonneg (R - 1), htri]
  have hratio := norm_gaussSampleRatio_pow_le hm1 k p hKb I j
  have hqle : 2 * q ≤ 2 * m := by omega
  have hq1le : 2 * q + 2 ≤ 2 * m := by omega
  have hpowq : R ^ (2 * q) ≤ 1 + R ^ (2 * m) := by
    rcases le_or_gt R 1 with h | h
    · have h1 : R ^ (2 * q) ≤ 1 := pow_le_one₀ hR0 h
      exact h1.trans (le_add_of_nonneg_right (pow_nonneg hR0 _))
    · have h1 : R ^ (2 * q) ≤ R ^ (2 * m) := pow_le_pow_right₀ h.le hqle
      linarith
  have hpowq1 : R ^ (2 * q + 2) ≤ 1 + R ^ (2 * m) := by
    rcases le_or_gt R 1 with h | h
    · have h1 : R ^ (2 * q + 2) ≤ 1 := pow_le_one₀ hR0 h
      exact h1.trans (le_add_of_nonneg_right (pow_nonneg hR0 _))
    · have h1 : R ^ (2 * q + 2) ≤ R ^ (2 * m) := pow_le_pow_right₀ h.le hq1le
      linarith
  have hkey : R ^ (2 * q) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
      ≤ 2 * R ^ (2 * q + 2) + 2 * R ^ (2 * q) := by
    calc
      R ^ (2 * q) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
          ≤ R ^ (2 * q) * (2 * R ^ 2 + 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * R ^ (2 * q + 2) + 2 * R ^ (2 * q) := by ring
  calc
    R ^ (2 * q) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
        ≤ 2 * R ^ (2 * q + 2) + 2 * R ^ (2 * q) := hkey
    _ ≤ 2 * (1 + R ^ (2 * m)) + 2 * (1 + R ^ (2 * m)) := by linarith
    _ ≤ 4 + 4 * (K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ)) := by linarith
    _ = 4 + 4 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) := by ring

/-- The depth-`q` ratio-weighted `ℓ²` translation defect. -/
def gaussTranslationL2RatioPowerDefectBound {m : ℕ} (k : Fin m) (p : Nat.Primes)
    (q : ℕ) (A : ℝ) (i : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal
    (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
      ((‖gaussSampleValue k p (i + j)‖ / ‖gaussSampleValue k p i‖) ^ (2 * q) *
        ‖gaussSampleRatioDefect k p j i‖ ^ 2))

/-- Every admissible ratio-power defect vanishes along natural frequencies. -/
theorem tendsto_gaussTranslationL2RatioPowerDefectBound
    {m q : ℕ} (hq : q + 1 ≤ m) (k : Fin m) (p : Nat.Primes) (A : ℝ) :
    Tendsto (fun I : ℕ =>
      gaussTranslationL2RatioPowerDefectBound k p q A (I : ℤ)) atTop (nhds 0) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm1 k p
  refine GaloisForLFunctions.tendsto_tsum_zero_of_dominated
    (F := fun j I => ENNReal.ofReal
      (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
        ((‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖) ^
            (2 * q) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)))
    (G := fun j _ => ENNReal.ofReal ((4 + 8 * K) * A ^ 2) *
      GaloisForLFunctions.intQuadWeight j)
    (H := fun j I => if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (4 * K * A ^ 2 * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ))) else 0)
    ?_ ?_ ?_ ?_
  · intro j
    have hdef := tendsto_gaussSampleRatioDefect_nat hm1 k p j
    have hnorm : Tendsto (fun I : ℕ => ‖gaussSampleRatioDefect k p j (I : ℤ)‖)
        atTop (nhds 0) := by simpa using hdef.norm
    have hratioBound : ∀ I : ℕ,
        ‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖
          ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ + 1 :=
      fun I => norm_gaussSampleRatio_le k p (I : ℤ) j
    have hpow : Tendsto (fun I : ℕ =>
        (‖gaussSampleRatioDefect k p j (I : ℤ)‖ + 1) ^ (2 * q))
        atTop (nhds 1) := by
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      have h := (hnorm.add hone).pow (2 * q)
      simpa using h
    have hsq : Tendsto (fun I : ℕ =>
        ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2) atTop (nhds 0) := by
      simpa using hnorm.pow 2
    have hmaj : Tendsto (fun I : ℕ =>
        (‖gaussSampleRatioDefect k p j (I : ℤ)‖ + 1) ^ (2 * q) *
          ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2) atTop (nhds 0) := by
      simpa using hpow.mul hsq
    have hR : Tendsto (fun I : ℕ =>
        (‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖) ^
            (2 * q) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)
        atTop (nhds 0) := by
      refine squeeze_zero (fun I => by positivity) (fun I => ?_) hmaj
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (hratioBound I) (2 * q)) (by positivity)
    have hmul := hR.const_mul (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2)
    rw [mul_zero] at hmul
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
    simpa [Function.comp_def] using hcont
  · intro j I
    set a : ℕ := j.natAbs with ha
    set n : ℕ := ((I : ℤ) + j).natAbs with hn
    have hbound := norm_gaussSampleRatioDefect_sq_mul_ratio_pow_le hq k p hKb I j
    have hden : (0 : ℝ) < (1 + (a : ℝ)) ^ 2 := by positivity
    have hquad : GaloisForLFunctions.intQuadWeight j =
        ENNReal.ofReal (1 / (1 + (a : ℝ)) ^ 2) := by
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
        ((‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖) ^
            (2 * q) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)
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
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * K) hAsq) hden.le]
      · rw [if_pos ⟨hcase, hn0⟩, hGval,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have hexp : A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 4 * K * (I : ℝ) / (n : ℝ))
            = 4 * A ^ 2 / (1 + (a : ℝ)) ^ 2 +
              4 * K * A ^ 2 * (I : ℝ) / ((1 + (a : ℝ)) ^ 2 * (n : ℝ)) := by
          field_simp
        rw [hexp]
        have h1 : 4 * A ^ 2 / (1 + (a : ℝ)) ^ 2
            ≤ (4 + 8 * K) * A ^ 2 / (1 + (a : ℝ)) ^ 2 := by
          rw [div_le_div_iff₀ hden hden]
          nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * K) hAsq) hden.le]
        linarith
    · rw [if_neg (by simp [hcase]), add_zero, hGval]
      refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
      have hIn : (I : ℝ) ≤ 2 * (n : ℝ) := by
        have : I ≤ 2 * n := by omega
        exact_mod_cast this
      have hratio : 4 * K * (I : ℝ) / (n : ℝ) ≤ 8 * K := by
        rcases Nat.eq_zero_or_pos n with hnzero | hnpos
        · rw [hnzero, Nat.cast_zero, div_zero]
          positivity
        · rw [div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < (n : ℝ))]
          nlinarith [hK.le, hIn]
      have hle : A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 4 * K * (I : ℝ) / (n : ℝ))
          ≤ A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 8 * K) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      refine hle.trans (le_of_eq ?_)
      field_simp
  · intro ε hε
    obtain ⟨S, hS⟩ := GaloisForLFunctions.exists_finset_tsum_compl_intQuadWeight_le
      (C := ENNReal.ofReal ((4 + 8 * K) * A ^ 2)) ENNReal.ofReal_ne_top hε
    exact ⟨S, fun _ => hS⟩
  · have hc : (0 : ℝ) ≤ 4 * K * A ^ 2 := by positivity
    exact GaloisForLFunctions.tendsto_tsum_farBandRatio_zero hc

/-- First unresolved cubic propagation weight: the fourth-ratio defect vanishes at `m = 3`. -/
theorem tendsto_gaussTranslationL2RatioFourthDefectBound
    (k : Fin 3) (p : Nat.Primes) (A : ℝ) :
    Tendsto (fun I : ℕ =>
      gaussTranslationL2RatioPowerDefectBound k p 2 A (I : ℤ)) atTop (nhds 0) := by
  exact tendsto_gaussTranslationL2RatioPowerDefectBound (m := 3) (q := 2) (by omega) k p A

/-- The higher ratio-weighted bound is even in the base frequency. -/
theorem gaussTranslationL2RatioPowerDefectBound_neg
    {m : ℕ} (k : Fin m) (p : Nat.Primes) (q : ℕ) (A : ℝ) (i : ℤ) :
    gaussTranslationL2RatioPowerDefectBound k p q A (-i) =
      gaussTranslationL2RatioPowerDefectBound k p q A i := by
  rw [gaussTranslationL2RatioPowerDefectBound, gaussTranslationL2RatioPowerDefectBound,
    ← (Equiv.neg ℤ).tsum_eq (fun j : ℤ => ENNReal.ofReal
      (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
        ((‖gaussSampleValue k p (i + j)‖ / ‖gaussSampleValue k p i‖) ^ (2 * q) *
          ‖gaussSampleRatioDefect k p j i‖ ^ 2)))]
  refine tsum_congr fun j => ?_
  have hdef : gaussSampleRatioDefect k p j (-i) =
      starRingEnd ℂ (gaussSampleRatioDefect k p (-j) i) := by
    have h := gaussSampleRatioDefect_neg k p (-j) i
    rwa [neg_neg] at h
  have hnum : ‖gaussSampleValue k p (-i + j)‖ =
      ‖gaussSampleValue k p (i + -j)‖ := by
    rw [show -i + j = -(i + -j) by ring, gaussSampleValue_neg, RCLike.norm_conj]
  have hden : ‖gaussSampleValue k p (-i)‖ = ‖gaussSampleValue k p i‖ := by
    rw [gaussSampleValue_neg, RCLike.norm_conj]
  rw [hdef, hnum, hden, RCLike.norm_conj]
  simp [Equiv.neg]

/-- Reflection transports the bound from the absolute frequency. -/
theorem gaussTranslationL2RatioPowerDefectBound_natAbs
    {m : ℕ} (k : Fin m) (p : Nat.Primes) (q : ℕ) (A : ℝ) (i : ℤ) :
    gaussTranslationL2RatioPowerDefectBound k p q A ((i.natAbs : ℤ)) =
      gaussTranslationL2RatioPowerDefectBound k p q A i := by
  rcases Int.natAbs_eq i with h | h
  · rw [← h]
  · have hb := gaussTranslationL2RatioPowerDefectBound_neg k p q A ((i.natAbs : ℤ))
    rw [← h] at hb
    exact hb.symm

/-- The depth-`q` hierarchy holds along every two-sided escaping frequency sequence. -/
theorem tendsto_gaussTranslationL2RatioPowerDefectBound_comp
    {m q : ℕ} (hq : q + 1 ≤ m) (k : Fin m) (p : Nat.Primes) (A : ℝ)
    {ι : ℕ → ℤ} (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      gaussTranslationL2RatioPowerDefectBound k p q A (ι n)) atTop (nhds 0) := by
  have hcomp := (tendsto_gaussTranslationL2RatioPowerDefectBound hq k p A).comp hι
  refine hcomp.congr fun n => ?_
  simp only [Function.comp_apply]
  exact gaussTranslationL2RatioPowerDefectBound_natAbs k p q A (ι n)

end

end RHTower
