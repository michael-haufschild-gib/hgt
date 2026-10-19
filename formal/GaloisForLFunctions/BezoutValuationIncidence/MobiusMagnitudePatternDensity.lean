import GaloisForLFunctions.BezoutValuationIncidence.MobiusMagnitudePeriodicApproximation
import GaloisForLFunctions.RHTower.Sieve.ResiduePartitionCount
import Mathlib.Data.Nat.Periodic
import Mathlib.Topology.MetricSpace.Cauchy
import GaloisForLFunctions.RHTower.SelbergCompactTestApproximation

/-!
# Natural densities of shifted complementary-band magnitudes

The finite-prime periodic model and its square-divisor mismatch bound give
unconditional frequencies for every fixed finite magnitude pattern. Existing
`SelbergCompactTestApproximation.exists_limit_of_eventual_approximation`
transfers convergence from constant finite-residue approximants. The limiting
probabilities have finite integer support, total mass one, and explicit
finite-residue error at most the number of shifts divided by the prime cutoff.
This leaf supplies the fixed-band law; transport to the varying source cutoff
is a separate boundary-counting argument.
-/

open Filter Topology Finset
open RHTower.Sieve
open scoped BigOperators Classical

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false
variable {m : ℕ}

/-- The literal frequency numerator of a fixed complementary-band magnitude pattern. -/
def moebiusBandPatternCount (j X : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) : ℕ :=
  ((Icc 1 X).filter (fun n => ∀ i, moebiusBandMagnitude j (n + h i) = a i)).card

/-- The finite-prime frequency numerator of the same shifted pattern. -/
def moebiusLocalBandPatternCount (j R X : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) : ℕ :=
  ((Icc 1 X).filter (fun n => ∀ i, moebiusLocalBandMagnitude j R (n + h i) = a i)).card

/-- The exact finite-residue probability of a shifted local magnitude pattern. -/
def moebiusLocalBandPatternDensity (j R : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) : ℝ :=
  (((range (moebiusLocalBandPeriod j R)).filter
    (fun n => ∀ i, moebiusLocalBandMagnitude j R (n + h i) = a i)).card : ℝ) /
      moebiusLocalBandPeriod j R

private theorem local_pattern_periodic (j R : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    Function.Periodic (fun n => ∀ i, moebiusLocalBandMagnitude j R (n + h i) = a i)
      (moebiusLocalBandPeriod j R) := by
  intro n
  have heq (i : Fin m) :
      moebiusLocalBandMagnitude j R (n + moebiusLocalBandPeriod j R + h i) =
        moebiusLocalBandMagnitude j R (n + h i) := by
    simpa only [Nat.add_right_comm] using moebiusLocalBandMagnitude_periodic j R (n + h i)
  apply propext
  simp only [heq]

private theorem periodic_pattern_count_error {T : ℕ} (hT : 0 < T) (X : ℕ)
    (P : ℕ → Prop) (hP : Function.Periodic P T) :
    |(((Icc 1 X).filter P).card : ℝ) -
      (((range T).filter P).card : ℝ) / T * X| ≤ T := by
  classical
  let S := (range T).filter P
  have hcongr : ∀ u v : ℕ, u % T = v % T → (P u ↔ P v) := by
    intro u v huv
    rw [← hP.map_mod_nat u, ← hP.map_mod_nat v, huv]
  have hs := card_filter_eq_sum_residues hT X P hcongr
  have hcast : (((Icc 1 X).filter P).card : ℝ) =
      ∑ r ∈ S, (((Icc 1 X).filter (fun n => n % T = r)).card : ℝ) := by
    exact_mod_cast hs
  have hmean : (S.card : ℝ) / T * X = ∑ _r ∈ S, (X : ℝ) / T := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hcast]
  change |(∑ r ∈ S, _) - (S.card : ℝ) / T * X| ≤ T
  rw [hmean, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ S, |(((Icc 1 X).filter (fun n => n % T = r)).card : ℝ) - (X : ℝ) / T| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hu := card_residue_class_le hT X r
      have hl := card_residue_class_ge hT X (mem_range.mp (mem_filter.mp hr).1)
      rw [abs_le]
      constructor <;> linarith only [hu, hl]
    _ = S.card := by simp
    _ ≤ T := by
      exact_mod_cast ((Finset.card_le_card (Finset.filter_subset P (range T))).trans_eq
        (Finset.card_range T))

private theorem pattern_count_difference_le (j R X : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    |(moebiusBandPatternCount j X h a : ℝ) - moebiusLocalBandPatternCount j R X h a| ≤
      (((Icc 1 X).filter (fun n => ∃ i : Fin m,
        moebiusBandMagnitude j (n + h i) ≠ moebiusLocalBandMagnitude j R (n + h i))).card : ℝ) := by
  have hb : (moebiusBandPatternCount j X h a : ℝ) =
      ∑ n ∈ Icc 1 X, if ∀ i, moebiusBandMagnitude j (n + h i) = a i then (1 : ℝ) else 0 := by
    simp only [Finset.sum_boole, moebiusBandPatternCount]
  have hl : (moebiusLocalBandPatternCount j R X h a : ℝ) =
      ∑ n ∈ Icc 1 X, if ∀ i, moebiusLocalBandMagnitude j R (n + h i) = a i then (1 : ℝ) else 0 := by
    simp only [Finset.sum_boole, moebiusLocalBandPatternCount]
  rw [hb, hl, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc 1 X, if ∃ i : Fin m,
        moebiusBandMagnitude j (n + h i) ≠ moebiusLocalBandMagnitude j R (n + h i)
          then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hbad : ∃ i : Fin m,
        moebiusBandMagnitude j (n + h i) ≠ moebiusLocalBandMagnitude j R (n + h i)
      · rw [if_pos hbad]
        split_ifs <;> norm_num
      · rw [if_neg hbad]
        push Not at hbad
        simp only [hbad, sub_self, abs_zero, le_refl]
    _ = _ := by simp only [Finset.sum_boole]

/-- Finite-residue probabilities approximate every shifted band pattern with explicit error. -/
theorem moebiusBandPatternCount_local_error (R : ℕ+) (j : Fin ((R : ℕ) + 1))
    (X : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    |(moebiusBandPatternCount j X h a : ℝ) - (X : ℝ) * moebiusLocalBandPatternDensity j R h a| ≤
      (∑ i : Fin m, ((X + h i : ℕ) : ℝ) / R) + moebiusLocalBandPeriod j R := by
  have hT : 0 < moebiusLocalBandPeriod j R := by
    unfold moebiusLocalBandPeriod
    exact Nat.mul_pos (Nat.factorial_pos _) (pow_pos (primorial_pos _) _)
  have hper := periodic_pattern_count_error hT X
    (fun n => ∀ i, moebiusLocalBandMagnitude j R (n + h i) = a i)
      (local_pattern_periodic j R h a)
  have hper' : |(moebiusLocalBandPatternCount j R X h a : ℝ) -
      moebiusLocalBandPatternDensity j R h a * X| ≤ moebiusLocalBandPeriod j R := by
    unfold moebiusLocalBandPatternCount moebiusLocalBandPatternDensity
    convert hper using 1
    congr 4
    · ext n
      simp only [Finset.mem_filter]
    · congr 2
      ext n
      simp only [Finset.mem_filter]
  have hdiff := (pattern_count_difference_le (j : ℕ) R X h a).trans
    (moebiusBandMagnitude_disagreement_count_le R j m X h)
  calc
    _ ≤ |(moebiusBandPatternCount j X h a : ℝ) - moebiusLocalBandPatternCount j R X h a| +
        |(moebiusLocalBandPatternCount j R X h a : ℝ) -
          (X : ℝ) * moebiusLocalBandPatternDensity j R h a| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hdiff (by simpa only [mul_comm] using hper')

private theorem pattern_frequency_local_error (R : ℕ+) (j : Fin ((R : ℕ) + 1))
    (X : ℕ+) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    |(moebiusBandPatternCount j X h a : ℝ) / X - moebiusLocalBandPatternDensity j R h a| ≤
      (m : ℝ) / R + ((∑ i : Fin m, (h i : ℝ) / R) + moebiusLocalBandPeriod j R) / X := by
  have hX : (0 : ℝ) < X := by exact_mod_cast X.pos
  have he := moebiusBandPatternCount_local_error R j X h a
  have he' := (div_le_div_iff_of_pos_right hX).mpr he
  have hsum : (∑ i : Fin m, (((X : ℕ) + h i : ℕ) : ℝ) / R) =
      (m : ℝ) * X / R + ∑ i : Fin m, (h i : ℝ) / R := by
    simp only [Nat.cast_add, add_div, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum] at he'
  have hleft : |(moebiusBandPatternCount j X h a : ℝ) -
      (X : ℝ) * moebiusLocalBandPatternDensity j R h a| / X =
      |(moebiusBandPatternCount j X h a : ℝ) / X -
        moebiusLocalBandPatternDensity j R h a| := by
    calc
      _ = |((moebiusBandPatternCount j X h a : ℝ) -
          (X : ℝ) * moebiusLocalBandPatternDensity j R h a) / X| := by
        rw [abs_div, abs_of_pos hX]
      _ = _ := by
        congr 1
        field_simp [ne_of_gt hX]
  rw [hleft] at he'
  exact he'.trans_eq (by field_simp [ne_of_gt hX]; ring)

/-- Limiting probability of an arbitrary finite shifted band-magnitude pattern. -/
def moebiusBandPatternDensity (j : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) : ℝ :=
  atTop.limUnder (fun X : ℕ => (moebiusBandPatternCount j X h a : ℝ) / X)

/-- Every finite shifted band-magnitude pattern has an unconditional natural density. -/
theorem tendsto_moebiusBandPatternFrequency (j : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    Tendsto (fun X : ℕ => (moebiusBandPatternCount j X h a : ℝ) / X) atTop
      (𝓝 (moebiusBandPatternDensity j h a)) := by
  apply tendsto_nhds_limUnder
  apply GaloisForLFunctions.RHTower.SelbergCompactTestApproximation.exists_limit_of_eventual_approximation
  intro ε hε
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)).comp
    (tendsto_add_atTop_nat (j + 1))
  obtain ⟨k, hk⟩ := (hsmall.eventually (gt_mem_nhds hε3)).exists
  let R : ℕ+ := ⟨k + (j + 1), by omega⟩
  let jR : Fin ((R : ℕ) + 1) := ⟨j, by dsimp [R]; omega⟩
  have hR : (m : ℝ) / R < ε / 3 := hk
  let C : ℝ := (∑ i : Fin m, (h i : ℝ) / R) + moebiusLocalBandPeriod j R
  refine ⟨fun _ => moebiusLocalBandPatternDensity j R h a,
    moebiusLocalBandPatternDensity j R h a, tendsto_const_nhds, ?_⟩
  have htail := (tendsto_const_div_atTop_nhds_zero_nat C).eventually (gt_mem_nhds hε3)
  filter_upwards [htail, eventually_ge_atTop 1] with X htail hX
  have he := pattern_frequency_local_error R jR ⟨X, by omega⟩ h a
  change |(moebiusBandPatternCount j X h a : ℝ) / X -
    moebiusLocalBandPatternDensity j R h a| ≤ (m : ℝ) / R + C / X at he
  rw [Real.norm_eq_abs]
  linarith

/-- The complete pattern density is approximated by a finite residue count with error m/R. -/
theorem moebiusBandPatternDensity_local_error (R : ℕ+) (j : Fin ((R : ℕ) + 1))
    (h : Fin m → ℕ) (a : Fin m → ℝ) :
    |moebiusBandPatternDensity j h a - moebiusLocalBandPatternDensity j R h a| ≤
      (m : ℝ) / R := by
  let C : ℝ := (∑ i : Fin m, (h i : ℝ) / R) + moebiusLocalBandPeriod j R
  have hleft := ((tendsto_moebiusBandPatternFrequency j h a).sub_const
    (moebiusLocalBandPatternDensity j R h a)).abs
  have hright : Tendsto (fun X : ℕ => (m : ℝ) / R + C / X) atTop
      (𝓝 ((m : ℝ) / R)) := by
    simpa only [add_zero] using (tendsto_const_div_atTop_nhds_zero_nat C).const_add ((m : ℝ) / R)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop 1] with X hX
  exact pattern_frequency_local_error R j ⟨X, by omega⟩ h a

/-- Every band-pattern probability is nonnegative. -/
theorem moebiusBandPatternDensity_nonneg (j : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    0 ≤ moebiusBandPatternDensity j h a := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_moebiusBandPatternFrequency j h a)
  exact Eventually.of_forall fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Every band-pattern probability is at most one. -/
theorem moebiusBandPatternDensity_le_one (j : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    moebiusBandPatternDensity j h a ≤ 1 := by
  apply le_of_tendsto (tendsto_moebiusBandPatternFrequency j h a)
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [div_le_iff₀ hXr, one_mul]
  unfold moebiusBandPatternCount
  exact_mod_cast ((Finset.card_le_card (Finset.filter_subset _ (Icc 1 X))).trans_eq (by simp))

/-- Enlarging the prime cutoff recovers the complete finite-pattern distribution. -/
theorem tendsto_moebiusLocalBandPatternDensity (j : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    Tendsto (fun R : ℕ => moebiusLocalBandPatternDensity j R h a) atTop
      (𝓝 (moebiusBandPatternDensity j h a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)).eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, eventually_ge_atTop (j + 1)] with R hR hj
  have he := moebiusBandPatternDensity_local_error ⟨R, by omega⟩
    ⟨j, by change j < R + 1; omega⟩ h a
  rw [Real.dist_eq, abs_sub_comm]
  exact he.trans_lt hR

/-- Band magnitudes belong to the finite integer alphabet from zero through the band index. -/
theorem moebiusBandMagnitude_mem_finite (j n : ℕ) :
    ∃ k : Fin (j + 1), moebiusBandMagnitude j n = ((k : ℕ) : ℝ) := by
  let z : ℤ := ∑ q ∈ Icc 1 j, if q ∣ n then (ArithmeticFunction.moebius (n / q) : ℤ) else 0
  have hz : moebiusBandMagnitude j n = |(z : ℝ)| := by
    simp [moebiusBandMagnitude, z, moebiusReal]
  have hb : moebiusBandMagnitude j n ≤ j := by
    unfold moebiusBandMagnitude
    calc
      _ ≤ ∑ q ∈ Icc 1 j, |if q ∣ n then moebiusReal (n / q) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ Icc 1 j, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro q _
        split_ifs
        · unfold moebiusReal
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n / q)
        · norm_num
      _ = j := by simp
  have ha : (z.natAbs : ℝ) = moebiusBandMagnitude j n := by
    rw [hz, Nat.cast_natAbs, Int.cast_abs]
  have hk : z.natAbs ≤ j := by exact_mod_cast (ha ▸ hb)
  exact ⟨⟨z.natAbs, by omega⟩, ha.symm⟩

private theorem sum_band_pattern_counts (j X : ℕ) (h : Fin m → ℕ) :
    ∑ a : Fin m → Fin (j + 1), moebiusBandPatternCount j X h (fun i => ((a i : ℕ) : ℝ)) = X := by
  have hone (n : ℕ) :
      ∑ a : Fin m → Fin (j + 1),
        (if ∀ i, moebiusBandMagnitude j (n + h i) = ((a i : ℕ) : ℝ) then 1 else 0) = (1 : ℕ) := by
    choose b hb using fun i : Fin m => moebiusBandMagnitude_mem_finite j (n + h i)
    have he (a : Fin m → Fin (j + 1)) :
        (∀ i, moebiusBandMagnitude j (n + h i) = ((a i : ℕ) : ℝ)) ↔ b = a := by
      constructor
      · intro ha
        funext i
        apply Fin.ext
        exact_mod_cast ((hb i).symm.trans (ha i))
      · rintro rfl
        exact hb
    simp only [he, Fintype.sum_ite_eq]
  have hb (a : Fin m → Fin (j + 1)) :
      moebiusBandPatternCount j X h (fun i => ((a i : ℕ) : ℝ)) =
        ∑ n ∈ Icc 1 X, if ∀ i, moebiusBandMagnitude j (n + h i) = ((a i : ℕ) : ℝ)
          then (1 : ℕ) else 0 := by
    simp only [Finset.sum_boole, moebiusBandPatternCount, Nat.cast_id]
  simp_rw [hb]
  rw [Finset.sum_comm]
  simp only [hone, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, Nat.cast_id]

/-- The finitely many magnitude-pattern probabilities have total mass one. -/
theorem sum_moebiusBandPatternDensity (j : ℕ) (h : Fin m → ℕ) :
    ∑ a : Fin m → Fin (j + 1), moebiusBandPatternDensity j h (fun i => ((a i : ℕ) : ℝ)) = 1 := by
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin m → Fin (j + 1)))
    (fun a _ => tendsto_moebiusBandPatternFrequency j h (fun i => ((a i : ℕ) : ℝ)))
  have he : (fun X : ℕ => ∑ a : Fin m → Fin (j + 1),
      (moebiusBandPatternCount j X h (fun i => ((a i : ℕ) : ℝ)) : ℝ) / X) =ᶠ[atTop]
        (fun _ => 1) := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    rw [← Finset.sum_div]
    have hcount : (∑ a : Fin m → Fin (j + 1),
        (moebiusBandPatternCount j X h (fun i => ((a i : ℕ) : ℝ)) : ℝ)) = X := by
      exact_mod_cast sum_band_pattern_counts j X h
    rw [hcount, div_self (by exact_mod_cast (show X ≠ 0 by omega))]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

/-- Every pattern outside the finite nonnegative integer alphabet has zero density. -/
theorem moebiusBandPatternDensity_support (j : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    moebiusBandPatternDensity j h a = 0 ∨
      ∃ b : Fin m → Fin (j + 1), ∀ i, a i = ((b i : ℕ) : ℝ) := by
  by_cases ha : ∃ b : Fin m → Fin (j + 1), ∀ i, a i = ((b i : ℕ) : ℝ)
  · exact Or.inr ha
  left
  have hcount (X : ℕ) : moebiusBandPatternCount j X h a = 0 := by
    unfold moebiusBandPatternCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hpat := (Finset.mem_filter.mp hn).2
    choose b hb using fun i : Fin m => moebiusBandMagnitude_mem_finite j (n + h i)
    exact ha ⟨b, fun i => (hpat i).symm.trans (hb i)⟩
  have hz : Tendsto (fun X : ℕ => (moebiusBandPatternCount j X h a : ℝ) / X)
      atTop (𝓝 0) := by simpa only [hcount, Nat.cast_zero, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique (tendsto_moebiusBandPatternFrequency j h a) hz

end
end GaloisForLFunctions.BezoutValuationIncidence
