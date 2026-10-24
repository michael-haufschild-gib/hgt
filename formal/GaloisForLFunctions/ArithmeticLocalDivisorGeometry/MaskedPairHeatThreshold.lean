import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.MaskedPairHeatCone
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HeatConeEvolution
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.MaskedHeatContactIndex

/-!
# The heat threshold of a centrally masked pair

The admissible heat times form a closed ray. Exact coefficient signs give its inverse
multiplicity bounds, and the middle index identifies the active coefficient at its boundary.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- Dimensionless first heat time with every coefficient nonnegative. -/
def maskedPairHeatThreshold (m : ℕ) : ℝ :=
  sInf {t : ℝ | CoeffNonneg (forwardPolyHeat t (centralMaskedPair 1 m))}

/-- The highest adverse coefficient excludes every nonpositive heat time. -/
theorem centralMaskedPair_heat_time_pos {a t : ℝ} (ha : 0 < a) (m : ℕ)
    (h : CoeffNonneg (forwardPolyHeat (a * t) (centralMaskedPair a m))) : 0 < t := by
  have hc := h (2 * (m + 1))
  rw [centralMaskedPair_heat_coeff_penultimate, mul_nonneg_iff_of_pos_left ha] at hc
  by_contra hn
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (2 * m + 4 : ℝ) * (2 * m + 3) by positivity) (le_of_not_gt hn)
  linarith only [hc, hp]

/-- A universal admissible heat time supplies the nonempty threshold set. -/
theorem maskedPairHeatCone_nonempty (m : ℕ) :
    {t : ℝ | CoeffNonneg (forwardPolyHeat t (centralMaskedPair 1 m))}.Nonempty := by
  refine ⟨1 / (8 * m + 5 : ℝ), ?_⟩
  have he : (8 * m + 5 : ℝ) ≠ 0 := by positivity
  have h := coeffNonneg_centralMaskedPair_heat_of_upper (by norm_num : (0 : ℝ) < 1) m
    (show 1 ≤ (8 * m + 5 : ℝ) * (1 / (8 * m + 5 : ℝ)) by rw [mul_one_div_cancel he])
  simpa only [one_mul] using h

/-- Every admissible heat time pays the lower inverse-multiplicity cost. -/
theorem le_heat_time_of_centralMaskedPair_cone (m : ℕ) {t : ℝ}
    (h : CoeffNonneg (forwardPolyHeat t (centralMaskedPair 1 m))) :
    1 / (8 * m + 10 : ℝ) ≤ t := by
  have hd : 0 < (8 * m + 10 : ℝ) := by positivity
  have ht := centralMaskedPair_heat_time_pos (by norm_num : (0 : ℝ) < 1) m
    (by simpa only [one_mul] using h)
  by_contra hn
  have hsmall : (8 * m + 10 : ℝ) * t < 1 := by
    have hh := (lt_div_iff₀ hd).mp (lt_of_not_ge hn)
    simpa only [mul_comm] using hh
  have hneg := centralMaskedPair_heat_floor_coeff_neg (by norm_num : (0 : ℝ) < 1) ht m hsmall
  simp only [one_mul] at hneg
  exact (not_le_of_gt hneg) (h _)

theorem maskedPairHeatCone_bddBelow (m : ℕ) :
    BddBelow {t : ℝ | CoeffNonneg (forwardPolyHeat t (centralMaskedPair 1 m))} :=
  ⟨1 / (8 * m + 10 : ℝ), fun _ h => le_heat_time_of_centralMaskedPair_cone m h⟩

theorem maskedPairHeatThreshold_mem (m : ℕ) :
    CoeffNonneg (forwardPolyHeat (maskedPairHeatThreshold m) (centralMaskedPair 1 m)) :=
  (isClosed_forwardPolyHeat_cone (centralMaskedPair 1 m)).csInf_mem
    (maskedPairHeatCone_nonempty m) (maskedPairHeatCone_bddBelow m)

/-- The admissible set is exactly the closed ray starting at its first heat time. -/
theorem coeffNonneg_centralMaskedPair_one_iff (m : ℕ) (t : ℝ) :
    CoeffNonneg (forwardPolyHeat t (centralMaskedPair 1 m)) ↔ maskedPairHeatThreshold m ≤ t := by
  constructor
  · exact fun h => csInf_le (maskedPairHeatCone_bddBelow m) h
  · exact fun h => coeffNonneg_forwardPolyHeat_mono _ h (maskedPairHeatThreshold_mem m)

theorem maskedPairHeatThreshold_lower (m : ℕ) :
    1 / (8 * m + 10 : ℝ) ≤ maskedPairHeatThreshold m :=
  le_heat_time_of_centralMaskedPair_cone m (maskedPairHeatThreshold_mem m)

theorem maskedPairHeatThreshold_upper (m : ℕ) :
    maskedPairHeatThreshold m ≤ 1 / (8 * m + 5 : ℝ) := by
  apply (coeffNonneg_centralMaskedPair_one_iff m _).mp
  have he : (8 * m + 5 : ℝ) ≠ 0 := by positivity
  simpa only [one_mul] using coeffNonneg_centralMaskedPair_heat_of_upper
    (by norm_num : (0 : ℝ) < 1) m
    (show 1 ≤ (8 * m + 5 : ℝ) * (1 / (8 * m + 5 : ℝ)) by rw [mul_one_div_cancel he])

theorem maskedPairHeatThreshold_pos (m : ℕ) : 0 < maskedPairHeatThreshold m :=
  (by positivity : 0 < 1 / (8 * m + 10 : ℝ)).trans_le (maskedPairHeatThreshold_lower m)

/-- Each added central multiplicity strictly lowers the full heat threshold. -/
theorem maskedPairHeatThreshold_strictAnti : StrictAnti maskedPairHeatThreshold := by
  intro m n hmn
  have hm : 0 < (8 * m + 10 : ℝ) := by positivity
  have hn : 0 < (8 * n + 5 : ℝ) := by positivity
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hmn
  have hgap : (8 * m + 10 : ℝ) < 8 * n + 5 := by linarith only [hmn']
  have hinv : 1 / (8 * n + 5 : ℝ) < 1 / (8 * m + 10 : ℝ) := by
    apply (lt_div_iff₀ hm).mpr
    rw [show 1 / (8 * n + 5 : ℝ) * (8 * m + 10) = (8 * m + 10) / (8 * n + 5) by ring]
    exact (div_lt_iff₀ hn).mpr (by simpa only [one_mul] using hgap)
  exact (maskedPairHeatThreshold_upper n).trans_lt (hinv.trans_le (maskedPairHeatThreshold_lower m))

/-- Squared pair depth scales the threshold exactly, without changing the multiplicity. -/
theorem coeffNonneg_centralMaskedPair_heat_iff_threshold {a : ℝ} (ha : 0 < a) (m : ℕ) (t : ℝ) :
    CoeffNonneg (forwardPolyHeat (a * t) (centralMaskedPair a m)) ↔ maskedPairHeatThreshold m ≤ t := by
  by_cases ht : 0 < t
  · rw [coeffNonneg_centralMaskedPair_heat_iff ha ht]
    have h := coeffNonneg_centralMaskedPair_heat_iff (by norm_num : (0 : ℝ) < 1) ht m
    simp only [one_mul] at h
    rw [← h, coeffNonneg_centralMaskedPair_one_iff]
  · constructor
    · intro h
      exact (ht (centralMaskedPair_heat_time_pos ha m h)).elim
    · intro h
      exact (ht ((maskedPairHeatThreshold_pos m).trans_le h)).elim

theorem maskedPairHeatThreshold_band (m : ℕ) :
    1 ≤ (8 * m + 10 : ℝ) * maskedPairHeatThreshold m ∧
      (8 * m + 5 : ℝ) * maskedPairHeatThreshold m ≤ 1 := by
  constructor
  · have h := (div_le_iff₀ (show 0 < (8 * m + 10 : ℝ) by positivity)).mp
      (maskedPairHeatThreshold_lower m)
    simpa only [mul_comm] using h
  · have h := (le_div_iff₀ (show 0 < (8 * m + 5 : ℝ) by positivity)).mp
      (maskedPairHeatThreshold_upper m)
    simpa only [mul_comm] using h

theorem maskedHeatIndex_at_threshold_nonneg (m k : ℕ) (hk : k ≤ m + 1) :
    0 ≤ maskedHeatIndex m (maskedPairHeatThreshold m) k := by
  have h := coeffNonneg_centralMaskedPair_heat_iff (by norm_num : (0 : ℝ) < 1)
    (maskedPairHeatThreshold_pos m) m
  simp only [one_mul] at h
  exact h.mp (maskedPairHeatThreshold_mem m) k hk

/-- The first cone contact is exactly the unique zero of the middle index in the bracket. -/
theorem maskedHeatIndex_middle_at_threshold (m : ℕ) :
    maskedHeatIndex m (maskedPairHeatThreshold m) (m / 2) = 0 := by
  have he : 0 < (8 * m + 5 : ℝ) := by positivity
  have hd : 0 < (8 * m + 10 : ℝ) := by positivity
  have hupper : 0 < maskedHeatIndex m (1 / (8 * m + 5 : ℝ)) (m / 2) := by
    apply maskedHeatIndex_pos_of_upper
    rw [mul_one_div_cancel he.ne']
  have hcont : Continuous (fun t : ℝ => maskedHeatIndex m t (m / 2)) := by
    unfold maskedHeatIndex
    fun_prop
  have hab := (maskedPairHeatThreshold_lower m).trans (maskedPairHeatThreshold_upper m)
  obtain ⟨r, ⟨hrlo, hrhi⟩, hrzero⟩ := intermediate_value_Icc hab hcont.continuousOn
    ⟨(maskedHeatIndex_middle_neg_at_lower m).le, hupper.le⟩
  have hrpos : 0 < r := (by positivity : 0 < 1 / (8 * m + 10 : ℝ)).trans_le hrlo
  have hrlo' : 1 ≤ (8 * m + 10 : ℝ) * r := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hrlo
  have hrhi' : (8 * m + 5 : ℝ) * r ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ he).mp hrhi
  have hrcone : CoeffNonneg (forwardPolyHeat r (centralMaskedPair 1 m)) := by
    have h := (coeffNonneg_centralMaskedPair_heat_iff (by norm_num : (0 : ℝ) < 1) hrpos m).mpr
      ((maskedHeatIndex_all_iff_middle m hrlo' hrhi').mpr hrzero.ge)
    simpa only [one_mul] using h
  have hτr : maskedPairHeatThreshold m ≤ r := (coeffNonneg_centralMaskedPair_one_iff m r).mp hrcone
  have heq : maskedPairHeatThreshold m = r := by
    apply le_antisymm hτr
    apply le_of_not_gt
    intro hlt
    have hneg := maskedHeatIndex_middle_strictMono m (maskedPairHeatThreshold_band m).1
      (maskedPairHeatThreshold_band m).2 hlt
    rw [hrzero] at hneg
    exact (not_le_of_gt hneg) (maskedHeatIndex_at_threshold_nonneg m (m / 2) (by omega))
  rw [heq]
  exact hrzero

/-- Every other index is strictly positive at first contact. -/
theorem maskedHeatIndex_at_threshold_pos (m k : ℕ) (hk : k ≠ m / 2) :
    0 < maskedHeatIndex m (maskedPairHeatThreshold m) k := by
  have h := maskedHeatIndex_middle_strict_min m k (maskedPairHeatThreshold_band m).1
    (maskedPairHeatThreshold_band m).2 hk
  rwa [maskedHeatIndex_middle_at_threshold] at h

/-- The exact active even degree grows with the central multiplicity. -/
theorem centralMaskedPair_heat_contact {a : ℝ} (ha : 0 < a) (m : ℕ) :
    (forwardPolyHeat (a * maskedPairHeatThreshold m) (centralMaskedPair a m)).coeff
      (m + 2 + m % 2) = 0 := by
  rw [← maskedPair_contact_degree]
  exact (centralMaskedPair_heat_coeff_index_zero_iff ha (maskedPairHeatThreshold_pos m)
    m (m / 2) (by omega)).mpr (maskedHeatIndex_middle_at_threshold m)

/-- Among the nonleading even coefficients, exactly the middle index is a contact. -/
theorem centralMaskedPair_heat_contact_iff {a : ℝ} (ha : 0 < a) (m k : ℕ) (hk : k ≤ m + 1) :
    (forwardPolyHeat (a * maskedPairHeatThreshold m) (centralMaskedPair a m)).coeff
      (2 * (m + 1 - k)) = 0 ↔ k = m / 2 := by
  rw [centralMaskedPair_heat_coeff_index_zero_iff ha (maskedPairHeatThreshold_pos m) m k hk]
  constructor
  · intro h
    by_contra hne
    exact (maskedHeatIndex_at_threshold_pos m k hne).ne' h
  · rintro rfl
    exact maskedHeatIndex_middle_at_threshold m

/-- Among all even coefficients through the degree, exactly one vanishes at first contact. -/
theorem centralMaskedPair_heat_even_contact_iff {a : ℝ} (ha : 0 < a) (m j : ℕ) (hj : j ≤ m + 2) :
    (forwardPolyHeat (a * maskedPairHeatThreshold m) (centralMaskedPair a m)).coeff (2 * j) = 0 ↔
      2 * j = m + 2 + m % 2 := by
  by_cases htop : j = m + 2
  · subst j
    rw [centralMaskedPair_heat_coeff_leading]
    constructor
    · intro h
      norm_num at h
    · intro h
      omega
  · have h := centralMaskedPair_heat_contact_iff ha m (m + 1 - j) (by omega)
    rw [show m + 1 - (m + 1 - j) = j by omega] at h
    rw [h]
    have hd := maskedPair_contact_degree m
    omega

/-- The constant coefficient is strictly positive at the threshold for every multiplicity. -/
theorem centralMaskedPair_heat_constant_pos_at_threshold {a : ℝ} (ha : 0 < a) (m : ℕ) :
    0 < (forwardPolyHeat (a * maskedPairHeatThreshold m) (centralMaskedPair a m)).coeff 0 := by
  have h := (centralMaskedPair_heat_coeff_index_pos_iff ha (maskedPairHeatThreshold_pos m)
    m (m + 1) (by omega)).mpr (maskedHeatIndex_at_threshold_pos m (m + 1) (by omega))
  simpa only [Nat.sub_self, mul_zero] using h

private theorem larger_index_root {B C k t : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hbranch : k + 1 < C * t)
    (hzero : k * (k + 1) - 2 * B * (k + 1) * t + B * C * t ^ 2 = 0) :
    t = (B * (k + 1) + Real.sqrt (B * (k + 1) * (B - (C - B) * k))) / (B * C) := by
  have hsq : (B * C * t - B * (k + 1)) ^ 2 = B * (k + 1) * (B - (C - B) * k) := by
    linear_combination B * C * hzero
  have hpos : 0 < B * C * t - B * (k + 1) := by
    have h := mul_pos hB (sub_pos.mpr hbranch)
    nlinarith only [h]
  have hsqrt : Real.sqrt (B * (k + 1) * (B - (C - B) * k)) = B * C * t - B * (k + 1) := by
    rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_pos hpos]
  rw [eq_div_iff (mul_ne_zero hB.ne' hC.ne'), hsqrt]
  ring

/-- The full threshold has an exact radical formula with the integer middle index. -/
theorem maskedPairHeatThreshold_eq (m : ℕ) :
    let B : ℝ := (2 * m + 2 : ℝ) * (2 * m + 1)
    let C : ℝ := (2 * m + 4 : ℝ) * (2 * m + 3)
    let h : ℝ := (m / 2 : ℕ)
    maskedPairHeatThreshold m =
      (B * (h + 1) + Real.sqrt (B * (h + 1) * (B - (C - B) * h))) / (B * C) := by
  dsimp only
  apply larger_index_root (by positivity) (by positivity)
  · have hl := (maskedHeatIndex_middle_location m (maskedPairHeatThreshold_band m).1
      (maskedPairHeatThreshold_band m).2).1
    have hd := (maskedPairHeatThreshold_band m).1
    nlinarith only [hl, hd]
  · exact maskedHeatIndex_middle_at_threshold m

private theorem tendsto_heat_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => (8 * m : ℝ) / (8 * m + c)) atTop (𝓝 1) := by
  refine (tendsto_natCast_div_add_atTop (c / 8)).congr fun m => ?_
  have hden : (m : ℝ) + c / 8 ≠ 0 := by positivity
  have hden' : (8 * m : ℝ) + c ≠ 0 := by positivity
  field_simp <;> ring

/-- The full all-order heat threshold has inverse multiplicity scale with leading constant
one eighth, in contrast to the inverse-square scale of the highest adverse coefficient. -/
theorem tendsto_maskedPairHeatThreshold :
    Tendsto (fun m : ℕ => (8 * m : ℝ) * maskedPairHeatThreshold m) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_heat_ratio (by norm_num : (0 : ℝ) < 10))
    (tendsto_heat_ratio (by norm_num : (0 : ℝ) < 5))
  · intro m
    have h := mul_le_mul_of_nonneg_left (maskedPairHeatThreshold_lower m)
      (show 0 ≤ (8 * m : ℝ) by positivity)
    simpa only [one_div, div_eq_mul_inv, mul_assoc] using h
  · intro m
    have h := mul_le_mul_of_nonneg_left (maskedPairHeatThreshold_upper m)
      (show 0 ≤ (8 * m : ℝ) by positivity)
    simpa only [one_div, div_eq_mul_inv, mul_assoc] using h

theorem coeffNonneg_centralMaskedPair_of_nonpos {a : ℝ} (ha : a ≤ 0) (m : ℕ) :
    CoeffNonneg (centralMaskedPair a m) := by
  have hX (n : ℕ) : CoeffNonneg ((X : ℝ[X]) ^ n) := by
    intro k
    simp only [coeff_X_pow]
    split_ifs <;> norm_num
  rw [centralMaskedPair_eq]
  exact ((hX _).add ((hX _).C_mul (by linarith only [ha]))).add ((hX _).C_mul (sq_nonneg a))

/-- Complete nonnegative-time classification for every real pair parameter, including the
central degeneration. No zero-location or coefficient premise is required. -/
theorem centralMaskedPair_heat_cone_classification (a s : ℝ) (m : ℕ) :
    (0 ≤ s ∧ CoeffNonneg (forwardPolyHeat s (centralMaskedPair a m))) ↔
      max a 0 * maskedPairHeatThreshold m ≤ s := by
  by_cases ha : 0 < a
  · rw [max_eq_left ha.le]
    have hscale : a * (s / a) = s := by field_simp
    constructor
    · rintro ⟨_, h⟩
      have hh := (coeffNonneg_centralMaskedPair_heat_iff_threshold ha m (s / a)).mp
        (by rwa [hscale])
      have hmul := (le_div_iff₀ ha).mp hh
      simpa only [mul_comm] using hmul
    · intro h
      refine ⟨(mul_pos ha (maskedPairHeatThreshold_pos m)).le.trans h, ?_⟩
      have hdiv : maskedPairHeatThreshold m ≤ s / a := (le_div_iff₀ ha).mpr
        (by simpa only [mul_comm] using h)
      have hc := (coeffNonneg_centralMaskedPair_heat_iff_threshold ha m (s / a)).mpr hdiv
      rwa [hscale] at hc
  · rw [max_eq_right (le_of_not_gt ha), zero_mul]
    constructor
    · exact And.left
    · intro hs
      exact ⟨hs, coeffNonneg_forwardPolyHeat (coeffNonneg_centralMaskedPair_of_nonpos (le_of_not_gt ha) m) hs⟩
end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry

#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.maskedPairHeatThreshold_eq
#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.centralMaskedPair_heat_cone_classification
#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.centralMaskedPair_heat_even_contact_iff
#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.tendsto_maskedPairHeatThreshold
