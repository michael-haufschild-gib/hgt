import GaloisForLFunctions.RHTower.ChronologicalSelbergTaperEnergy
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovScaledKernels

/-!
# A bounded squareful tail for harmonic charge correction

Multiples of four in the outer half of a row have zero Möbius coefficient.
Their indicator has harmonic charge bounded below and Selberg energy at most
a constant times `1 + log N`. It therefore provides unused coefficient slots
for correcting a logarithmic taper's small harmonic charge.
-/

open Finset
open scoped BigOperators

namespace RHTower

open Sieve GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- Indicator of the multiples of four in the outer half of the row. -/
def squarefulTailMask (N d : ℕ) : ℝ :=
  if d ∈ (Finset.Ioc (N / 2) N).filter (fun k => 4 ∣ k) then 1 else 0

theorem squarefulTailMask_nonneg (N d : ℕ) : 0 ≤ squarefulTailMask N d := by
  unfold squarefulTailMask
  split_ifs <;> norm_num

theorem squarefulTailMask_le_one (N d : ℕ) : squarefulTailMask N d ≤ 1 := by
  unfold squarefulTailMask
  split_ifs <;> norm_num

theorem squarefulTailMask_eq_zero_of_le_half {N d : ℕ} (hd : d ≤ N / 2) :
    squarefulTailMask N d = 0 := by
  simp [squarefulTailMask, Finset.mem_filter, Finset.mem_Ioc, not_lt.mpr hd]

theorem squarefulTailMask_eq_zero_of_lt {N d : ℕ} (hd : N < d) :
    squarefulTailMask N d = 0 := by
  simp [squarefulTailMask, Finset.mem_filter, Finset.mem_Ioc, not_le.mpr hd]

theorem moebius_eq_zero_of_squarefulTailMask_ne_zero {N d : ℕ}
    (hd : squarefulTailMask N d ≠ 0) : (ArithmeticFunction.moebius d : ℝ) = 0 := by
  have hmem : d ∈ (Finset.Ioc (N / 2) N).filter (fun k => 4 ∣ k) := by
    by_contra h
    simp [squarefulTailMask, h] at hd
  have hfour := (Finset.mem_filter.mp hmem).2
  have hnsq : ¬ Squarefree d := by
    intro hsf
    have hunit := hsf 2 (by simpa using hfour : 2 * 2 ∣ d)
    norm_num [Nat.isUnit_iff] at hunit
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]

theorem sum_squarefulTailMask_div_eq (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, squarefulTailMask N d / d) =
      ∑ d ∈ (Finset.Ioc (N / 2) N).filter (fun k => 4 ∣ k), 1 / (d : ℝ) := by
  let t := (Finset.Ioc (N / 2) N).filter (fun k => 4 ∣ k)
  have ht : t ⊆ Finset.Icc 1 N := by
    intro d hd
    have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have hfilter : (Finset.Icc 1 N).filter (fun d => d ∈ t) = t := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨ht h, h⟩⟩
  calc
    _ = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∈ t), 1 / (d : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      change (if d ∈ t then 1 else 0) / (d : ℝ) = _
      split_ifs <;> simp
    _ = _ := by rw [hfilter]

/-- A fixed amount of harmonic charge is available in squareful tail slots. -/
theorem one_div_sixteen_le_squarefulTailMask_charge {N : ℕ} (hN : 16 ≤ N) :
    (1 : ℝ) / 16 ≤ ∑ d ∈ Finset.Icc 1 N, squarefulTailMask N d / d := by
  rw [sum_squarefulTailMask_div_eq]
  let t := (Finset.Ioc (N / 2) N).filter (fun k => 4 ∣ k)
  have hcount := sum_filter_dvd_Ioc_eq_sum_scaled
    (e := 4) (L := N / 2) (U := N) (by norm_num) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc,
    Nat.div_div_eq_div_mul] at hcount
  norm_num at hcount
  change t.card = N / 4 - N / 8 at hcount
  have hnat : N ≤ 16 * t.card := by rw [hcount]; omega
  have hcard : (N : ℝ) / 16 ≤ t.card := by
    have h : (N : ℝ) ≤ 16 * (t.card : ℝ) := by exact_mod_cast hnat
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  calc
    (1 : ℝ) / 16 = ((N : ℝ) / 16) * (1 / N) := by field_simp
    _ ≤ (t.card : ℝ) * (1 / N) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ _d ∈ t, 1 / (N : ℝ) := by simp
    _ ≤ ∑ d ∈ t, 1 / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdL, hdN⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
      apply one_div_le_one_div_of_le
      · exact_mod_cast (by omega : 0 < d)
      · exact_mod_cast hdN

/-- The multiples coordinates of the squareful tail decay as reciprocals. -/
theorem selbergMultiplesCoord_squarefulTailMask_le {N e : ℕ}
    (hN : 2 ≤ N) (he : 0 < e) :
    0 ≤ selbergMultiplesCoord N (squarefulTailMask N) e ∧
      selbergMultiplesCoord N (squarefulTailMask N) e ≤ 3 / (e : ℝ) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hL : 1 ≤ N / 2 := by omega
  have hL0 : (0 : ℝ) < (N / 2 : ℕ) := by exact_mod_cast hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  constructor
  · unfold selbergMultiplesCoord
    exact Finset.sum_nonneg fun d _ => div_nonneg (squarefulTailMask_nonneg N d) (Nat.cast_nonneg d)
  let s := (Finset.Icc 1 (N / e)).filter (fun k : ℕ => N / 2 < e * k)
  have hs : ∀ k ∈ s, 0 < k ∧ ((N / 2 : ℕ) : ℝ) / e < k ∧
      (k : ℝ) ≤ (N : ℝ) / e := by
    intro k hk
    obtain ⟨hkI, hkL⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hkI
    refine ⟨hk1, (div_lt_iff₀ he0).mpr ?_, ?_⟩
    · exact_mod_cast (by simpa [Nat.mul_comm] using hkL : N / 2 < k * e)
    · exact (by exact_mod_cast hkN : (k : ℝ) ≤ (N / e : ℕ)).trans (Nat.cast_div_le)
  have hwindow := sum_one_div_log_window_le (div_pos hL0 he0)
    (div_le_div_of_nonneg_right (by exact_mod_cast Nat.div_le_self N 2) he0.le) hs
  have hratio : ((N : ℝ) / e) / (((N / 2 : ℕ) : ℝ) / e) =
      (N : ℝ) / (N / 2 : ℕ) := by field_simp
  rw [hratio] at hwindow
  have hratio3 : (N : ℝ) / (N / 2 : ℕ) ≤ 3 := by
    apply (div_le_iff₀ hL0).mpr
    exact_mod_cast (by omega : N ≤ 3 * (N / 2))
  have hlog := Real.log_le_sub_one_of_pos (div_pos hN0 hL0)
  have hwindow3 : ∑ k ∈ s, 1 / (k : ℝ) ≤ 3 := by linarith
  have hinner :
      (∑ k ∈ Finset.Icc 1 (N / e), squarefulTailMask N (e * k) / k) ≤
        ∑ k ∈ s, 1 / (k : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    by_cases hmem : e * k ∈ (Finset.Ioc (N / 2) N).filter (fun d => 4 ∣ d)
    · have hlow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem).1).1
      simp [squarefulTailMask, hmem, hlow]
    · simp only [squarefulTailMask, if_neg hmem, zero_div]
      split_ifs <;> positivity
  calc
    selbergMultiplesCoord N (squarefulTailMask N) e =
        (1 / (e : ℝ)) *
          ∑ k ∈ Finset.Icc 1 (N / e), squarefulTailMask N (e * k) / k := by
      rw [selbergMultiplesCoord, sum_filter_dvd_eq_sum_scaled he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (1 / (e : ℝ)) * ∑ k ∈ s, 1 / (k : ℝ) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ (1 / (e : ℝ)) * 3 := mul_le_mul_of_nonneg_left hwindow3 (by positivity)
    _ = _ := by ring

/-- The squareful charge correction has only logarithmic Selberg cost. -/
theorem selberg_squarefulTailMask_le {N : ℕ} (hN : 2 ≤ N) :
    selbergTotientDiagonalForm N (squarefulTailMask N) ≤ 9 * (1 + Real.log N) := by
  unfold selbergTotientDiagonalForm
  calc
    _ ≤ ∑ e ∈ Finset.Icc 1 N, 9 / (e : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      have heN := (Finset.mem_Icc.mp he).1
      have he0 : (0 : ℝ) < e := by exact_mod_cast heN
      obtain ⟨hcoord0, hcoord⟩ := selbergMultiplesCoord_squarefulTailMask_le hN heN
      have hphi : (Nat.totient e : ℝ) ≤ e := by exact_mod_cast Nat.totient_le e
      calc
        _ ≤ (Nat.totient e : ℝ) * (3 / (e : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcoord0 hcoord 2) (Nat.cast_nonneg _)
        _ ≤ (e : ℝ) * (3 / (e : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right hphi (sq_nonneg _)
        _ = _ := by field_simp; ring
    _ = 9 * ∑ e ∈ Finset.Icc 1 N, 1 / (e : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log N) (by norm_num)

/-- Enlarging the cutoff does not change the Selberg form of a supported row. -/
theorem selbergTotientDiagonalForm_eq_of_support_le {L N : ℕ} (hLN : L ≤ N)
    (c : ℕ → ℝ) (hc : ∀ d : ℕ, L < d → c d = 0) :
    selbergTotientDiagonalForm N c = selbergTotientDiagonalForm L c := by
  have hcoord : ∀ e : ℕ, selbergMultiplesCoord N c e = selbergMultiplesCoord L c e := by
    intro e
    unfold selbergMultiplesCoord
    have hsub : (Finset.Icc 1 L).filter (fun d => e ∣ d) ⊆
        (Finset.Icc 1 N).filter (fun d => e ∣ d) := by
      intro d hd
      obtain ⟨hdI, hed⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd1, hdL⟩ := Finset.mem_Icc.mp hdI
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hdL.trans hLN⟩, hed⟩
    symm
    apply Finset.sum_subset hsub
    intro d hd hnot
    obtain ⟨hdI, hed⟩ := Finset.mem_filter.mp hd
    have hdL : L < d := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hdI).1, le_of_not_gt h⟩, hed⟩)
    simp [hc d hdL]
  have hzero : ∀ e : ℕ, L < e → selbergMultiplesCoord L c e = 0 := by
    intro e he
    unfold selbergMultiplesCoord
    apply Finset.sum_eq_zero
    intro d hd
    obtain ⟨hdI, hed⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdL⟩ := Finset.mem_Icc.mp hdI
    have hedle := Nat.le_of_dvd hd1 hed
    omega
  unfold selbergTotientDiagonalForm
  simp only [hcoord]
  symm
  apply Finset.sum_subset
  · intro e he
    obtain ⟨he1, heL⟩ := Finset.mem_Icc.mp he
    exact Finset.mem_Icc.mpr ⟨he1, heL.trans hLN⟩
  · intro e he hnot
    have heL : L < e := by
      have he1 := (Finset.mem_Icc.mp he).1
      simp only [Finset.mem_Icc, not_and] at hnot
      exact lt_of_not_ge (hnot he1)
    simp [hzero e heL]

/-- A charge mask placed near the prefix pays for its own scale, independently
of the larger ambient cutoff. -/
theorem selberg_squarefulTailMask_le_of_le {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    selbergTotientDiagonalForm N (squarefulTailMask L) ≤ 9 * (1 + Real.log L) := by
  rw [selbergTotientDiagonalForm_eq_of_support_le hLN (squarefulTailMask L)
    (fun _ hd => squarefulTailMask_eq_zero_of_lt hd)]
  exact selberg_squarefulTailMask_le hL

end

end RHTower
