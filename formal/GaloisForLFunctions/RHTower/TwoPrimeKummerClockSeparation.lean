import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The two-prime arithmetic clock separation

The rectangular source modes of depth `N` are the integer pairs `(m, n)` with `|m|, |n| ≤ N`,
excluding the origin; their clock frequencies are `μ = m·log 2 + n·log 3`.  The **clock separation
scale** is the least absolute frequency,

`d N = min {|μ| : (m,n) ∈ box N}`.

The elementary window is

`3^(−N) ≤ d N ≤ log 2 / ⌊N/2⌋`,

the lower bound from integer separation of `2^p` and `3^q`, the upper bound from Dirichlet's
pigeonhole applied to `log 3 / log 2 ∈ (1, 2)`.  In particular `d N → 0`.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.RHTower

/-- The two-prime clock frequency of an integer mode. -/
noncomputable def kummerFreq (p : ℤ × ℤ) : ℝ :=
  (p.1 : ℝ) * Real.log 2 + (p.2 : ℝ) * Real.log 3

/-- The rectangular source modes of depth `N`. -/
noncomputable def kummerBox (N : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(N : ℤ)) (N : ℤ)) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ))).erase (0, 0)

theorem mem_kummerBox {N : ℕ} {p : ℤ × ℤ} :
    p ∈ kummerBox N ↔ (|p.1| ≤ (N : ℤ) ∧ |p.2| ≤ (N : ℤ)) ∧ p ≠ (0, 0) := by
  rw [kummerBox, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · rintro ⟨hne, ⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨abs_le.mpr ⟨h1, h2⟩, abs_le.mpr ⟨h3, h4⟩⟩, hne⟩
  · rintro ⟨⟨h1, h2⟩, hne⟩
    obtain ⟨ha, hb⟩ := abs_le.mp h1
    obtain ⟨hc, hd⟩ := abs_le.mp h2
    exact ⟨hne, ⟨ha, hb⟩, hc, hd⟩

theorem kummerBox_nonempty {N : ℕ} (hN : 1 ≤ N) : (kummerBox N).Nonempty := by
  refine ⟨(1, 0), mem_kummerBox.mpr ⟨⟨?_, ?_⟩, ?_⟩⟩
  · show |(1 : ℤ)| ≤ (N : ℤ)
    rw [abs_one]
    exact_mod_cast hN
  · show |(0 : ℤ)| ≤ (N : ℤ)
    simp
  · intro hcon
    have := congrArg Prod.fst hcon
    simp at this

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_two_lt_log_three : Real.log 2 ≤ Real.log 3 :=
  Real.log_le_log (by norm_num) (by norm_num)

theorem one_third_lt_log_two : (1 : ℝ) / 3 < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num
  linarith

/-- Distinct positive integers have logarithms separated by at least the reciprocal of the
larger one. -/
theorem inv_max_le_abs_log_sub_log {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hAB : A ≠ B) :
    1 / (max (A : ℝ) (B : ℝ)) ≤ |Real.log A - Real.log B| := by
  have key : ∀ C D : ℕ, 0 < C → 0 < D → D < C →
      1 / (C : ℝ) ≤ Real.log C - Real.log D := by
    intro C D hC hD hDC
    have hCR : (0 : ℝ) < C := by exact_mod_cast hC
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have hquot : (0 : ℝ) < (D : ℝ) / C := by positivity
    have hlog := Real.log_le_sub_one_of_pos hquot
    rw [Real.log_div (ne_of_gt hDR) (ne_of_gt hCR)] at hlog
    have hDle : (D : ℝ) + 1 ≤ (C : ℝ) := by exact_mod_cast hDC
    have hfrac : (D : ℝ) / C ≤ 1 - 1 / C := by
      rw [div_le_iff₀ hCR]
      field_simp
      linarith
    linarith
  rcases lt_trichotomy A B with h | h | h
  · have hmax : max (A : ℝ) (B : ℝ) = (B : ℝ) := by
      apply max_eq_right
      exact_mod_cast h.le
    rw [hmax, abs_sub_comm]
    have hkey := key B A hB hA h
    have hBpos : (0 : ℝ) < 1 / (B : ℝ) := by
      have : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
      positivity
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.log B - Real.log A)]
    exact hkey
  · exact absurd h hAB
  · have hmax : max (A : ℝ) (B : ℝ) = (A : ℝ) := by
      apply max_eq_left
      exact_mod_cast h.le
    rw [hmax]
    have hkey := key A B hA hB h
    have hApos : (0 : ℝ) < 1 / (A : ℝ) := by
      have : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
      positivity
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.log A - Real.log B)]
    exact hkey

/-- **Integer separation of the two arithmetic clocks.**  Every nonzero rectangular mode of depth
`N` has frequency at least `3^(−N)` in absolute value. -/
theorem kummerFreq_lower_bound {N : ℕ} (hN : 1 ≤ N) {p : ℤ × ℤ} (hp : p ∈ kummerBox N) :
    (3 : ℝ) ^ (-(N : ℤ)) ≤ |kummerFreq p| := by
  obtain ⟨⟨h1, h2⟩, hne⟩ := mem_kummerBox.mp hp
  have h3N : (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 / 3 := by
    have hexp : (-(N : ℤ)) ≤ (-1 : ℤ) := by omega
    have hle : (3 : ℝ) ^ (-(N : ℤ)) ≤ (3 : ℝ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) hexp
    calc (3 : ℝ) ^ (-(N : ℤ)) ≤ (3 : ℝ) ^ (-1 : ℤ) := hle
      _ = 1 / 3 := by norm_num
  have hsameSign : ∀ q : ℤ × ℤ, q ≠ (0, 0) → 0 ≤ q.1 → 0 ≤ q.2 →
      Real.log 2 ≤ kummerFreq q := by
    intro q hq0 hq1 hq2
    have hq1' : (0 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast hq1
    have hq2' : (0 : ℝ) ≤ (q.2 : ℝ) := by exact_mod_cast hq2
    rcases eq_or_lt_of_le hq1 with h | h
    · have hq2pos : 1 ≤ q.2 := by
        rcases eq_or_lt_of_le hq2 with h2' | h2'
        · exact absurd (Prod.ext h.symm h2'.symm) hq0
        · omega
      have hq2R : (1 : ℝ) ≤ (q.2 : ℝ) := by exact_mod_cast hq2pos
      rw [kummerFreq, ← h]
      have : Real.log 2 ≤ (q.2 : ℝ) * Real.log 3 := by
        calc Real.log 2 ≤ Real.log 3 := log_two_lt_log_three
          _ = 1 * Real.log 3 := (one_mul _).symm
          _ ≤ (q.2 : ℝ) * Real.log 3 :=
            mul_le_mul_of_nonneg_right hq2R (le_trans log_two_pos.le log_two_lt_log_three)
      simpa using this
    · have hq1R : (1 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast h
      rw [kummerFreq]
      have hpart : Real.log 2 ≤ (q.1 : ℝ) * Real.log 2 := by
        calc Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
          _ ≤ (q.1 : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hq1R log_two_pos.le
      have hrest : (0 : ℝ) ≤ (q.2 : ℝ) * Real.log 3 :=
        mul_nonneg hq2' (le_trans log_two_pos.le log_two_lt_log_three)
      linarith
  have hneg : ∀ q : ℤ × ℤ, kummerFreq (-q.1, -q.2) = -kummerFreq q := by
    intro q
    rw [kummerFreq, kummerFreq]
    push_cast
    ring
  rcases le_or_gt 0 (p.1 * p.2) with hsign | hsign
  · -- both coordinates have the same sign
    have hmain : Real.log 2 ≤ |kummerFreq p| := by
      rcases Int.mul_nonneg_iff.mp hsign with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
      · have := hsameSign p hne hp1 hp2
        rw [abs_of_nonneg (le_trans log_two_pos.le this)]
        exact this
      · have hne' : (-p.1, -p.2) ≠ (0, 0) := by
          intro hcon
          apply hne
          have hx := congrArg Prod.fst hcon
          have hy := congrArg Prod.snd hcon
          simp only at hx hy
          exact Prod.ext (by omega) (by omega)
        have := hsameSign (-p.1, -p.2) hne' (by simpa using hp1) (by simpa using hp2)
        rw [hneg p] at this
        rw [abs_of_nonpos (by linarith [log_two_pos])]
        linarith
    calc (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 / 3 := h3N
      _ ≤ Real.log 2 := one_third_lt_log_two.le
      _ ≤ |kummerFreq p| := hmain
  · -- opposite signs: an integer logarithm separation
    have hgen : ∀ q : ℤ × ℤ, |q.1| ≤ (N : ℤ) → |q.2| ≤ (N : ℤ) → 0 < q.1 → q.2 < 0 →
        (3 : ℝ) ^ (-(N : ℤ)) ≤ |kummerFreq q| := by
      intro q hq1 hq2 hq1pos hq2neg
      obtain ⟨hq1l, hq1r⟩ := abs_le.mp hq1
      obtain ⟨hq2l, hq2r⟩ := abs_le.mp hq2
      set a : ℕ := q.1.toNat with ha
      set b : ℕ := (-q.2).toNat with hb
      have hapos : 0 < a := by omega
      have hbpos : 0 < b := by omega
      have haN : a ≤ N := by omega
      have hbN : b ≤ N := by omega
      have hcast1 : (q.1 : ℝ) = (a : ℝ) := by
        have hz : ((a : ℕ) : ℤ) = q.1 := Int.toNat_of_nonneg hq1pos.le
        exact_mod_cast hz.symm
      have hcast2 : (q.2 : ℝ) = -(b : ℝ) := by
        have hz : ((b : ℕ) : ℤ) = -q.2 := Int.toNat_of_nonneg (by omega)
        have hz' : q.2 = -((b : ℕ) : ℤ) := by omega
        rw [hz']
        push_cast
        ring
      have hfreq : kummerFreq q
          = Real.log (((2 ^ a : ℕ) : ℝ)) - Real.log (((3 ^ b : ℕ) : ℝ)) := by
        rw [kummerFreq, hcast1, hcast2]
        push_cast
        rw [Real.log_pow, Real.log_pow]
        ring
      have hne2 : (2 : ℕ) ^ a ≠ (3 : ℕ) ^ b := by
        intro hcon
        have heven : 2 ∣ (2 : ℕ) ^ a := dvd_pow_self 2 hapos.ne'
        rw [hcon] at heven
        have hodd : ¬ (2 ∣ (3 : ℕ) ^ b) := by
          intro hdvd
          have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
          omega
        exact hodd heven
      have hposA : 0 < (2 : ℕ) ^ a := pow_pos (by norm_num) a
      have hposB : 0 < (3 : ℕ) ^ b := pow_pos (by norm_num) b
      have hsep := inv_max_le_abs_log_sub_log hposA hposB hne2
      rw [← hfreq] at hsep
      refine le_trans ?_ hsep
      have hmaxle : max (((2 : ℕ) ^ a : ℕ) : ℝ) (((3 : ℕ) ^ b : ℕ) : ℝ) ≤ (3 : ℝ) ^ (N : ℕ) := by
        refine max_le ?_ ?_
        · calc (((2 : ℕ) ^ a : ℕ) : ℝ) = (2 : ℝ) ^ a := by push_cast; ring
            _ ≤ (3 : ℝ) ^ a := by
                exact pow_le_pow_left₀ (by norm_num) (by norm_num) a
            _ ≤ (3 : ℝ) ^ (N : ℕ) := by
                exact pow_le_pow_right₀ (by norm_num) haN
        · calc (((3 : ℕ) ^ b : ℕ) : ℝ) = (3 : ℝ) ^ b := by push_cast; ring
            _ ≤ (3 : ℝ) ^ (N : ℕ) := by
                exact pow_le_pow_right₀ (by norm_num) hbN
      have hmaxpos : (0 : ℝ) < max (((2 : ℕ) ^ a : ℕ) : ℝ) (((3 : ℕ) ^ b : ℕ) : ℝ) := by
        refine lt_of_lt_of_le ?_ (le_max_left _ _)
        exact_mod_cast hposA
      rw [zpow_neg, zpow_natCast, ← one_div]
      exact one_div_le_one_div_of_le hmaxpos hmaxle
    rcases Int.mul_neg_iff.mp hsign with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · exact hgen p h1 h2 hp1 hp2
    · have hb1 : |(-p.1)| ≤ (N : ℤ) := by rwa [abs_neg]
      have hb2 : |(-p.2)| ≤ (N : ℤ) := by rwa [abs_neg]
      have := hgen (-p.1, -p.2) hb1 hb2 (by simpa using hp1) (by simpa using hp2)
      rw [hneg p, abs_neg] at this
      exact this

/-! ## The clock separation scale -/

/-- The arithmetic clock-separation scale: the least absolute frequency of a rectangular mode. -/
noncomputable def kummerSeparation (N : ℕ) : ℝ :=
  sInf ((fun p => |kummerFreq p|) '' (kummerBox N : Set (ℤ × ℤ)))

theorem kummerFreqImage_finite (N : ℕ) :
    ((fun p => |kummerFreq p|) '' (kummerBox N : Set (ℤ × ℤ))).Finite :=
  ((kummerBox N).finite_toSet).image _

theorem kummerSeparation_le {N : ℕ} {p : ℤ × ℤ} (hp : p ∈ kummerBox N) :
    kummerSeparation N ≤ |kummerFreq p| := by
  refine csInf_le ((kummerFreqImage_finite N).bddBelow) ?_
  exact ⟨p, hp, rfl⟩

theorem exists_kummerSeparation_eq {N : ℕ} (hN : 1 ≤ N) :
    ∃ p ∈ kummerBox N, kummerSeparation N = |kummerFreq p| := by
  have hne : ((fun p => |kummerFreq p|) '' (kummerBox N : Set (ℤ × ℤ))).Nonempty := by
    obtain ⟨p, hp⟩ := kummerBox_nonempty hN
    exact ⟨|kummerFreq p|, ⟨p, hp, rfl⟩⟩
  obtain ⟨p, hp, hval⟩ := hne.csInf_mem (kummerFreqImage_finite N)
  exact ⟨p, hp, hval.symm⟩

/-- **The elementary lower window.**  The clock separation is at least `3^(−N)`. -/
theorem kummerSeparation_lower_bound {N : ℕ} (hN : 1 ≤ N) :
    (3 : ℝ) ^ (-(N : ℤ)) ≤ kummerSeparation N := by
  obtain ⟨p, hp, hval⟩ := exists_kummerSeparation_eq hN
  rw [hval]
  exact kummerFreq_lower_bound hN hp

theorem kummerSeparation_pos {N : ℕ} (hN : 1 ≤ N) : 0 < kummerSeparation N :=
  lt_of_lt_of_le (by positivity) (kummerSeparation_lower_bound hN)

/-! ## The Dirichlet upper window -/

/-- The two-prime clock ratio. -/
noncomputable def kummerClockRatio : ℝ := Real.log 3 / Real.log 2

theorem one_lt_kummerClockRatio : 1 < kummerClockRatio := by
  rw [kummerClockRatio, lt_div_iff₀ log_two_pos, one_mul]
  exact Real.log_lt_log (by norm_num) (by norm_num)

theorem kummerClockRatio_lt_two : kummerClockRatio < 2 := by
  rw [kummerClockRatio, div_lt_iff₀ log_two_pos]
  have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h44 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  linarith

/-- **The elementary upper window.**  Dirichlet's pigeonhole produces a rectangular mode whose
frequency is at most `log 2 / ⌊N/2⌋`. -/
theorem kummerSeparation_upper_bound {N : ℕ} (hN : 2 ≤ N) :
    kummerSeparation N ≤ Real.log 2 / ((N / 2 : ℕ) : ℝ) := by
  set M : ℕ := N / 2 with hM
  have hMpos : 0 < M := by omega
  have h2M : 2 * M ≤ N := by omega
  obtain ⟨j, k, hk0, hkM, habs⟩ := Real.exists_int_int_abs_mul_sub_le kummerClockRatio hMpos
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hMR1 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hkMR : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hkM
  have hhalf : (1 : ℝ) / ((M : ℝ) + 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  obtain ⟨hlow, hhigh⟩ := abs_le.mp habs
  -- the numerator stays inside the rectangle
  have hjpos : 0 < j := by
    have hcalc : (1 : ℝ) / 2 < (j : ℝ) := by
      have h1 : (k : ℝ) * kummerClockRatio - 1 / 2 ≤ (j : ℝ) := by
        have := hlow
        have hkc : (1 : ℝ) * kummerClockRatio ≤ (k : ℝ) * kummerClockRatio :=
          mul_le_mul_of_nonneg_right hkR (by linarith [one_lt_kummerClockRatio])
        linarith
      have h2 : (1 : ℝ) * kummerClockRatio ≤ (k : ℝ) * kummerClockRatio :=
        mul_le_mul_of_nonneg_right hkR (by linarith [one_lt_kummerClockRatio])
      have h3 : (1 : ℝ) < kummerClockRatio := one_lt_kummerClockRatio
      linarith
    have : (0 : ℝ) < (j : ℝ) := by linarith
    exact_mod_cast this
  have hjle : j ≤ 2 * (M : ℤ) := by
    have hcalc : (j : ℝ) < 2 * (M : ℝ) + 1 := by
      have h1 : (j : ℝ) ≤ (k : ℝ) * kummerClockRatio + 1 / ((M : ℝ) + 1) := by linarith
      have h2 : (k : ℝ) * kummerClockRatio < (M : ℝ) * 2 := by
        have hlt := kummerClockRatio_lt_two
        have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
        calc (k : ℝ) * kummerClockRatio < (k : ℝ) * 2 := by nlinarith
          _ ≤ (M : ℝ) * 2 := by linarith
      have h3 : (1 : ℝ) / ((M : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hMR1]; linarith
      linarith
    have : (j : ℝ) < 2 * (M : ℝ) + 1 := hcalc
    have hcast : ((2 * (M : ℤ) + 1 : ℤ) : ℝ) = 2 * (M : ℝ) + 1 := by push_cast; ring
    have hlt : (j : ℤ) < 2 * (M : ℤ) + 1 := by
      have := this
      rw [← hcast] at this
      exact_mod_cast this
    omega
  have hmem : ((-j, k) : ℤ × ℤ) ∈ kummerBox N := by
    refine mem_kummerBox.mpr ⟨⟨?_, ?_⟩, ?_⟩
    · show |(-j)| ≤ (N : ℤ)
      rw [abs_neg, abs_of_nonneg hjpos.le]
      omega
    · show |k| ≤ (N : ℤ)
      rw [abs_of_nonneg hk0.le]
      omega
    · intro hcon
      have := congrArg Prod.snd hcon
      simp only at this
      omega
  have hvalue : kummerFreq (-j, k) = Real.log 2 * ((k : ℝ) * kummerClockRatio - (j : ℝ)) := by
    rw [kummerFreq, kummerClockRatio]
    push_cast
    field_simp
    ring
  have hbound : |kummerFreq (-j, k)| ≤ Real.log 2 / ((M : ℝ) + 1) := by
    rw [hvalue, abs_mul, abs_of_nonneg log_two_pos.le]
    calc Real.log 2 * |(k : ℝ) * kummerClockRatio - (j : ℝ)|
        ≤ Real.log 2 * (1 / ((M : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left habs log_two_pos.le
      _ = Real.log 2 / ((M : ℝ) + 1) := by ring
  calc kummerSeparation N ≤ |kummerFreq (-j, k)| := kummerSeparation_le hmem
    _ ≤ Real.log 2 / ((M : ℝ) + 1) := hbound
    _ ≤ Real.log 2 / (M : ℝ) := by
        apply div_le_div_of_nonneg_left log_two_pos.le hMR
        linarith

/-- **The clock separation vanishes.** -/
theorem tendsto_kummerSeparation_zero :
    Tendsto kummerSeparation atTop (𝓝 0) := by
  have hlow : ∀ᶠ N : ℕ in atTop, 0 ≤ kummerSeparation N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (kummerSeparation_pos hN).le
  have hupp : ∀ᶠ N : ℕ in atTop,
      kummerSeparation N ≤ Real.log 2 / ((N / 2 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact kummerSeparation_upper_bound hN
  have hM : Tendsto (fun N : ℕ => ((N / 2 : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt b
    refine ⟨2 * n, fun N hN => ?_⟩
    have hnN : n ≤ N / 2 := by omega
    have hnNR : (n : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hnN
    linarith
  have hdiv : Tendsto (fun N : ℕ => Real.log 2 / ((N / 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    hM.const_div_atTop (Real.log 2)
  exact squeeze_zero' hlow hupp hdiv

end GaloisForLFunctions.RHTower
