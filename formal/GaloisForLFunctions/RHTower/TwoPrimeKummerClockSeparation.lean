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

/-! ## Injectivity and accumulation of the frequency map -/

theorem kummerFreq_ne_zero {p : ℤ × ℤ} (hp : p ≠ (0, 0)) : kummerFreq p ≠ 0 := by
  set N : ℕ := max 1 (max p.1.natAbs p.2.natAbs) with hN
  have hN1 : 1 ≤ N := le_max_left _ _
  have hmem : p ∈ kummerBox N := by
    refine mem_kummerBox.mpr ⟨⟨?_, ?_⟩, hp⟩
    · have hle : p.1.natAbs ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hle
    · have hle : p.2.natAbs ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hle
  have hlow := kummerFreq_lower_bound hN1 hmem
  intro h0
  rw [h0, abs_zero] at hlow
  have : (0 : ℝ) < (3 : ℝ) ^ (-(N : ℤ)) := by positivity
  linarith

theorem kummerFreq_add (p q : ℤ × ℤ) :
    kummerFreq (p.1 + q.1, p.2 + q.2) = kummerFreq p + kummerFreq q := by
  rw [kummerFreq, kummerFreq, kummerFreq]
  push_cast
  ring

theorem kummerFreq_zsmul (k : ℤ) (p : ℤ × ℤ) :
    kummerFreq (k * p.1, k * p.2) = (k : ℝ) * kummerFreq p := by
  rw [kummerFreq, kummerFreq]
  push_cast
  ring

theorem kummerFreq_injective : Function.Injective kummerFreq := by
  intro p q hpq
  by_contra hne
  have hdiff : (p.1 - q.1, p.2 - q.2) ≠ (0, 0) := by
    intro hcon
    apply hne
    have hx := congrArg Prod.fst hcon
    have hy := congrArg Prod.snd hcon
    simp only at hx hy
    exact Prod.ext (by omega) (by omega)
  have hval : kummerFreq (p.1 - q.1, p.2 - q.2) = 0 := by
    rw [kummerFreq, kummerFreq] at hpq
    rw [kummerFreq]
    push_cast
    linarith
  exact kummerFreq_ne_zero hdiff hval

/-- Arbitrarily small nonzero clock frequencies exist. -/
theorem exists_small_kummerFreq {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℤ × ℤ, p ≠ (0, 0) ∧ 0 < |kummerFreq p| ∧ |kummerFreq p| < ε := by
  obtain ⟨N, hN⟩ := (tendsto_kummerSeparation_zero.eventually
    (gt_mem_nhds hε)).and (eventually_ge_atTop 1) |>.exists
  obtain ⟨p, hp, hval⟩ := exists_kummerSeparation_eq hN.2
  refine ⟨p, (mem_kummerBox.mp hp).2, ?_, ?_⟩
  · rw [← hval]
    exact kummerSeparation_pos hN.2
  · rw [← hval]
    exact hN.1

/-- The nonzero clock frequencies are dense in the line. -/
theorem exists_kummerFreq_near (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℤ × ℤ, p ≠ (0, 0) ∧ |kummerFreq p - t| < ε := by
  obtain ⟨p₀, hp₀, hpos, hsmall⟩ := exists_small_kummerFreq (show (0:ℝ) < ε / 2 by linarith)
  set μ : ℝ := kummerFreq p₀ with hμ
  have hμne : μ ≠ 0 := by
    intro h; rw [h, abs_zero] at hpos; linarith
  set k : ℤ := round (t / μ) with hk
  have hround : |t / μ - (k : ℝ)| ≤ 1 / 2 := by
    rw [hk]
    have := abs_sub_round (t / μ)
    simpa [abs_sub_comm] using this
  have hdist : |(k : ℝ) * μ - t| ≤ |μ| / 2 := by
    have hfac : (k : ℝ) * μ - t = -((t / μ - (k : ℝ)) * μ) := by
      field_simp
      ring
    rw [hfac, abs_neg, abs_mul]
    calc |t / μ - (k : ℝ)| * |μ| ≤ (1 / 2) * |μ| :=
          mul_le_mul_of_nonneg_right hround (abs_nonneg _)
      _ = |μ| / 2 := by ring
  by_cases hk0 : k = 0
  · refine ⟨p₀, hp₀, ?_⟩
    have ht : |t| ≤ |μ| / 2 := by
      rw [hk0] at hdist
      simpa using hdist
    calc |kummerFreq p₀ - t| ≤ |kummerFreq p₀| + |t| := abs_sub _ _
      _ ≤ |μ| + |μ| / 2 := by rw [← hμ]; linarith
      _ < ε := by rw [hμ] at hsmall ⊢; linarith
  · refine ⟨(k * p₀.1, k * p₀.2), ?_, ?_⟩
    · intro hcon
      have hx := congrArg Prod.fst hcon
      have hy := congrArg Prod.snd hcon
      simp only at hx hy
      apply hp₀
      have h1 : p₀.1 = 0 := by
        rcases mul_eq_zero.mp hx with h | h
        · exact absurd h hk0
        · exact h
      have h2 : p₀.2 = 0 := by
        rcases mul_eq_zero.mp hy with h | h
        · exact absurd h hk0
        · exact h
      exact Prod.ext h1 h2
    · rw [kummerFreq_zsmul, ← hμ]
      calc |(k : ℝ) * μ - t| ≤ |μ| / 2 := hdist
        _ < ε := by rw [hμ] at hsmall; linarith

/-! ## Injective mode families with prescribed frequency limit -/

/-- Near any real number there are nonzero modes whose frequency is close but not equal. -/
theorem exists_kummerFreq_near_ne (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : ℤ × ℤ, p ≠ (0, 0) ∧ 0 < |kummerFreq p - s| ∧ |kummerFreq p - s| < δ := by
  obtain ⟨p₀, hp₀, hpos₀, hsmall₀⟩ := exists_small_kummerFreq (show (0:ℝ) < δ / 8 by linarith)
  obtain ⟨p₁, hp₁, hnear₁⟩ := exists_kummerFreq_near s (show (0:ℝ) < δ / 4 by linarith)
  set μ₀ : ℝ := kummerFreq p₀ with hμ₀
  set μ₁ : ℝ := kummerFreq p₁ with hμ₁
  have hμ₀ne : μ₀ ≠ 0 := by
    intro h; rw [h, abs_zero] at hpos₀; linarith
  set c : ℕ → ℤ × ℤ := fun k => (p₁.1 + (k + 1 : ℤ) * p₀.1, p₁.2 + (k + 1 : ℤ) * p₀.2) with hc
  have hcfreq : ∀ k : ℕ, kummerFreq (c k) = μ₁ + ((k : ℝ) + 1) * μ₀ := by
    intro k
    rw [hc, kummerFreq, hμ₁, kummerFreq, hμ₀, kummerFreq]
    push_cast
    ring
  have hinj : ∀ k l : ℕ, k ≠ l → kummerFreq (c k) ≠ kummerFreq (c l) := by
    intro k l hkl heq
    rw [hcfreq, hcfreq] at heq
    have hk : ((k : ℝ) + 1) * μ₀ = ((l : ℝ) + 1) * μ₀ := by linarith
    have heq1 : ((k : ℝ) + 1) = ((l : ℝ) + 1) := mul_right_cancel₀ hμ₀ne hk
    have : (k : ℝ) = (l : ℝ) := by linarith
    exact hkl (by exact_mod_cast this)
  -- among three candidates at most one has frequency `0` and at most one has frequency `s`
  have hzero : ∀ k l : ℕ, k ≠ l → ¬ (kummerFreq (c k) = 0 ∧ kummerFreq (c l) = 0) := by
    rintro k l hkl ⟨h1, h2⟩
    exact hinj k l hkl (by rw [h1, h2])
  have hs : ∀ k l : ℕ, k ≠ l → ¬ (kummerFreq (c k) = s ∧ kummerFreq (c l) = s) := by
    rintro k l hkl ⟨h1, h2⟩
    exact hinj k l hkl (by rw [h1, h2])
  have hexists : ∃ k : ℕ, k < 3 ∧ kummerFreq (c k) ≠ 0 ∧ kummerFreq (c k) ≠ s := by
    by_contra hcon
    push Not at hcon
    have h0 := hcon 0 (by norm_num)
    have h1 := hcon 1 (by norm_num)
    have h2 := hcon 2 (by norm_num)
    rcases eq_or_ne (kummerFreq (c 0)) 0 with e0 | e0
    · rcases eq_or_ne (kummerFreq (c 1)) 0 with e1 | e1
      · exact hzero 0 1 (by norm_num) ⟨e0, e1⟩
      · rcases eq_or_ne (kummerFreq (c 2)) 0 with e2 | e2
        · exact hzero 0 2 (by norm_num) ⟨e0, e2⟩
        · exact hs 1 2 (by norm_num) ⟨h1 e1, h2 e2⟩
    · rcases eq_or_ne (kummerFreq (c 1)) 0 with e1 | e1
      · rcases eq_or_ne (kummerFreq (c 2)) 0 with e2 | e2
        · exact hzero 1 2 (by norm_num) ⟨e1, e2⟩
        · exact hs 0 2 (by norm_num) ⟨h0 e0, h2 e2⟩
      · exact hs 0 1 (by norm_num) ⟨h0 e0, h1 e1⟩
  obtain ⟨k, hk3, hkzero, hks⟩ := hexists
  refine ⟨c k, ?_, ?_, ?_⟩
  · intro hcon
    apply hkzero
    rw [hcon, kummerFreq]
    norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr hks)
  · rw [hcfreq]
    have hkR : ((k : ℝ) + 1) ≤ 3 := by
      have : (k : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hk3
      linarith
    have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    calc |μ₁ + ((k : ℝ) + 1) * μ₀ - s| ≤ |μ₁ - s| + |((k : ℝ) + 1) * μ₀| := by
          have : μ₁ + ((k : ℝ) + 1) * μ₀ - s = (μ₁ - s) + ((k : ℝ) + 1) * μ₀ := by ring
          rw [this]
          exact abs_add_le _ _
      _ = |μ₁ - s| + ((k : ℝ) + 1) * |μ₀| := by rw [abs_mul, abs_of_nonneg hk1]
      _ < δ / 4 + 3 * (δ / 8) := by
          have h1 : |μ₁ - s| < δ / 4 := hnear₁
          have h2 : ((k : ℝ) + 1) * |μ₀| ≤ 3 * |μ₀| :=
            mul_le_mul_of_nonneg_right hkR (abs_nonneg _)
          have h3 : |μ₀| < δ / 8 := hsmall₀
          nlinarith
      _ ≤ δ := by linarith

/-- Every real number is the limit of the frequencies of an injective family of nonzero modes. -/
theorem exists_injective_modes_tendsto (s : ℝ) :
    ∃ q : ℕ → ℤ × ℤ, Function.Injective q ∧ (∀ n, q n ≠ (0, 0)) ∧
      Tendsto (fun n => kummerFreq (q n)) atTop (𝓝 s) := by
  classical
  have key : ∀ δ : ℝ, 0 < δ → ∃ p : ℤ × ℤ, p ≠ (0, 0) ∧ 0 < |kummerFreq p - s| ∧
      |kummerFreq p - s| < δ := fun δ hδ => exists_kummerFreq_near_ne s hδ
  choose F hF0 hFpos hFlt using key
  set G : ℝ → ℤ × ℤ := fun δ => if h : 0 < δ then F δ h else F 1 one_pos with hG
  have hG0 : ∀ δ, G δ ≠ (0, 0) := by
    intro δ
    rw [hG]
    by_cases h : 0 < δ
    · simpa [h] using hF0 δ h
    · simpa [h] using hF0 1 one_pos
  have hGpos : ∀ δ, 0 < |kummerFreq (G δ) - s| := by
    intro δ
    rw [hG]
    by_cases h : 0 < δ
    · simpa [h] using hFpos δ h
    · simpa [h] using hFpos 1 one_pos
  have hGlt : ∀ δ, 0 < δ → |kummerFreq (G δ) - s| < δ := by
    intro δ h
    rw [hG]
    simpa [h] using hFlt δ h
  set q : ℕ → ℤ × ℤ := fun n =>
    Nat.rec (G 1) (fun k pk => G (min |kummerFreq pk - s| (1 / (k + 2)))) n with hq
  have hqsucc : ∀ n, q (n + 1) = G (min |kummerFreq (q n) - s| (1 / (n + 2))) := fun n => rfl
  have hq0 : ∀ n, q n ≠ (0, 0) := by
    intro n
    cases n with
    | zero => exact hG0 1
    | succ k => rw [hqsucc]; exact hG0 _
  have hqpos : ∀ n, 0 < |kummerFreq (q n) - s| := by
    intro n
    cases n with
    | zero => exact hGpos 1
    | succ k => rw [hqsucc]; exact hGpos _
  have hstep : ∀ n, |kummerFreq (q (n + 1)) - s|
      < min |kummerFreq (q n) - s| (1 / ((n : ℝ) + 2)) := by
    intro n
    rw [hqsucc]
    refine hGlt _ ?_
    refine lt_min (hqpos n) ?_
    positivity
  have hanti : StrictAnti (fun n => |kummerFreq (q n) - s|) := by
    refine strictAnti_nat_of_succ_lt fun n => ?_
    exact lt_of_lt_of_le (hstep n) (min_le_left _ _)
  refine ⟨q, ?_, hq0, ?_⟩
  · intro n m hnm
    have := hanti.injective (a₁ := n) (a₂ := m)
    apply this
    show |kummerFreq (q n) - s| = |kummerFreq (q m) - s|
    rw [hnm]
  · rw [tendsto_iff_dist_tendsto_zero]
    have hbound : ∀ n, dist (kummerFreq (q n)) s ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      cases n with
      | zero =>
        rw [Real.dist_eq]
        have hq0eq : q 0 = G 1 := rfl
        rw [hq0eq]
        have h0 := hGlt 1 one_pos
        norm_num
        linarith
      | succ k =>
        rw [Real.dist_eq]
        have h := lt_of_lt_of_le (hstep k) (min_le_right _ _)
        have hcast : ((k : ℝ) + 2) = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hcast] at h
        exact h.le
    refine squeeze_zero (fun n => dist_nonneg) hbound ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat

end GaloisForLFunctions.RHTower
