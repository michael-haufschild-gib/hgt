import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarReserveThroughTheWindowAverage

/-!
# The far reserve below the eighth root

The explicit far reserve `exists_completeWeilEnergy_prefix_top_window_reserve` holds at every
smoothing length `h`, Gamma threshold `T` and short-row cutoff `K'`. Choosing, with
`ℓ = log N` and `α' = (α + 1/8)/2`,

* `λ = ℓ^{α'}`, `T = e^λ`, `h = e^{−λ}/ℓ` (so `T h = 1/ℓ`), and
* `K' = ⌈exp β⌉`, `β = 1 + ((2 log(1/h) + log(4C + 1))/c₀)² + |log t₀|` (`exists_short_cutoff`),
  so that the prime number theorem error is at most `h²` and `log K' ≍ ℓ^{2α'}`,

every cost is a power of `ℓ` below the reserves once `α < 1/8`: the window cost is
`O(c⁹ (log K')² / ℓ)` per unit prefix mass and `O(c^{16} log c / ℓ²)` against the top reserve
(`far_window_cost`), the translate cost is `O(c⁹ log c / ℓ²) + O(c ℓ log c / λ)` per unit prefix
mass (`far_translate_cost`), and the mass costs are `O(c log c)` and `O(c)`
(`far_mass_costs`). The result `eventually_completeWeilEnergy_far_reserve_below_one_eighth`:
for every `θ > 0`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`, every
pole-orthogonal vector satisfies

`(7/8) D_M + κ/(4c⁷) · log N · S − θ log N · P ≤ completeWeilEnergy`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory
  ArithmeticPositivityTheory

/-- **The window bound per unit smoothing.** Under `4 C ε ≤ h²` and `w B ≤ e c`,
`(w/h²) windowSumBound ≤ 8e²c σ² + [8e²c (1 + log 2K' + 4h² H) + 48 e c h H
  + 2 Λ_K (e²c Λ_K + (w/h) Ψ_K)] P`, with `Λ_K ≥ Σ_{k<K'} Λ(k)/k` and `Ψ_K ≥ Σ_{k<K'} Λ(k)`. -/
theorem windowSumBound_div_le {C c₀ A w h c ΛK ΨK : ℝ} {B M K' : ℕ} (x : ℕ → ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hC : 0 ≤ C) (hε : 4 * C * pntRate c₀ K' ≤ h ^ 2)
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hwB : w * B ≤ Real.exp 1 * c) (hA0 : 0 ≤ A) (hAB : A ≤ B)
    (hLK : shortOrderWeight K' ≤ ΛK) (hΨK : ∑ k ∈ range K', (Λ k : ℝ) ≤ ΨK) :
    (w / h ^ 2) * windowSumBound C c₀ A B M K' x h ≤
      8 * Real.exp 2 * c * prefixPoleMoment M x ^ 2 +
        (8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
          48 * Real.exp 1 * c * h * prefixHarmonic M +
          2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK)) * prefixMass M x := by
  set P := prefixMass M x
  set H := prefixHarmonic M
  set σ := prefixPoleMoment M x
  set ε := pntRate c₀ K'
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hH : 0 ≤ H := sum_nonneg fun m _ => by positivity
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hLK0 : 0 ≤ shortOrderWeight K' :=
    sum_nonneg fun k _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  have heh : Real.exp h ≤ Real.exp 1 := Real.exp_le_exp.mpr hh1
  have heh1 : Real.exp h - 1 ≤ 3 * h := by
    have h1 : Real.exp h - 1 ≤ h * Real.exp h := by
      have h2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-h)) (Real.exp_pos h).le
      have h3 : Real.exp (-h) * Real.exp h = 1 := by rw [← Real.exp_add]; simp
      linarith only [h2, h3]
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith only [this]
    nlinarith only [h1, heh, he3, hh.le]
  have heh0 : 0 ≤ Real.exp h - 1 := by linarith only [Real.add_one_le_exp h, hh.le]
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hwBh : w * (B * Real.exp h) ≤ Real.exp 2 * c := by
    rw [he2]
    calc w * (B * Real.exp h) = (w * B) * Real.exp h := by ring
      _ ≤ (Real.exp 1 * c) * Real.exp 1 :=
          mul_le_mul hwB heh (Real.exp_pos h).le (by positivity)
      _ = Real.exp 1 * Real.exp 1 * c := by ring
  have hdev : (4 * C * ε + h ^ 2) ^ 2 ≤ 4 * h ^ 2 * h ^ 2 := by
    have h0 : 0 ≤ 4 * C * ε + h ^ 2 := by positivity
    have := pow_le_pow_left₀ h0 (show 4 * C * ε + h ^ 2 ≤ 2 * h ^ 2 by linarith only [hε]) 2
    nlinarith only [this]
  have hB0 : (0 : ℝ) ≤ B := hA0.trans hAB
  -- term by term
  have t1 : (w / h ^ 2) * (8 * (h ^ 2 * σ ^ 2 + h ^ 2 * (P * (1 + Real.log (2 * K'))) +
      (4 * C * ε + h ^ 2) ^ 2 * (P * H)) * (B * Real.exp h)) ≤
      8 * Real.exp 2 * c * σ ^ 2 +
        8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P := by
    have hin : h ^ 2 * σ ^ 2 + h ^ 2 * (P * (1 + Real.log (2 * K'))) +
        (4 * C * ε + h ^ 2) ^ 2 * (P * H) ≤
        h ^ 2 * (σ ^ 2 + (1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P) := by
      have := mul_le_mul_of_nonneg_right hdev (mul_nonneg hP hH)
      nlinarith only [this]
    have hpos : 0 ≤ σ ^ 2 + (1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P := by
      have hK1 : 0 ≤ 1 + Real.log (2 * K') := by
        rcases Nat.eq_zero_or_pos K' with h0 | h0
        · rw [h0]; simp
        · have : (1 : ℝ) ≤ 2 * K' := by
            have : (1 : ℝ) ≤ K' := by exact_mod_cast h0
            linarith only [this]
          have := Real.log_nonneg this; linarith only [this]
      positivity
    have hh2 : 0 < h ^ 2 := by positivity
    calc (w / h ^ 2) * (8 * (h ^ 2 * σ ^ 2 + h ^ 2 * (P * (1 + Real.log (2 * K'))) +
          (4 * C * ε + h ^ 2) ^ 2 * (P * H)) * (B * Real.exp h))
        ≤ (w / h ^ 2) * (8 * (h ^ 2 * (σ ^ 2 + (1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P)) *
            (B * Real.exp h)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hin (by norm_num)) (by positivity)) (by positivity)
      _ = 8 * (w * (B * Real.exp h)) *
            (σ ^ 2 + (1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P) := by
          field_simp
      _ ≤ 8 * (Real.exp 2 * c) * (σ ^ 2 + (1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwBh (by norm_num)) hpos
      _ = _ := by ring
  have t2 : (w / h ^ 2) * (8 * (h ^ 2 * (P * H)) * ((A * Real.exp h - A) + (B * Real.exp h - B))) ≤
      48 * Real.exp 1 * c * h * H * P := by
    have hAB2 : (A * Real.exp h - A) + (B * Real.exp h - B) ≤ 2 * B * (3 * h) := by
      have e1 : (A * Real.exp h - A) + (B * Real.exp h - B) = (A + B) * (Real.exp h - 1) := by
        ring
      rw [e1]
      calc (A + B) * (Real.exp h - 1) ≤ (2 * B) * (3 * h) :=
            mul_le_mul (by linarith only [hAB]) heh1 heh0 (by positivity)
        _ = 2 * B * (3 * h) := by ring
    have hh2 : 0 < h ^ 2 := by positivity
    calc (w / h ^ 2) * (8 * (h ^ 2 * (P * H)) * ((A * Real.exp h - A) + (B * Real.exp h - B)))
        = 8 * w * (P * H) * ((A * Real.exp h - A) + (B * Real.exp h - B)) := by field_simp
      _ ≤ 8 * w * (P * H) * (2 * B * (3 * h)) :=
          mul_le_mul_of_nonneg_left hAB2 (by positivity)
      _ = 48 * (w * B) * (h * H * P) := by ring
      _ ≤ 48 * (Real.exp 1 * c) * (h * H * P) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwB (by norm_num)) (by positivity)
      _ = 48 * Real.exp 1 * c * h * H * P := by ring
  have t3 : (w / h ^ 2) * (2 * shortOrderWeight K' * ∑ k ∈ range K', (Λ k : ℝ) *
      (h * (B * Real.exp h) / k + 1) * (h * P)) ≤
      2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) * P := by
    have hh2 : 0 < h ^ 2 := by positivity
    have hsum : (w / h ^ 2) * ∑ k ∈ range K', (Λ k : ℝ) * (h * (B * Real.exp h) / k + 1) * (h * P) =
        (w * (B * Real.exp h) * shortOrderWeight K' + (w / h) * ∑ k ∈ range K', (Λ k : ℝ)) * P := by
      unfold shortOrderWeight
      rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, sum_mul]
      refine sum_congr rfl fun k _ => ?_
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
    have h1 : w * (B * Real.exp h) * shortOrderWeight K' ≤ Real.exp 2 * c * ΛK :=
      mul_le_mul hwBh hLK hLK0 (by positivity)
    have h2 : (w / h) * ∑ k ∈ range K', (Λ k : ℝ) ≤ (w / h) * ΨK :=
      mul_le_mul_of_nonneg_left hΨK (by positivity)
    have hinner : w * (B * Real.exp h) * shortOrderWeight K' + (w / h) * ∑ k ∈ range K', (Λ k : ℝ) ≤
        Real.exp 2 * c * ΛK + (w / h) * ΨK := add_le_add h1 h2
    have hinner0 : 0 ≤ w * (B * Real.exp h) * shortOrderWeight K' +
        (w / h) * ∑ k ∈ range K', (Λ k : ℝ) := by
      have : 0 ≤ ∑ k ∈ range K', (Λ k : ℝ) := sum_nonneg fun k _ => vonMangoldt_nonneg
      positivity
    calc (w / h ^ 2) * (2 * shortOrderWeight K' * ∑ k ∈ range K', (Λ k : ℝ) *
          (h * (B * Real.exp h) / k + 1) * (h * P))
        = 2 * shortOrderWeight K' * ((w / h ^ 2) * ∑ k ∈ range K', (Λ k : ℝ) *
          (h * (B * Real.exp h) / k + 1) * (h * P)) := by ring
      _ = 2 * shortOrderWeight K' * ((w * (B * Real.exp h) * shortOrderWeight K' +
          (w / h) * ∑ k ∈ range K', (Λ k : ℝ)) * P) := by rw [hsum]
      _ ≤ 2 * ΛK * ((Real.exp 2 * c * ΛK + (w / h) * ΨK) * P) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hLK (by norm_num))
            (mul_le_mul_of_nonneg_right hinner hP) (by positivity)
            (by linarith only [hLK0, hLK])
      _ = _ := by ring
  unfold windowSumBound
  rw [mul_add, mul_add]
  have e : 8 * Real.exp 2 * c * σ ^ 2 +
      (8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * H) +
        48 * Real.exp 1 * c * h * H + 2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK)) * P =
      (8 * Real.exp 2 * c * σ ^ 2 + 8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * H) * P) +
        48 * Real.exp 1 * c * h * H * P + 2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) * P := by
    ring
  rw [e]
  exact add_le_add (add_le_add t1 t2) t3

/-- `K ℓ^a (1 + log ℓ)^B ≤ ℓ^b` eventually, for `a < b`. -/
theorem eventually_mul_rpow_polylog_le_rpow {a b : ℝ} (hab : a < b) (B : ℕ) (K : ℝ) :
    ∀ᶠ ℓ : ℝ in atTop, K * ℓ ^ a * (1 + Real.log ℓ) ^ B ≤ ℓ ^ b := by
  filter_upwards [eventually_const_mul_polylog_le_rpow B (sub_pos.mpr hab) K,
    eventually_gt_atTop (0 : ℝ)] with ℓ hℓ hℓ0
  have h1 := mul_le_mul_of_nonneg_right hℓ (Real.rpow_nonneg hℓ0.le a)
  rw [← Real.rpow_add hℓ0, sub_add_cancel] at h1
  linarith only [h1, (by ring : K * ℓ ^ a * (1 + Real.log ℓ) ^ B =
    K * (1 + Real.log ℓ) ^ B * ℓ ^ a)]

/-- Mertens over the short orders: `Σ_{k<K'} Λ(k)/k ≤ log K' + log 4 + 4`. -/
theorem shortOrderWeight_le {K' : ℕ} (hK' : 1 ≤ K') :
    shortOrderWeight K' ≤ Real.log K' + (Real.log 4 + 4) := by
  have hK'R : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
  have h := sum_vonMangoldt_div_Icc_floor_le' hK'R
  rw [Nat.floor_natCast] at h
  refine le_trans ?_ h
  unfold shortOrderWeight
  have hsub : range K' ⊆ insert 0 (Icc 1 K') := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact mem_insert.mpr (Or.inl h0)
    · exact mem_insert_of_mem (mem_Icc.mpr ⟨h0, (mem_range.mp hk).le⟩)
  refine (sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
    div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)).trans (le_of_eq ?_)
  rw [sum_insert (by simp)]
  simp

/-- Chebyshev over the short orders: `Σ_{k<K'} Λ(k) ≤ (log 4 + 4) K'`. -/
theorem sum_vonMangoldt_range_le (K' : ℕ) :
    ∑ k ∈ range K', (Λ k : ℝ) ≤ (Real.log 4 + 4) * K' := by
  refine le_trans ?_ (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg K'))
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  have hsub : range K' ⊆ insert 0 (Ioc 0 K') := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact mem_insert.mpr (Or.inl h0)
    · exact mem_insert_of_mem (mem_Ioc.mpr ⟨h0, (mem_range.mp hk).le⟩)
  refine (sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => vonMangoldt_nonneg).trans (le_of_eq ?_)
  rw [sum_insert (by simp)]
  simp

/-- The top harmonic mass: `Σ_{M < n ≤ N} 1/n ≤ 1 + log(N/(M+1))`. -/
theorem sum_inv_Ioc_le {M N : ℕ} (hMN : M ≤ N) (hN : 1 ≤ N) :
    ∑ n ∈ Ioc M N, (1 : ℝ) / n ≤ 1 + Real.log N - Real.log ((M : ℝ) + 1) := by
  have hsplit : ∑ n ∈ Icc 1 N, (1 : ℝ) / n =
      ∑ n ∈ Icc 1 M, (1 : ℝ) / n + ∑ n ∈ Ioc M N, (1 : ℝ) / n := by
    have hdisj : Icc 1 N = Icc 1 M ∪ Ioc M N := by
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hdisj, sum_union]
    exact disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc] at h1; simp only [mem_Ioc] at h2; omega
  have hup := RHTower.sum_Icc_one_div_le hN
  have hlo := RHTower.harmonic_Icc_ge_log M
  linarith only [hsplit, hup, hlo]

/-- **The short-row cutoff.** For a smoothing length `h`, the order cutoff
`K' = ⌈exp β⌉`, `β = 1 + ((2 log(1/h) + log(4C + 1))/c₀)² + |log t₀|`, lies above the prime
number theorem threshold and makes its error at most `h²`. -/
theorem exists_short_cutoff {C c₀ t₀ h : ℝ} (hC : 0 ≤ C) (hc₀ : 0 < c₀) (ht₀ : 1 ≤ t₀)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    ∃ K' : ℕ, 1 ≤ K' ∧ t₀ ≤ K' * Real.exp (-1) ∧ 4 * C * pntRate c₀ K' ≤ h ^ 2 ∧
      Real.log K' ≤ (1 + ((2 * Real.log (1 / h) + Real.log (4 * C + 1)) / c₀) ^ 2 +
        |Real.log t₀|) + 1 ∧
      (K' : ℝ) ≤ 2 * Real.exp (1 + ((2 * Real.log (1 / h) + Real.log (4 * C + 1)) / c₀) ^ 2 +
        |Real.log t₀|) := by
  set ν := (2 * Real.log (1 / h) + Real.log (4 * C + 1)) / c₀
  set β := 1 + ν ^ 2 + |Real.log t₀|
  have hlog1h : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by rw [le_div_iff₀ hh]; linarith)
  have hlogC : 0 ≤ Real.log (4 * C + 1) := Real.log_nonneg (by linarith)
  have hν0 : 0 ≤ ν := by simp only [ν]; positivity
  have hβ1 : 1 ≤ β := by have := sq_nonneg ν; have := abs_nonneg (Real.log t₀); simp only [β]; linarith
  have heβ : 1 ≤ Real.exp β := Real.one_le_exp (by linarith)
  refine ⟨⌈Real.exp β⌉₊, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (by
      intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
  · have h1 : Real.exp β ≤ (⌈Real.exp β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : t₀ ≤ Real.exp β * Real.exp (-1) := by
      rw [← Real.exp_add]
      have h3 : Real.log t₀ ≤ β + -1 := by
        have := le_abs_self (Real.log t₀); have := sq_nonneg ν; simp only [β]; linarith
      calc t₀ = Real.exp (Real.log t₀) := (Real.exp_log (by linarith)).symm
        _ ≤ _ := Real.exp_le_exp.mpr h3
    exact h2.trans (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
  · -- the prime number theorem error at the cutoff
    have h1 : Real.exp β ≤ (⌈Real.exp β⌉₊ : ℝ) := Nat.le_ceil _
    have hK0 : (0 : ℝ) < (⌈Real.exp β⌉₊ : ℝ) := lt_of_lt_of_le (Real.exp_pos β) h1
    have hlogK : β ≤ Real.log (⌈Real.exp β⌉₊ : ℝ) :=
      (Real.log_exp β).symm.le.trans (Real.log_le_log (Real.exp_pos β) h1)
    have hlogKe : ν ^ 2 ≤ Real.log ((⌈Real.exp β⌉₊ : ℝ) * Real.exp (-1)) := by
      rw [Real.log_mul hK0.ne' (Real.exp_pos _).ne', Real.log_exp]
      have := abs_nonneg (Real.log t₀); simp only [β] at hlogK; linarith
    have hsq : ν ≤ Real.sqrt (Real.log ((⌈Real.exp β⌉₊ : ℝ) * Real.exp (-1))) := by
      rw [← Real.sqrt_sq hν0]; exact Real.sqrt_le_sqrt hlogKe
    have hexp : pntRate c₀ ⌈Real.exp β⌉₊ ≤ Real.exp (-(c₀ * ν)) := by
      unfold pntRate
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hsq hc₀.le
      linarith
    have hcν : c₀ * ν = 2 * Real.log (1 / h) + Real.log (4 * C + 1) := by
      simp only [ν]; field_simp
    have hval : Real.exp (-(c₀ * ν)) = h ^ 2 / (4 * C + 1) := by
      rw [hcν, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log (by linarith),
        show 2 * Real.log (1 / h) = Real.log ((1 / h) ^ 2) by
          rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
      field_simp
    rw [hval] at hexp
    have h4C : 4 * C ≤ 4 * C + 1 := by linarith
    calc 4 * C * pntRate c₀ ⌈Real.exp β⌉₊ ≤ 4 * C * (h ^ 2 / (4 * C + 1)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (4 * C + 1) * (h ^ 2 / (4 * C + 1)) :=
          mul_le_mul_of_nonneg_right h4C (by positivity)
      _ = h ^ 2 := by field_simp
  · have h1 : (⌈Real.exp β⌉₊ : ℝ) ≤ 2 * Real.exp β := by
      have := Nat.ceil_lt_add_one (Real.exp_pos β).le; linarith
    have hK0 : (0 : ℝ) < (⌈Real.exp β⌉₊ : ℝ) := lt_of_lt_of_le (Real.exp_pos β) (Nat.le_ceil _)
    calc Real.log (⌈Real.exp β⌉₊ : ℝ) ≤ Real.log (2 * Real.exp β) := Real.log_le_log hK0 h1
      _ = Real.log 2 + β := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ β + 1 := by have := Real.log_two_lt_d9; linarith
  · have := Nat.ceil_lt_add_one (Real.exp_pos β).le; linarith

/-- The mass factor of the prime translate is `O(c (1 + log N)(1 + log c))`. -/
theorem translate_factor_le {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (h2LN : 2 * linearDefectCutoff c ≤ N) :
    (1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
        (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
          (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ /
            (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)) + 2 * (Real.log 4 + 4))) ≤
      (1 + 2 * Real.exp 2) *
        (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) *
        c * (1 + Real.log N) * (1 + Real.log c) := by
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc1
  set L := linearDefectCutoff c with hL_def
  set M := N / L with hM_def
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL1 : 1 ≤ L := by omega
  have hLN : L ≤ N := by omega
  have hN1 : 1 ≤ N := hL1.trans hLN
  have hM1 : 1 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < L)).mpr (by omega)
  have hNlt : N < (M + 1) * L := by
    have := Nat.lt_mul_div_succ N (show 0 < L by omega)
    rw [hM_def]; linarith [Nat.mul_comm L (N / L + 1)]
  have hMN : M ≤ N := Nat.div_le_self N L
  clear_value L M
  set w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  have hNle : (N : ℝ) ≤ N * Real.exp w := le_mul_of_one_le_right hNR.le (Real.one_le_exp hw.le)
  have hBn_ge : (N : ℝ) ≤ ⌊(N : ℝ) * Real.exp w⌋₊ := by exact_mod_cast Nat.le_floor hNle
  have hBn_le : (⌊(N : ℝ) * Real.exp w⌋₊ : ℝ) ≤ N * Real.exp w :=
    Nat.floor_le (by positivity)
  set Bn : ℝ := (⌊(N : ℝ) * Real.exp w⌋₊ : ℝ)
  have hBn1 : 1 ≤ Bn := hN1R.trans hBn_ge
  have hew : Real.exp w ≤ Real.exp 1 := Real.exp_le_exp.mpr hw1
  have he1 : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hwB : w * Bn ≤ Real.exp 1 * c := by
    have hwN : w * N = c := by simp only [w]; field_simp [hNR.ne']
    calc w * Bn ≤ w * (N * Real.exp w) := mul_le_mul_of_nonneg_left hBn_le hw.le
      _ = c * Real.exp w := by rw [← mul_assoc, hwN]
      _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left hew hc0.le
      _ = Real.exp 1 * c := by ring
  have hfac1 : 1 + 2 * Real.exp 1 * (w * Bn) ≤ (1 + 2 * Real.exp 2) * c := by
    have := mul_le_mul_of_nonneg_left hwB (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1)
    rw [he2]; nlinarith only [this, hc1, he1]
  have hlogBn : Real.log Bn ≤ 1 + Real.log N := by
    have h1 : Bn ≤ Real.exp 1 * N := by linarith only [hBn_le, mul_le_mul_of_nonneg_left hew hNR.le]
    calc Real.log Bn ≤ Real.log (Real.exp 1 * N) := Real.log_le_log (by linarith) h1
      _ = 1 + Real.log N := by rw [Real.log_mul he1.ne' hNR.ne', Real.log_exp]
  have hlogBn0 : 0 ≤ Real.log Bn := Real.log_nonneg hBn1
  -- `2 Bn / (M/2) ≤ 8 e C_L c`
  have hNM : (N : ℝ) ≤ 2 * M * L := by
    have : (N : ℝ) < (M + 1) * L := by exact_mod_cast hNlt
    have hLR : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith only [this, hMR, hLR]
  have hratio : 2 * Bn / ((M : ℝ) / 2) ≤ 8 * Real.exp 1 * (256 * Real.exp 2 + 4) * c := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Bn ≤ Real.exp 1 * N := by linarith only [hBn_le, mul_le_mul_of_nonneg_left hew hNR.le]
    have h2 : (N : ℝ) ≤ 2 * M * ((256 * Real.exp 2 + 4) * c) :=
      hNM.trans (mul_le_mul_of_nonneg_left hLup (by positivity))
    nlinarith only [h1, h2, he1, hMR]
  have hratio0 : 0 < 2 * Bn / ((M : ℝ) / 2) := by positivity
  have hK₂ : 1 ≤ Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4) := by
    have h1 : 0 ≤ Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) :=
      Real.log_nonneg (by have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
                          have := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num); nlinarith)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith only [h1, h2]
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hlograt : Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4) ≤
      (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) *
        (1 + Real.log c) := by
    have h1 := Real.log_le_log hratio0 hratio
    rw [Real.log_mul (by positivity) hc0.ne'] at h1
    nlinarith only [h1, hK₂, hlogc0]
  have hlograt0 : 0 ≤ Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4) := by
    have h1 : 1 ≤ 2 * Bn / ((M : ℝ) / 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : (M : ℝ) ≤ N := by exact_mod_cast hMN
      nlinarith only [this, hBn_ge]
    have := Real.log_nonneg h1
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  calc (1 + 2 * Real.exp 1 * (w * Bn)) * (Real.log Bn *
        (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))
      ≤ ((1 + 2 * Real.exp 2) * c) * ((1 + Real.log N) *
          ((Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) *
            (1 + Real.log c))) := by
        refine mul_le_mul hfac1 (mul_le_mul hlogBn hlograt hlograt0 (by
          have := Real.log_nonneg hN1R; linarith)) (by positivity) (by positivity)
    _ = _ := by ring

theorem splineWindowConstant_nonneg : 0 ≤ splineWindowConstant := by
  unfold splineWindowConstant
  exact div_nonneg (sq_nonneg _) integral_tiltedUnitSpline_sq_pos.le

/-- Combining the four costs of the far reserve. -/
theorem far_costs_combine {D δ ℓ S P E CS CP X Y θ : ℝ} (hS : 0 ≤ S) (hP : 0 ≤ P)
    (hθℓ : 0 ≤ θ * ℓ)
    (hE : (7 / 8 : ℝ) * D + (3 / 8 : ℝ) * δ * ℓ * S - CS * S - CP * P - X - Y * P ≤ E)
    (ha : CS ≤ (1 / 16 : ℝ) * δ * ℓ) (hb : CP ≤ θ / 4 * ℓ)
    (hc : X ≤ (1 / 16 : ℝ) * δ * ℓ * S + θ / 4 * ℓ * P) (hd : Y ≤ θ / 4 * ℓ) :
    (7 / 8 : ℝ) * D + δ / 4 * ℓ * S - θ * ℓ * P ≤ E := by
  have h1 := mul_le_mul_of_nonneg_right ha hS
  have h2 := mul_le_mul_of_nonneg_right hb hP
  have h3 := mul_le_mul_of_nonneg_right hd hP
  have h4 := mul_nonneg hθℓ hP
  linarith only [hE, h1, h2, h3, hc, h4]

/-- `c^k ≤ ℓ^{k a}` for `1 ≤ c ≤ ℓ^a`. -/
theorem pow_le_rpow_of_le_rpow {c ℓ a : ℝ} (hc : 1 ≤ c) (hca : c ≤ ℓ ^ a) (hℓ : 0 ≤ ℓ) (k : ℕ) :
    c ^ k ≤ ℓ ^ ((k : ℝ) * a) := by
  have h := pow_le_pow_left₀ (by linarith) hca k
  rw [← Real.rpow_mul_natCast hℓ] at h
  rwa [mul_comm] at h

/-- The short-order Chebyshev term per unit smoothing is at most one once
`2 (log 4 + 4) c ℓ e^{λ + β} ≤ N`. -/
theorem window_ratio_le {c ℓ lam β N : ℝ} (hN : 0 < N) (hℓ : 0 < ℓ)
    (hexp : 2 * (Real.log 4 + 4) * c * ℓ * Real.exp (lam + β) ≤ N) :
    (c / N) / (Real.exp (-lam) / ℓ) * ((Real.log 4 + 4) * (2 * Real.exp β)) ≤ 1 := by
  have e : (c / N) / (Real.exp (-lam) / ℓ) * ((Real.log 4 + 4) * (2 * Real.exp β)) =
      (2 * (Real.log 4 + 4) * c * ℓ * Real.exp (lam + β)) / N := by
    rw [Real.exp_add, Real.exp_neg]
    field_simp
  rw [e, div_le_one hN]; exact hexp

/-- The translate cost of the far reserve, as an inequality between reals. -/
theorem far_cost_translate {ℓ c lam G₀ θ g₀ K₂ ηi Φ α α' : ℝ} (hℓ1 : 1 ≤ ℓ) (hc1 : 1 ≤ c)
    (hθ : 0 < θ) (hg₀ : 0 < g₀) (hK₂ : 0 ≤ K₂)
    (hηi : ηi ≤ 16 * (1 + 2 * Real.exp 1) * c ^ 8 / (g₀ * ℓ))
    (hΦ : Φ ≤ (1 + 2 * Real.exp 2) * K₂ * c * (2 * ℓ) * (1 + Real.log c)) (hΦ0 : 0 ≤ Φ)
    (h9 : c ^ 9 ≤ ℓ ^ (9 * α')) (hca : c ≤ ℓ ^ α) (hlogc : Real.log c ≤ Real.log ℓ)
    (hlogc0 : 0 ≤ Real.log c)
    (hQd : 256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ / (g₀ * θ) *
      ℓ ^ (9 * α' + 1) * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (4 : ℝ))
    (hQd' : 256 * (1 + 2 * Real.exp 2) * K₂ / θ * ℓ ^ (α + 1) * (1 + Real.log ℓ) ^ 1 ≤
      ℓ ^ (1 + α'))
    (hlam : lam = ℓ ^ α') (hlamG : lam / 2 ≤ lam - G₀) (hlam0 : 0 < lam) :
    (ηi * (1 / ℓ) ^ 2 + 8 / (lam - G₀)) * Φ ≤ θ / 4 * ℓ := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hlc : 1 + Real.log c ≤ 1 + Real.log ℓ := by linarith
  -- part 1
  have hp1 : ηi * (1 / ℓ) ^ 2 * Φ ≤ θ / 8 * ℓ := by
    have hb1 : ηi * (1 / ℓ) ^ 2 * Φ ≤
        16 * (1 + 2 * Real.exp 1) * c ^ 8 / (g₀ * ℓ) * (1 / ℓ) ^ 2 *
          ((1 + 2 * Real.exp 2) * K₂ * c * (2 * ℓ) * (1 + Real.log c)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hηi (by positivity)) hΦ hΦ0 (by positivity)
    refine hb1.trans ?_
    have hc9 : c ^ 9 * (1 + Real.log c) ≤ ℓ ^ (9 * α') * (1 + Real.log ℓ) :=
      mul_le_mul h9 hlc (by linarith) (by positivity)
    have hQd2 : 256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ / (g₀ * θ) *
        (ℓ ^ (9 * α') * (1 + Real.log ℓ)) * ℓ ≤ ℓ ^ 4 := by
      rw [Real.rpow_add hℓ, Real.rpow_one, pow_one,
        show (ℓ ^ (4 : ℝ)) = ℓ ^ 4 by norm_cast] at hQd
      linarith only [hQd]
    have e : 16 * (1 + 2 * Real.exp 1) * c ^ 8 / (g₀ * ℓ) * (1 / ℓ) ^ 2 *
        ((1 + 2 * Real.exp 2) * K₂ * c * (2 * ℓ) * (1 + Real.log c)) =
        θ / 8 * (256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ / (g₀ * θ) *
          (c ^ 9 * (1 + Real.log c)) * ℓ) / ℓ ^ 3 := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have hK0 : 0 ≤ 256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ / (g₀ * θ) := by
      positivity
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc9 hK0) hℓ.le
    have h3 : θ / 8 * (256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ / (g₀ * θ) *
        (c ^ 9 * (1 + Real.log c)) * ℓ) ≤ θ / 8 * ℓ ^ 4 :=
      mul_le_mul_of_nonneg_left (h2.trans hQd2) (by positivity)
    linarith only [h3, (by ring : θ / 8 * ℓ * ℓ ^ 3 = θ / 8 * ℓ ^ 4)]
  -- part 2
  have hp2 : 8 / (lam - G₀) * Φ ≤ θ / 8 * ℓ := by
    have hlG : 0 < lam - G₀ := by linarith
    have h1 : 8 / (lam - G₀) ≤ 16 / lam := by
      rw [div_le_div_iff₀ hlG hlam0]; linarith
    have hca1 : c * (1 + Real.log c) ≤ ℓ ^ α * (1 + Real.log ℓ) :=
      mul_le_mul hca hlc (by linarith) (by positivity)
    have hQd2 : 256 * (1 + 2 * Real.exp 2) * K₂ / θ * (ℓ ^ α * (1 + Real.log ℓ)) * ℓ ≤ lam * ℓ := by
      rw [Real.rpow_add hℓ, Real.rpow_one, pow_one, Real.rpow_add hℓ, Real.rpow_one] at hQd'
      rw [hlam]; linarith only [hQd']
    have hΦ2 : Φ ≤ (1 + 2 * Real.exp 2) * K₂ * (2 * ℓ) * (ℓ ^ α * (1 + Real.log ℓ)) := by
      refine hΦ.trans ?_
      have := mul_le_mul_of_nonneg_left hca1
        (show 0 ≤ (1 + 2 * Real.exp 2) * K₂ * (2 * ℓ) by positivity)
      linarith only [this]
    calc 8 / (lam - G₀) * Φ ≤ 16 / lam * ((1 + 2 * Real.exp 2) * K₂ * (2 * ℓ) *
          (ℓ ^ α * (1 + Real.log ℓ))) :=
          mul_le_mul h1 hΦ2 hΦ0 (by positivity)
      _ = θ / 8 * (256 * (1 + 2 * Real.exp 2) * K₂ / θ * (ℓ ^ α * (1 + Real.log ℓ)) * ℓ) / lam := by
          field_simp; ring
      _ ≤ θ / 8 * (lam * ℓ) / lam :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQd2 (by positivity)) hlam0.le
      _ = θ / 8 * ℓ := by field_simp
  linarith only [hp1, hp2, (by ring : (ηi * (1 / ℓ) ^ 2 + 8 / (lam - G₀)) * Φ =
    ηi * (1 / ℓ) ^ 2 * Φ + 8 / (lam - G₀) * Φ)]

/-- The window cost of the far reserve, as an inequality between reals. -/
theorem far_cost_window {ℓ c lam θ g₀ κ ηi w h WSB σ2 Ht P S H L2K ΛK whΨ C_B C_L α' : ℝ}
    (hℓ1 : 1 ≤ ℓ) (hc1 : 1 ≤ c) (hθ : 0 < θ) (hg₀ : 0 < g₀) (hκ : 0 ≤ κ) (hS : 0 ≤ S)
    (hP : 0 ≤ P) (hh0 : 0 < h) (hh1 : h ≤ 1) (hhℓ : h * (1 + ℓ) ≤ 2) (hH0 : 0 ≤ H)
    (hH : H ≤ 1 + ℓ) (hηi : ηi ≤ 16 * (1 + 2 * Real.exp 1) * c ^ 8 / (g₀ * ℓ)) (hηi0 : 0 ≤ ηi)
    (hWS : (w / h ^ 2) * WSB ≤ 8 * Real.exp 2 * c * σ2 +
      (8 * Real.exp 2 * c * (1 + L2K + 4 * h ^ 2 * H) + 48 * Real.exp 1 * c * h * H +
        2 * ΛK * (Real.exp 2 * c * ΛK + whΨ)) * P)
    (hσ : σ2 ≤ Ht * S) (hσ0 : 0 ≤ σ2) (hHt : Ht ≤ (1 + Real.log C_L) * (1 + Real.log c))
    (hCL : 1 ≤ C_L) (hL2K : L2K ≤ ΛK + 1) (hL2K0 : 0 ≤ 1 + L2K) (hΛK1 : 1 ≤ ΛK)
    (hΛK : ΛK ≤ C_B * lam ^ 2) (hwhΨ : whΨ ≤ 1) (hwhΨ0 : 0 ≤ whΨ)
    (hlogc : Real.log c ≤ Real.log ℓ) (hlogc0 : 0 ≤ Real.log c)
    (h16 : c ^ 16 ≤ ℓ ^ (16 * α')) (h9 : c ^ 9 ≤ ℓ ^ (9 * α')) (hlam : lam = ℓ ^ α')
    (hQS : 2048 * (1 + 2 * Real.exp 1) * κ * Real.exp 2 * (1 + Real.log C_L) / g₀ ^ 2 *
      ℓ ^ (16 * α') * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (2 : ℝ))
    (hQP : 64 * (1 + 2 * Real.exp 1) * κ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
      C_B ^ 2 / (g₀ * θ) * ℓ ^ (13 * α') * (1 + Real.log ℓ) ^ 0 ≤ ℓ ^ (2 : ℝ)) :
    ηi * (κ * (w / h ^ 2)) * WSB ≤
      (1 / 16 : ℝ) * (g₀ / c ^ 7) * ℓ * S + θ / 4 * ℓ * P := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hlc : 1 + Real.log c ≤ 1 + Real.log ℓ := by linarith
  have hlCL : 0 ≤ Real.log C_L := Real.log_nonneg hCL
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : 0 < Real.exp 2 := Real.exp_pos 2
  have hηκ : 0 ≤ ηi * κ := mul_nonneg hηi0 hκ
  have hX := mul_le_mul_of_nonneg_left hWS hηκ
  have e1 : ηi * (κ * (w / h ^ 2)) * WSB = ηi * κ * ((w / h ^ 2) * WSB) := by ring
  rw [e1]
  refine hX.trans ?_
  -- the pole part
  have hS1 : ηi * κ * (8 * Real.exp 2 * c * σ2) ≤ (1 / 16 : ℝ) * (g₀ / c ^ 7) * ℓ * S := by
    have hσ' : σ2 ≤ (1 + Real.log C_L) * (1 + Real.log c) * S :=
      hσ.trans (mul_le_mul_of_nonneg_right hHt hS)
    have hb : ηi * κ * (8 * Real.exp 2 * c * σ2) ≤
        16 * (1 + 2 * Real.exp 1) * c ^ 8 / (g₀ * ℓ) * κ *
          (8 * Real.exp 2 * c * ((1 + Real.log C_L) * (1 + Real.log c) * S)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hηi hκ)
        (mul_le_mul_of_nonneg_left hσ' (by positivity)) (by positivity) (by positivity)
    refine hb.trans ?_
    have hc16 : c ^ 16 * (1 + Real.log c) ≤ ℓ ^ (16 * α') * (1 + Real.log ℓ) :=
      mul_le_mul h16 hlc (by linarith) (by positivity)
    rw [pow_one, Real.rpow_two] at hQS
    have hK0 : 0 ≤ 2048 * (1 + 2 * Real.exp 1) * κ * Real.exp 2 * (1 + Real.log C_L) / g₀ ^ 2 := by
      positivity
    have h2 : (2048 * (1 + 2 * Real.exp 1) * κ * Real.exp 2 * (1 + Real.log C_L) / g₀ ^ 2) *
        (c ^ 16 * (1 + Real.log c)) ≤ ℓ ^ 2 :=
      (mul_le_mul_of_nonneg_left hc16 hK0).trans (by rw [← mul_assoc]; exact hQS)
    have e : 16 * (1 + 2 * Real.exp 1) * c ^ 8 / (g₀ * ℓ) * κ *
        (8 * Real.exp 2 * c * ((1 + Real.log C_L) * (1 + Real.log c) * S)) =
        (1 / 16 : ℝ) * (g₀ / c ^ 7) * ℓ * S *
          ((2048 * (1 + 2 * Real.exp 1) * κ * Real.exp 2 * (1 + Real.log C_L) / g₀ ^ 2) *
            (c ^ 16 * (1 + Real.log c)) / ℓ ^ 2) := by
      field_simp; ring
    rw [e]
    have hq : (2048 * (1 + 2 * Real.exp 1) * κ * Real.exp 2 * (1 + Real.log C_L) / g₀ ^ 2) *
        (c ^ 16 * (1 + Real.log c)) / ℓ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith only [h2]
    have hA : 0 ≤ (1 / 16 : ℝ) * (g₀ / c ^ 7) * ℓ * S := by positivity
    calc (1 / 16 : ℝ) * (g₀ / c ^ 7) * ℓ * S * ((2048 * (1 + 2 * Real.exp 1) * κ *
          Real.exp 2 * (1 + Real.log C_L) / g₀ ^ 2) * (c ^ 16 * (1 + Real.log c)) / ℓ ^ 2)
        ≤ (1 / 16 : ℝ) * (g₀ / c ^ 7) * ℓ * S * 1 := mul_le_mul_of_nonneg_left hq hA
      _ = _ := by ring
  -- the mass part
  have hPc : 8 * Real.exp 2 * c * (1 + L2K + 4 * h ^ 2 * H) + 48 * Real.exp 1 * c * h * H +
      2 * ΛK * (Real.exp 2 * c * ΛK + whΨ) ≤
      c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2 := by
    have hhH : h * H ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hH hh0.le; linarith only [this, hhℓ]
    have hh2H : h ^ 2 * H ≤ 2 := by
      have e : h ^ 2 * H = h * (h * H) := by ring
      rw [e]
      calc h * (h * H) ≤ 1 * 2 := mul_le_mul hh1 hhH (mul_nonneg hh0.le hH0) zero_le_one
        _ = 2 := by ring
    have hΛ2 : ΛK ≤ ΛK ^ 2 := le_self_pow₀ hΛK1 two_ne_zero
    have hΛ1 : 1 ≤ ΛK ^ 2 := one_le_pow₀ hΛK1
    have t1 : 1 + L2K + 4 * h ^ 2 * H ≤ 11 * ΛK ^ 2 := by
      linarith only [hL2K, hh2H, hΛ2, hΛ1, hΛK1]
    have t1' := mul_le_mul_of_nonneg_left t1 (show 0 ≤ 8 * Real.exp 2 * c by positivity)
    have t2 : 48 * Real.exp 1 * c * h * H ≤ 96 * Real.exp 1 * c * ΛK ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left hhH (show 0 ≤ 48 * Real.exp 1 * c by positivity)
      have a2 := mul_le_mul_of_nonneg_left hΛ1 (show 0 ≤ 96 * Real.exp 1 * c by positivity)
      linarith only [a1, a2, (by ring : 48 * Real.exp 1 * c * h * H = 48 * Real.exp 1 * c * (h * H))]
    have t3 : 2 * ΛK * (Real.exp 2 * c * ΛK + whΨ) ≤ (2 * Real.exp 2 + 2) * c * ΛK ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left hwhΨ (show 0 ≤ 2 * ΛK by linarith only [hΛK1])
      have a2 : ΛK ^ 2 ≤ c * ΛK ^ 2 := le_mul_of_one_le_left (by positivity) hc1
      linarith only [a1, a2, hΛ2, (by ring : 2 * ΛK * (Real.exp 2 * c * ΛK + whΨ) =
        2 * Real.exp 2 * c * ΛK ^ 2 + 2 * ΛK * whΨ),
        (by ring : (2 * Real.exp 2 + 2) * c * ΛK ^ 2 = 2 * Real.exp 2 * c * ΛK ^ 2 + 2 * (c * ΛK ^ 2))]
    have hcΛ : 0 ≤ (10 * Real.exp 2 + 4 * Real.exp 1 + 8) * (c * ΛK ^ 2) := by positivity
    linarith only [t1', t2, t3, hcΛ]
  have hΛ2 : ΛK ^ 2 ≤ C_B ^ 2 * lam ^ 4 := by
    have := pow_le_pow_left₀ (by linarith) hΛK 2
    rw [mul_pow, ← pow_mul] at this; exact this
  have hlam4 : lam ^ 4 = ℓ ^ (4 * α') := by
    rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]; ring_nf
  have hP1 : ηi * κ * ((8 * Real.exp 2 * c * (1 + L2K + 4 * h ^ 2 * H) +
      48 * Real.exp 1 * c * h * H + 2 * ΛK * (Real.exp 2 * c * ΛK + whΨ)) * P) ≤
      θ / 4 * ℓ * P := by
    have hb : ηi * κ * ((8 * Real.exp 2 * c * (1 + L2K + 4 * h ^ 2 * H) +
        48 * Real.exp 1 * c * h * H + 2 * ΛK * (Real.exp 2 * c * ΛK + whΨ)) * P) ≤
        16 * (1 + 2 * Real.exp 1) * c ^ 8 / (g₀ * ℓ) * κ *
          ((c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * (C_B ^ 2 * lam ^ 4)) * P) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hηi hκ) ?_ (by
        have : 0 ≤ 8 * Real.exp 2 * c * (1 + L2K + 4 * h ^ 2 * H) +
          48 * Real.exp 1 * c * h * H + 2 * ΛK * (Real.exp 2 * c * ΛK + whΨ) := by
          have : 0 ≤ 1 + L2K + 4 * h ^ 2 * H := by positivity
          positivity
        positivity) (by positivity)
      refine mul_le_mul_of_nonneg_right (hPc.trans ?_) hP
      exact mul_le_mul_of_nonneg_left hΛ2 (by positivity)
    refine hb.trans ?_
    have hc13 : c ^ 9 * lam ^ 4 ≤ ℓ ^ (13 * α') := by
      rw [hlam4, show 13 * α' = 9 * α' + 4 * α' by ring, Real.rpow_add hℓ]
      exact mul_le_mul_of_nonneg_right h9 (by positivity)
    rw [pow_zero, mul_one, Real.rpow_two] at hQP
    have hK0 : 0 ≤ 64 * (1 + 2 * Real.exp 1) * κ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        C_B ^ 2 / (g₀ * θ) := by positivity
    have h2 := (mul_le_mul_of_nonneg_left hc13 hK0).trans hQP
    have e : 16 * (1 + 2 * Real.exp 1) * c ^ 8 / (g₀ * ℓ) * κ *
        ((c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * (C_B ^ 2 * lam ^ 4)) * P) =
        θ / 4 * ℓ * P * ((64 * (1 + 2 * Real.exp 1) * κ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
          C_B ^ 2 / (g₀ * θ)) * (c ^ 9 * lam ^ 4) / ℓ ^ 2) := by
      field_simp; ring
    rw [e]
    have hq : (64 * (1 + 2 * Real.exp 1) * κ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        C_B ^ 2 / (g₀ * θ)) * (c ^ 9 * lam ^ 4) / ℓ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h2
    calc θ / 4 * ℓ * P * ((64 * (1 + 2 * Real.exp 1) * κ *
          (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 / (g₀ * θ)) *
          (c ^ 9 * lam ^ 4) / ℓ ^ 2)
        ≤ θ / 4 * ℓ * P * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring
  have e2 : ηi * κ * (8 * Real.exp 2 * c * σ2 +
      (8 * Real.exp 2 * c * (1 + L2K + 4 * h ^ 2 * H) + 48 * Real.exp 1 * c * h * H +
        2 * ΛK * (Real.exp 2 * c * ΛK + whΨ)) * P) =
      ηi * κ * (8 * Real.exp 2 * c * σ2) + ηi * κ * ((8 * Real.exp 2 * c * (1 + L2K + 4 * h ^ 2 * H) +
        48 * Real.exp 1 * c * h * H + 2 * ΛK * (Real.exp 2 * c * ΛK + whΨ)) * P) := by ring
  rw [e2]
  exact add_le_add hS1 hP1

/-- The harmonic mass of the top: `Σ_{M < n ≤ N} 1/n ≤ (1 + log C_L)(1 + log c)`. -/
theorem harmonic_top_le {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (h2LN : 2 * linearDefectCutoff c ≤ N) :
    ∑ n ∈ Ioc (N / linearDefectCutoff c) N, (1 : ℝ) / n ≤
      (1 + Real.log (256 * Real.exp 2 + 4)) * (1 + Real.log c) := by
  obtain ⟨hL3, -, -, hLup⟩ := linearDefectCutoff_bounds hc1
  set L := linearDefectCutoff c
  set M := N / L with hM_def
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hL1 : 1 ≤ L := by omega
  have hN1 : 1 ≤ N := by omega
  have hMN : M ≤ N := Nat.div_le_self N L
  have hNlt : N < (M + 1) * L := by
    have := Nat.lt_mul_div_succ N (show 0 < L by omega)
    rw [hM_def]; linarith [Nat.mul_comm L (N / L + 1)]
  clear_value L M
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hHt := sum_inv_Ioc_le hMN hN1
  have hM1R : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hNL : (N : ℝ) ≤ ((M : ℝ) + 1) * L := by exact_mod_cast hNlt.le
  have hA0 : (0 : ℝ) < 256 * Real.exp 2 + 4 := by positivity
  have h1 : Real.log N ≤ Real.log (((M : ℝ) + 1) * ((256 * Real.exp 2 + 4) * c)) :=
    Real.log_le_log hNR (hNL.trans (mul_le_mul_of_nonneg_left hLup hM1R.le))
  rw [Real.log_mul hM1R.ne' (mul_pos hA0 hc0).ne', Real.log_mul hA0.ne' hc0.ne'] at h1
  have hCL : 1 ≤ 256 * Real.exp 2 + 4 := by have := Real.exp_pos 2; linarith
  have hlCL := Real.log_nonneg hCL
  have hlc := Real.log_nonneg hc1
  have := mul_nonneg hlCL hlc
  nlinarith only [hHt, h1, this]

/-- The window cost of the far reserve at fixed parameters. -/
theorem far_window_cost {C_ψ c₀ θ α' c ℓ lam h β C_β : ℝ} {N K' : ℕ}
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hc1 : 1 ≤ c) (hcℓ : c ≤ ℓ) (hcα' : c ≤ ℓ ^ α')
    (hℓN : ℓ = Real.log N) (hℓ1 : 1 ≤ ℓ) (h2LN : 2 * linearDefectCutoff c ≤ N) (hN2 : 2 ≤ N)
    (hz : z ∈ (conductorSubspace 1 N)ᗮ) (hh0 : 0 < h) (hh1 : h ≤ 1) (hhℓ : h * (1 + ℓ) ≤ 2)
    (hhdef : h = Real.exp (-lam) / ℓ) (hθ : 0 < θ) (hCψ : 0 ≤ C_ψ)
    (hpnt : 4 * C_ψ * pntRate c₀ K' ≤ h ^ 2) (hK'1 : 1 ≤ K')
    (hlogK' : Real.log K' ≤ β + 1) (hK'le : (K' : ℝ) ≤ 2 * Real.exp β) (hβ : β ≤ C_β * lam ^ 2)
    (hβ0 : 0 ≤ β) (hlam : lam = ℓ ^ α') (hlam1 : 1 ≤ lam)
    (hexp : 2 * (Real.log 4 + 4) * c * ℓ * Real.exp (lam + β) ≤ N)
    (hQS : 2048 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 *
      (1 + Real.log (256 * Real.exp 2 + 4)) / growingMassConstant ^ 2 *
      ℓ ^ (16 * α') * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (2 : ℝ))
    (hQP : 64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
      (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * (C_β + 1 + (Real.log 4 + 4)) ^ 2 /
      (growingMassConstant * θ) * ℓ ^ (13 * α') * (1 + Real.log ℓ) ^ 0 ≤ ℓ ^ (2 : ℝ)) :
    16 * (1 + 2 * Real.exp 1 * c) / ((growingMassConstant / c ^ 7) * ℓ) *
        (splineWindowConstant * ((c / N) / h ^ 2)) *
        windowSumBound C_ψ c₀ (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)
          ⌊(N : ℝ) * Real.exp (c / N)⌋₊ (N / linearDefectCutoff c) K' (primeHorizonExtension z) h ≤
      (1 / 16 : ℝ) * (growingMassConstant / c ^ 7) * ℓ *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) +
        θ / 4 * ℓ * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) := by
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hℓ0 : 0 ≤ ℓ := hℓpos.le
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hC₄ : 1 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hCL : 1 ≤ 256 * Real.exp 2 + 4 := by have := Real.exp_pos 2; linarith
  have hHt' := harmonic_top_le hc1 h2LN
  have hMN : N / linearDefectCutoff c ≤ N := Nat.div_le_self _ _
  have hM1 : 1 ≤ N / linearDefectCutoff c :=
    (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  have hσ := prefixPoleMoment_sq_le hN2 hMN hz
  have hHM : prefixHarmonic (N / linearDefectCutoff c) ≤ 1 + ℓ := by
    have h1 := RHTower.sum_Icc_one_div_le hM1
    have h2 : Real.log (N / linearDefectCutoff c : ℕ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hM1) (by exact_mod_cast hMN)
    unfold prefixHarmonic; rw [hℓN]; linarith only [h1, h2]
  have hLK := shortOrderWeight_le hK'1
  have hΨK := sum_vonMangoldt_range_le K'
  set M := N / linearDefectCutoff c
  set x := primeHorizonExtension z
  have hw0 : 0 < c / (N : ℝ) := div_pos hc0 hNR
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast (show linearDefectCutoff c ≤ N by omega)
    linarith only [h4c, hLNR, hc0]
  have hw1 : c / (N : ℝ) ≤ 1 := (div_le_one hNR).mpr hcN
  have hwB : (c / (N : ℝ)) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ ≤ Real.exp 1 * c := by
    have hBn_le : (⌊(N : ℝ) * Real.exp (c / N)⌋₊ : ℝ) ≤ N * Real.exp (c / N) :=
      Nat.floor_le (by positivity)
    have hwN : (c / (N : ℝ)) * N = c := by field_simp
    calc (c / (N : ℝ)) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊
        ≤ (c / (N : ℝ)) * (N * Real.exp (c / N)) := mul_le_mul_of_nonneg_left hBn_le hw0.le
      _ = c * Real.exp (c / N) := by rw [← mul_assoc, hwN]
      _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hc0.le
      _ = Real.exp 1 * c := by ring
  have hAB : ((M : ℝ) / 2) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
    have h1 : (N : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
      exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hNR.le (Real.one_le_exp hw0.le))
    have h2 : (M : ℝ) ≤ N := by exact_mod_cast hMN
    linarith only [h1, h2]
  obtain ⟨ΛK, hΛK_def⟩ : ∃ L : ℝ, L = β + 1 + (Real.log 4 + 4) := ⟨_, rfl⟩
  have hLK' : shortOrderWeight K' ≤ ΛK := by rw [hΛK_def]; linarith only [hLK, hlogK']
  have hΨK' : ∑ k ∈ range K', (Λ k : ℝ) ≤ (Real.log 4 + 4) * (2 * Real.exp β) :=
    hΨK.trans (mul_le_mul_of_nonneg_left hK'le (le_trans zero_le_one hC₄))
  have hWS := windowSumBound_div_le (M := M) x hh0 hh1 hCψ hpnt hw0.le hc0.le hwB
    (by positivity) hAB hLK' hΨK'
  have hwhΨ : ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)) ≤ 1 := by
    rw [hhdef]; exact window_ratio_le hNR hℓpos hexp
  have hwhΨ0 : 0 ≤ ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)) :=
    mul_nonneg (div_nonneg hw0.le hh0.le)
      (mul_nonneg (le_trans zero_le_one hC₄) (mul_nonneg zero_le_two (Real.exp_pos _).le))
  have hL2K : Real.log (2 * K') ≤ ΛK + 1 := by
    have hK'R : (0 : ℝ) < K' := by exact_mod_cast hK'1
    rw [Real.log_mul (by norm_num) hK'R.ne']
    have := Real.log_two_lt_d9
    rw [hΛK_def]; linarith only [hlogK', this, hC₄]
  have hL2K0 : 0 ≤ 1 + Real.log (2 * K') := by
    have hK'R : (1 : ℝ) ≤ K' := by exact_mod_cast hK'1
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * K' by linarith only [hK'R])
    linarith only [this]
  have hΛK1 : 1 ≤ ΛK := by rw [hΛK_def]; linarith only [hβ0, hC₄]
  have hΛKb : ΛK ≤ (C_β + 1 + (Real.log 4 + 4)) * lam ^ 2 := by
    have hl2 : 1 ≤ lam ^ 2 := one_le_pow₀ hlam1
    rw [hΛK_def]
    have := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ 1 + (Real.log 4 + 4) by linarith only [hC₄])
    linarith only [hβ, this]
  have hlogc : Real.log c ≤ Real.log ℓ := Real.log_le_log hc0 hcℓ
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have h9 := pow_le_rpow_of_le_rpow hc1 hcα' hℓ0 9
  have h16 := pow_le_rpow_of_le_rpow hc1 hcα' hℓ0 16
  norm_num at h9 h16
  have hγ : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
    nlinarith only [hc1, Real.exp_pos 1]
  have hηi : 16 * (1 + 2 * Real.exp 1 * c) / ((growingMassConstant / c ^ 7) * ℓ) ≤
      16 * (1 + 2 * Real.exp 1) * c ^ 8 / (growingMassConstant * ℓ) := by
    have hg₀ := growingMassConstant_pos
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : 16 * (1 + 2 * Real.exp 1 * c) * (growingMassConstant * ℓ) =
        (16 * (1 + 2 * Real.exp 1 * c) * c ^ 7) * ((growingMassConstant / c ^ 7) * ℓ) := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hγ (show (0 : ℝ) ≤ 16 * c ^ 7 by positivity)
    nlinarith only [this]
  have hηi0 : 0 ≤ 16 * (1 + 2 * Real.exp 1 * c) / ((growingMassConstant / c ^ 7) * ℓ) := by
    have hg₀ := growingMassConstant_pos; positivity
  have hH0 : 0 ≤ prefixHarmonic M := by
    unfold prefixHarmonic; exact sum_nonneg fun m _ => div_nonneg zero_le_one (Nat.cast_nonneg m)
  exact far_cost_window (C_B := C_β + 1 + (Real.log 4 + 4)) (C_L := 256 * Real.exp 2 + 4)
    (lam := lam) (α' := α') (H := prefixHarmonic M) (Ht := ∑ n ∈ Ioc M N, (1 : ℝ) / n)
    (L2K := Real.log (2 * K')) (ΛK := ΛK)
    (whΨ := ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)))
    hℓ1 hc1 hθ growingMassConstant_pos splineWindowConstant_nonneg
    (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _) hh0 hh1 hhℓ hH0 hHM
    hηi hηi0 hWS hσ (sq_nonneg _) hHt' hCL hL2K hL2K0 hΛK1 hΛKb hwhΨ hwhΨ0 hlogc hlogc0 h16 h9
    hlam hQS hQP

/-- The translate cost of the far reserve at fixed parameters. -/
theorem far_translate_cost {θ α α' c ℓ lam T h : ℝ} {N : ℕ} (hc1 : 1 ≤ c) (hcα : c ≤ ℓ ^ α)
    (hcα' : c ≤ ℓ ^ α') (hcℓ : c ≤ ℓ) (hℓN : ℓ = Real.log N) (hℓ1 : 1 ≤ ℓ)
    (h2LN : 2 * linearDefectCutoff c ≤ N) (hTh : T * h = 1 / ℓ) (hlogT : Real.log T = lam)
    (hlam : lam = ℓ ^ α') (hlamG : lam / 2 ≤ lam - factorialSpanGammaOffset) (hlam0 : 0 < lam)
    (hθ : 0 < θ)
    (hQd : 256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) *
      (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) /
      (growingMassConstant * θ) * ℓ ^ (9 * α' + 1) * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (4 : ℝ))
    (hQd' : 256 * (1 + 2 * Real.exp 2) *
      (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) / θ *
      ℓ ^ (α + 1) * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (1 + α')) :
    (16 * (1 + 2 * Real.exp 1 * c) / ((growingMassConstant / c ^ 7) * ℓ) * (T * h) ^ 2 +
        8 / (Real.log T - factorialSpanGammaOffset)) *
      ((1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
        (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
          (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ /
            (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) ≤
      θ / 4 * ℓ := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hN1 : 1 ≤ N := by
    have := (linearDefectCutoff_bounds hc1).1; omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hg₀ := growingMassConstant_pos
  have hK₂ : 0 ≤ Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4) := by
    have he1 := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    have he2 := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    have h1 : 0 ≤ Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) :=
      Real.log_nonneg (by nlinarith only [he1, he2])
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  have hΦ := translate_factor_le hc1 h2LN
  rw [← hℓN] at hΦ
  generalize hΦdef : (1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
      (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
        (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ /
          (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)) + 2 * (Real.log 4 + 4))) = Φ at hΦ ⊢
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hΦ' : Φ ≤ (1 + 2 * Real.exp 2) *
      (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) * c * (2 * ℓ) *
      (1 + Real.log c) := by
    refine hΦ.trans ?_
    have h1 : 1 + ℓ ≤ 2 * ℓ := by linarith only [hℓ1]
    have : 0 ≤ (1 + 2 * Real.exp 2) *
        (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) * c := by
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 this) (by linarith only [hlogc0])
  have hΦ0 : 0 ≤ Φ := by
    rw [← hΦdef]
    have hBn1 : (1 : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have : 1 ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := Nat.le_floor (by
        push_cast
        exact hN1R.trans (le_mul_of_one_le_right hNR.le
          (Real.one_le_exp (div_nonneg hc0.le hNR.le))))
      exact_mod_cast this
    have hlogBn := Real.log_nonneg hBn1
    have hM1 : 1 ≤ N / linearDefectCutoff c :=
      (Nat.le_div_iff_mul_le (by have := (linearDefectCutoff_bounds hc1).1; omega)).mpr (by omega)
    have hMN : N / linearDefectCutoff c ≤ N := Nat.div_le_self _ _
    have hrat : 1 ≤ 2 * (⌊(N : ℝ) * Real.exp (c / N)⌋₊ : ℝ) /
        (((N / linearDefectCutoff c : ℕ) : ℝ) / 2) := by
      have hM1R : (1 : ℝ) ≤ ((N / linearDefectCutoff c : ℕ) : ℝ) := by exact_mod_cast hM1
      rw [le_div_iff₀ (by linarith only [hM1R])]
      have h1 : ((N / linearDefectCutoff c : ℕ) : ℝ) ≤ N := by exact_mod_cast hMN
      have h2 : (N : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
        exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hNR.le
          (Real.one_le_exp (div_nonneg hc0.le hNR.le)))
      linarith only [h1, h2]
    have h3 := Real.log_nonneg hrat
    have hl4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    refine mul_nonneg (add_nonneg zero_le_one (mul_nonneg (by positivity)
      (mul_nonneg (div_nonneg hc0.le hNR.le) (Nat.cast_nonneg _)))) ?_
    exact mul_nonneg hlogBn (by linarith only [h3, hl4])
  have hγ : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
    nlinarith only [hc1, Real.exp_pos 1]
  have hηi : 16 * (1 + 2 * Real.exp 1 * c) / ((growingMassConstant / c ^ 7) * ℓ) ≤
      16 * (1 + 2 * Real.exp 1) * c ^ 8 / (growingMassConstant * ℓ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : 16 * (1 + 2 * Real.exp 1 * c) * (growingMassConstant * ℓ) =
        (16 * (1 + 2 * Real.exp 1 * c) * c ^ 7) * ((growingMassConstant / c ^ 7) * ℓ) := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hγ (show (0 : ℝ) ≤ 16 * c ^ 7 by positivity)
    nlinarith only [this]
  have h9 := pow_le_rpow_of_le_rpow hc1 hcα' hℓpos.le 9
  norm_num at h9
  rw [hTh, hlogT]
  exact far_cost_translate hℓ1 hc1 hθ hg₀ hK₂ hηi hΦ' hΦ0 h9 hcα
    (Real.log_le_log hc0 hcℓ) hlogc0 hQd hQd' hlam hlamG hlam0

/-- **The smoothing parameters.** At `λ = ℓ^{α'}`, `T = e^λ`, `h = e^{−λ}/ℓ` and the short-row
cutoff of `exists_short_cutoff`. -/
theorem exists_far_parameters {C_ψ c₀ t₀ α' ℓ : ℝ} (hCψ : 0 ≤ C_ψ) (hc₀ : 0 < c₀) (ht₀1 : 1 ≤ t₀)
    (hℓ1 : 1 ≤ ℓ)
    (hC0 : 2 * factorialSpanGammaOffset + 2 + Real.log (4 * C_ψ + 1) ≤ ℓ ^ α')
    (hlogℓ : Real.log ℓ ≤ ℓ ^ α') :
    ∃ (h T lam β : ℝ) (K' : ℕ), lam = ℓ ^ α' ∧ 1 ≤ lam ∧ h = Real.exp (-lam) / ℓ ∧ 0 < h ∧
      h ≤ 1 ∧ 0 < T ∧ factorialSpanGammaOffset + 1 ≤ Real.log T ∧ Real.log T = lam ∧
      T * h = 1 / ℓ ∧ h * (1 + ℓ) ≤ 2 ∧ lam / 2 ≤ lam - factorialSpanGammaOffset ∧ 1 ≤ K' ∧
      t₀ ≤ K' * Real.exp (-1) ∧ 4 * C_ψ * pntRate c₀ K' ≤ h ^ 2 ∧ Real.log K' ≤ β + 1 ∧
      (K' : ℝ) ≤ 2 * Real.exp β ∧ β ≤ (1 + 25 / c₀ ^ 2 + |Real.log t₀|) * lam ^ 2 ∧ 0 ≤ β := by
  have hG₀ : 0 ≤ factorialSpanGammaOffset := factorialSpanGammaOffset_nonneg
  have hlogC := Real.log_nonneg (show (1 : ℝ) ≤ 4 * C_ψ + 1 by linarith)
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  set lam := ℓ ^ α' with hlam
  have hlam1 : 1 ≤ lam := by linarith
  set h := Real.exp (-lam) / ℓ with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one hℓpos]
    exact (Real.exp_le_one_iff.mpr (by linarith)).trans hℓ1
  have hlog1h : Real.log (1 / h) = lam + Real.log ℓ := by
    rw [hh, one_div_div, Real.log_div hℓpos.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  obtain ⟨K', hK'1, ht₀', hpnt', hlogK', hK'le⟩ := exists_short_cutoff hCψ hc₀ ht₀1 hh0 hh1
  rw [hlog1h] at hlogK' hK'le
  refine ⟨h, Real.exp lam, lam,
    1 + ((2 * (lam + Real.log ℓ) + Real.log (4 * C_ψ + 1)) / c₀) ^ 2 + |Real.log t₀|, K',
    rfl, hlam1, rfl, hh0, hh1, Real.exp_pos _, ?_, Real.log_exp _, ?_, ?_, ?_, hK'1, ht₀', hpnt',
    hlogK', hK'le, ?_, by positivity⟩
  · rw [Real.log_exp]; linarith
  · rw [hh, mul_div_assoc', ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  · have h1 : h ≤ 1 / ℓ := by
      rw [hh]; exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) hℓpos.le
    have h2 : h * (1 + ℓ) ≤ 1 / ℓ * (1 + ℓ) := mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : 1 / ℓ * (1 + ℓ) ≤ 2 := by
      rw [one_div_mul_eq_div, div_le_iff₀ hℓpos]; linarith
    linarith
  · linarith
  · have hν : (2 * (lam + Real.log ℓ) + Real.log (4 * C_ψ + 1)) / c₀ ≤ 5 * lam / c₀ :=
      div_le_div_of_nonneg_right (by linarith) hc₀.le
    have hν0 : 0 ≤ (2 * (lam + Real.log ℓ) + Real.log (4 * C_ψ + 1)) / c₀ := by positivity
    have hsq := pow_le_pow_left₀ hν0 hν 2
    have e : (5 * lam / c₀) ^ 2 = 25 / c₀ ^ 2 * lam ^ 2 := by field_simp; ring
    have hl2 : 1 ≤ lam ^ 2 := one_le_pow₀ hlam1
    have := abs_nonneg (Real.log t₀)
    have h25 : 0 ≤ 25 / c₀ ^ 2 := by positivity
    nlinarith only [hsq, e, hl2, this, h25]

/-- The short-order Chebyshev condition `2 (log 4 + 4) c ℓ e^{λ+β} ≤ N`. -/
theorem far_exp_le {c ℓ lam β C_β α' : ℝ} {N : ℕ} (hN : Real.exp ℓ = N) (hc1 : 1 ≤ c)
    (hcℓ : c ≤ ℓ) (hℓ1 : 1 ≤ ℓ) (hα'0 : 0 < α') (hlam : lam = ℓ ^ α') (hCβ : 0 ≤ C_β)
    (hβ : β ≤ C_β * lam ^ 2)
    (hQ5 : (|Real.log (2 * (Real.log 4 + 4))| + 4 + C_β) * ℓ ^ (2 * α') *
      (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (1 : ℝ)) :
    2 * (Real.log 4 + 4) * c * ℓ * Real.exp (lam + β) ≤ N := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hC₄ : 1 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  rw [← hN]
  have hpos : 0 < 2 * (Real.log 4 + 4) * c * ℓ := by positivity
  rw [← Real.exp_log hpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by positivity) hℓpos.ne', Real.log_mul (by positivity) hc0.ne']
  have hlogc : Real.log c ≤ Real.log ℓ := Real.log_le_log hc0 hcℓ
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hl1 : Real.log (2 * (Real.log 4 + 4)) ≤ |Real.log (2 * (Real.log 4 + 4))| := le_abs_self _
  have hr1 : 1 ≤ ℓ ^ (2 * α') := Real.one_le_rpow hℓ1 (by linarith)
  have hlam2 : lam ≤ ℓ ^ (2 * α') := by
    rw [hlam]; exact Real.rpow_le_rpow_of_exponent_le hℓ1 (by linarith)
  have hlamsq : lam ^ 2 = ℓ ^ (2 * α') := by
    rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hℓpos.le]; ring_nf
  have hP1 : 1 ≤ 1 + Real.log ℓ := by linarith
  rw [pow_one, Real.rpow_one] at hQ5
  have hβ' : β ≤ C_β * ℓ ^ (2 * α') := hβ.trans_eq (by rw [hlamsq])
  have hA0 : 0 ≤ |Real.log (2 * (Real.log 4 + 4))| := abs_nonneg _
  set X := ℓ ^ (2 * α')
  set Y := 1 + Real.log ℓ
  have hXY : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hr1 hP1
  have hY0 : 0 ≤ Y := by linarith
  have t1 : |Real.log (2 * (Real.log 4 + 4))| ≤ |Real.log (2 * (Real.log 4 + 4))| * X * Y := by
    rw [mul_assoc]; exact le_mul_of_one_le_right hA0 hXY
  have t2 : Y ≤ X * Y := le_mul_of_one_le_left hY0 hr1
  have t3 : lam ≤ X * Y := hlam2.trans (le_mul_of_one_le_right (by linarith) hP1)
  have t4 : C_β * X ≤ C_β * X * Y := le_mul_of_one_le_right (by positivity) hP1
  linarith only [hQ5, hl1, t1, t2, t3, t4, hβ', hlogc, hlogℓ0]

/-- The two mass costs of the far reserve. -/
theorem far_mass_costs {C_S C_P θ α' c ℓ : ℝ} (hCS : 0 < C_S) (hCP : 0 < C_P) (hθ : 0 < θ)
    (hc1 : 1 ≤ c) (hcℓ : c ≤ ℓ) (hcα' : c ≤ ℓ ^ α') (hℓ1 : 1 ≤ ℓ)
    (hQa : 16 * C_S / growingMassConstant * ℓ ^ (8 * α') * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (1 : ℝ))
    (hQb : 4 * C_P / θ * ℓ ^ α' * (1 + Real.log ℓ) ^ 0 ≤ ℓ ^ (1 : ℝ)) :
    C_S * c * (1 + Real.log c) ≤ (1 / 16 : ℝ) * (growingMassConstant / c ^ 7) * ℓ ∧
      C_P * c ≤ θ / 4 * ℓ := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hℓ0 : 0 ≤ ℓ := le_trans zero_le_one hℓ1
  have hg₀ := growingMassConstant_pos
  have hlogc : 1 + Real.log c ≤ 1 + Real.log ℓ := by
    have := Real.log_le_log hc0 hcℓ; linarith
  have hlogc0 := Real.log_nonneg hc1
  have h8 := pow_le_rpow_of_le_rpow hc1 hcα' hℓ0 8
  norm_num at h8
  rw [pow_one, Real.rpow_one] at hQa
  rw [pow_zero, mul_one, Real.rpow_one] at hQb
  constructor
  · have key : 16 * C_S * c ^ 8 * (1 + Real.log c) ≤ growingMassConstant * ℓ := by
      calc 16 * C_S * c ^ 8 * (1 + Real.log c)
          ≤ 16 * C_S * ℓ ^ (8 * α') * (1 + Real.log ℓ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h8 (by positivity)) hlogc (by positivity)
              (by positivity)
        _ = growingMassConstant * (16 * C_S / growingMassConstant * ℓ ^ (8 * α') *
            (1 + Real.log ℓ)) := by field_simp
        _ ≤ growingMassConstant * ℓ := mul_le_mul_of_nonneg_left hQa hg₀.le
    rw [show (1 / 16 : ℝ) * (growingMassConstant / c ^ 7) * ℓ =
      (growingMassConstant * ℓ) / (16 * c ^ 7) by field_simp, le_div_iff₀ (by positivity)]
    linarith only [key, (by ring : C_S * c * (1 + Real.log c) * (16 * c ^ 7) =
      16 * C_S * c ^ 8 * (1 + Real.log c))]
  · calc C_P * c ≤ C_P * ℓ ^ α' := mul_le_mul_of_nonneg_left hcα' hCP.le
      _ = θ / 4 * (4 * C_P / θ * ℓ ^ α') := by field_simp
      _ ≤ θ / 4 * ℓ := mul_le_mul_of_nonneg_left hQb (by positivity)

/-- The eventual inequalities in `ℓ = log N` behind the far reserve below the eighth root. -/
theorem eventually_far_facts {α α' θ C_S C_P C_ψ c₀ t₀ : ℝ} (hαα' : α < α')
    (hα'0 : 0 < α') (hα'8 : α' < 1 / 8) :
    ∀ᶠ ℓ : ℝ in atTop, 1 ≤ ℓ ∧
      2 * factorialSpanGammaOffset + 2 + Real.log (4 * C_ψ + 1) ≤ ℓ ^ α' ∧
      Real.log ℓ ≤ ℓ ^ α' ∧ 2 * (256 * Real.exp 2 + 4) * ℓ ≤ Real.exp ℓ ∧
      2048 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 *
        (1 + Real.log (256 * Real.exp 2 + 4)) / growingMassConstant ^ 2 *
        ℓ ^ (16 * α') * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (2 : ℝ) ∧
      64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
        (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        ((1 + 25 / c₀ ^ 2 + |Real.log t₀|) + 1 + (Real.log 4 + 4)) ^ 2 /
        (growingMassConstant * θ) * ℓ ^ (13 * α') * (1 + Real.log ℓ) ^ 0 ≤ ℓ ^ (2 : ℝ) ∧
      16 * C_S / growingMassConstant * ℓ ^ (8 * α') * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (1 : ℝ) ∧
      4 * C_P / θ * ℓ ^ α' * (1 + Real.log ℓ) ^ 0 ≤ ℓ ^ (1 : ℝ) ∧
      256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) *
        (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) /
        (growingMassConstant * θ) * ℓ ^ (9 * α' + 1) * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (4 : ℝ) ∧
      256 * (1 + 2 * Real.exp 2) *
        (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)) / θ *
        ℓ ^ (α + 1) * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (1 + α') ∧
      (|Real.log (2 * (Real.log 4 + 4))| + 4 + (1 + 25 / c₀ ^ 2 + |Real.log t₀|)) *
        ℓ ^ (2 * α') * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (1 : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hα'0).eventually_ge_atTop
      (2 * factorialSpanGammaOffset + 2 + Real.log (4 * C_ψ + 1)),
    eventually_mul_rpow_polylog_le_rpow hα'0 1 1,
    eventually_ge_atTop (4 * (256 * Real.exp 2 + 4)),
    eventually_mul_rpow_polylog_le_rpow (show 16 * α' < 2 by linarith) 1 _,
    eventually_mul_rpow_polylog_le_rpow (show 13 * α' < 2 by linarith) 0 _,
    eventually_mul_rpow_polylog_le_rpow (show 8 * α' < 1 by linarith) 1 _,
    eventually_mul_rpow_polylog_le_rpow (show α' < 1 by linarith) 0 _,
    eventually_mul_rpow_polylog_le_rpow (show 9 * α' + 1 < 4 by linarith) 1 _,
    eventually_mul_rpow_polylog_le_rpow (show α + 1 < 1 + α' by linarith) 1 _,
    eventually_mul_rpow_polylog_le_rpow (show 2 * α' < 1 by linarith) 1 _]
    with ℓ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨h1, h2, ?_, ?_, h5, h6, h7, h8, h9, h10, h11⟩
  · rw [Real.rpow_zero, mul_one, one_mul, pow_one] at h3; linarith only [h3]
  · have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ ℓ by linarith)
    nlinarith only [hq, h4, h1]

/-- **The far reserve below the eighth root.** For `0 < α < 1/8` and every `θ > 0`, eventually
in `N` and uniformly across `1 ≤ c ≤ (log N)^α`, every pole-orthogonal vector keeps
`(7/8) D_M` on the prefix and `κ/(4c⁷) · log N` per unit top mass, at a cost of only
`θ log N` per unit prefix mass. The parameters are `log T = (log N)^{α'}`,
`h = 1/(T log N)` and `log K' ≍ (log 1/h)²` with `α' = (α + 1/8)/2`. -/
theorem eventually_completeWeilEnergy_far_reserve_below_one_eighth {α : ℝ} (hα0 : 0 < α)
    (hα : α < 1 / 8) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α →
      ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
        (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) +
          (growingMassConstant / c ^ 7) / 4 * Real.log N *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) -
          θ * Real.log N *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨C_S, C_P, C_ψ, c₀, t₀, hCS, hCP, hCψ, hc₀, ht₀1, hres⟩ :=
    exists_completeWeilEnergy_prefix_top_window_reserve
  have hαα' : α < (α + 1 / 8) / 2 := by linarith
  have hα'8 : (α + 1 / 8) / 2 < 1 / 8 := by linarith
  have hα'0 : 0 < (α + 1 / 8) / 2 := by linarith
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogN.eventually (eventually_far_facts (θ := θ) (C_S := C_S) (C_P := C_P)
    (C_ψ := C_ψ) (c₀ := c₀) (t₀ := t₀) hαα' hα'0 hα'8), eventually_ge_atTop 2] with N hN hN2
  intro c hc1 hcα z hz
  obtain ⟨hℓ1, hC0, hlogℓ, hexpℓ, hQS, hQP, hQa, hQb, hQd, hQd', hQ5⟩ := hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNexp : Real.exp (Real.log N) = N := Real.exp_log hNR
  have hcα' : c ≤ Real.log N ^ ((α + 1 / 8) / 2) :=
    hcα.trans (Real.rpow_le_rpow_of_exponent_le hℓ1 hαα'.le)
  have hcℓ : c ≤ Real.log N := hcα.trans ((Real.rpow_le_rpow_of_exponent_le hℓ1
    (show α ≤ 1 by linarith)).trans_eq (Real.rpow_one _))
  have h2LN : 2 * linearDefectCutoff c ≤ N := by
    obtain ⟨-, -, -, hLup⟩ := linearDefectCutoff_bounds hc1
    have hCL : (0 : ℝ) ≤ 256 * Real.exp 2 + 4 := by positivity
    have h1 : (2 * linearDefectCutoff c : ℝ) ≤ 2 * (256 * Real.exp 2 + 4) * Real.log N := by
      have := mul_le_mul_of_nonneg_left hcℓ hCL
      linarith only [this, hLup]
    have : ((2 * linearDefectCutoff c : ℕ) : ℝ) ≤ N := by
      push_cast; linarith only [h1, hexpℓ, hNexp]
    exact_mod_cast this
  obtain ⟨h, T, lam, β, K', hlam, hlam1, hhdef, hh0, hh1, hT0, hT, hlogT, hTh, hhℓ, hlamG, hK'1,
    ht₀', hpnt', hlogK', hK'le, hβ, hβ0⟩ := exists_far_parameters hCψ hc₀ ht₀1 hℓ1 hC0 hlogℓ
  have hCβ : 0 ≤ 1 + 25 / c₀ ^ 2 + |Real.log t₀| := by positivity
  have hexp := far_exp_le hNexp hc1 hcℓ hℓ1 hα'0 hlam hCβ hβ hQ5
  have hE := hres hc1 h2LN hz hh0 hh1 hT0 hT hK'1 ht₀'
  have hc := far_window_cost hc1 hcℓ hcα' rfl hℓ1 h2LN hN2 hz hh0 hh1 hhℓ hhdef hθ hCψ hpnt' hK'1
    hlogK' hK'le hβ hβ0 hlam hlam1 hexp hQS hQP
  have hd := far_translate_cost hc1 hcα hcα' hcℓ rfl hℓ1 h2LN hTh hlogT hlam hlamG
    (lt_of_lt_of_le one_pos hlam1) hθ hQd hQd'
  obtain ⟨ha, hb⟩ := far_mass_costs hCS hCP hθ hc1 hcℓ hcα' hℓ1 hQa hQb
  exact far_costs_combine (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg hθ.le (le_trans zero_le_one hℓ1)) hE ha hb hc hd

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
