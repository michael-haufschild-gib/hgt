import GaloisForLFunctions.RHTower.SelectionResonanceFactorizationBlock

/-!
# The large-value set of a factorized Dirichlet polynomial resonates: assembly

For `m ≥ 1000`, `D(u) = (2^{iu} + 3^{iu}) · Σ_{3m⁴ ≤ k ≤ 4m⁴} (k/4m⁴)^{20} k^{iu}` and the threshold
`V = 4m³ ≍ N^{3/4}` (`N = 6m⁴` the length), the large-value set
`E = {u ∈ [0, W] : |D(u)| ≥ V}` on the window `W = ⌊m²/P⌋ P` (`P = 2π/log(3/2)`) satisfies

* `E ⊆ [0, 3m]`, so `vol(E) ≤ 3m`;
* `∫_E cos(u log(3/2)) du ≥ m/10`, i.e. `Re ∫_E (3/2)^{iu} du ≥ m/10`.

Hence `|∫_E x^{iu} du| ≥ (m/10) ≥ (vol E)^{1/2} · √m/(10√3)` at the ratio `x = 3/2`: the measure part
of the large-value set has no square-root cancellation at this multiplicative frequency.  The proof
sums the period lower bound over the core periods `(k+1)P ≤ 1.38m`, bounds the transition periods
trivially, and uses nonnegativity beyond `kP ≥ 1.44m`.
-/

open Complex Set Finset intervalIntegral MeasureTheory Real

namespace RHTower

noncomputable section

/-- Number of full periods in `[0, m²]`. -/
def resWindowCount (m : ℕ) : ℕ := ⌊(m : ℝ) ^ 2 / resPeriod⌋₊

/-- The window `W = ⌊m²/P⌋ P`. -/
def resWindow (m : ℕ) : ℝ := (resWindowCount m : ℝ) * resPeriod

/-- The large-value set on the window. -/
def resLargeSet (m : ℕ) : Set ℝ :=
  Icc (0 : ℝ) (resWindow m) ∩ {u | 4 * (m : ℝ) ^ 3 ≤ ‖resPoly m u‖}

/-- Core period count `⌊1.38 m / P⌋`. -/
def resKA (m : ℕ) : ℕ := ⌊(69 / 50 : ℝ) * (m : ℝ) / resPeriod⌋₊

/-- First nonnegative period `⌊1.44 m / P⌋ + 1`. -/
def resKB (m : ℕ) : ℕ := ⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriod⌋₊ + 1

theorem resWindow_nonneg (m : ℕ) : 0 ≤ resWindow m := by
  unfold resWindow; have := resPeriod_pos; positivity

theorem resWindow_le (m : ℕ) : resWindow m ≤ (m : ℝ) ^ 2 := by
  unfold resWindow resWindowCount
  have hP := resPeriod_pos
  have h := Nat.floor_le (a := (m : ℝ) ^ 2 / resPeriod) (by positivity)
  calc (⌊(m : ℝ) ^ 2 / resPeriod⌋₊ : ℝ) * resPeriod ≤ ((m : ℝ) ^ 2 / resPeriod) * resPeriod := by
        gcongr
    _ = (m : ℝ) ^ 2 := by field_simp

theorem measurableSet_resLargeSet {m : ℕ} (hm : 1 ≤ m) : MeasurableSet (resLargeSet m) :=
  measurableSet_Icc.inter
    (measurableSet_le measurable_const ((continuous_resPoly hm).norm.measurable))

theorem resLargeSet_subset {m : ℕ} (hm : 5 ≤ m) : resLargeSet m ⊆ Icc 0 (3 * (m : ℝ)) := by
  intro u hu
  obtain ⟨⟨hu0, huW⟩, hlarge⟩ := hu
  refine ⟨hu0, ?_⟩
  by_contra hcon
  push Not at hcon
  have := norm_resPoly_lt_of_window hm hcon.le (le_trans huW (resWindow_le m))
  exact absurd hlarge (not_le.mpr this)

theorem volume_resLargeSet_le {m : ℕ} (hm : 5 ≤ m) :
    (volume (resLargeSet m)).toReal ≤ 3 * (m : ℝ) := by
  have h := measure_mono (μ := volume) (resLargeSet_subset hm)
  rw [Real.volume_Icc, sub_zero] at h
  have hfin : ENNReal.ofReal (3 * (m : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc (volume (resLargeSet m)).toReal ≤ (ENNReal.ofReal (3 * (m : ℝ))).toReal :=
        ENNReal.toReal_mono hfin h
    _ = 3 * (m : ℝ) := ENNReal.toReal_ofReal (by positivity)

/-! ## From the set integral to the window integral and its period decomposition -/

theorem integral_resLargeSet_eq {m : ℕ} (hm : 1 ≤ m) :
    ∫ u in resLargeSet m, Real.cos (resLam * u) =
      ∫ u in (0 : ℝ)..(resWindow m),
        (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u := by
  rw [intervalIntegral.integral_of_le (resWindow_nonneg m), ← integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_indicator (measurableSet_resLargeSet hm)]
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  apply Set.indicator_of_notMem
  intro hE
  exact hu hE.1

theorem intervalIntegrable_indicator_cos {m : ℕ} (hm : 1 ≤ m) (a b : ℝ) :
    IntervalIntegrable (fun u => (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u)
      volume a b := by
  have hcont : Continuous fun u : ℝ => Real.cos (resLam * u) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  exact ⟨(hcont.intervalIntegrable a b).1.indicator (measurableSet_resLargeSet hm),
    (hcont.intervalIntegrable a b).2.indicator (measurableSet_resLargeSet hm)⟩

theorem integral_window_eq_sum {m : ℕ} (hm : 1 ≤ m) :
    (∫ u in (0 : ℝ)..(resWindow m),
        (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u) =
      ∑ k ∈ Finset.range (resWindowCount m),
        ∫ u in ((k : ℝ) * resPeriod)..(((k : ℝ) + 1) * resPeriod),
          (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * resPeriod) (n := resWindowCount m)
    (f := fun u => (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u)
    (μ := volume) (fun k _ => intervalIntegrable_indicator_cos hm _ _)
  simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at h
  unfold resWindow
  rw [← h]

/-! ## Period lower bounds -/

theorem resKA_le_resWindowCount {m : ℕ} (hm : 2 ≤ m) : resKA m ≤ resWindowCount m := by
  unfold resKA resWindowCount
  apply Nat.floor_le_floor
  have hP := resPeriod_pos
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  apply div_le_div_of_nonneg_right _ hP.le
  nlinarith

theorem resKB_le_resWindowCount {m : ℕ} (hm : 1000 ≤ m) : resKB m ≤ resWindowCount m := by
  unfold resKB resWindowCount
  have hP := resPeriod_pos
  have hP19 := resPeriod_lt_nineteen
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriod⌋₊ : ℝ) ≤ (36 / 25 : ℝ) * (m : ℝ) / resPeriod :=
    Nat.floor_le (by positivity)
  have h2 : (m : ℝ) ^ 2 / resPeriod < (⌊(m : ℝ) ^ 2 / resPeriod⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h3 : (36 / 25 : ℝ) * (m : ℝ) / resPeriod + 1 ≤ (m : ℝ) ^ 2 / resPeriod - 1 := by
    rw [div_add_one hP.ne', div_sub_one hP.ne', div_le_div_iff_of_pos_right hP]
    nlinarith
  have : ((⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriod⌋₊ + 1 : ℕ) : ℝ) ≤
      (⌊(m : ℝ) ^ 2 / resPeriod⌋₊ : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

theorem resKA_le_resKB (m : ℕ) : resKA m ≤ resKB m := by
  unfold resKA resKB
  have hP := resPeriod_pos
  have : ⌊(69 / 50 : ℝ) * (m : ℝ) / resPeriod⌋₊ ≤ ⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriod⌋₊ := by
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hP.le
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  omega

/-- The core periods. -/
theorem period_lower_core {m : ℕ} (hm : 1000 ≤ m) {k : ℕ} (hk : k < resKA m) :
    2 * Real.sqrt 2 / resLam * ((k : ℝ) * resPeriod / ((201 / 100) * (m : ℝ))) ≤
      ∫ u in ((k : ℝ) * resPeriod)..(((k : ℝ) + 1) * resPeriod),
        (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hlam := resLam_pos
  -- `(k+1)P ≤ 1.38 m`
  have hkA : ((k : ℝ) + 1) * resPeriod ≤ (69 / 50) * (m : ℝ) := by
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ (resKA m : ℝ) := by exact_mod_cast hk
    have h2 : (resKA m : ℝ) ≤ (69 / 50 : ℝ) * (m : ℝ) / resPeriod :=
      Nat.floor_le (by positivity)
    push_cast at h1
    calc ((k : ℝ) + 1) * resPeriod ≤ ((69 / 50 : ℝ) * (m : ℝ) / resPeriod) * resPeriod := by
          gcongr; linarith
      _ = (69 / 50) * (m : ℝ) := by field_simp
  have hk0 : (k : ℝ) * resPeriod ≤ (69 / 50) * (m : ℝ) := by nlinarith
  -- `(k+1)P ≤ W ≤ m²`
  have hkW : ((k : ℝ) + 1) * resPeriod ≤ resWindow m := by
    unfold resWindow
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ (resWindowCount m : ℝ) := by
      exact_mod_cast le_trans hk (resKA_le_resWindowCount (by omega))
    push_cast at h1
    gcongr
  have hkm : ((k : ℝ) + 1) * resPeriod ≤ (m : ℝ) ^ 2 := le_trans hkW (resWindow_le m)
  -- the outer threshold
  have hκpos := resKappa_pos (by omega) (m := m) k
  have hκle := resKappa_le_sqrt_two_div_two hm hk0
  have hκ1 : resKappa m k ≤ 1 := by
    have := sqrt_two_lt; linarith
  set θ := Real.arccos (resKappa m k) with hθ
  have hθ1 : π / 4 ≤ θ := by
    have h := Real.arccos_le_arccos hκle
    have h4 : Real.arccos (Real.sqrt 2 / 2) = π / 4 :=
      Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos])
        Real.cos_pi_div_four.symm
    rw [h4] at h; exact h
  have hθ2 : θ < π / 2 := Real.arccos_lt_pi_div_two.mpr hκpos
  have hcosθ : Real.cos θ = resKappa m k := Real.cos_arccos (by linarith) hκ1
  have hsinθ : Real.sin θ = Real.sqrt (1 - resKappa m k ^ 2) := Real.sin_arccos _
  have hcore : ∀ u ∈ Icc ((k : ℝ) * resPeriod) (((k : ℝ) + 1) * resPeriod),
      Real.sqrt 2 / 2 ≤ |Real.cos (resLam * u / 2)| → u ∈ resLargeSet m := by
    intro u hu hcos
    refine ⟨⟨le_trans (by positivity) hu.1, le_trans hu.2 hkW⟩, ?_⟩
    exact resPoly_core hm hkA hu hcos
  have houter : ∀ u ∈ Icc ((k : ℝ) * resPeriod) (((k : ℝ) + 1) * resPeriod),
      u ∈ resLargeSet m → Real.cos θ ≤ |Real.cos (resLam * u / 2)| := by
    intro u hu hE
    rw [hcosθ]
    exact resPoly_outer (by omega) hkm hu hE.2
  have hmain := integral_indicator_cos_period_ge resLam_pos (measurableSet_resLargeSet (by omega))
    k hθ1 hθ2 hcore houter
  -- `sin 2θ ≥ √2 κ`
  have hsin : Real.sqrt 2 * resKappa m k ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul, hsinθ, hcosθ]
    have hsq : resKappa m k ^ 2 ≤ 1 / 2 := by
      have := pow_le_pow_left₀ hκpos.le hκle 2
      rw [div_pow, Real.sq_sqrt (by norm_num)] at this
      linarith
    have h1 : Real.sqrt 2 / 2 ≤ Real.sqrt (1 - resKappa m k ^ 2) := by
      rw [Real.le_sqrt (by positivity) (by linarith), div_pow, Real.sq_sqrt (by norm_num)]
      linarith
    nlinarith [hκpos.le]
  have hκge := resKappa_ge hm hk0
  calc 2 * Real.sqrt 2 / resLam * ((k : ℝ) * resPeriod / ((201 / 100) * (m : ℝ)))
      ≤ 2 * Real.sqrt 2 / resLam * resKappa m k := by gcongr
    _ = 2 / resLam * (Real.sqrt 2 * resKappa m k) := by ring
    _ ≤ 2 / resLam * Real.sin (2 * θ) := by gcongr
    _ ≤ _ := hmain

/-- Every period: the trivial bound `−P`. -/
theorem period_lower_neg {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    -resPeriod ≤ ∫ u in ((k : ℝ) * resPeriod)..(((k : ℝ) + 1) * resPeriod),
        (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u := by
  unfold resPeriod
  exact integral_indicator_cos_period_ge_neg resLam_pos (measurableSet_resLargeSet hm) k

/-- The nonnegative periods `kP ≥ 1.44 m`. -/
theorem period_lower_nonneg {m : ℕ} (hm : 1000 ≤ m) {k : ℕ} (hk : resKB m ≤ k)
    (hk' : k < resWindowCount m) :
    0 ≤ ∫ u in ((k : ℝ) * resPeriod)..(((k : ℝ) + 1) * resPeriod),
        (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hkB : (36 / 25) * (m : ℝ) ≤ (k : ℝ) * resPeriod := by
    have h1 : (resKB m : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : (36 / 25 : ℝ) * (m : ℝ) / resPeriod < (⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriod⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h3 : (resKB m : ℝ) = (⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriod⌋₊ : ℝ) + 1 := by
      unfold resKB; push_cast; ring
    have h4 : (36 / 25 : ℝ) * (m : ℝ) / resPeriod < k := by linarith
    rw [div_lt_iff₀ hP] at h4
    exact h4.le
  have hkW : ((k : ℝ) + 1) * resPeriod ≤ (m : ℝ) ^ 2 := by
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ (resWindowCount m : ℝ) := by exact_mod_cast hk'
    push_cast at h1
    calc ((k : ℝ) + 1) * resPeriod ≤ (resWindowCount m : ℝ) * resPeriod := by gcongr
      _ = resWindow m := rfl
      _ ≤ (m : ℝ) ^ 2 := resWindow_le m
  unfold resPeriod
  apply integral_indicator_cos_period_nonneg resLam_pos k
  intro u hu hE
  exact resPoly_nonneg_period hm hkB hkW hu hE.2

/-! ## Assembly -/

theorem resKA_ge (m : ℕ) : (69 / 50 : ℝ) * (m : ℝ) - resPeriod < (resKA m : ℝ) * resPeriod := by
  have hP := resPeriod_pos
  have h := Nat.lt_floor_add_one ((69 / 50 : ℝ) * (m : ℝ) / resPeriod)
  unfold resKA
  rw [div_lt_iff₀ hP] at h
  linarith

theorem resKA_le {m : ℕ} : (resKA m : ℝ) * resPeriod ≤ (69 / 50 : ℝ) * (m : ℝ) := by
  have hP := resPeriod_pos
  have h := Nat.floor_le (a := (69 / 50 : ℝ) * (m : ℝ) / resPeriod) (by positivity)
  unfold resKA
  calc (⌊(69 / 50 : ℝ) * (m : ℝ) / resPeriod⌋₊ : ℝ) * resPeriod
      ≤ ((69 / 50 : ℝ) * (m : ℝ) / resPeriod) * resPeriod := by gcongr
    _ = (69 / 50 : ℝ) * (m : ℝ) := by field_simp

theorem resKB_le {m : ℕ} : (resKB m : ℝ) * resPeriod ≤ (36 / 25 : ℝ) * (m : ℝ) + resPeriod := by
  have hP := resPeriod_pos
  have h := Nat.floor_le (a := (36 / 25 : ℝ) * (m : ℝ) / resPeriod) (by positivity)
  unfold resKB
  push_cast
  calc ((⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriod⌋₊ : ℝ) + 1) * resPeriod
      ≤ ((36 / 25 : ℝ) * (m : ℝ) / resPeriod + 1) * resPeriod := by gcongr
    _ = (36 / 25 : ℝ) * (m : ℝ) + resPeriod := by field_simp

theorem one_le_resKA {m : ℕ} (hm : 1000 ≤ m) : 1 ≤ resKA m := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hP19 := resPeriod_lt_nineteen
  have h := resKA_ge m
  by_contra hcon
  push Not at hcon
  have : resKA m = 0 := by omega
  rw [this] at h
  simp at h
  linarith

/-- **The resonance integral is at least `m/10`.** -/
theorem integral_resLargeSet_ge {m : ℕ} (hm : 1000 ≤ m) :
    (m : ℝ) / 10 ≤ ∫ u in resLargeSet m, Real.cos (resLam * u) := by
  rw [integral_resLargeSet_eq (by omega), integral_window_eq_sum (by omega)]
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hP12 := resPeriod_gt_twelve
  have hP19 := resPeriod_lt_nineteen
  have hlam := resLam_pos
  have hAB := resKA_le_resKB m
  have hBT := resKB_le_resWindowCount hm
  have hAT : resKA m ≤ resWindowCount m := le_trans hAB hBT
  -- split the sum
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, I = fun k : ℕ =>
      ∫ u in ((k : ℝ) * resPeriod)..(((k : ℝ) + 1) * resPeriod),
        (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u := ⟨_, rfl⟩
  have hsum0 : (∑ k ∈ Finset.range (resWindowCount m),
      ∫ u in ((k : ℝ) * resPeriod)..(((k : ℝ) + 1) * resPeriod),
        (resLargeSet m).indicator (fun u => Real.cos (resLam * u)) u) =
      ∑ k ∈ Finset.range (resWindowCount m), I k := by rw [hI]
  have hsum : (∑ k ∈ Finset.range (resWindowCount m), I k) =
      ∑ k ∈ Finset.range (resKA m), I k + ∑ k ∈ Finset.Ico (resKA m) (resKB m), I k +
        ∑ k ∈ Finset.Ico (resKB m) (resWindowCount m), I k := by
    rw [← Finset.sum_range_add_sum_Ico I hAT, ← Finset.sum_Ico_consecutive I hAB hBT]
    ring
  rw [hsum0, hsum]
  -- the three pieces
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * Real.sqrt 2 / resLam * (resPeriod / ((201 / 100) * (m : ℝ))) :=
    ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hS1 : c * ((resKA m : ℝ) * ((resKA m : ℝ) - 1) / 2) ≤ ∑ k ∈ Finset.range (resKA m), I k := by
    have h1 : ∑ k ∈ Finset.range (resKA m), c * (k : ℝ) ≤ ∑ k ∈ Finset.range (resKA m), I k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hI, hc]
      have := period_lower_core hm (Finset.mem_range.mp hk)
      calc 2 * Real.sqrt 2 / resLam * (resPeriod / ((201 / 100) * (m : ℝ))) * (k : ℝ)
          = 2 * Real.sqrt 2 / resLam * ((k : ℝ) * resPeriod / ((201 / 100) * (m : ℝ))) := by ring
        _ ≤ _ := this
    have h2 : ∑ k ∈ Finset.range (resKA m), c * (k : ℝ) =
        c * ((resKA m : ℝ) * ((resKA m : ℝ) - 1) / 2) := by
      rw [← Finset.mul_sum]
      congr 1
      have h3 := Finset.sum_range_id_mul_two (resKA m)
      have h4 : ((∑ i ∈ Finset.range (resKA m), i : ℕ) : ℝ) = ∑ k ∈ Finset.range (resKA m), (k : ℝ) := by
        push_cast; rfl
      have h5 : (((∑ i ∈ Finset.range (resKA m), i) * 2 : ℕ) : ℝ) =
          ((resKA m * (resKA m - 1) : ℕ) : ℝ) := by rw [h3]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (one_le_resKA hm), h4] at h5
      push_cast at h5
      linarith
    linarith
  have hS2 : -(resPeriod * (((resKB m : ℝ)) - (resKA m : ℝ))) ≤ ∑ k ∈ Finset.Ico (resKA m) (resKB m), I k := by
    have h := Finset.card_nsmul_le_sum (Finset.Ico (resKA m) (resKB m)) I (-resPeriod)
      (fun k _ => by rw [hI]; exact period_lower_neg (by omega) k)
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hAB] at h
    linarith
  have hS3 : 0 ≤ ∑ k ∈ Finset.Ico (resKB m) (resWindowCount m), I k := by
    apply Finset.sum_nonneg
    intro k hk
    rw [hI]
    have hk' := Finset.mem_Ico.mp hk
    exact period_lower_nonneg hm hk'.1 hk'.2
  -- the numerical assembly
  have hA1 := resKA_ge m
  have hA2 := resKA_le (m := m)
  have hB1 := resKB_le (m := m)
  have hs1 := sqrt_two_lt
  have hs2 : (14142 / 10000 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have hlamP : resLam * resPeriod = 2 * π := by unfold resPeriod; field_simp
  -- rewrite `c` through `1/λ = P/(2π)`
  have hcT : c * ((resKA m : ℝ) * ((resKA m : ℝ) - 1) / 2) =
      Real.sqrt 2 * (((resKA m : ℝ) * resPeriod) * (((resKA m : ℝ) - 1) * resPeriod)) /
        ((402 / 100) * π * (m : ℝ)) := by
    rw [hc]
    have hlam' : resLam = 2 * π / resPeriod := by
      rw [eq_div_iff hP.ne']; linarith [hlamP]
    rw [hlam']
    field_simp
    ring
  rw [hcT] at hS1
  -- lower bound of the product
  have hyA : (69 / 50 : ℝ) * (m : ℝ) - 19 ≤ (resKA m : ℝ) * resPeriod := by linarith
  have hyA' : (69 / 50 : ℝ) * (m : ℝ) - 38 ≤ ((resKA m : ℝ) - 1) * resPeriod := by nlinarith
  have hQ1 : (0 : ℝ) ≤ (69 / 50 : ℝ) * (m : ℝ) - 19 := by linarith
  have hQ2 : (0 : ℝ) ≤ (69 / 50 : ℝ) * (m : ℝ) - 38 := by linarith
  have hprod : ((69 / 50 : ℝ) * (m : ℝ) - 19) * ((69 / 50 : ℝ) * (m : ℝ) - 38) ≤
      ((resKA m : ℝ) * resPeriod) * (((resKA m : ℝ) - 1) * resPeriod) :=
    mul_le_mul hyA hyA' hQ2 (by linarith)
  have hT : (21 / 100 : ℝ) * (m : ℝ) - 9 ≤
      Real.sqrt 2 * (((resKA m : ℝ) * resPeriod) * (((resKA m : ℝ) - 1) * resPeriod)) /
        ((402 / 100) * π * (m : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hQ0 : 0 ≤ ((69 / 50 : ℝ) * (m : ℝ) - 19) * ((69 / 50 : ℝ) * (m : ℝ) - 38) :=
      mul_nonneg hQ1 hQ2
    have h1 : (14142 / 10000 : ℝ) * (((69 / 50 : ℝ) * (m : ℝ) - 19) * ((69 / 50 : ℝ) * (m : ℝ) - 38)) ≤
        Real.sqrt 2 * (((resKA m : ℝ) * resPeriod) * (((resKA m : ℝ) - 1) * resPeriod)) := by
      calc (14142 / 10000 : ℝ) * (((69 / 50 : ℝ) * (m : ℝ) - 19) * ((69 / 50 : ℝ) * (m : ℝ) - 38))
          ≤ Real.sqrt 2 * (((69 / 50 : ℝ) * (m : ℝ) - 19) * ((69 / 50 : ℝ) * (m : ℝ) - 38)) := by
            gcongr
        _ ≤ _ := by gcongr
    have hπ3 : π ≤ 315 / 100 := by norm_num at hπ2 ⊢; linarith
    have h2 : ((21 / 100 : ℝ) * (m : ℝ) - 9) * ((402 / 100) * π * (m : ℝ)) ≤
        ((21 / 100 : ℝ) * (m : ℝ) - 9) * ((402 / 100) * (315 / 100) * (m : ℝ)) := by
      have : (0 : ℝ) ≤ (21 / 100 : ℝ) * (m : ℝ) - 9 := by linarith
      gcongr
    have h3 : ((21 / 100 : ℝ) * (m : ℝ) - 9) * ((402 / 100) * (315 / 100) * (m : ℝ)) ≤
        (14142 / 10000 : ℝ) * (((69 / 50 : ℝ) * (m : ℝ) - 19) * ((69 / 50 : ℝ) * (m : ℝ) - 38)) := by
      nlinarith
    linarith
  have hloss : resPeriod * ((resKB m : ℝ) - (resKA m : ℝ)) ≤ (6 / 100 : ℝ) * (m : ℝ) + 38 := by
    nlinarith
  linarith

/-! ## The resonance integral of `(3/2)^{iu}` -/

theorem re_threeHalf_cpow (u : ℝ) :
    (((3 / 2 : ℝ) : ℂ) ^ ((u : ℂ) * I)).re = Real.cos (resLam * u) := by
  rw [cpow_ofReal_mul_I_eq_exp (by norm_num) u, Complex.exp_re]
  simp [resLam]

theorem integrableOn_threeHalf_cpow_resLargeSet {m : ℕ} (hm : 5 ≤ m) :
    IntegrableOn (fun u : ℝ => ((3 / 2 : ℝ) : ℂ) ^ ((u : ℂ) * I)) (resLargeSet m) := by
  have hc : Continuous fun u : ℝ => ((3 / 2 : ℝ) : ℂ) ^ ((u : ℂ) * I) :=
    continuous_cpow_const_ofReal_mul_I (by
      rw [Complex.mem_slitPlane_iff]; left; norm_num)
  exact (hc.integrableOn_Icc (a := 0) (b := 3 * (m : ℝ))).mono_set (resLargeSet_subset hm)

theorem re_integral_resLargeSet {m : ℕ} (hm : 5 ≤ m) :
    (∫ u in resLargeSet m, ((3 / 2 : ℝ) : ℂ) ^ ((u : ℂ) * I)).re =
      ∫ u in resLargeSet m, Real.cos (resLam * u) := by
  have h := integral_re (𝕜 := ℂ) (μ := volume.restrict (resLargeSet m))
    (integrableOn_threeHalf_cpow_resLargeSet hm)
  simp only [RCLike.re_to_complex, re_threeHalf_cpow] at h
  exact h.symm

/-- **The large-value set of the factorized polynomial resonates at the ratio `3/2`.**
For `m ≥ 1000`, with `D(u) = (2^{iu} + 3^{iu}) Σ_{3m⁴ ≤ k ≤ 4m⁴} (k/4m⁴)^{20} k^{iu}`, threshold `4m³`
and `E` its large-value set on the window `[0, ⌊m²/P⌋P]`:
`E ⊆ [0, 3m]`, `vol E ≤ 3m`, `Re ∫_E (3/2)^{iu} du ≥ m/10 ≥ vol(E)/30`, and
`(Re ∫_E (3/2)^{iu} du)² ≥ (m/300) · vol E`, so the resonance integral is not `O((vol E)^{1/2})`. -/
theorem selection_resonance_factorized {m : ℕ} (hm : 1000 ≤ m) :
    resLargeSet m ⊆ Icc 0 (3 * (m : ℝ)) ∧
    (volume (resLargeSet m)).toReal ≤ 3 * (m : ℝ) ∧
    (m : ℝ) / 10 ≤ (∫ u in resLargeSet m, ((3 / 2 : ℝ) : ℂ) ^ ((u : ℂ) * I)).re ∧
    (volume (resLargeSet m)).toReal / 30 ≤
      (∫ u in resLargeSet m, ((3 / 2 : ℝ) : ℂ) ^ ((u : ℂ) * I)).re ∧
    (m : ℝ) / 300 * (volume (resLargeSet m)).toReal ≤
      (∫ u in resLargeSet m, ((3 / 2 : ℝ) : ℂ) ^ ((u : ℂ) * I)).re ^ 2 := by
  have hm5 : 5 ≤ m := by omega
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hsub := resLargeSet_subset hm5
  have hvol := volume_resLargeSet_le hm5
  have hvol0 : 0 ≤ (volume (resLargeSet m)).toReal := ENNReal.toReal_nonneg
  have hre : (m : ℝ) / 10 ≤ (∫ u in resLargeSet m, ((3 / 2 : ℝ) : ℂ) ^ ((u : ℂ) * I)).re := by
    rw [re_integral_resLargeSet hm5]
    exact integral_resLargeSet_ge hm
  refine ⟨hsub, hvol, hre, by linarith, ?_⟩
  have h0 : 0 ≤ (m : ℝ) / 10 := by positivity
  calc (m : ℝ) / 300 * (volume (resLargeSet m)).toReal ≤ (m : ℝ) / 300 * (3 * (m : ℝ)) := by
        gcongr
    _ = ((m : ℝ) / 10) ^ 2 := by ring
    _ ≤ _ := pow_le_pow_left₀ h0 hre 2

end

end RHTower
