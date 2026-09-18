import GaloisForLFunctions.RHTower.SelectionResonanceFactorizationGeneralBlock

/-!
# The large-value set of the general factorized polynomial resonates: assembly

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
def resWindowCountL (L m : ℕ) : ℕ := ⌊(m : ℝ) ^ 2 / resPeriodL L⌋₊

/-- The window `W = ⌊m²/P⌋ P`. -/
def resWindowL (L m : ℕ) : ℝ := (resWindowCountL L m : ℝ) * resPeriodL L

/-- The large-value set on the window. -/
def resLargeSetL (L m : ℕ) : Set ℝ :=
  Icc (0 : ℝ) (resWindowL L m) ∩ {u | 4 * (m : ℝ) ^ 3 ≤ ‖resPolyL L m u‖}

/-- Core period count `⌊1.38 m / P⌋`. -/
def resKAL (L m : ℕ) : ℕ := ⌊(69 / 50 : ℝ) * (m : ℝ) / resPeriodL L⌋₊

/-- First nonnegative period `⌊1.44 m / P⌋ + 1`. -/
def resKBL (L m : ℕ) : ℕ := ⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ + 1

theorem resWindowL_nonneg {L : ℕ} (hL : 1 ≤ L) (m : ℕ) : 0 ≤ resWindowL L m := by
  unfold resWindowL; have := resPeriodL_pos hL; positivity

theorem resWindowL_le {L : ℕ} (hL : 1 ≤ L) (m : ℕ) : resWindowL L m ≤ (m : ℝ) ^ 2 := by
  unfold resWindowL resWindowCountL
  have hP := resPeriodL_pos hL
  have h := Nat.floor_le (a := (m : ℝ) ^ 2 / resPeriodL L) (by positivity)
  calc (⌊(m : ℝ) ^ 2 / resPeriodL L⌋₊ : ℝ) * resPeriodL L ≤ ((m : ℝ) ^ 2 / resPeriodL L) * resPeriodL L := by
        gcongr
    _ = (m : ℝ) ^ 2 := by field_simp

theorem measurableSet_resLargeSetL {L m : ℕ} (hL : 1 ≤ L) (hm : 1 ≤ m) : MeasurableSet (resLargeSetL L m) :=
  measurableSet_Icc.inter
    (measurableSet_le measurable_const ((continuous_resPolyL hL hm).norm.measurable))

theorem resLargeSetL_subset {L m : ℕ} (hL : 1 ≤ L) (hm : 5 ≤ m) : resLargeSetL L m ⊆ Icc 0 (3 * (m : ℝ)) := by
  intro u hu
  obtain ⟨⟨hu0, huW⟩, hlarge⟩ := hu
  refine ⟨hu0, ?_⟩
  by_contra hcon
  push Not at hcon
  have := norm_resPolyL_lt_of_window hL hm hcon.le (le_trans huW (resWindowL_le hL m))
  exact absurd hlarge (not_le.mpr this)

theorem volume_resLargeSetL_le {L m : ℕ} (hL : 1 ≤ L) (hm : 5 ≤ m) :
    (volume (resLargeSetL L m)).toReal ≤ 3 * (m : ℝ) := by
  have h := measure_mono (μ := volume) (resLargeSetL_subset hL hm)
  rw [Real.volume_Icc, sub_zero] at h
  have hfin : ENNReal.ofReal (3 * (m : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc (volume (resLargeSetL L m)).toReal ≤ (ENNReal.ofReal (3 * (m : ℝ))).toReal :=
        ENNReal.toReal_mono hfin h
    _ = 3 * (m : ℝ) := ENNReal.toReal_ofReal (by positivity)

/-! ## From the set integral to the window integral and its period decomposition -/

theorem integral_resLargeSetL_eq {L m : ℕ} (hL : 1 ≤ L) (hm : 1 ≤ m) :
    ∫ u in resLargeSetL L m, Real.cos (resLamL L * u) =
      ∫ u in (0 : ℝ)..(resWindowL L m),
        (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u := by
  rw [intervalIntegral.integral_of_le (resWindowL_nonneg hL m), ← integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_indicator (measurableSet_resLargeSetL hL hm)]
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  apply Set.indicator_of_notMem
  intro hE
  exact hu hE.1

theorem intervalIntegrable_indicator_cosL {L m : ℕ} (hL : 1 ≤ L) (hm : 1 ≤ m) (a b : ℝ) :
    IntervalIntegrable (fun u => (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u)
      volume a b := by
  have hcont : Continuous fun u : ℝ => Real.cos (resLamL L * u) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  exact ⟨(hcont.intervalIntegrable a b).1.indicator (measurableSet_resLargeSetL hL hm),
    (hcont.intervalIntegrable a b).2.indicator (measurableSet_resLargeSetL hL hm)⟩

theorem integral_windowL_eq_sum {L m : ℕ} (hL : 1 ≤ L) (hm : 1 ≤ m) :
    (∫ u in (0 : ℝ)..(resWindowL L m),
        (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u) =
      ∑ k ∈ Finset.range (resWindowCountL L m),
        ∫ u in ((k : ℝ) * resPeriodL L)..(((k : ℝ) + 1) * resPeriodL L),
          (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * resPeriodL L) (n := resWindowCountL L m)
    (f := fun u => (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u)
    (μ := volume) (fun k _ => intervalIntegrable_indicator_cosL hL hm _ _)
  simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at h
  unfold resWindowL
  rw [← h]

/-! ## Period lower bounds -/

theorem resKAL_le_resWindowCountL {L m : ℕ} (hL : 1 ≤ L) (hm : 2 ≤ m) : resKAL L m ≤ resWindowCountL L m := by
  unfold resKAL resWindowCountL
  apply Nat.floor_le_floor
  have hP := resPeriodL_pos hL
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  apply div_le_div_of_nonneg_right _ hP.le
  nlinarith

theorem resPeriodL_le_small {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) (hLm : 1000 * L ≤ m) :
    resPeriodL L ≤ (13 / 1000 : ℝ) * (m : ℝ) := by
  have h := resPeriodL_le hL
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hLmR : 1000 * (L : ℝ) ≤ m := by exact_mod_cast hLm
  have hπ := Real.pi_lt_d2
  norm_num at hπ
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith

theorem resKBL_le_resWindowCountL {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) (hLm : 1000 * L ≤ m) :
    resKBL L m ≤ resWindowCountL L m := by
  unfold resKBL resWindowCountL
  have hP := resPeriodL_pos hL
  have hP19 := resPeriodL_le_small hL hm hLm
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ : ℝ) ≤ (36 / 25 : ℝ) * (m : ℝ) / resPeriodL L :=
    Nat.floor_le (by positivity)
  have h2 : (m : ℝ) ^ 2 / resPeriodL L < (⌊(m : ℝ) ^ 2 / resPeriodL L⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h3 : (36 / 25 : ℝ) * (m : ℝ) / resPeriodL L + 1 ≤ (m : ℝ) ^ 2 / resPeriodL L - 1 := by
    rw [div_add_one hP.ne', div_sub_one hP.ne', div_le_div_iff_of_pos_right hP]
    nlinarith
  have : ((⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ + 1 : ℕ) : ℝ) ≤
      (⌊(m : ℝ) ^ 2 / resPeriodL L⌋₊ : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

theorem resKAL_le_resKBL {L : ℕ} (hL : 1 ≤ L) (m : ℕ) : resKAL L m ≤ resKBL L m := by
  unfold resKAL resKBL
  have hP := resPeriodL_pos hL
  have : ⌊(69 / 50 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ ≤ ⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ := by
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hP.le
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  omega

/-- The core periods. -/
theorem period_lowerL_core {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) {k : ℕ} (hk : k < resKAL L m) :
    2 * Real.sqrt 2 / resLamL L * ((k : ℝ) * resPeriodL L / ((201 / 100) * (m : ℝ))) ≤
      ∫ u in ((k : ℝ) * resPeriodL L)..(((k : ℝ) + 1) * resPeriodL L),
        (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hlam := resLamL_pos hL
  -- `(k+1)P ≤ 1.38 m`
  have hkA : ((k : ℝ) + 1) * resPeriodL L ≤ (69 / 50) * (m : ℝ) := by
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ (resKAL L m : ℝ) := by exact_mod_cast hk
    have h2 : (resKAL L m : ℝ) ≤ (69 / 50 : ℝ) * (m : ℝ) / resPeriodL L :=
      Nat.floor_le (by positivity)
    push_cast at h1
    calc ((k : ℝ) + 1) * resPeriodL L ≤ ((69 / 50 : ℝ) * (m : ℝ) / resPeriodL L) * resPeriodL L := by
          gcongr; linarith
      _ = (69 / 50) * (m : ℝ) := by field_simp
  have hk0 : (k : ℝ) * resPeriodL L ≤ (69 / 50) * (m : ℝ) := by nlinarith
  -- `(k+1)P ≤ W ≤ m²`
  have hkW : ((k : ℝ) + 1) * resPeriodL L ≤ resWindowL L m := by
    unfold resWindowL
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ (resWindowCountL L m : ℝ) := by
      exact_mod_cast le_trans hk (resKAL_le_resWindowCountL hL (by omega))
    push_cast at h1
    gcongr
  have hkm : ((k : ℝ) + 1) * resPeriodL L ≤ (m : ℝ) ^ 2 := le_trans hkW (resWindowL_le hL m)
  -- the outer threshold
  have hκpos := resKappaL_pos (L := L) (m := m) (by omega) k
  have hκle := resKappaL_le_sqrt_two_div_two hL hm hk0
  have hκ1 : resKappaL L m k ≤ 1 := by
    have := sqrt_two_lt; linarith
  set θ := Real.arccos (resKappaL L m k) with hθ
  have hθ1 : π / 4 ≤ θ := by
    have h := Real.arccos_le_arccos hκle
    have h4 : Real.arccos (Real.sqrt 2 / 2) = π / 4 :=
      Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos])
        Real.cos_pi_div_four.symm
    rw [h4] at h; exact h
  have hθ2 : θ < π / 2 := Real.arccos_lt_pi_div_two.mpr hκpos
  have hcosθ : Real.cos θ = resKappaL L m k := Real.cos_arccos (by linarith) hκ1
  have hsinθ : Real.sin θ = Real.sqrt (1 - resKappaL L m k ^ 2) := Real.sin_arccos _
  have hcore : ∀ u ∈ Icc ((k : ℝ) * resPeriodL L) (((k : ℝ) + 1) * resPeriodL L),
      Real.sqrt 2 / 2 ≤ |Real.cos (resLamL L * u / 2)| → u ∈ resLargeSetL L m := by
    intro u hu hcos
    refine ⟨⟨le_trans (by positivity) hu.1, le_trans hu.2 hkW⟩, ?_⟩
    exact resPolyL_core hL hm hkA hu hcos
  have houter : ∀ u ∈ Icc ((k : ℝ) * resPeriodL L) (((k : ℝ) + 1) * resPeriodL L),
      u ∈ resLargeSetL L m → Real.cos θ ≤ |Real.cos (resLamL L * u / 2)| := by
    intro u hu hE
    rw [hcosθ]
    exact resPolyL_outer hL (by omega) hkm hu hE.2
  have hmain := integral_indicator_cos_period_ge (resLamL_pos hL) (measurableSet_resLargeSetL hL (by omega))
    k hθ1 hθ2 hcore houter
  -- `sin 2θ ≥ √2 κ`
  have hsin : Real.sqrt 2 * resKappaL L m k ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul, hsinθ, hcosθ]
    have hsq : resKappaL L m k ^ 2 ≤ 1 / 2 := by
      have := pow_le_pow_left₀ hκpos.le hκle 2
      rw [div_pow, Real.sq_sqrt (by norm_num)] at this
      linarith
    have h1 : Real.sqrt 2 / 2 ≤ Real.sqrt (1 - resKappaL L m k ^ 2) := by
      rw [Real.le_sqrt (by positivity) (by linarith), div_pow, Real.sq_sqrt (by norm_num)]
      linarith
    nlinarith [hκpos.le]
  have hκge := resKappaL_ge hL hm hk0
  calc 2 * Real.sqrt 2 / resLamL L * ((k : ℝ) * resPeriodL L / ((201 / 100) * (m : ℝ)))
      ≤ 2 * Real.sqrt 2 / resLamL L * resKappaL L m k := by gcongr
    _ = 2 / resLamL L * (Real.sqrt 2 * resKappaL L m k) := by ring
    _ ≤ 2 / resLamL L * Real.sin (2 * θ) := by gcongr
    _ ≤ _ := hmain

/-- Every period: the trivial bound `−P`. -/
theorem period_lowerL_neg {L m : ℕ} (hL : 1 ≤ L) (hm : 1 ≤ m) (k : ℕ) :
    -resPeriodL L ≤ ∫ u in ((k : ℝ) * resPeriodL L)..(((k : ℝ) + 1) * resPeriodL L),
        (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u := by
  unfold resPeriodL
  exact integral_indicator_cos_period_ge_neg (resLamL_pos hL) (measurableSet_resLargeSetL hL hm) k

/-- The nonnegative periods `kP ≥ 1.44 m`. -/
theorem period_lowerL_nonneg {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) {k : ℕ} (hk : resKBL L m ≤ k)
    (hk' : k < resWindowCountL L m) :
    0 ≤ ∫ u in ((k : ℝ) * resPeriodL L)..(((k : ℝ) + 1) * resPeriodL L),
        (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hkB : (36 / 25) * (m : ℝ) ≤ (k : ℝ) * resPeriodL L := by
    have h1 : (resKBL L m : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : (36 / 25 : ℝ) * (m : ℝ) / resPeriodL L < (⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h3 : (resKBL L m : ℝ) = (⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ : ℝ) + 1 := by
      unfold resKBL; push_cast; ring
    have h4 : (36 / 25 : ℝ) * (m : ℝ) / resPeriodL L < k := by linarith
    rw [div_lt_iff₀ hP] at h4
    exact h4.le
  have hkW : ((k : ℝ) + 1) * resPeriodL L ≤ (m : ℝ) ^ 2 := by
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ (resWindowCountL L m : ℝ) := by exact_mod_cast hk'
    push_cast at h1
    calc ((k : ℝ) + 1) * resPeriodL L ≤ (resWindowCountL L m : ℝ) * resPeriodL L := by gcongr
      _ = resWindowL L m := rfl
      _ ≤ (m : ℝ) ^ 2 := resWindowL_le hL m
  unfold resPeriodL
  apply integral_indicator_cos_period_nonneg (resLamL_pos hL) k
  intro u hu hE
  exact resPolyL_nonneg_period hL hm hkB hkW hu hE.2

/-! ## Assembly -/

theorem resKAL_ge {L : ℕ} (hL : 1 ≤ L) (m : ℕ) : (69 / 50 : ℝ) * (m : ℝ) - resPeriodL L < (resKAL L m : ℝ) * resPeriodL L := by
  have hP := resPeriodL_pos hL
  have h := Nat.lt_floor_add_one ((69 / 50 : ℝ) * (m : ℝ) / resPeriodL L)
  unfold resKAL
  rw [div_lt_iff₀ hP] at h
  linarith

theorem resKAL_le {L m : ℕ} (hL : 1 ≤ L) : (resKAL L m : ℝ) * resPeriodL L ≤ (69 / 50 : ℝ) * (m : ℝ) := by
  have hP := resPeriodL_pos hL
  have h := Nat.floor_le (a := (69 / 50 : ℝ) * (m : ℝ) / resPeriodL L) (by positivity)
  unfold resKAL
  calc (⌊(69 / 50 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ : ℝ) * resPeriodL L
      ≤ ((69 / 50 : ℝ) * (m : ℝ) / resPeriodL L) * resPeriodL L := by gcongr
    _ = (69 / 50 : ℝ) * (m : ℝ) := by field_simp

theorem resKBL_le {L m : ℕ} (hL : 1 ≤ L) : (resKBL L m : ℝ) * resPeriodL L ≤ (36 / 25 : ℝ) * (m : ℝ) + resPeriodL L := by
  have hP := resPeriodL_pos hL
  have h := Nat.floor_le (a := (36 / 25 : ℝ) * (m : ℝ) / resPeriodL L) (by positivity)
  unfold resKBL
  push_cast
  calc ((⌊(36 / 25 : ℝ) * (m : ℝ) / resPeriodL L⌋₊ : ℝ) + 1) * resPeriodL L
      ≤ ((36 / 25 : ℝ) * (m : ℝ) / resPeriodL L + 1) * resPeriodL L := by gcongr
    _ = (36 / 25 : ℝ) * (m : ℝ) + resPeriodL L := by field_simp

theorem one_le_resKAL {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) (hLm : 1000 * L ≤ m) :
    1 ≤ resKAL L m := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hP19 := resPeriodL_le_small hL hm hLm
  have h := resKAL_ge hL m
  by_contra hcon
  push Not at hcon
  have : resKAL L m = 0 := by omega
  rw [this] at h
  simp at h
  linarith

/-- **The resonance integral is at least `m/10`.** -/
theorem integral_resLargeSetL_ge {L m : ℕ} (hL2 : 2 ≤ L) (hm : 1000 ≤ m) (hLm : 1000 * L ≤ m) :
    (m : ℝ) / 10 ≤ ∫ u in resLargeSetL L m, Real.cos (resLamL L * u) := by
  have hL : 1 ≤ L := by omega
  rw [integral_resLargeSetL_eq hL (by omega), integral_windowL_eq_sum hL (by omega)]
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hP12 := resPeriodL_gt_twelve hL2
  have hP19 := resPeriodL_le_small hL hm hLm
  have hlam := resLamL_pos hL
  have hAB := resKAL_le_resKBL hL m
  have hBT := resKBL_le_resWindowCountL hL hm hLm
  have hAT : resKAL L m ≤ resWindowCountL L m := le_trans hAB hBT
  -- split the sum
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, I = fun k : ℕ =>
      ∫ u in ((k : ℝ) * resPeriodL L)..(((k : ℝ) + 1) * resPeriodL L),
        (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u := ⟨_, rfl⟩
  have hsum0 : (∑ k ∈ Finset.range (resWindowCountL L m),
      ∫ u in ((k : ℝ) * resPeriodL L)..(((k : ℝ) + 1) * resPeriodL L),
        (resLargeSetL L m).indicator (fun u => Real.cos (resLamL L * u)) u) =
      ∑ k ∈ Finset.range (resWindowCountL L m), I k := by rw [hI]
  have hsum : (∑ k ∈ Finset.range (resWindowCountL L m), I k) =
      ∑ k ∈ Finset.range (resKAL L m), I k + ∑ k ∈ Finset.Ico (resKAL L m) (resKBL L m), I k +
        ∑ k ∈ Finset.Ico (resKBL L m) (resWindowCountL L m), I k := by
    rw [← Finset.sum_range_add_sum_Ico I hAT, ← Finset.sum_Ico_consecutive I hAB hBT]
    ring
  rw [hsum0, hsum]
  -- the three pieces
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * Real.sqrt 2 / resLamL L * (resPeriodL L / ((201 / 100) * (m : ℝ))) :=
    ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hS1 : c * ((resKAL L m : ℝ) * ((resKAL L m : ℝ) - 1) / 2) ≤ ∑ k ∈ Finset.range (resKAL L m), I k := by
    have h1 : ∑ k ∈ Finset.range (resKAL L m), c * (k : ℝ) ≤ ∑ k ∈ Finset.range (resKAL L m), I k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hI, hc]
      have := period_lowerL_core hL hm (Finset.mem_range.mp hk)
      calc 2 * Real.sqrt 2 / resLamL L * (resPeriodL L / ((201 / 100) * (m : ℝ))) * (k : ℝ)
          = 2 * Real.sqrt 2 / resLamL L * ((k : ℝ) * resPeriodL L / ((201 / 100) * (m : ℝ))) := by ring
        _ ≤ _ := this
    have h2 : ∑ k ∈ Finset.range (resKAL L m), c * (k : ℝ) =
        c * ((resKAL L m : ℝ) * ((resKAL L m : ℝ) - 1) / 2) := by
      rw [← Finset.mul_sum]
      congr 1
      have h3 := Finset.sum_range_id_mul_two (resKAL L m)
      have h4 : ((∑ i ∈ Finset.range (resKAL L m), i : ℕ) : ℝ) = ∑ k ∈ Finset.range (resKAL L m), (k : ℝ) := by
        push_cast; rfl
      have h5 : (((∑ i ∈ Finset.range (resKAL L m), i) * 2 : ℕ) : ℝ) =
          ((resKAL L m * (resKAL L m - 1) : ℕ) : ℝ) := by rw [h3]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (one_le_resKAL hL hm hLm), h4] at h5
      push_cast at h5
      linarith
    linarith
  have hS2 : -(resPeriodL L * (((resKBL L m : ℝ)) - (resKAL L m : ℝ))) ≤ ∑ k ∈ Finset.Ico (resKAL L m) (resKBL L m), I k := by
    have h := Finset.card_nsmul_le_sum (Finset.Ico (resKAL L m) (resKBL L m)) I (-resPeriodL L)
      (fun k _ => by rw [hI]; exact period_lowerL_neg hL (by omega) k)
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hAB] at h
    linarith
  have hS3 : 0 ≤ ∑ k ∈ Finset.Ico (resKBL L m) (resWindowCountL L m), I k := by
    apply Finset.sum_nonneg
    intro k hk
    rw [hI]
    have hk' := Finset.mem_Ico.mp hk
    exact period_lowerL_nonneg hL hm hk'.1 hk'.2
  -- the numerical assembly
  have hA1 := resKAL_ge hL m
  have hA2 := resKAL_le (m := m) hL
  have hB1 := resKBL_le (m := m) hL
  have hs1 := sqrt_two_lt
  have hs2 : (14142 / 10000 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have hlamP : resLamL L * resPeriodL L = 2 * π := by unfold resPeriodL; field_simp
  -- rewrite `c` through `1/λ = P/(2π)`
  have hcT : c * ((resKAL L m : ℝ) * ((resKAL L m : ℝ) - 1) / 2) =
      Real.sqrt 2 * (((resKAL L m : ℝ) * resPeriodL L) * (((resKAL L m : ℝ) - 1) * resPeriodL L)) /
        ((402 / 100) * π * (m : ℝ)) := by
    rw [hc]
    have hlam' : resLamL L = 2 * π / resPeriodL L := by
      rw [eq_div_iff hP.ne']; linarith [hlamP]
    rw [hlam']
    field_simp
    ring
  rw [hcT] at hS1
  -- lower bound of the product
  have hyA : (1367 / 1000 : ℝ) * (m : ℝ) ≤ (resKAL L m : ℝ) * resPeriodL L := by linarith
  have hyA' : (1354 / 1000 : ℝ) * (m : ℝ) ≤ ((resKAL L m : ℝ) - 1) * resPeriodL L := by nlinarith
  have hQ1 : (0 : ℝ) ≤ (1367 / 1000 : ℝ) * (m : ℝ) := by positivity
  have hQ2 : (0 : ℝ) ≤ (1354 / 1000 : ℝ) * (m : ℝ) := by positivity
  have hprod : ((1367 / 1000 : ℝ) * (m : ℝ)) * ((1354 / 1000 : ℝ) * (m : ℝ)) ≤
      ((resKAL L m : ℝ) * resPeriodL L) * (((resKAL L m : ℝ) - 1) * resPeriodL L) :=
    mul_le_mul hyA hyA' hQ2 (by linarith)
  have hT : (206 / 1000 : ℝ) * (m : ℝ) ≤
      Real.sqrt 2 * (((resKAL L m : ℝ) * resPeriodL L) * (((resKAL L m : ℝ) - 1) * resPeriodL L)) /
        ((402 / 100) * π * (m : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hQ0 : 0 ≤ ((1367 / 1000 : ℝ) * (m : ℝ)) * ((1354 / 1000 : ℝ) * (m : ℝ)) := mul_nonneg hQ1 hQ2
    have h1 : (14142 / 10000 : ℝ) * (((1367 / 1000 : ℝ) * (m : ℝ)) * ((1354 / 1000 : ℝ) * (m : ℝ))) ≤
        Real.sqrt 2 * (((resKAL L m : ℝ) * resPeriodL L) * (((resKAL L m : ℝ) - 1) * resPeriodL L)) := by
      calc (14142 / 10000 : ℝ) * (((1367 / 1000 : ℝ) * (m : ℝ)) * ((1354 / 1000 : ℝ) * (m : ℝ)))
          ≤ Real.sqrt 2 * (((1367 / 1000 : ℝ) * (m : ℝ)) * ((1354 / 1000 : ℝ) * (m : ℝ))) := by
            gcongr
        _ ≤ _ := by gcongr
    have hπ3 : π ≤ 315 / 100 := by norm_num at hπ2 ⊢; linarith
    have h2 : ((206 / 1000 : ℝ) * (m : ℝ)) * ((402 / 100) * π * (m : ℝ)) ≤
        ((206 / 1000 : ℝ) * (m : ℝ)) * ((402 / 100) * (315 / 100) * (m : ℝ)) := by
      have : (0 : ℝ) ≤ (206 / 1000 : ℝ) * (m : ℝ) := by positivity
      gcongr
    have h3 : ((206 / 1000 : ℝ) * (m : ℝ)) * ((402 / 100) * (315 / 100) * (m : ℝ)) ≤
        (14142 / 10000 : ℝ) * (((1367 / 1000 : ℝ) * (m : ℝ)) * ((1354 / 1000 : ℝ) * (m : ℝ))) := by
      nlinarith
    linarith
  have hloss : resPeriodL L * ((resKBL L m : ℝ) - (resKAL L m : ℝ)) ≤ (86 / 1000 : ℝ) * (m : ℝ) := by
    nlinarith
  linarith

/-! ## The resonance integral of `(3/2)^{iu}` -/

/-- The factor `(L+1)/L` as a real number. -/
def resFactor (L : ℕ) : ℝ := ((L : ℝ) + 1) / (L : ℝ)

theorem resFactor_pos {L : ℕ} (hL : 1 ≤ L) : 0 < resFactor L := by
  unfold resFactor
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity

theorem re_factorL_cpow {L : ℕ} (hL : 1 ≤ L) (u : ℝ) :
    (((resFactor L : ℝ) : ℂ) ^ ((u : ℂ) * I)).re = Real.cos (resLamL L * u) := by
  rw [cpow_ofReal_mul_I_eq_exp (resFactor_pos hL) u, Complex.exp_re]
  simp [resLamL, resFactor]

theorem integrableOn_factorL_cpow_resLargeSetL {L m : ℕ} (hL : 1 ≤ L) (hm : 5 ≤ m) :
    IntegrableOn (fun u : ℝ => ((resFactor L : ℝ) : ℂ) ^ ((u : ℂ) * I)) (resLargeSetL L m) := by
  have hpos := resFactor_pos hL
  have hc : Continuous fun u : ℝ => ((resFactor L : ℝ) : ℂ) ^ ((u : ℂ) * I) :=
    continuous_cpow_const_ofReal_mul_I (by
      rw [Complex.mem_slitPlane_iff]; left; simpa using hpos)
  exact (hc.integrableOn_Icc (a := 0) (b := 3 * (m : ℝ))).mono_set (resLargeSetL_subset hL hm)

theorem re_integral_resLargeSetL {L m : ℕ} (hL : 1 ≤ L) (hm : 5 ≤ m) :
    (∫ u in resLargeSetL L m, ((resFactor L : ℝ) : ℂ) ^ ((u : ℂ) * I)).re =
      ∫ u in resLargeSetL L m, Real.cos (resLamL L * u) := by
  have h := integral_re (𝕜 := ℂ) (μ := volume.restrict (resLargeSetL L m))
    (integrableOn_factorL_cpow_resLargeSetL hL hm)
  simp only [RCLike.re_to_complex, re_factorL_cpow hL] at h
  exact h.symm

/-- **Threshold-scaling instance of the resonance law.**  For `2 ≤ L ≤ m/1000` and `m ≥ 1000`,
`D_L(u) = (L^{iu} + (L+1)^{iu}) Σ_{3m⁴ ≤ k ≤ 4m⁴} (k/4m⁴)^{20} k^{iu}` (length `N = 3Lm⁴`, bounded
coefficients) at threshold `4m³` has large-value set `E` on the window with `E ⊆ [0,3m]`,
`vol E ≤ 3m`, and `Re ∫_E ((L+1)/L)^{iu} du ≥ m/10 ≥ vol(E)/30`: full resonance at the coprime
ratio `(L+1)/L` of height `L + 1`. -/
theorem selection_resonance_factorized_general {L m : ℕ} (hL2 : 2 ≤ L) (hm : 1000 ≤ m)
    (hLm : 1000 * L ≤ m) :
    resLargeSetL L m ⊆ Icc 0 (3 * (m : ℝ)) ∧
    (volume (resLargeSetL L m)).toReal ≤ 3 * (m : ℝ) ∧
    (m : ℝ) / 10 ≤ (∫ u in resLargeSetL L m, ((resFactor L : ℝ) : ℂ) ^ ((u : ℂ) * I)).re ∧
    (volume (resLargeSetL L m)).toReal / 30 ≤
      (∫ u in resLargeSetL L m, ((resFactor L : ℝ) : ℂ) ^ ((u : ℂ) * I)).re := by
  have hL : 1 ≤ L := by omega
  have hm5 : 5 ≤ m := by omega
  have hsub := resLargeSetL_subset hL hm5
  have hvol := volume_resLargeSetL_le hL hm5
  have hre : (m : ℝ) / 10 ≤
      (∫ u in resLargeSetL L m, ((resFactor L : ℝ) : ℂ) ^ ((u : ℂ) * I)).re := by
    rw [re_integral_resLargeSetL hL hm5]
    exact integral_resLargeSetL_ge hL2 hm hLm
  exact ⟨hsub, hvol, hre, by linarith⟩

end

end RHTower
