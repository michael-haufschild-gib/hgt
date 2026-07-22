import GaloisForLFunctions.RHTower.ConstrainedProlateLeakageStructure

/-!
# The constrained transfer needs only a polynomial ladder over a shared clock

Every ratio the exact constrained transfer forms between leakages at different indices cancels
the factor common to all of them.  The Gaussian factor `e^(−4πλ²)` of the Fuchs rate is
therefore inert: what drives the transfer is only the polynomial index ladder `λ^(2n+1)` and
the step-four separation `λ⁸`.

Accordingly this module replaces the Gaussian by an arbitrary eventually positive *clock*
`E : ℝ → ℝ`, setting

```text
clockRate E A n λ = A · λ^(2n+1) · E λ,
```

and shows that a leakage family trapped between two such rates at every fixed index — with
constants unrelated across indices, and with no assumption whatsoever on `E` beyond eventual
positivity — already satisfies every constrained law of the cards.

This matters for the passage to the true prolate operator: the exponential factor produced by a
particular Fourier normalization need not be `e^(−4πλ²)`, and the transfer must not depend on
which one it is.  A `FuchsEnvelope` is the special case whose clock is the Gaussian.
-/

open Filter

namespace RHTower

private theorem div_le_div_of_le_of_pos₅ {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  rw [div_le_iff₀ hc, div_mul_cancel₀ _ hc.ne']
  exact h

/-- A polynomial index ladder over a shared clock. -/
noncomputable def clockRate (E : ℝ → ℝ) (A : ℝ) (n : ℕ) (lam : ℝ) : ℝ :=
  A * lam ^ (2 * n + 1) * E lam

theorem clockRate_pos {E : ℝ → ℝ} {A lam : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hE : 0 < E lam) (n : ℕ) : 0 < clockRate E A n lam :=
  mul_pos (mul_pos hA (pow_pos hlam _)) hE

/-- One ladder step beats any constant ratio. -/
theorem clockRate_lt_step4 {E : ℝ → ℝ} {C c : ℝ} (hc : 0 < c) {lam : ℝ} (hlam : 0 < lam)
    (hE : 0 < E lam) (n : ℕ) (hpow : C / c < lam ^ 8) :
    clockRate E C n lam < clockRate E c (n + 4) lam := by
  have hpow' : C < lam ^ 8 * c := (div_lt_iff₀ hc).mp hpow
  have hCc : C < c * lam ^ 8 := by linarith
  have hP : (0 : ℝ) < lam ^ (2 * n + 1) := pow_pos hlam _
  unfold clockRate
  rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add lam (2 * n + 1) 8]
  calc C * lam ^ (2 * n + 1) * E lam
      = C * (lam ^ (2 * n + 1) * E lam) := by ring
    _ < c * lam ^ 8 * (lam ^ (2 * n + 1) * E lam) :=
        mul_lt_mul_of_pos_right hCc (mul_pos hP hE)
    _ = c * (lam ^ (2 * n + 1) * lam ^ 8) * E lam := by ring

/-- A ladder step beats twice any constant ratio, leaving half the higher rate as slack. -/
theorem clockRate_le_half_step4 {E : ℝ → ℝ} {C c : ℝ} (hc : 0 < c) {lam : ℝ} (hlam : 0 < lam)
    (hE : 0 < E lam) (n : ℕ) (hpow : 2 * C / c ≤ lam ^ 8) :
    clockRate E C n lam ≤ clockRate E c (n + 4) lam / 2 := by
  have hpow' : 2 * C ≤ lam ^ 8 * c := (div_le_iff₀ hc).mp hpow
  have hCc : C ≤ c * lam ^ 8 / 2 := by linarith
  have hP : (0 : ℝ) < lam ^ (2 * n + 1) := pow_pos hlam _
  unfold clockRate
  rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add lam (2 * n + 1) 8]
  calc C * lam ^ (2 * n + 1) * E lam
      = C * (lam ^ (2 * n + 1) * E lam) := by ring
    _ ≤ c * lam ^ 8 / 2 * (lam ^ (2 * n + 1) * E lam) :=
        mul_le_mul_of_nonneg_right hCc (mul_pos hP hE).le
    _ = c * (lam ^ (2 * n + 1) * lam ^ 8) * E lam / 2 := by ring

/-- The clock cancels across one ladder step, leaving an exact `λ⁻⁸`. -/
theorem clockRate_div_step4 {E : ℝ → ℝ} {C c : ℝ} (hc : c ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hE : E lam ≠ 0) (n : ℕ) :
    clockRate E C n lam / clockRate E c (n + 4) lam = C / c * (lam ^ 8)⁻¹ := by
  have hP : (lam : ℝ) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hlam.ne'
  unfold clockRate
  rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add lam (2 * n + 1) 8]
  field_simp

/-- The aperture-weighted step ratio against half the higher rate is exactly `2(C/c)λ⁻⁷`. -/
theorem clockRate_tail_bound_eq {E : ℝ → ℝ} {C c : ℝ} (hc : c ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hE : E lam ≠ 0) (n : ℕ) :
    lam * clockRate E C n lam / (clockRate E c (n + 4) lam / 2)
      = 2 * (C / c) * (lam ^ 7)⁻¹ := by
  have hP : (lam : ℝ) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hlam.ne'
  have h7 : (lam : ℝ) ^ 7 ≠ 0 := pow_ne_zero _ hlam.ne'
  have h8 : (lam : ℝ) ^ 8 = lam ^ 7 * lam := by ring
  unfold clockRate
  rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add lam (2 * n + 1) 8, h8]
  field_simp

/-! ## The clock envelope contract -/

/-- A leakage family along a step-four index ladder, trapped at every fixed index between two
polynomial rates over one shared, eventually positive clock. -/
structure ClockEnvelope (D : ℝ → ℕ → ℝ) (e : ℕ → ℕ) (E : ℝ → ℝ) : Prop where
  /-- One ladder step advances the index by four. -/
  step : ∀ j, e (j + 1) = e j + 4
  /-- The shared clock is eventually positive; nothing else about it is assumed. -/
  clock_pos : ∀ᶠ lam in atTop, 0 < E lam
  /-- Leakages are nonnegative. -/
  nonneg : ∀ lam j, 0 ≤ D lam j
  /-- Leakages increase along the ladder. -/
  mono : ∀ lam {i j : ℕ}, i ≤ j → D lam i ≤ D lam j
  /-- Each leakage is eventually bounded below by a positive rate of its own index. -/
  lower : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ᶠ lam in atTop, clockRate E c (e j) lam ≤ D lam j
  /-- Each leakage is eventually bounded above by a positive rate of its own index. -/
  upper : ∀ j, ∃ C : ℝ, 0 < C ∧ ∀ᶠ lam in atTop, D lam j ≤ clockRate E C (e j) lam

variable {D : ℝ → ℕ → ℝ} {e : ℕ → ℕ} {E : ℝ → ℝ}

/-- A clock envelope depends only on the germ of its clock at `atTop`. -/
theorem ClockEnvelope.congr_clock (h : ClockEnvelope D e E) {F : ℝ → ℝ}
    (hEF : E =ᶠ[atTop] F) : ClockEnvelope D e F where
  step := h.step
  clock_pos := by
    filter_upwards [h.clock_pos, hEF] with lam hpos hEq
    simpa only [hEq] using hpos
  nonneg := h.nonneg
  mono := h.mono
  lower := by
    intro j
    obtain ⟨c, hc, hlo⟩ := h.lower j
    refine ⟨c, hc, ?_⟩
    filter_upwards [hlo, hEF] with lam hlam hEq
    simpa only [clockRate, hEq] using hlam
  upper := by
    intro j
    obtain ⟨C, hC, hup⟩ := h.upper j
    refine ⟨C, hC, ?_⟩
    filter_upwards [hup, hEF] with lam hlam hEq
    simpa only [clockRate, hEq] using hlam

/-- Eventually equal clocks define equivalent envelope interfaces. -/
theorem clockEnvelope_congr_clock_iff {F : ℝ → ℝ} (hEF : E =ᶠ[atTop] F) :
    ClockEnvelope D e E ↔ ClockEnvelope D e F :=
  ⟨fun h => h.congr_clock hEF, fun h => h.congr_clock hEF.symm⟩

/-- Adjacent leakages eventually separate strictly. -/
theorem ClockEnvelope.lt_succ (h : ClockEnvelope D e E) (j : ℕ) :
    ∀ᶠ lam in atTop, D lam j < D lam (j + 1) := by
  obtain ⟨C, hC, hup⟩ := h.upper j
  obtain ⟨c, hc, hlo⟩ := h.lower (j + 1)
  filter_upwards [hup, hlo, h.clock_pos, eventually_gt_atTop (0 : ℝ),
    (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num)).eventually_gt_atTop (C / c)]
    with lam hu hl hEp hlam hpow
  have hkey : clockRate E C (e j) lam < clockRate E c (e (j + 1)) lam := by
    rw [h.step j]
    exact clockRate_lt_step4 hc hlam hEp (e j) hpow
  linarith

/-- **The collapse rate.**  Each leakage is negligible against its successor. -/
theorem ClockEnvelope.ratio_tendsto_zero (h : ClockEnvelope D e E) (j : ℕ) :
    Tendsto (fun lam => D lam j / D lam (j + 1)) atTop (nhds 0) := by
  obtain ⟨C, hC, hup⟩ := h.upper j
  obtain ⟨c, hc, hlo⟩ := h.lower (j + 1)
  have hbound : Tendsto (fun lam : ℝ => C / c * (lam ^ 8)⁻¹) atTop (nhds 0) := by
    have h8 := (tendsto_pow_atTop (α := ℝ) (n := 8)
      (by norm_num : (8 : ℕ) ≠ 0)).inv_tendsto_atTop
    simpa using h8.const_mul (C / c)
  refine squeeze_zero' (Eventually.of_forall fun lam =>
    div_nonneg (h.nonneg lam j) (h.nonneg lam (j + 1))) ?_ hbound
  filter_upwards [hup, hlo, h.clock_pos, eventually_gt_atTop (0 : ℝ)]
    with lam hu hl hEp hlam
  have hF2pos : 0 < clockRate E c (e (j + 1)) lam := clockRate_pos hc hlam hEp _
  have hD1pos : 0 < D lam (j + 1) := lt_of_lt_of_le hF2pos hl
  calc D lam j / D lam (j + 1)
      ≤ clockRate E C (e j) lam / D lam (j + 1) := div_le_div_of_le_of_pos₅ hu hD1pos
    _ ≤ clockRate E C (e j) lam / clockRate E c (e (j + 1)) lam :=
        div_le_div_of_nonneg_left (clockRate_pos hC hlam hEp _).le hF2pos hl
    _ = C / c * (lam ^ 8)⁻¹ := by
        rw [h.step j]
        exact clockRate_div_step4 hc.ne' hlam hEp.ne' (e j)

/-- **The tail rate.**  The aperture-weighted leakage is negligible against the next gap. -/
theorem ClockEnvelope.tail_tendsto_zero (h : ClockEnvelope D e E) (j : ℕ) :
    Tendsto (fun lam => lam * D lam (j + 1) / (D lam (j + 2) - D lam (j + 1)))
      atTop (nhds 0) := by
  obtain ⟨C, hC, hup⟩ := h.upper (j + 1)
  obtain ⟨c, hc, hlo⟩ := h.lower (j + 2)
  have hbound : Tendsto (fun lam : ℝ => 2 * (C / c) * (lam ^ 7)⁻¹) atTop (nhds 0) := by
    have h7 := (tendsto_pow_atTop (α := ℝ) (n := 7)
      (by norm_num : (7 : ℕ) ≠ 0)).inv_tendsto_atTop
    simpa using h7.const_mul (2 * (C / c))
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
    have hmon : D lam (j + 1) ≤ D lam (j + 2) := h.mono lam (by omega)
    exact div_nonneg (mul_nonneg hlam (h.nonneg lam (j + 1))) (by linarith)
  · filter_upwards [hup, hlo, h.clock_pos, eventually_gt_atTop (0 : ℝ),
      (tendsto_pow_atTop (α := ℝ) (n := 8)
        (by norm_num : (8 : ℕ) ≠ 0)).eventually_ge_atTop (2 * C / c)]
      with lam hu hl hEp hlam hpow
    have hF1pos : 0 < clockRate E C (e (j + 1)) lam := clockRate_pos hC hlam hEp _
    have hF2pos : 0 < clockRate E c (e (j + 2)) lam := clockRate_pos hc hlam hEp _
    have hhalf : clockRate E C (e (j + 1)) lam ≤ clockRate E c (e (j + 2)) lam / 2 := by
      rw [h.step (j + 1)]
      exact clockRate_le_half_step4 hc hlam hEp (e (j + 1)) hpow
    have hdenpos : 0 < clockRate E c (e (j + 2)) lam / 2 := by linarith
    have hden : clockRate E c (e (j + 2)) lam / 2 ≤ D lam (j + 2) - D lam (j + 1) := by
      linarith
    have hnum : lam * D lam (j + 1) ≤ lam * clockRate E C (e (j + 1)) lam :=
      mul_le_mul_of_nonneg_left hu hlam.le
    calc lam * D lam (j + 1) / (D lam (j + 2) - D lam (j + 1))
        ≤ lam * clockRate E C (e (j + 1)) lam / (D lam (j + 2) - D lam (j + 1)) :=
          div_le_div_of_le_of_pos₅ hnum (lt_of_lt_of_le hdenpos hden)
      _ ≤ lam * clockRate E C (e (j + 1)) lam / (clockRate E c (e (j + 2)) lam / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hlam.le hF1pos.le) hdenpos hden
      _ = 2 * (C / c) * (lam ^ 7)⁻¹ := by
          rw [h.step (j + 1)]
          exact clockRate_tail_bound_eq hc.ne' hlam hEp.ne' (e (j + 1))

/-- The first-gap structural hypothesis of the exact transfer theorems. -/
theorem ClockEnvelope.first_struct (h : ClockEnvelope D e E) :
    ∀ᶠ lam in atTop,
      (0 ≤ D lam 0 ∧ D lam 0 < D lam 1 ∧ D lam 1 < D lam 2) ∧
        ∀ j, D lam 2 ≤ D lam (j + 2) := by
  filter_upwards [h.lt_succ 0, h.lt_succ 1] with lam h1 h2
  exact ⟨⟨h.nonneg lam 0, h1, h2⟩, fun j => h.mono lam (by omega)⟩

/-- The depth-`k` structural hypothesis of the exact ladder theorems. -/
theorem ClockEnvelope.depth_struct (h : ClockEnvelope D e E) (k : ℕ) :
    ∀ᶠ lam in atTop,
      ((∀ j, j ≤ k → 0 ≤ D lam j ∧ D lam j ≤ D lam k) ∧
        D lam k < D lam (k + 1) ∧ D lam (k + 1) < D lam (k + 2)) ∧
        ∀ j, D lam (k + 2) ≤ D lam (j + (k + 2)) := by
  filter_upwards [h.lt_succ k, h.lt_succ (k + 1)] with lam h1 h2
  exact ⟨⟨fun j hj => ⟨h.nonneg lam j, h.mono lam hj⟩, h1, h2⟩,
    fun j => h.mono lam (by omega)⟩

/-! ## Every constrained law, over an arbitrary clock -/

variable {ℓ : ℝ → ℕ → ℝ}

/-- The exact constrained ground ratio for a clock-enveloped leakage family. -/
theorem ClockEnvelope.ground_ratio_tendsto (h : ClockEnvelope D e E)
    {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam => infiniteSecularRoot (D lam) (ℓ lam) / D lam 1) atTop
      (nhds (a0 ^ 2 / (a0 ^ 2 + a1 ^ 2))) :=
  infiniteSecularRoot_ratio_tendsto ha0 ha1 h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1

/-- The complementary exact constrained gap ratio. -/
theorem ClockEnvelope.gap_ratio_tendsto (h : ClockEnvelope D e E)
    {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam => (D lam 1 - infiniteSecularRoot (D lam) (ℓ lam)) / D lam 1) atTop
      (nhds (a1 ^ 2 / (a0 ^ 2 + a1 ^ 2))) :=
  infiniteSecularRoot_gap_ratio_tendsto ha0 ha1 h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1

/-- **The CCM `8/11` law over an arbitrary clock.** -/
theorem ClockEnvelope.ccm_ground_ratio_tendsto (h : ClockEnvelope D e E)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam => infiniteSecularRoot (D lam) (ℓ lam) / D lam 1) atTop
      (nhds (8 / 11)) :=
  ccm_infiniteSecularRoot_ratio_tendsto h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1

/-- **The CCM `3/11` gap law over an arbitrary clock.** -/
theorem ClockEnvelope.ccm_gap_ratio_tendsto (h : ClockEnvelope D e E)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam => (D lam 1 - infiniteSecularRoot (D lam) (ℓ lam)) / D lam 1) atTop
      (nhds (3 / 11)) :=
  ccm_infiniteSecularRoot_gap_ratio_tendsto h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1

/-- **The quantified CCM constrained spectral gap over an arbitrary clock.** -/
theorem ClockEnvelope.ccm_spectralGap_eventually (h : ClockEnvelope D e E)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))))
    {cst : ℝ} (hc : cst < 3 / 11) :
    ∀ᶠ lam in atTop, ∀ μ' : ℝ, infiniteSecular (D lam) (ℓ lam) μ' = 0 →
      μ' ≠ infiniteSecularRoot (D lam) (ℓ lam) →
      cst * D lam 1 ≤ μ' - infiniteSecularRoot (D lam) (ℓ lam) :=
  ccm_infiniteSecularRoot_spectralGap_eventually h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1 hc

/-- **The negative-sector `8/13` law over an arbitrary clock.** -/
theorem ClockEnvelope.ccm_negativeSector_ratio_tendsto (h : ClockEnvelope D e E)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam => infiniteSecularRoot (D lam) (ℓ lam) / D lam 1) atTop
      (nhds (8 / 13)) := by
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have hr := h.ground_ratio_tendsto ha0 ha1 hsum hbessel hl0 hl1
  rwa [ccm_negativeSector_hermite_weight_eq] at hr

/-- **The negative-sector `5/13` gap law over an arbitrary clock.** -/
theorem ClockEnvelope.ccm_negativeSector_gap_ratio_tendsto (h : ClockEnvelope D e E)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam => (D lam 1 - infiniteSecularRoot (D lam) (ℓ lam)) / D lam 1) atTop
      (nhds (5 / 13)) := by
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have hr := h.gap_ratio_tendsto ha0 ha1 hsum hbessel hl0 hl1
  rwa [ccm_negativeSector_hermite_weight_complement_eq] at hr

/-- **The exact all-depth CCM ladder over an arbitrary clock.** -/
theorem ClockEnvelope.ccm_depth_ratio_tendsto (h : ClockEnvelope D e E) (k : ℕ)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam => depthSecularRoot (D lam) (ℓ lam) k / D lam (k + 1)) atTop
      (nhds (constrainedProlateHermiteTheta k)) :=
  ccm_depthSecularRoot_ratio_tendsto (h.depth_struct k) hsum hbessel
    (h.ratio_tendsto_zero k) (h.tail_tendsto_zero k) hl

/-! ## The Gaussian clock is the Fuchs case -/

theorem fuchsRate_eq_clockRate (A : ℝ) (n : ℕ) (lam : ℝ) :
    fuchsRate A n lam
      = clockRate (fun l => Real.exp (-(4 * Real.pi * l ^ 2))) A n lam := rfl

/-- A Fuchs envelope is exactly a clock envelope whose clock is the Gaussian. -/
theorem FuchsEnvelope.toClockEnvelope (h : FuchsEnvelope D e) :
    ClockEnvelope D e (fun l => Real.exp (-(4 * Real.pi * l ^ 2))) where
  step := h.step
  clock_pos := Eventually.of_forall fun _ => Real.exp_pos _
  nonneg := h.nonneg
  mono := h.mono
  lower := h.lower
  upper := h.upper

/-- A Gaussian-clock envelope carries precisely the Fuchs bounds; its separate clock-positivity
field is automatic and can be discarded. -/
theorem ClockEnvelope.toFuchsEnvelope
    (h : ClockEnvelope D e (fun l => Real.exp (-(4 * Real.pi * l ^ 2)))) :
    FuchsEnvelope D e where
  step := h.step
  nonneg := h.nonneg
  mono := h.mono
  lower := h.lower
  upper := h.upper

/-- The Fuchs and Gaussian-clock envelope interfaces are logically equivalent. -/
theorem fuchsEnvelope_iff_gaussianClockEnvelope :
    FuchsEnvelope D e ↔
      ClockEnvelope D e (fun l => Real.exp (-(4 * Real.pi * l ^ 2))) :=
  ⟨FuchsEnvelope.toClockEnvelope, ClockEnvelope.toFuchsEnvelope⟩

/-- Any clock eventually equal to the Gaussian yields exactly the Fuchs envelope interface. -/
theorem fuchsEnvelope_iff_clockEnvelope_of_eventuallyEq_gaussian
    (hE : E =ᶠ[atTop] fun l => Real.exp (-(4 * Real.pi * l ^ 2))) :
    FuchsEnvelope D e ↔ ClockEnvelope D e E := by
  rw [fuchsEnvelope_iff_gaussianClockEnvelope,
    clockEnvelope_congr_clock_iff hE.symm]

end RHTower
