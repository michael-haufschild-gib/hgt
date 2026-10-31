import GaloisForLFunctions.RHTower.Heat.TheLocalHeatThreshold
import GaloisForLFunctions.RHTower.SpeiserShadowExponentialDensity

/-!
# The local heat threshold has Selberg's exponential tail

Let `λ_t` be the local heat threshold (`localHeatThreshold`) and `L = log U`.

**Theorem** (`exists_volume_localHeatThreshold_gt_le_exp`).  There are `A, K ≥ 0` such that for all
large `U` there are heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` with, for every
`2 ≤ κ ≤ L/2 − 2`,

  `|{t ∈ [T₁ + ½, T₂ − ½] : λ_t > κ²/(3L²)}| ≤ A (T₂ − T₁) e^{−κ/2400} + K L²`.

So `λ_t log² t` has an exponential tail in `√·` on average: `λ_t ≍ 1/log² t` at typical heights, and
the heights with `λ_t > κ/log U` have measure `≪ U exp(−√(3κ log U)/2400) + log² U`
(`eventually_volume_localHeatThreshold_gt_le_exp`), a rate for the density statement
`eventually_volume_localHeatThreshold_gt_le`.

**Mean value** (`exists_integral_localHeatThreshold_le`).  `∫_{U/4+2}^{U/2−2} λ_t dt ≤ C U/log² U`.
The layer-cake bound (`setIntegral_le_layers`) over the layers `λ_j = (j + 2)²/(3L²)`, `j ≤ L/2 − 4`,
capped by `λ_t ≤ λ_WD < 1/12`, sums the tail: `Σ_j (2j + 5) e^{−(j+2)/2400}` is bounded.

**Proof.**  If `λ_t > κ²/(3L²)`, the cone-defect bound (`localHeatThreshold_le_of_cone`) gives a zero
`ρ` with `(Re ρ − ½)² > (Im ρ − t)² + κ²/L²`: depth `> κ/L` and `|t − Im ρ| < |Re ρ − ½|`.  So `t` lies in
the `κ`-shadow of the zeros of depth `≥ κ/L`, whose measure is the Selberg tail bound
`exists_speiserShadow_exponential_density`.
-/

open Complex Set MeasureTheory Filter

namespace RHTower.DeBruijn

/-- Above heat `κ²/(3L²)` the height lies in the `κ`-shadow: some zero has depth `≥ κ/L` and lies
within its depth of `t`. -/
theorem exists_shadow_of_lt_localHeatThreshold {t κ L : ℝ} (hκ : 0 ≤ κ) (hL : 0 < L)
    (h : κ ^ 2 / (3 * L ^ 2) < localHeatThreshold t) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ κ / L ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2| := by
  by_contra hne
  have hcone : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2
      ≤ ((xiSpectralPoint q).re - t) ^ 2 + 3 * (κ ^ 2 / (3 * L ^ 2)) := by
    intro q
    by_contra hq
    push Not at hq
    have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    rw [hre, him, neg_sq, show 3 * (κ ^ 2 / (3 * L ^ 2)) = (κ / L) ^ 2 by field_simp] at hq
    refine hne ⟨q.1, xi_eq_zero_of_mem_divisor_support q.1, ?_, ?_⟩
    · have h1 : (κ / L) ^ 2 < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by nlinarith [sq_nonneg ((q.1 : ℂ).im - t)]
      have := sq_lt_sq.mp h1
      rw [abs_of_nonneg (div_nonneg hκ hL.le)] at this
      exact this.le
    · have h1 : (t - (q.1 : ℂ).im) ^ 2 < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
        nlinarith [sq_nonneg (κ / L)]
      exact (sq_lt_sq.mp h1).le
  have := localHeatThreshold_le_of_cone (by positivity) hcone
  linarith

/-- **The exponential tail of the local heat threshold.**  For all large `U`, at admissible heights
`T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)`, every `2 ≤ κ ≤ L/2 − 2` gives
`|{t ∈ [T₁ + ½, T₂ − ½] : λ_t > κ²/(3L²)}| ≤ A (T₂ − T₁) e^{−κ/2400} + K L²`. -/
theorem exists_volume_localHeatThreshold_gt_le_exp :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ κ : ℝ, 2 ≤ κ → κ ≤ Real.log U / 2 - 2 →
          volume {t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) |
              κ ^ 2 / (3 * Real.log U ^ 2) < localHeatThreshold t} ≤
            ENNReal.ofReal (A * (T₂ - T₁) * Real.exp (-(κ / 2400)) + K * Real.log U ^ 2) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_speiserShadow_exponential_density
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)] with U hU hL4
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun κ hκ hκL => (measure_mono ?_).trans (hbound κ hκ hκL)⟩
  rintro t ⟨ht, hlt⟩
  exact ⟨ht, exists_shadow_of_lt_localHeatThreshold (by linarith) (by linarith) hlt⟩

/-- **A rate for the vanishing heat rate.**  For every `κ > 0`, for all large `U`,
`|{t ∈ [U/4 + 2, U/2 − 2] : λ_t > κ/log U}| ≤ A U exp(−√(3κ log U)/2400) + K log² U`. -/
theorem eventually_volume_localHeatThreshold_gt_le_exp :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ κ : ℝ, 0 < κ → ∀ᶠ U in atTop,
      volume {t ∈ Icc (U / 4 + 2) (U / 2 - 2) | κ / Real.log U < localHeatThreshold t} ≤
        ENNReal.ofReal (A * U * Real.exp (-(Real.sqrt (3 * κ * Real.log U) / 2400))
          + K * Real.log U ^ 2) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_volume_localHeatThreshold_gt_le_exp
  refine ⟨A / 4, K, by positivity, hK, fun κ hκ => ?_⟩
  -- `√(3κL)` lies in `[2, L/2 − 2]` once `L` is large
  have hlow : ∀ᶠ U : ℝ in atTop, 4 / (3 * κ) ≤ Real.log U :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hhigh : ∀ᶠ U : ℝ in atTop, 2 ≤ Real.log U / 2 - 2 - Real.sqrt (3 * κ * Real.log U) := by
    have h : Tendsto (fun L : ℝ => L / 2 - 2 - Real.sqrt (3 * κ * L)) atTop atTop := by
      have hsq : ∀ L : ℝ, 0 ≤ L → Real.sqrt (3 * κ * L) ≤ L / 4 + 12 * κ := by
        intro L hL
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [sq_nonneg (L / 4 - 6 * κ)]
      refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-(2 + 12 * κ))
        (tendsto_id.atTop_mul_const' (show (0 : ℝ) < 1 / 4 by norm_num)))
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
      have := hsq L hL
      simp only [id]
      linarith
    exact Real.tendsto_log_atTop.eventually (h.eventually_ge_atTop 2)
  filter_upwards [hev, hlow, hhigh, Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ),
    eventually_ge_atTop (0 : ℝ)] with U hU hUlow hUhigh hL4 hU0
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  set L := Real.log U with hLdef
  have hL : 0 < L := by linarith
  set s := Real.sqrt (3 * κ * L) with hs
  have hs2 : 2 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (by positivity)]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * κ)).mp hUlow
    nlinarith
  have hsq : s ^ 2 / (3 * L ^ 2) = κ / L := by
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  have h := hbound s hs2 (by linarith)
  rw [hsq] at h
  refine (measure_mono ?_).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · rintro t ⟨ht, hlt⟩
    exact ⟨⟨by linarith [hT₁.2, ht.1], by linarith [hT₂.1, ht.2]⟩, hlt⟩
  · have hT : T₂ - T₁ ≤ U / 4 := by linarith [hT₁.1, hT₂.2]
    have he := Real.exp_pos (-(s / 2400))
    have : A * (T₂ - T₁) * Real.exp (-(s / 2400)) ≤ A / 4 * U * Real.exp (-(s / 2400)) := by
      have := mul_le_mul_of_nonneg_left hT hA
      nlinarith
    linarith

/-! ## The mean value -/

/-- **Layer bound.**  For a monotone `λ` and `x ≤ λ_N`,
`x ≤ λ_0 + Σ_{j<N} [λ_j < x](λ_{j+1} − λ_j)`. -/
theorem le_add_sum_layers {lam : ℕ → ℝ} (hmono : Monotone lam) {x : ℝ} :
    ∀ N : ℕ, x ≤ lam N →
      x ≤ lam 0 + ∑ j ∈ Finset.range N, if lam j < x then lam (j + 1) - lam j else 0
  | 0, h => by simpa using h
  | N + 1, h => by
    rw [Finset.sum_range_succ]
    by_cases hN : x ≤ lam N
    · have := le_add_sum_layers hmono N hN
      have h0 : 0 ≤ (if lam N < x then lam (N + 1) - lam N else 0) := by
        split_ifs
        · linarith [hmono (Nat.le_succ N)]
        · exact le_rfl
      linarith
    · push Not at hN
      have hall : ∀ j ∈ Finset.range N, (if lam j < x then lam (j + 1) - lam j else 0)
          = lam (j + 1) - lam j := fun j hj =>
        if_pos ((hmono (Finset.mem_range.mp hj).le).trans_lt hN)
      rw [Finset.sum_congr rfl hall, Finset.sum_range_sub, if_pos hN]
      linarith

/-- **Layer cake on an interval.**  If `0 ≤ f ≤ λ_N` with `λ` monotone and the layers
`{f > λ_j} ∩ [a, b]` have measure `≤ B_j`, then `∫_a^b f ≤ λ_0 (b − a) + Σ_{j<N} (λ_{j+1} − λ_j) B_j`. -/
theorem setIntegral_le_layers {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) {a b : ℝ}
    (hab : a ≤ b) {lam : ℕ → ℝ} (hmono : Monotone lam) {N : ℕ} (hfN : ∀ t, f t ≤ lam N)
    {B : ℕ → ℝ} (hB : ∀ j < N, volume {t ∈ Icc a b | lam j < f t} ≤ ENNReal.ofReal (B j))
    (hB0 : ∀ j, 0 ≤ B j) :
    ∫ t in Icc a b, f t ≤ lam 0 * (b - a) + ∑ j ∈ Finset.range N, (lam (j + 1) - lam j) * B j := by
  have hS : ∀ j, MeasurableSet {t | lam j < f t} := fun j => measurableSet_lt measurable_const hf
  have hind : ∀ j, Integrable ({t | lam j < f t}.indicator fun _ => lam (j + 1) - lam j)
      (volume.restrict (Icc a b)) := fun j => (integrable_const _).indicator (hS j)
  have hsumint : Integrable (fun t => ∑ j ∈ Finset.range N,
      {t | lam j < f t}.indicator (fun _ => lam (j + 1) - lam j) t) (volume.restrict (Icc a b)) :=
    integrable_finsetSum _ fun j _ => hind j
  have hfint : Integrable f (volume.restrict (Icc a b)) :=
    Integrable.of_bound hf.aestronglyMeasurable (lam N) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]; exact hfN t)
  have hfg : ∀ t, f t ≤ lam 0 + ∑ j ∈ Finset.range N,
      {t | lam j < f t}.indicator (fun _ => lam (j + 1) - lam j) t := by
    intro t
    have h := le_add_sum_layers hmono N (hfN t)
    have e : ∀ j ∈ Finset.range N, {t | lam j < f t}.indicator (fun _ => lam (j + 1) - lam j) t
        = if lam j < f t then lam (j + 1) - lam j else 0 := fun j _ => by
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rwa [Finset.sum_congr rfl e]
  calc ∫ t in Icc a b, f t
      ≤ ∫ t in Icc a b, (lam 0 + ∑ j ∈ Finset.range N,
          {t | lam j < f t}.indicator (fun _ => lam (j + 1) - lam j) t) :=
        integral_mono hfint ((integrable_const _).add hsumint) hfg
    _ = lam 0 * (b - a) + ∑ j ∈ Finset.range N,
          (lam (j + 1) - lam j) * volume.real ({t | lam j < f t} ∩ Icc a b) := by
        rw [integral_add (integrable_const _) hsumint, integral_const,
          integral_finsetSum _ fun j _ => hind j]
        congr 1
        · rw [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le hab, smul_eq_mul, mul_comm]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_indicator_const _ (hS j), measureReal_restrict_apply (hS j), smul_eq_mul,
            mul_comm]
    _ ≤ _ := by
        gcongr with j hj
        · linarith [hmono (Nat.le_succ j)]
        · have e : {t | lam j < f t} ∩ Icc a b = {t ∈ Icc a b | lam j < f t} := by
            ext t; simp [and_comm]
          rw [e, measureReal_def]
          exact ENNReal.toReal_le_of_le_ofReal (hB0 j) (hB j (Finset.mem_range.mp hj))

/-- `Σ_{j<N} (2j + 5) e^{−(j+2)/2400} ≤ 18 · 2400³`: `e^y ≥ y³/6` and telescoping `1/(j+1) − 1/(j+2)`. -/
theorem sum_layer_exp_le (N : ℕ) :
    ∑ j ∈ Finset.range N, (2 * (j : ℝ) + 5) * Real.exp (-(((j : ℝ) + 2) / 2400))
      ≤ 18 * 2400 ^ 3 := by
  have hterm : ∀ j : ℕ, (2 * (j : ℝ) + 5) * Real.exp (-(((j : ℝ) + 2) / 2400))
      ≤ 18 * 2400 ^ 3 * (1 / ((j : ℝ) + 1) - 1 / (((j + 1 : ℕ) : ℝ) + 1)) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have he := Real.pow_div_factorial_le_exp (((j : ℝ) + 2) / 2400) (by positivity) 3
    have hpos := Real.exp_pos (((j : ℝ) + 2) / 2400)
    rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 by norm_num [Nat.factorial]] at he
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have e1 : 18 * 2400 ^ 3 * (1 / ((j : ℝ) + 1) - 1 / (((j + 1 : ℕ) : ℝ) + 1))
        = 18 * 2400 ^ 3 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      push_cast; field_simp; ring
    have e2 : 18 * 2400 ^ 3 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * ((((j : ℝ) + 2) / 2400) ^ 3 / 6)
        = 3 * ((j : ℝ) + 2) ^ 2 / ((j : ℝ) + 1) := by
      field_simp; ring
    rw [e1]
    calc 2 * (j : ℝ) + 5 ≤ 3 * ((j : ℝ) + 2) ^ 2 / ((j : ℝ) + 1) := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
      _ = _ := e2.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  rw [← Finset.mul_sum, Finset.sum_range_sub' (fun j : ℕ => 1 / ((j : ℝ) + 1)) N]
  have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
  push_cast
  nlinarith

/-- **The layer sum.**  With `λ_j = (j + 2)²/(3L²)` for `j ≤ N`, `λ_j = 1/12` beyond, and
`A' e^{−(N+2)/2400} ≤ A'/L²`:
`Σ_{j ≤ N} (λ_{j+1} − λ_j)(A' e^{−(j+2)/2400} + E) ≤ 18 · 2400³ A'/(3L²) + A'/(12L²) + E/12`. -/
theorem layer_sum_le {L A' E : ℝ} (hL : 0 < L) (hA' : 0 ≤ A') (hE : 0 ≤ E) {N : ℕ}
    {lam : ℕ → ℝ} (hlam : ∀ j, lam j = if j ≤ N then ((j : ℝ) + 2) ^ 2 / (3 * L ^ 2) else 1 / 12)
    (hNL : ((N : ℝ) + 2) ^ 2 / (3 * L ^ 2) ≤ 1 / 12)
    (heN : A' * Real.exp (-(((N : ℝ) + 2) / 2400)) ≤ A' / L ^ 2) :
    ∑ j ∈ Finset.range (N + 1), (lam (j + 1) - lam j) * (A' * Real.exp (-(((j : ℝ) + 2) / 2400)) + E)
      ≤ 18 * 2400 ^ 3 * A' / (3 * L ^ 2) + A' / (12 * L ^ 2) + E / 12 := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hE' : ∑ j ∈ Finset.range (N + 1), (lam (j + 1) - lam j) * E ≤ E / 12 := by
    rw [← Finset.sum_mul, Finset.sum_range_sub, hlam (N + 1), hlam 0, if_neg (by omega),
      if_pos (Nat.zero_le _)]
    have : 0 ≤ ((0 : ℕ) + 2 : ℝ) ^ 2 / (3 * L ^ 2) := by positivity
    nlinarith
  have hlow : ∀ j ∈ Finset.range N, (lam (j + 1) - lam j) * (A' * Real.exp (-(((j : ℝ) + 2) / 2400)))
      = A' / (3 * L ^ 2) * ((2 * (j : ℝ) + 5) * Real.exp (-(((j : ℝ) + 2) / 2400))) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [hlam (j + 1), hlam j, if_pos (by omega), if_pos (by omega)]
    push_cast
    field_simp
    ring
  have hA : ∑ j ∈ Finset.range (N + 1), (lam (j + 1) - lam j)
        * (A' * Real.exp (-(((j : ℝ) + 2) / 2400)))
      ≤ 18 * 2400 ^ 3 * A' / (3 * L ^ 2) + A' / (12 * L ^ 2) := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hlow, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (sum_layer_exp_le N)
      (by positivity : 0 ≤ A' / (3 * L ^ 2))
    have htop : (lam (N + 1) - lam N) * (A' * Real.exp (-(((N : ℝ) + 2) / 2400)))
        ≤ A' / (12 * L ^ 2) := by
      rw [hlam (N + 1), hlam N, if_neg (by omega), if_pos le_rfl]
      have hw0 : 0 ≤ 1 / 12 - ((N : ℝ) + 2) ^ 2 / (3 * L ^ 2) := by linarith
      have hw1 : 1 / 12 - ((N : ℝ) + 2) ^ 2 / (3 * L ^ 2) ≤ 1 / 12 := by
        have : 0 ≤ ((N : ℝ) + 2) ^ 2 / (3 * L ^ 2) := by positivity
        linarith
      have hx0 : 0 ≤ A' * Real.exp (-(((N : ℝ) + 2) / 2400)) := by positivity
      calc _ ≤ 1 / 12 * (A' * Real.exp (-(((N : ℝ) + 2) / 2400))) :=
            mul_le_mul_of_nonneg_right hw1 hx0
        _ ≤ 1 / 12 * (A' / L ^ 2) := by gcongr
        _ = A' / (12 * L ^ 2) := by field_simp
    have e : A' / (3 * L ^ 2) * (18 * 2400 ^ 3) = 18 * 2400 ^ 3 * A' / (3 * L ^ 2) := by ring
    linarith
  linarith

/-- **The mean value of the local heat threshold.**  `∫_{U/4+2}^{U/2−2} λ_t dt ≤ C U/log² U` for all
large `U`. -/
theorem exists_integral_localHeatThreshold_le :
    ∃ C : ℝ, ∀ᶠ U in atTop,
      ∫ t in Icc (U / 4 + 2) (U / 2 - 2), localHeatThreshold t ≤ C * U / Real.log U ^ 2 := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_volume_localHeatThreshold_gt_le_exp
  refine ⟨1 / 3 + A * (18 * 2400 ^ 3) / 12 + A / 48 + 1, ?_⟩
  -- `L² ≤ e^{L/9600}` and `K L⁴ ≤ U` for large `U`
  have hexp : ∀ᶠ U : ℝ in atTop, Real.log U ^ 2 ≤ Real.exp (Real.log U / 9600) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (6 * 9600 ^ 3 : ℝ)] with U hU
    have he := Real.pow_div_factorial_le_exp (Real.log U / 9600) (by positivity) 3
    rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 by norm_num [Nat.factorial]] at he
    refine le_trans ?_ he
    rw [div_pow, div_div, le_div_iff₀ (by norm_num)]
    have h0 : 0 ≤ Real.log U ^ 2 := sq_nonneg _
    nlinarith
  have hpoly : ∀ᶠ U : ℝ in atTop, K * Real.log U ^ 4 ≤ U := by
    filter_upwards [eventually_ge_atTop ((K * 8 ^ 4 + 1) ^ 2), eventually_ge_atTop (1 : ℝ)]
      with U hU hU1
    have hlog := Real.log_le_rpow_div (le_trans zero_le_one hU1) (by norm_num : (0 : ℝ) < 1 / 8)
    have hL0 := Real.log_nonneg hU1
    have hr : (U ^ (1 / 8 : ℝ)) ^ 4 = Real.sqrt U := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]; norm_num
    have h1 : Real.log U ^ 4 ≤ 8 ^ 4 * Real.sqrt U := by
      calc Real.log U ^ 4 ≤ (U ^ (1 / 8 : ℝ) / (1 / 8)) ^ 4 := by gcongr
        _ = 8 ^ 4 * Real.sqrt U := by rw [div_pow, hr]; ring
    have hs : K * 8 ^ 4 + 1 ≤ Real.sqrt U := Real.le_sqrt_of_sq_le hU
    have hsU : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt U := Real.sqrt_nonneg U
    calc K * Real.log U ^ 4 ≤ K * (8 ^ 4 * Real.sqrt U) := mul_le_mul_of_nonneg_left h1 hK
      _ ≤ Real.sqrt U * Real.sqrt U := by nlinarith
      _ = U := hsU
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_ge_atTop (100 : ℝ), hexp, hpoly,
    eventually_ge_atTop (12 : ℝ)] with U hU hL100 hexpU hpolyU hU12
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log U := ⟨_, rfl⟩
  rw [← hLdef] at hL100 hexpU hpolyU hbound ⊢
  have hL : 0 < L := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊L / 2 - 4⌋₊ := ⟨_, rfl⟩
  have hN1 : (N : ℝ) ≤ L / 2 - 4 := by rw [hN]; exact Nat.floor_le (by linarith)
  have hN2 : L / 2 - 5 < N := by
    have := Nat.lt_floor_add_one (L / 2 - 4); rw [← hN] at this; linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℕ → ℝ, lam =
      fun j => if j ≤ N then ((j : ℝ) + 2) ^ 2 / (3 * L ^ 2) else 1 / 12 := ⟨_, rfl⟩
  have hlamj : ∀ j, lam j = if j ≤ N then ((j : ℝ) + 2) ^ 2 / (3 * L ^ 2) else 1 / 12 := by
    intro j; rw [hlam]
  have hNL : ((N : ℝ) + 2) ^ 2 / (3 * L ^ 2) ≤ 1 / 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h2 : ((N : ℝ) + 2) ^ 2 ≤ (L / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  have hmono : Monotone lam := by
    refine monotone_nat_of_le_succ fun j => ?_
    rw [hlamj j, hlamj (j + 1)]
    split_ifs with h1 h2 h2
    · gcongr
      linarith
    · have : j = N := by omega
      rw [this]; exact hNL
    · omega
    · exact le_rfl
  have hT : T₁ + 1 / 2 ≤ T₂ - 1 / 2 := by linarith [hT₁.2, hT₂.1]
  have hΔ0 : 0 ≤ T₂ - T₁ := by linarith
  have hΔ : T₂ - T₁ ≤ U / 4 := by linarith [hT₁.1, hT₂.2]
  have hB0 : ∀ j : ℕ, 0 ≤ A * (T₂ - T₁) * Real.exp (-(((j : ℝ) + 2) / 2400)) + K * L ^ 2 :=
    fun j => by positivity
  have hfN : ∀ t, localHeatThreshold t ≤ lam (N + 1) := fun t => by
    rw [hlamj, if_neg (by omega)]
    exact (localHeatThreshold_le_wdHeatThreshold t).trans wdHeatThreshold_lt_twelfth.le
  have hBj : ∀ j < N + 1, volume {t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) | lam j < localHeatThreshold t}
      ≤ ENNReal.ofReal (A * (T₂ - T₁) * Real.exp (-(((j : ℝ) + 2) / 2400)) + K * L ^ 2) := by
    intro j hj
    have hjN : j ≤ N := by omega
    have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
    rw [hlamj, if_pos hjN]
    exact hbound ((j : ℝ) + 2) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) (by linarith)
  have hmain := setIntegral_le_layers lowerSemicontinuous_localHeatThreshold.measurable
    localHeatThreshold_nonneg hT hmono hfN hBj hB0
  have hI : ∫ t in Icc (U / 4 + 2) (U / 2 - 2), localHeatThreshold t
      ≤ ∫ t in Icc (T₁ + 1 / 2) (T₂ - 1 / 2), localHeatThreshold t := by
    refine setIntegral_mono_set ?_ (Eventually.of_forall fun t => localHeatThreshold_nonneg t)
      (Eventually.of_forall (Icc_subset_Icc (by linarith [hT₁.2]) (by linarith [hT₂.1])))
    exact Integrable.of_bound lowerSemicontinuous_localHeatThreshold.measurable.aestronglyMeasurable
      (1 / 12) (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (localHeatThreshold_nonneg t)]
        exact (localHeatThreshold_le_wdHeatThreshold t).trans wdHeatThreshold_lt_twelfth.le)
  -- the top layer is below `1/L²`
  have heN : A * (T₂ - T₁) * Real.exp (-(((N : ℝ) + 2) / 2400)) ≤ A * (T₂ - T₁) / L ^ 2 := by
    have h1 : Real.exp (-(((N : ℝ) + 2) / 2400)) ≤ Real.exp (-(L / 9600)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(L / 9600)) ≤ 1 / L ^ 2 := by
      rw [Real.exp_neg, ← one_div, one_div_le_one_div (Real.exp_pos _) (by positivity)]
      exact hexpU
    have hAΔ : 0 ≤ A * (T₂ - T₁) := by positivity
    calc _ ≤ A * (T₂ - T₁) * (1 / L ^ 2) := mul_le_mul_of_nonneg_left (h1.trans h2) hAΔ
      _ = _ := by ring
  have hsum := layer_sum_le hL (by positivity : 0 ≤ A * (T₂ - T₁)) (by positivity : 0 ≤ K * L ^ 2)
    hlamj hNL heN
  have hlam0 : lam 0 = 4 / (3 * L ^ 2) := by rw [hlamj, if_pos (Nat.zero_le _)]; norm_num
  rw [hlam0] at hmain
  have hKL : K * L ^ 2 / 12 ≤ U / L ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have e : K * L ^ 2 * L ^ 2 = K * L ^ 4 := by ring
    linarith
  have hfin : 4 / (3 * L ^ 2) * (T₂ - 1 / 2 - (T₁ + 1 / 2)) + (18 * 2400 ^ 3 * (A * (T₂ - T₁))
      / (3 * L ^ 2) + A * (T₂ - T₁) / (12 * L ^ 2) + K * L ^ 2 / 12)
      ≤ (1 / 3 + A * (18 * 2400 ^ 3) / 12 + A / 48 + 1) * U / L ^ 2 := by
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    have hAΔ := mul_le_mul_of_nonneg_left hΔ hA
    have hnum : 4 * (T₂ - 1 / 2 - (T₁ + 1 / 2)) / 3 + 6 * 2400 ^ 3 * (A * (T₂ - T₁))
        + A * (T₂ - T₁) / 12 ≤ (1 / 3 + A * (18 * 2400 ^ 3) / 12 + A / 48) * U := by
      linarith
    have e1 : 4 / (3 * L ^ 2) * (T₂ - 1 / 2 - (T₁ + 1 / 2)) + (18 * 2400 ^ 3 * (A * (T₂ - T₁))
        / (3 * L ^ 2) + A * (T₂ - T₁) / (12 * L ^ 2))
        = (4 * (T₂ - 1 / 2 - (T₁ + 1 / 2)) / 3 + 6 * 2400 ^ 3 * (A * (T₂ - T₁))
          + A * (T₂ - T₁) / 12) / L ^ 2 := by ring
    have e2 : (1 / 3 + A * (18 * 2400 ^ 3) / 12 + A / 48 + 1) * U / L ^ 2
        = (1 / 3 + A * (18 * 2400 ^ 3) / 12 + A / 48) * U / L ^ 2 + U / L ^ 2 := by ring
    have h3 := div_le_div_of_nonneg_right hnum hL2
    rw [e2, ← add_assoc, e1]
    linarith
  linarith

end RHTower.DeBruijn
