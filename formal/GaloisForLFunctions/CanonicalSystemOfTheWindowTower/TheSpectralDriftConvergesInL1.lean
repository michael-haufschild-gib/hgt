import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilTracesAreAbsolutelyContinuous

/-!
# The spectral drift converges in `L¹`

Write `q = Ψ′`, `L_y = artanh r_y` and `q_y = y sinh 2L_y` (`spectralDrift`). By universality `L_y′ = q − q_y` almost
everywhere.

**Kato's inequality** (`integral_abs_spectralDrift_sub_const_le`). If `y sinh 2ℓ = c`, then on `[x₀, x₁]`

  `∫ |q_y − c| ≤ ∫ |q − c| + |L_y(x₀) − ℓ|`.

The derivative of `|L_y − ℓ|` is at most `|q − c| − |q_y − c|`, because `q_y − c` and `L_y − ℓ` have the same sign: `sinh` is
increasing. So the flow is an `L¹` contraction towards each of its slow states `ℓ`.

**Theorem** (`tendsto_integral_abs_spectralDrift_sub_deriv`). `∫_{x₀}^{x₁} |q_y − q| → 0` as `y → ∞`, on every compact
precontact interval. Approximate `q` in `L¹` by a continuous function, freeze it on the cells of a fine partition, and apply
Kato on each cell: `L_y → 0` at the finitely many nodes (`tendsto_artanh_spectralReflection_zero`), and so do the slow
states `½ arsinh(c_j/y)`.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
open _root_.RHTower HTGeometry GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

private theorem Icc_sub_precontact {x₀ x₁ : ℝ} (h₀ : x₀ ∈ precontactSet) (h₁ : x₁ ∈ precontactSet) :
    Icc x₀ x₁ ⊆ precontactSet := fun _ ht =>
  ⟨h₀.1.trans_le ht.1, (EReal.coe_le_coe_iff.mpr ht.2).trans_lt h₁.2⟩

private theorem continuousOn_spectralDrift {y : ℝ} (hy : 0 < y) {x₀ x₁ : ℝ}
    (hs : Icc x₀ x₁ ⊆ precontactSet) : ContinuousOn (spectralDrift y) (Icc x₀ x₁) := fun _ hx =>
  (continuousAt_spectralDrift hy (toPrecontact (hs hx))).continuousWithinAt

private theorem lipschitzOnWith_abs : LipschitzOnWith 1 (fun r : ℝ => |r|) univ := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x _ y _
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  exact abs_abs_sub_abs_le x y

/-- **Kato's inequality for the spectral flow.** The flow contracts `L¹` towards each slow state. -/
theorem integral_abs_spectralDrift_sub_const_le {y : ℝ} (hy : 0 < y) {base : ℝ}
    (hbase : base ∈ precontactSet) {x₀ x₁ : ℝ} (hp₀ : x₀ ∈ precontactSet)
    (hp₁ : x₁ ∈ precontactSet) (h : x₀ ≤ x₁) {c ℓ : ℝ} (hℓ : y * Real.sinh (2 * ℓ) = c) :
    ∫ x in x₀..x₁, |spectralDrift y x - c| ≤
      (∫ x in x₀..x₁, |deriv (canonicalPotential base) x - c|) +
        |Real.artanh (spectralReflection y x₀) - ℓ| := by
  have hs := Icc_sub_precontact hp₀ hp₁
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = canonicalPotential base := ⟨_, rfl⟩
  rw [← hΨ]
  have hΨac : AbsolutelyContinuousOnInterval Ψ x₀ x₁ := by
    rw [hΨ]
    exact absolutelyContinuousOnInterval_canonicalPotential hbase (a₁ := toPrecontact hp₀)
      (a₂ := toPrecontact hp₁) h
  have hqi : IntervalIntegrable (deriv Ψ) volume x₀ x₁ := hΨac.intervalIntegrable_deriv
  have hdc := continuousOn_spectralDrift hy hs
  have hdi : IntervalIntegrable (spectralDrift y) volume x₀ x₁ := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le h]
  -- The distance to the slow state.
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, D = fun x => Real.artanh (spectralReflection y x) - ℓ := ⟨_, rfl⟩
  have hDv (x : ℝ) : D x = Real.artanh (spectralReflection y x) - ℓ := by rw [hD]
  obtain ⟨C, hCd⟩ : ∃ C, C = Real.artanh (spectralReflection y x₀) - ℓ - Ψ x₀ := ⟨_, rfl⟩
  have hDform (x : ℝ) (hx : x ∈ Icc x₀ x₁) : D x = C + Ψ x - ∫ t in x₀..x, spectralDrift y t := by
    have hT := artanh_spectralReflection_sub hy hbase hx.1
      (fun t ht => hs ⟨ht.1, ht.2.trans hx.2⟩)
    rw [hDv, hCd, hΨ]
    linarith only [hT]
  have hIac : AbsolutelyContinuousOnInterval (fun x => ∫ t in x₀..x, spectralDrift y t) x₀ x₁ :=
    hdi.absolutelyContinuousOnInterval_intervalIntegral (by
      rw [uIcc_of_le h]
      exact ⟨le_rfl, h⟩)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) x₀ x₁ := by
    rw [absolutelyContinuousOnInterval_iff]
    intro e he
    exact ⟨1, one_pos, fun E _ _ => by simpa using he⟩
  have hDac : AbsolutelyContinuousOnInterval D x₀ x₁ :=
    absolutelyContinuousOnInterval_congr ((hconst.add hΨac).sub hIac) fun x hx => by
      rw [uIcc_of_le h] at hx
      exact hDform x hx
  have habsac : AbsolutelyContinuousOnInterval (fun x => |D x|) x₀ x₁ :=
    absolutelyContinuousOnInterval_comp (g := fun r : ℝ => |r|) (s := univ) hDac
      (fun _ _ => mem_univ _) lipschitzOnWith_abs
  have hFTC := habsac.integral_deriv_eq_sub
  -- The pointwise inequality.
  have hpt : ∀ᵐ x ∂volume, x ∈ Ioo x₀ x₁ →
      deriv (fun x => |D x|) x ≤ |deriv Ψ x - c| - |spectralDrift y x - c| := by
    filter_upwards [hΨac.ae_differentiableAt] with x hdiff hx
    have hxI : x ∈ Icc x₀ x₁ := Ioo_subset_Icc_self hx
    have hxp := hs hxI
    have hΨd : HasDerivAt Ψ (deriv Ψ x) x := (hdiff (by
      rw [uIcc_of_le h]
      exact hxI)).hasDerivAt
    have hId : HasDerivAt (fun x => ∫ t in x₀..x, spectralDrift y t) (spectralDrift y x) x := by
      apply intervalIntegral.integral_hasDerivAt_right
      · exact hdi.mono_set (by
          rw [uIcc_of_le h, uIcc_of_le hx.1.le]
          exact Icc_subset_Icc le_rfl hx.2.le)
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          (hdc.mono Ioo_subset_Icc_self) x hx
      · exact continuousAt_spectralDrift hy (toPrecontact hxp)
    have hDd : HasDerivAt D (deriv Ψ x - spectralDrift y x) x := by
      refine ((hΨd.const_add C).sub hId).congr_of_eventuallyEq ?_
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with t ht
      exact hDform t ht
    have hsinh : spectralDrift y x = y * Real.sinh (2 * Real.artanh (spectralReflection y x)) :=
      spectralDrift_eq_sinh hy (toPrecontact hxp)
    rcases lt_trichotomy (D x) 0 with hneg | hzero | hpos
    · -- Below the slow state.
      have hlt : Real.artanh (spectralReflection y x) < ℓ := by
        have := hDv x
        linarith only [this, hneg]
      have hq : spectralDrift y x - c < 0 := by
        have hsh := Real.sinh_lt_sinh.mpr
          (show 2 * Real.artanh (spectralReflection y x) < 2 * ℓ by linarith only [hlt])
        have := mul_lt_mul_of_pos_left hsh hy
        linarith only [this, hsinh, hℓ]
      have hevt : ∀ᶠ t in 𝓝 x, D t < 0 := hDd.continuousAt.eventually_lt continuousAt_const hneg
      have hd' : HasDerivAt (fun x => |D x|) (-(deriv Ψ x - spectralDrift y x)) x := by
        refine hDd.neg.congr_of_eventuallyEq ?_
        filter_upwards [hevt] with t ht
        exact abs_of_neg ht
      rw [hd'.deriv, abs_of_neg hq]
      have := neg_abs_le (deriv Ψ x - c)
      linarith only [this]
    · -- At the slow state.
      have hmin : IsLocalMin (fun x => |D x|) x := by
        refine Eventually.of_forall fun t => ?_
        change |D x| ≤ |D t|
        rw [hzero, abs_zero]
        exact abs_nonneg _
      rw [hmin.deriv_eq_zero]
      have hat : Real.artanh (spectralReflection y x) = ℓ := by
        have := hDv x
        linarith only [this, hzero]
      rw [hsinh, hat, hℓ, sub_self, abs_zero, sub_zero]
      exact abs_nonneg _
    · -- Above the slow state.
      have hlt : ℓ < Real.artanh (spectralReflection y x) := by
        have := hDv x
        linarith only [this, hpos]
      have hq : 0 < spectralDrift y x - c := by
        have hsh := Real.sinh_lt_sinh.mpr
          (show 2 * ℓ < 2 * Real.artanh (spectralReflection y x) by linarith only [hlt])
        have := mul_lt_mul_of_pos_left hsh hy
        linarith only [this, hsinh, hℓ]
      have hevt : ∀ᶠ t in 𝓝 x, 0 < D t := continuousAt_const.eventually_lt hDd.continuousAt hpos
      have hd' : HasDerivAt (fun x => |D x|) (deriv Ψ x - spectralDrift y x) x := by
        refine hDd.congr_of_eventuallyEq ?_
        filter_upwards [hevt] with t ht
        exact abs_of_pos ht
      rw [hd'.deriv, abs_of_pos hq]
      have := le_abs_self (deriv Ψ x - c)
      linarith only [this]
  -- Integrate.
  have i₁ : IntervalIntegrable (fun x => |deriv Ψ x - c|) volume x₀ x₁ :=
    (hqi.sub intervalIntegrable_const).abs
  have i₂ : IntervalIntegrable (fun x => |spectralDrift y x - c|) volume x₀ x₁ :=
    (hdi.sub intervalIntegrable_const).abs
  have hmono : ∫ x in x₀..x₁, deriv (fun x => |D x|) x ≤
      ∫ x in x₀..x₁, (|deriv Ψ x - c| - |spectralDrift y x - c|) := by
    rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_mono_on_ae (habsac.intervalIntegrable_deriv.1.mono_set Ioo_subset_Ioc_self)
      ((i₁.sub i₂).1.mono_set Ioo_subset_Ioc_self) measurableSet_Ioo hpt
  rw [hFTC, intervalIntegral.integral_sub i₁ i₂] at hmono
  have hD₁ : 0 ≤ |D x₁| := abs_nonneg _
  rw [← hDv]
  linarith only [hmono, hD₁]

/-- Kato's inequality on one cell, compared with a continuous function which oscillates at most `η` around `c`. -/
private theorem cell_le {y : ℝ} (hy : 0 < y) {base : ℝ} (hbase : base ∈ precontactSet) {u w : ℝ}
    (hu : u ∈ precontactSet) (hw : w ∈ precontactSet) (huw : u ≤ w) {g : ℝ → ℝ} (hg : Continuous g)
    {c η : ℝ} (hη : ∀ x ∈ Icc u w, |g x - c| ≤ η) :
    ∫ x in u..w, |spectralDrift y x - deriv (canonicalPotential base) x| ≤
      2 * ((∫ x in u..w, |deriv (canonicalPotential base) x - g x|) + η * (w - u)) +
        |Real.artanh (spectralReflection y u) - 1 / 2 * Real.arsinh (c / y)| := by
  have hy' : y ≠ 0 := hy.ne'
  have hℓ : y * Real.sinh (2 * (1 / 2 * Real.arsinh (c / y))) = c := by
    rw [show 2 * (1 / 2 * Real.arsinh (c / y)) = Real.arsinh (c / y) by ring, Real.sinh_arsinh]
    field_simp
  have hK := integral_abs_spectralDrift_sub_const_le hy hbase hu hw huw hℓ
  have hqi0 : IntervalIntegrable (deriv (canonicalPotential base)) volume u w :=
    (absolutelyContinuousOnInterval_canonicalPotential hbase (a₁ := toPrecontact hu)
      (a₂ := toPrecontact hw) huw).intervalIntegrable_deriv
  obtain ⟨q, hq⟩ : ∃ q, q = deriv (canonicalPotential base) := ⟨_, rfl⟩
  rw [← hq] at hK hqi0 ⊢
  have hdi : IntervalIntegrable (spectralDrift y) volume u w := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huw]
    exact continuousOn_spectralDrift hy (Icc_sub_precontact hu hw)
  have i₁ : IntervalIntegrable (fun x => |spectralDrift y x - c|) volume u w :=
    (hdi.sub intervalIntegrable_const).abs
  have i₂ : IntervalIntegrable (fun x => |q x - c|) volume u w :=
    (hqi0.sub intervalIntegrable_const).abs
  have i₃ : IntervalIntegrable (fun x => |spectralDrift y x - q x|) volume u w :=
    (hdi.sub hqi0).abs
  have i₄ : IntervalIntegrable (fun x => |q x - g x|) volume u w :=
    (hqi0.sub (hg.intervalIntegrable _ _)).abs
  have h₁ : ∫ x in u..w, |spectralDrift y x - q x| ≤
      (∫ x in u..w, |spectralDrift y x - c|) + ∫ x in u..w, |q x - c| := by
    rw [← intervalIntegral.integral_add i₁ i₂]
    refine intervalIntegral.integral_mono_on huw i₃ (i₁.add i₂) fun x _ => ?_
    have := abs_sub_le (spectralDrift y x) c (q x)
    rwa [abs_sub_comm c] at this
  have h₂ : ∫ x in u..w, |q x - c| ≤ (∫ x in u..w, |q x - g x|) + η * (w - u) := by
    have hc : ∫ x in u..w, (|q x - g x| + η) = (∫ x in u..w, |q x - g x|) + η * (w - u) := by
      rw [intervalIntegral.integral_add i₄ intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, mul_comm η]
    rw [← hc]
    refine intervalIntegral.integral_mono_on huw i₂ (i₄.add intervalIntegrable_const) fun x hx => ?_
    exact (abs_sub_le _ (g x) _).trans (add_le_add le_rfl (hη x hx))
  linarith only [h₁, h₂, hK]

/-- **The spectral drift converges to the potential in `L¹`**, on every compact precontact interval. -/
theorem tendsto_integral_abs_spectralDrift_sub_deriv {base : ℝ} (hbase : base ∈ precontactSet)
    {x₀ x₁ : ℝ} (hp₀ : x₀ ∈ precontactSet) (hp₁ : x₁ ∈ precontactSet) (h : x₀ ≤ x₁) :
    Tendsto (fun y : ℝ => ∫ x in x₀..x₁, |spectralDrift y x - deriv (canonicalPotential base) x|)
      atTop (𝓝 0) := by
  have hs := Icc_sub_precontact hp₀ hp₁
  have hqi0 : IntervalIntegrable (deriv (canonicalPotential base)) volume x₀ x₁ :=
    (absolutelyContinuousOnInterval_canonicalPotential hbase (a₁ := toPrecontact hp₀)
      (a₂ := toPrecontact hp₁) h).intervalIntegrable_deriv
  have hcell₀ := fun (y : ℝ) (hy : 0 < y) {u w : ℝ} (hu : u ∈ precontactSet)
      (hw : w ∈ precontactSet) (huw : u ≤ w) {g : ℝ → ℝ} (hg : Continuous g) {c η : ℝ}
      (hη : ∀ x ∈ Icc u w, |g x - c| ≤ η) => cell_le hy hbase hu hw huw hg hη
  obtain ⟨q, hq⟩ : ∃ q, q = deriv (canonicalPotential base) := ⟨_, rfl⟩
  simp only [← hq] at hqi0 hcell₀ ⊢
  rw [Metric.tendsto_nhds]
  intro e he
  -- A continuous approximation of the potential.
  have hfi : Integrable ((Ioc x₀ x₁).indicator q) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).mp hqi0)
  obtain ⟨g, -, hg, hgc, hgi⟩ := hfi.exists_hasCompactSupport_integral_sub_le
    (show 0 < e / 8 by positivity)
  have hgL : ∫ x in x₀..x₁, |q x - g x| ≤ e / 8 := by
    rw [intervalIntegral.integral_of_le h]
    have hint : Integrable (fun x => ‖(Ioc x₀ x₁).indicator q x - g x‖) := (hfi.sub hgi).norm
    have hle' := setIntegral_le_integral (s := Ioc x₀ x₁) hint
      (Eventually.of_forall fun _ => norm_nonneg _)
    have heq : ∫ x in Ioc x₀ x₁, |q x - g x| =
        ∫ x in Ioc x₀ x₁, ‖(Ioc x₀ x₁).indicator q x - g x‖ :=
      setIntegral_congr_fun measurableSet_Ioc fun x hx => by
        simp only [indicator_of_mem hx, Real.norm_eq_abs]
    rw [heq]
    exact hle'.trans hg
  -- A partition on whose cells `g` oscillates little.
  have hL : 0 < x₁ - x₀ + 1 := by linarith only [h]
  have hLne : x₁ - x₀ + 1 ≠ 0 := hL.ne'
  obtain ⟨η, hηd⟩ : ∃ η : ℝ, η = e / (8 * (x₁ - x₀ + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hηd]
    exact div_pos he (mul_pos (by norm_num) hL)
  have hηL : η * (x₁ - x₀ + 1) = e / 8 := by
    rw [hηd]
    field_simp
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc x₀ x₁) hgc.continuousOn) η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((x₁ - x₀) / δ)
  have hn0 : (0 : ℝ) < n := (div_nonneg (sub_nonneg.mpr h) hδ.le).trans_lt hn
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  obtain ⟨d, hdd⟩ : ∃ d, d = (x₁ - x₀) / n := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by
    rw [hdd]
    exact div_nonneg (sub_nonneg.mpr h) hn0.le
  have hdδ : d < δ := by
    rw [hdd, div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ] at hn
    linarith only [hn]
  have hnd : (n : ℝ) * d = x₁ - x₀ := by
    rw [hdd]
    field_simp
  obtain ⟨pt, hpt⟩ : ∃ pt : ℕ → ℝ, pt = fun j : ℕ => x₀ + (j : ℝ) * d := ⟨_, rfl⟩
  have hptv (j : ℕ) : pt j = x₀ + j * d := by rw [hpt]
  have hstep (j : ℕ) : pt (j + 1) = pt j + d := by
    rw [hptv, hptv]
    push_cast
    ring
  have hpt0 : pt 0 = x₀ := by
    rw [hptv]
    simp
  have hptn : pt n = x₁ := by
    rw [hptv, hnd]
    ring
  have hptI (j : ℕ) (hj : j ≤ n) : pt j ∈ Icc x₀ x₁ := by
    rw [hptv]
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
    have h1 : 0 ≤ (j : ℝ) * d := mul_nonneg (Nat.cast_nonneg j) hd0
    have h2 : (j : ℝ) * d ≤ n * d := mul_le_mul_of_nonneg_right hjn hd0
    exact ⟨by linarith only [h1], by linarith only [h2, hnd]⟩
  have hle (j : ℕ) : pt j ≤ pt (j + 1) := by
    rw [hstep]
    linarith only [hd0]
  have hP (j : ℕ) (hj : j ≤ n) : pt j ∈ precontactSet := hs (hptI j hj)
  have hadj (F : ℝ → ℝ) (hF : IntervalIntegrable F volume x₀ x₁) :
      ∑ j ∈ Finset.range n, ∫ x in pt j..pt (j + 1), F x = ∫ x in x₀..x₁, F x := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := F) (μ := volume) (a := pt)
      (n := n) fun k hk => hF.mono_set (by
        rw [uIcc_of_le h, uIcc_of_le (hle k)]
        exact Icc_subset_Icc (hptI k hk.le).1 (hptI (k + 1) hk).2)
    rw [hsum, hpt0, hptn]
  -- Kato on each cell, frozen at the left node.
  have hcell (y : ℝ) (hy : 0 < y) (j : ℕ) (hj : j < n) :
      ∫ x in pt j..pt (j + 1), |spectralDrift y x - q x| ≤
        2 * ((∫ x in pt j..pt (j + 1), |q x - g x|) + η * d) +
          |Real.artanh (spectralReflection y (pt j)) - 1 / 2 * Real.arsinh (g (pt j) / y)| := by
    have hj' := hptI j hj.le
    have hj'' := hptI (j + 1) hj
    have hosc : ∀ x ∈ Icc (pt j) (pt (j + 1)), |g x - g (pt j)| ≤ η := fun x hx => by
      have hxI : x ∈ Icc x₀ x₁ := ⟨hj'.1.trans hx.1, hx.2.trans hj''.2⟩
      have hd : dist x (pt j) < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
        have hx2 := hx.2
        rw [hstep] at hx2
        linarith only [hx2, hdδ]
      have hlt := hunif x hxI (pt j) hj' hd
      rw [Real.dist_eq] at hlt
      exact hlt.le
    have hb := hcell₀ y hy (hP j hj.le) (hP (j + 1) hj) (hle j) hgc hosc
    have hvu : pt (j + 1) - pt j = d := by
      rw [hstep]
      ring
    rw [hvu] at hb
    exact hb
  -- The node terms vanish in the limit.
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = fun y => ∑ j ∈ Finset.range n,
      |Real.artanh (spectralReflection y (pt j)) - 1 / 2 * Real.arsinh (g (pt j) / y)| := ⟨_, rfl⟩
  have hRv (y : ℝ) : R y = ∑ j ∈ Finset.range n,
      |Real.artanh (spectralReflection y (pt j)) - 1 / 2 * Real.arsinh (g (pt j) / y)| := by rw [hR]
  have hRt : Tendsto R atTop (𝓝 0) := by
    have hlim : Tendsto R atTop
        (𝓝 (∑ _j ∈ Finset.range n, |(0 : ℝ) - 1 / 2 * Real.arsinh 0|)) := by
      rw [hR]
      refine tendsto_finsetSum _ fun j hj => ?_
      have hj' : j < n := Finset.mem_range.mp hj
      have h1 : Tendsto (fun y : ℝ => Real.artanh (spectralReflection y (pt j))) atTop (𝓝 0) :=
        tendsto_artanh_spectralReflection_zero (toPrecontact (hP j hj'.le))
      have h2 : Tendsto (fun y : ℝ => g (pt j) / y) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      exact (h1.sub (h2.arsinh.const_mul _)).abs
    simpa using hlim
  have hev := (hRt.eventually (Iio_mem_nhds (show (0 : ℝ) < e / 2 by positivity))).and
    (eventually_gt_atTop 0)
  filter_upwards [hev] with y hyb
  obtain ⟨hRy, hy⟩ := hyb
  have hRy' : R y < e / 2 := hRy
  rw [Real.dist_eq, sub_zero]
  have hdi : IntervalIntegrable (spectralDrift y) volume x₀ x₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h]
    exact continuousOn_spectralDrift hy hs
  have hi₁ : IntervalIntegrable (fun x => |spectralDrift y x - q x|) volume x₀ x₁ :=
    (hdi.sub hqi0).abs
  have hi₂ : IntervalIntegrable (fun x => |q x - g x|) volume x₀ x₁ :=
    (hqi0.sub (hgc.intervalIntegrable _ _)).abs
  have hnn : 0 ≤ ∫ x in x₀..x₁, |spectralDrift y x - q x| :=
    intervalIntegral.integral_nonneg h fun _ _ => abs_nonneg _
  rw [abs_of_nonneg hnn]
  have e₁ := hadj _ hi₁
  have e₂ := hadj _ hi₂
  have hsum := Finset.sum_le_sum fun j (hj : j ∈ Finset.range n) =>
    hcell y hy j (Finset.mem_range.mp hj)
  rw [e₁, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, e₂, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← hRv] at hsum
  have hnη : (n : ℝ) * (η * d) = η * (x₁ - x₀) := by
    rw [← hnd]
    ring
  have hηL' : η * (x₁ - x₀) ≤ e / 8 := by
    have hexp : η * (x₁ - x₀ + 1) = η * (x₁ - x₀) + η := by ring
    linarith only [hexp, hηL, hη]
  rw [hnη] at hsum
  linarith only [hsum, hgL, hηL', hRy']

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
