import GaloisForLFunctions.RHTower.ZetaLocalWindowTail
import GaloisForLFunctions.RHTower.XiSliceCoeffDensity
import GaloisForLFunctions.RHTower.SpeiserCleanHeights
import GaloisForLFunctions.RHTower.XiHadamardSignDensity

/-!
# Laguerre, slice and Speiser signs on a positive proportion of every window `[T, T + T^{24/25}]`

The shadow of the off-line zeros meets a window `[a, b]` in measure at most twice the off-line
first moment of the zeros with ordinates in `(a − ½, b + ½]`
(`volume_xiShadow_inter_Icc_le_windowTail`).  The window moment bound of `ZetaLocalWindowTail`
at `R = 9/10` gives `Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½)⁺ ≤ (11/50) H` for all large `T` and
every `T^{24/25} ≤ H ≤ T` (`eventually_windowTail_zero_le`).  Hence on every such window the
first Laguerre inequality with vertical monotonicity of `|Ξ|`, all-order slice positivity and
the Speiser clean-height condition hold on a set of measure at least `(14/25) H − 3`
(`eventually_volume_laguerre_monotone_window_ge`, `eventually_volume_sliceCoeff_window_ge`,
`eventually_volume_speiserUnshadowed_window_ge`), and the Hadamard sign `Re(ξ'/ξ) ≥ 0` holds on
area at least `(7/25) H − 3/2` of `{½ < Re s < 1, T + 3/2 ≤ Im s ≤ T + H − 3/2}`
(`eventually_volume_hadamardSign_window_ge`).  In particular every window of length
`T^{24/25}` contains Speiser-clean heights (`eventually_exists_speiserUnshadowed_window`).

The global density versions control `[0, V]` as a whole; these hold in every window of length
`T^{24/25}`, with no averaging over the window position.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexOrder

namespace RHTower

noncomputable section

namespace DeBruijn

/-- **The shadow in a window against the window moment.**
`vol(S ∩ [a, b]) ≤ 2 Σ_{a−½ < Im ρ ≤ b+½} m(ρ)(Re ρ − ½)⁺` for `a ≥ 1`. -/
theorem volume_xiShadow_inter_Icc_le_windowTail {a b : ℝ} (ha : 1 ≤ a) :
    volume (xiShadow ∩ Icc a b) ≤ ENNReal.ofReal (2 * windowTail 0 (a - 1 / 2) (b + 1 / 2)) := by
  classical
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty (not_le.mpr hba), inter_empty, measure_empty]
    exact bot_le
  set B := (boxFinsetLe (b + 1 / 2)).filter (fun ρ => a - 1 / 2 < ρ.im) with hBdef
  have hsub : xiShadow ∩ Icc a b ⊆
      ⋃ ρ ∈ B, Ioo (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2)) := by
    intro x hx
    have hx0 : x ∈ xiShadow ∩ Icc 0 b := ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩
    obtain ⟨ρ, hρ, hxρ⟩ := exists_boxZero_of_mem_xiShadow hx0
    have hρm := (mem_boxFinsetLe.mp hρ)
    have hre1 : ρ.re < 1 := hρm.2.1
    refine mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρ, ?_⟩, hxρ⟩
    have := hxρ.2
    linarith [hx.2.1]
  have hB : ∀ ρ ∈ B, 1 / 2 < ρ.re ∧ xi ρ = 0 := by
    intro ρ hρ
    have h := mem_boxFinsetLe.mp (Finset.mem_filter.mp hρ).1
    exact ⟨h.1, h.2.2.2.2⟩
  have hwin : windowTail 0 (a - 1 / 2) (b + 1 / 2)
      = ∑ z ∈ stripFinsetPos (b + 1 / 2) \ stripFinsetPos (a - 1 / 2),
          ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - 0) 0 :=
    windowTail_eq_sum (by linarith)
  calc volume (xiShadow ∩ Icc a b)
      ≤ volume (⋃ ρ ∈ B, Ioo (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2))) := measure_mono hsub
    _ ≤ ∑ ρ ∈ B, volume (Ioo (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2))) :=
        measure_biUnion_finset_le _ _
    _ = ∑ ρ ∈ B, ENNReal.ofReal (2 * (ρ.re - 1 / 2)) := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Real.volume_Ioo]
        congr 1
        ring
    _ = ENNReal.ofReal (∑ ρ ∈ B, 2 * (ρ.re - 1 / 2)) :=
        (ENNReal.ofReal_sum_of_nonneg fun ρ hρ => by linarith [(hB ρ hρ).1]).symm
    _ ≤ ENNReal.ofReal (2 * windowTail 0 (a - 1 / 2) (b + 1 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hwin, Finset.mul_sum]
        have hBsub : B ⊆ stripFinsetPos (b + 1 / 2) \ stripFinsetPos (a - 1 / 2) := by
          intro z hz
          have hzB := Finset.mem_filter.mp hz
          have h := mem_boxFinsetLe.mp hzB.1
          rw [Finset.mem_sdiff, mem_stripFinsetPos, mem_stripFinsetPos]
          refine ⟨⟨by linarith [h.1], h.2.1, by linarith [hzB.2], h.2.2.2.1, h.2.2.2.2⟩,
            fun hh => ?_⟩
          linarith [hh.2.2.2.1, hzB.2]
        calc ∑ ρ ∈ B, 2 * (ρ.re - 1 / 2)
            ≤ ∑ ρ ∈ B, 2 * (((analyticOrderAt xi ρ).toNat : ℝ) * max (ρ.re - 1 / 2 - 0) 0) := by
              refine Finset.sum_le_sum fun ρ hρ => ?_
              have h1 := one_le_toNat_analyticOrderAt_xi (hB ρ hρ).2
              have h1' : (1 : ℝ) ≤ ((analyticOrderAt xi ρ).toNat : ℝ) := by exact_mod_cast h1
              have hpos : 0 ≤ ρ.re - 1 / 2 := by linarith [(hB ρ hρ).1]
              rw [sub_zero, max_eq_left hpos]
              nlinarith
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hBsub fun z _ _ =>
              mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _))

/-- A property holding off the shadow holds on measure at least `(b − a) − c` of `[a, b]` once
the shadow occupies at most `c ≥ 0` of `[a, b]`. -/
theorem ofReal_window_sub_le_volume_of_not_mem_xiShadow {P : ℝ → Prop}
    (hP : ∀ x : ℝ, x ∉ xiShadow → P x) {a b c : ℝ} (hc : 0 ≤ c)
    (hV : volume (xiShadow ∩ Icc a b) ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (b - a - c) ≤ volume {x ∈ Icc a b | P x} := by
  have hsub : Icc a b \ (xiShadow ∩ Icc a b) ⊆ {x ∈ Icc a b | P x} :=
    fun x hx => ⟨hx.1, hP x fun h => hx.2 ⟨h, hx.1⟩⟩
  calc ENNReal.ofReal (b - a - c) = ENNReal.ofReal (b - a) - ENNReal.ofReal c :=
        ENNReal.ofReal_sub _ hc
    _ ≤ volume (Icc a b) - volume (xiShadow ∩ Icc a b) := by
        rw [Real.volume_Icc]
        exact tsub_le_tsub_left hV _
    _ ≤ volume (Icc a b \ (xiShadow ∩ Icc a b)) := le_measure_sdiff
    _ ≤ _ := measure_mono hsub

/-- A property holding off the shadow holds on measure at least `(1 − 2μ) H − 3` of
`[T + 3/2, T + H − 3/2]` once the window moment `Σ_{T+1 < Im ρ ≤ T+H−1}` is at most `μ H`. -/
theorem ofReal_window_le_volume_of_windowTail_le {P : ℝ → Prop}
    (hP : ∀ x : ℝ, x ∉ xiShadow → P x) {T H μ : ℝ} (hT : 0 ≤ T) (hH : 2 ≤ H)
    (hW : windowTail 0 (T + 1) (T + H - 1) ≤ μ * H) :
    ENNReal.ofReal ((1 - 2 * μ) * H - 3) ≤
      volume {x ∈ Icc (T + 3 / 2) (T + H - 3 / 2) | P x} := by
  have hV := volume_xiShadow_inter_Icc_le_windowTail (a := T + 3 / 2) (b := T + H - 3 / 2)
    (by linarith)
  rw [show T + 3 / 2 - 1 / 2 = T + 1 by ring, show T + H - 3 / 2 + 1 / 2 = T + H - 1 by ring] at hV
  have hW0 : 0 ≤ windowTail 0 (T + 1) (T + H - 1) := by
    rw [windowTail_eq_sum (by linarith)]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  have h := ofReal_window_sub_le_volume_of_not_mem_xiShadow hP (by positivity) hV
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
  linarith

/-- **The Hadamard failure set in a window against the window moment.**  For `a ≥ 1`, the set of
`s` with `½ < Re s`, `a ≤ Im s ≤ b` where `ξ(s) = 0` or `Re(ξ'/ξ)(s) < 0` has area at most
`Σ_{a−½ < Im ρ ≤ b+½} m(ρ)(Re ρ − ½)⁺`. -/
theorem volume_hadamardFail_window_le {a b : ℝ} (ha : 1 ≤ a) :
    volume {s : ℂ | 1 / 2 < s.re ∧ a ≤ s.im ∧ s.im ≤ b ∧ ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)}
      ≤ ENNReal.ofReal (windowTail 0 (a - 1 / 2) (b + 1 / 2)) := by
  classical
  rcases lt_or_ge b a with hba | hab
  · have : {s : ℂ | 1 / 2 < s.re ∧ a ≤ s.im ∧ s.im ≤ b ∧
        ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)} = ∅ := by
      ext s
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h1 h2
      linarith
    rw [this, measure_empty]
    exact bot_le
  set B := (boxFinsetLe (b + 1 / 2)).filter (fun ρ => a - 1 / 2 < ρ.im) with hBdef
  have hsub : {s : ℂ | 1 / 2 < s.re ∧ a ≤ s.im ∧ s.im ≤ b ∧
      ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)} ⊆ ⋃ ρ ∈ B, hadamardRect ρ := by
    intro s ⟨hs, has, hsb, hfail⟩
    obtain ⟨ρ, hρ, hsρ⟩ := exists_boxZero_of_hadamard_fail hs (by linarith) hsb hfail
    have hρm := mem_boxFinsetLe.mp hρ
    simp only [hadamardRect, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod,
      mem_Ioc, mem_Icc] at hsρ
    refine mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρ, ?_⟩, ?_⟩
    · linarith [hsρ.2.2, hρm.2.1]
    · simp only [hadamardRect, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod,
        mem_Ioc, mem_Icc]
      exact hsρ
  have hB : ∀ ρ ∈ B, 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ xi ρ = 0 := by
    intro ρ hρ
    have h := mem_boxFinsetLe.mp (Finset.mem_filter.mp hρ).1
    exact ⟨h.1, h.2.1, h.2.2.2.2⟩
  have hBsub : B ⊆ stripFinsetPos (b + 1 / 2) \ stripFinsetPos (a - 1 / 2) := by
    intro z hz
    have hzB := Finset.mem_filter.mp hz
    have h := mem_boxFinsetLe.mp hzB.1
    rw [Finset.mem_sdiff, mem_stripFinsetPos, mem_stripFinsetPos]
    refine ⟨⟨by linarith [h.1], h.2.1, by linarith [hzB.2], h.2.2.2.1, h.2.2.2.2⟩, fun hh => ?_⟩
    linarith [hh.2.2.2.1, hzB.2]
  calc volume {s : ℂ | 1 / 2 < s.re ∧ a ≤ s.im ∧ s.im ≤ b ∧
          ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)}
      ≤ volume (⋃ ρ ∈ B, hadamardRect ρ) := measure_mono hsub
    _ ≤ ∑ ρ ∈ B, volume (hadamardRect ρ) := measure_biUnion_finset_le _ _
    _ = ∑ ρ ∈ B, ENNReal.ofReal ((ρ.re - 1 / 2) * (2 * (ρ.re - 1 / 2))) := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [volume_hadamardRect, ← ENNReal.ofReal_mul (by linarith [(hB ρ hρ).1])]
    _ ≤ ∑ ρ ∈ B, ENNReal.ofReal (ρ.re - 1 / 2) := by
        refine Finset.sum_le_sum fun ρ hρ => ENNReal.ofReal_le_ofReal ?_
        have h1 := (hB ρ hρ).1
        have h2 := (hB ρ hρ).2.1
        nlinarith
    _ = ENNReal.ofReal (∑ ρ ∈ B, (ρ.re - 1 / 2)) :=
        (ENNReal.ofReal_sum_of_nonneg fun ρ hρ => by linarith [(hB ρ hρ).1]).symm
    _ ≤ ENNReal.ofReal (windowTail 0 (a - 1 / 2) (b + 1 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [windowTail_eq_sum (by linarith)]
        calc ∑ ρ ∈ B, (ρ.re - 1 / 2)
            ≤ ∑ ρ ∈ B, ((analyticOrderAt xi ρ).toNat : ℝ) * max (ρ.re - 1 / 2 - 0) 0 := by
              refine Finset.sum_le_sum fun ρ hρ => ?_
              have h1 := one_le_toNat_analyticOrderAt_xi (hB ρ hρ).2.2
              have h1' : (1 : ℝ) ≤ ((analyticOrderAt xi ρ).toNat : ℝ) := by exact_mod_cast h1
              have hpos : 0 ≤ ρ.re - 1 / 2 := by linarith [(hB ρ hρ).1]
              rw [sub_zero, max_eq_left hpos]
              nlinarith
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hBsub fun z _ _ =>
              mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)

theorem volume_rightHalfStrip_window (a b : ℝ) :
    volume {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ a ≤ s.im ∧ s.im ≤ b}
      = ENNReal.ofReal ((b - a) / 2) := by
  have e : {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ a ≤ s.im ∧ s.im ≤ b}
      = Complex.measurableEquivRealProd ⁻¹' (Ioo (1 / 2) 1 ×ˢ Icc a b) := by
    ext s
    simp only [mem_setOf_eq, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod,
      mem_Ioo, mem_Icc]
    tauto
  rw [e, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end DeBruijn

/-! ## The window moment `11/50` -/

/-- `log c_{9/10} − 9/10 + 1/50 ≤ 4π · 11/50`, from `e^{1/5} ≥ 61/50` and `e^{9/5} ≥ 61/11`. -/
theorem log_selbergBlockConstNinth_nine_tenths_le :
    Real.log (ZetaGateProductAFE.selbergBlockConstNinth (9 / 10)) - 9 / 10 + 1 / 50
      ≤ 4 * Real.pi * (11 / 50) := by
  set y : ℝ := Real.exp (-(1 / 5 : ℝ)) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy50 : y ≤ 50 / 61 := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 5 by norm_num)
    rw [hy, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h ⊢
    linarith
  have hc : ZetaGateProductAFE.selbergBlockConstNinth (9 / 10) = Real.exp (9 / 5) / (1 - y) := by
    unfold ZetaGateProductAFE.selbergBlockConstNinth
    rw [hy]
    norm_num
  have h1y : 0 < 1 - y := by linarith
  rw [hc, Real.log_div (Real.exp_pos _).ne' h1y.ne', Real.log_exp]
  -- `log(1 − y) ≥ log(11/61) ≥ −9/5`
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he45 : (1 + 4 / 5 + (4 / 5) ^ 2 / 2 : ℝ) ≤ Real.exp (4 / 5) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have he95 : (61 / 11 : ℝ) ≤ Real.exp (9 / 5) := by
    rw [show (9 / 5 : ℝ) = 1 + 4 / 5 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (4 / 5 : ℝ), Real.exp_pos (1 : ℝ)]
  have hlog : Real.log (61 / 11 : ℝ) ≤ 9 / 5 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact he95
  have hlog1y : Real.log (11 / 61 : ℝ) ≤ Real.log (1 - y) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hinv : Real.log (11 / 61 : ℝ) = -Real.log (61 / 11 : ℝ) := by
    rw [show (11 / 61 : ℝ) = (61 / 11)⁻¹ by norm_num, Real.log_inv]
  have hπ := Real.pi_gt_d2
  linarith

/-- **The window moment.**  For all large `T` and every `T^{24/25} ≤ H ≤ T`,
`Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½)⁺ ≤ (11/50) H`. -/
theorem eventually_windowTail_zero_le :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      windowTail 0 (T + 1) (T + H - 1) ≤ 11 / 50 * H := by
  filter_upwards [eventually_windowTail_le_selberg_ninth (R := 9 / 10) (η := 1 / 50)
    (by norm_num) (by norm_num), eventually_ge_atTop (0 : ℝ)] with T hT hT0
  intro H hH1 hH2
  have hH0 : 0 ≤ H := le_trans (Real.rpow_nonneg hT0 _) hH1
  have h := (hT H hH1 hH2).2
  have hc := log_selbergBlockConstNinth_nine_tenths_le
  have hπ : 0 < 4 * Real.pi := by positivity
  have h1 : 4 * Real.pi * windowTail 0 (T + 1) (T + H - 1) ≤ 4 * Real.pi * (11 / 50) * H :=
    h.trans (mul_le_mul_of_nonneg_right hc hH0)
  have h2 : 4 * Real.pi * (11 / 50) * H = 4 * Real.pi * (11 / 50 * H) := by ring
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hπ

/-! ## Signs on every window -/

theorem four_le_rpow_twentyfour_div_twentyfive {T : ℝ} (hT9 : (2 : ℝ) ^ 9 ≤ T) :
    (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25) := by
  have h1 : ((2 : ℝ) ^ 9) ^ ((24 : ℝ) / 25) ≤ T ^ ((24 : ℝ) / 25) :=
    Real.rpow_le_rpow (by positivity) hT9 (by norm_num)
  have h2 : (4 : ℝ) ≤ ((2 : ℝ) ^ 9) ^ ((24 : ℝ) / 25) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  linarith

/-- **Laguerre and vertical monotonicity on every window.**  For all large `T` and every
`T^{24/25} ≤ H ≤ T`, the set of `x ∈ [T + 3/2, T + H − 3/2]` with
`Ξ'(x)² − Ξ(x)Ξ''(x) ≥ 0` and `y ↦ |Ξ(x+iy)|` nondecreasing on `y ≥ 0` has measure at least
`(14/25) H − 3`. -/
theorem eventually_volume_laguerre_monotone_window_ge :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (14 / 25 * H - 3) ≤
        volume {x ∈ Icc (T + 3 / 2) (T + H - 3 / 2) |
          MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici 0) ∧
          0 ≤ (deriv (DeBruijn.riemannHeat 0) x ^ 2
            - DeBruijn.riemannHeat 0 x * deriv (deriv (DeBruijn.riemannHeat 0)) x).re} := by
  filter_upwards [eventually_windowTail_zero_le, eventually_ge_atTop ((2 : ℝ) ^ 9)]
    with T hT hT9
  intro H hH1 hH2
  have hH : 2 ≤ H := by linarith [four_le_rpow_twentyfour_div_twentyfive hT9]
  have h := DeBruijn.ofReal_window_le_volume_of_windowTail_le
    (fun x hx => DeBruijn.monotoneOn_laguerre_of_not_mem_xiShadow hx)
    (by linarith [show (0 : ℝ) ≤ 2 ^ 9 by norm_num]) hH (hT H hH1 hH2)
  rwa [show (1 - 2 * (11 / 50 : ℝ)) * H - 3 = 14 / 25 * H - 3 by ring] at h

/-- **All-order slice positivity on every window.** -/
theorem eventually_volume_sliceCoeff_window_ge :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (14 / 25 * H - 3) ≤
        volume {t ∈ Icc (T + 3 / 2) (T + H - 3 / 2) | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} := by
  filter_upwards [eventually_windowTail_zero_le, eventually_ge_atTop ((2 : ℝ) ^ 9)]
    with T hT hT9
  intro H hH1 hH2
  have hH : 2 ≤ H := by linarith [four_le_rpow_twentyfour_div_twentyfive hT9]
  have h := DeBruijn.ofReal_window_le_volume_of_windowTail_le
    (fun t ht => DeBruijn.xiSliceCoeff_nonneg_of_not_mem_xiShadow ht)
    (by linarith [show (0 : ℝ) ≤ 2 ^ 9 by norm_num]) hH (hT H hH1 hH2)
  rwa [show (1 - 2 * (11 / 50 : ℝ)) * H - 3 = 14 / 25 * H - 3 by ring] at h

/-- **Speiser-clean heights on every window.** -/
theorem eventually_volume_speiserUnshadowed_window_ge :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (14 / 25 * H - 3) ≤
        volume {t ∈ Icc (T + 3 / 2) (T + H - 3 / 2) | SpeiserUnshadowed t} := by
  filter_upwards [eventually_windowTail_zero_le, eventually_ge_atTop ((2 : ℝ) ^ 9)]
    with T hT hT9
  intro H hH1 hH2
  have hH : 2 ≤ H := by linarith [four_le_rpow_twentyfour_div_twentyfive hT9]
  have h := DeBruijn.ofReal_window_le_volume_of_windowTail_le
    (fun t ht => speiserUnshadowed_of_not_mem_xiShadow ht)
    (by linarith [show (0 : ℝ) ≤ 2 ^ 9 by norm_num]) hH (hT H hH1 hH2)
  rwa [show (1 - 2 * (11 / 50 : ℝ)) * H - 3 = 14 / 25 * H - 3 by ring] at h

/-- **The Hadamard sign on every window.**  For all large `T` and every `T^{24/25} ≤ H ≤ T`, the
set of `s` with `½ < Re s < 1`, `T + 3/2 ≤ Im s ≤ T + H − 3/2`, `ξ(s) ≠ 0` and `Re(ξ'/ξ)(s) ≥ 0` has
area at least `(7/25) H − 3/2`, against the window area `(H − 3)/2`. -/
theorem eventually_volume_hadamardSign_window_ge :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (7 / 25 * H - 3 / 2) ≤
        volume {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ T + 3 / 2 ≤ s.im ∧ s.im ≤ T + H - 3 / 2 ∧
          xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} := by
  filter_upwards [eventually_windowTail_zero_le, eventually_ge_atTop ((2 : ℝ) ^ 9)]
    with T hT hT9
  intro H hH1 hH2
  have hT0 : (0 : ℝ) ≤ T := by linarith [show (0 : ℝ) ≤ 2 ^ 9 by norm_num]
  have hH : 2 ≤ H := by linarith [four_le_rpow_twentyfour_div_twentyfive hT9]
  have hW := hT H hH1 hH2
  have hF := DeBruijn.volume_hadamardFail_window_le (a := T + 3 / 2) (b := T + H - 3 / 2)
    (by linarith)
  rw [show T + 3 / 2 - 1 / 2 = T + 1 by ring, show T + H - 3 / 2 + 1 / 2 = T + H - 1 by ring] at hF
  have hW0 : 0 ≤ windowTail 0 (T + 1) (T + H - 1) := by
    rw [windowTail_eq_sum (by linarith)]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  set Ω := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ T + 3 / 2 ≤ s.im ∧ s.im ≤ T + H - 3 / 2}
  set F := {s : ℂ | 1 / 2 < s.re ∧ T + 3 / 2 ≤ s.im ∧ s.im ≤ T + H - 3 / 2 ∧
    ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)}
  have hsub : Ω \ F ⊆ {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ T + 3 / 2 ≤ s.im ∧
      s.im ≤ T + H - 3 / 2 ∧ xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} := by
    intro s ⟨⟨h1, h2, h3, h4⟩, hnF⟩
    have hg : xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re := by
      by_contra hc
      exact hnF ⟨h1, h3, h4, hc⟩
    exact ⟨h1, h2, h3, h4, hg.1, hg.2⟩
  calc ENNReal.ofReal (7 / 25 * H - 3 / 2)
      ≤ ENNReal.ofReal ((T + H - 3 / 2 - (T + 3 / 2)) / 2)
          - ENNReal.ofReal (windowTail 0 (T + 1) (T + H - 1)) := by
        rw [← ENNReal.ofReal_sub _ hW0]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ volume Ω - volume F := by
        rw [DeBruijn.volume_rightHalfStrip_window]
        exact tsub_le_tsub_left hF _
    _ ≤ volume (Ω \ F) := le_measure_sdiff
    _ ≤ _ := measure_mono hsub

/-- **Every window of length `T^{24/25}` contains a Speiser-clean height.** -/
theorem eventually_exists_speiserUnshadowed_window :
    ∀ᶠ T in atTop, ∃ t ∈ Icc T (T + T ^ ((24 : ℝ) / 25)), SpeiserUnshadowed t := by
  filter_upwards [eventually_volume_speiserUnshadowed_window_ge, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop ((2 : ℝ) ^ 9)] with T hT hT1 hT9
  have hT0 : 0 < T := by linarith
  have hT2425 : (8 : ℝ) ≤ T ^ ((24 : ℝ) / 25) := by
    have h1 : ((2 : ℝ) ^ 9) ^ ((24 : ℝ) / 25) ≤ T ^ ((24 : ℝ) / 25) :=
      Real.rpow_le_rpow (by positivity) hT9 (by norm_num)
    have h2 : (8 : ℝ) ≤ ((2 : ℝ) ^ 9) ^ ((24 : ℝ) / 25) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have hHT : T ^ ((24 : ℝ) / 25) ≤ T := by
    have := Real.rpow_le_rpow_of_exponent_le hT1 (show (24 : ℝ) / 25 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h := hT _ le_rfl hHT
  have hpos : (0 : ENNReal) < ENNReal.ofReal (14 / 25 * T ^ ((24 : ℝ) / 25) - 3) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨t, ht, hts⟩ := nonempty_of_measure_ne_zero (lt_of_lt_of_le hpos h).ne'
  exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, hts⟩

end

end RHTower
