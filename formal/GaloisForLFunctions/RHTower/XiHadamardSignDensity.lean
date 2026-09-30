import GaloisForLFunctions.RHTower.XiLogDerivReLocality
import GaloisForLFunctions.RHTower.XiLaguerreShadowDensity

/-!
# The Hadamard sign `Re(ξ'/ξ) ≥ 0` on more than half of the right half of the critical strip

RH is equivalent to `Re(ξ'/ξ)(s) ≥ 0` on `Re s > ½`.  By the disk criterion
(`re_logDeriv_xi_nonneg_of_disk_bound`) a zero `ρ` obstructs the sign at `s` only if
`(Re ρ − ½)² ≥ (Re s − ½)² + (Im s − Im ρ)²`, i.e. only if `s` lies in the rectangle
`½ < Re s ≤ Re ρ`, `|Im s − Im ρ| ≤ Re ρ − ½` of an off-line zero, normalised by the functional
equation and conjugation to `Re ρ > ½`, `Im ρ ≥ 0` (`exists_boxZero_of_hadamard_fail`).  The rectangle
has area `2(Re ρ − ½)² ≤ Re ρ − ½`, so the failure set in `{Re s > ½, 0 ≤ Im s ≤ V}` has area at most
the off-line first moment `Σ_{0 ≤ Im ρ ≤ V + ½} m(ρ)(Re ρ − ½)` (`volume_hadamardFail_le`).  With the
unconditional bound `≤ (21/100) V`:

  `vol{s : ½ < Re s < 1, 0 ≤ Im s ≤ V, ξ(s) ≠ 0, Re(ξ'/ξ)(s) ≥ 0} ≥ (29/100) V − 21/200`

for all large `V` (`eventually_volume_hadamardSign_ge`), `58%` of the area `V/2`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.DeBruijn

noncomputable section

/-- The rectangle `½ < Re s ≤ Re ρ`, `|Im s − Im ρ| ≤ Re ρ − ½`. -/
def hadamardRect (ρ : ℂ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹'
    (Ioc (1 / 2) ρ.re ×ˢ Icc (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2)))

theorem volume_hadamardRect (ρ : ℂ) :
    volume (hadamardRect ρ) =
      ENNReal.ofReal (ρ.re - 1 / 2) * ENNReal.ofReal (2 * (ρ.re - 1 / 2)) := by
  unfold hadamardRect
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
  congr 2
  ring

/-- **Localisation of the failure of the Hadamard sign.** -/
theorem exists_boxZero_of_hadamard_fail {V : ℝ} {s : ℂ} (hs : 1 / 2 < s.re) (hs0 : 0 ≤ s.im)
    (hsV : s.im ≤ V) (hfail : ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)) :
    ∃ ρ ∈ boxFinsetLe (V + 1 / 2), s ∈ hadamardRect ρ := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hno' : ∀ ρ ∈ boxFinsetLe (V + 1 / 2), s.re ≤ ρ.re →
      |s.im - ρ.im| ≤ ρ.re - 1 / 2 → False := by
    intro ρ hρ h1 h2
    apply hno ρ hρ
    rw [abs_le] at h2
    simp only [hadamardRect, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod,
      mem_Ioc, mem_Icc]
    exact ⟨⟨hs, h1⟩, by linarith [h2.1], by linarith [h2.2]⟩
  -- every zero satisfies the disk condition at `s`
  have hdisk : ∀ w : ℂ, xi w = 0 → (w.re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - w.im) ^ 2 := by
    intro w hw
    by_contra hge
    rw [not_lt] at hge
    -- move the zero to the right of the line
    obtain ⟨w₁, hw₁, hre₁, him₁, hsq₁⟩ : ∃ w₁ : ℂ, xi w₁ = 0 ∧ 1 / 2 < w₁.re ∧ w₁.im = w.im ∧
        (w₁.re - 1 / 2) ^ 2 = (w.re - 1 / 2) ^ 2 := by
      have hne : w.re ≠ 1 / 2 := by
        intro h
        rw [h, sub_self, zero_pow two_ne_zero] at hge
        nlinarith [sq_nonneg (s.im - w.im)]
      rcases lt_or_gt_of_ne hne with h | h
      · refine ⟨1 - (starRingEnd ℂ) w, ?_, ?_, ?_, ?_⟩
        · rw [xi_one_sub, xi_conj, hw, map_zero]
        · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
          linarith
        · simp
        · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
          ring
      · exact ⟨w, hw, h, rfl, rfl⟩
    -- move it to the upper half-plane
    obtain ⟨ρ, hρ, hreρ, himρ, hsqρ, hdist⟩ : ∃ ρ : ℂ, xi ρ = 0 ∧ 1 / 2 < ρ.re ∧ 0 ≤ ρ.im ∧
        ρ.re = w₁.re ∧ |s.im - ρ.im| ≤ |s.im - w.im| := by
      rcases le_or_gt 0 w₁.im with h | h
      · exact ⟨w₁, hw₁, hre₁, h, rfl, by rw [him₁]⟩
      · refine ⟨(starRingEnd ℂ) w₁, ?_, ?_, ?_, ?_, ?_⟩
        · rw [xi_conj, hw₁, map_zero]
        · simpa using hre₁
        · simp only [Complex.conj_im]
          linarith
        · simp
        · simp only [Complex.conj_im, sub_neg_eq_add]
          rw [← him₁, abs_of_pos (by linarith : 0 < s.im - w₁.im), abs_le]
          constructor <;> linarith
    have hb : 0 < ρ.re - 1 / 2 := by linarith
    have hkey : (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
      have h1 : (s.im - ρ.im) ^ 2 ≤ (s.im - w.im) ^ 2 := by
        rw [← sq_abs (s.im - ρ.im), ← sq_abs (s.im - w.im)]
        exact pow_le_pow_left₀ (abs_nonneg _) hdist 2
      rw [hsqρ, hsq₁]
      linarith
    have hre : s.re ≤ ρ.re := by nlinarith [sq_nonneg (s.im - ρ.im)]
    have him : |s.im - ρ.im| ≤ ρ.re - 1 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) hb.le, sq_abs]
      nlinarith [sq_nonneg (s.re - 1 / 2)]
    have hρ1 := xi_zero_re_lt_one hρ
    have hρV : ρ.im ≤ V + 1 / 2 := by
      have := (abs_le.mp him).1
      linarith
    exact hno' ρ (by rw [mem_boxFinsetLe]; exact ⟨hreρ, hρ1, himρ, hρV, hρ⟩) hre him
  have hxi : xi s ≠ 0 := by
    intro h0
    have hmem : s ∈ boxFinsetLe (V + 1 / 2) := by
      rw [mem_boxFinsetLe]
      exact ⟨hs, xi_zero_re_lt_one h0, hs0, by linarith, h0⟩
    exact hno' s hmem le_rfl (by rw [sub_self, abs_zero]; linarith)
  exact hfail ⟨hxi, re_logDeriv_xi_nonneg_of_disk_bound hs hxi
    (fun q => hdisk _ (xi_eq_zero_of_mem_divisor_support q.1))⟩

/-- **The failure set of the Hadamard sign against the off-line first moment.** -/
theorem volume_hadamardFail_le (V : ℝ) :
    volume {s : ℂ | 1 / 2 < s.re ∧ 0 ≤ s.im ∧ s.im ≤ V ∧ ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)}
      ≤ ENNReal.ofReal (offLineMoment (V + 1 / 2)) := by
  classical
  set B := boxFinsetLe (V + 1 / 2)
  have hsub : {s : ℂ | 1 / 2 < s.re ∧ 0 ≤ s.im ∧ s.im ≤ V ∧
      ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)} ⊆ ⋃ ρ ∈ B, hadamardRect ρ := by
    intro s ⟨hs, hs0, hsV, hfail⟩
    obtain ⟨ρ, hρ, hsρ⟩ := exists_boxZero_of_hadamard_fail hs hs0 hsV hfail
    exact mem_iUnion₂.mpr ⟨ρ, hρ, hsρ⟩
  have hB : ∀ ρ ∈ B, 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ xi ρ = 0 := by
    intro ρ hρ
    rw [mem_boxFinsetLe] at hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.2.2⟩
  calc volume {s : ℂ | 1 / 2 < s.re ∧ 0 ≤ s.im ∧ s.im ≤ V ∧
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
    _ ≤ ENNReal.ofReal (offLineMoment (V + 1 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        unfold offLineMoment
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have h1 := one_le_toNat_analyticOrderAt_xi (hB ρ hρ).2.2
        have h1' : (1 : ℝ) ≤ ((analyticOrderAt xi ρ).toNat : ℝ) := by exact_mod_cast h1
        have hpos : 0 ≤ ρ.re - 1 / 2 := by linarith [(hB ρ hρ).1]
        nlinarith

theorem volume_rightHalfStrip (V : ℝ) :
    volume {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ V} = ENNReal.ofReal (V / 2) := by
  have e : {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ V}
      = Complex.measurableEquivRealProd ⁻¹' (Ioo (1 / 2) 1 ×ˢ Icc 0 V) := by
    ext s
    simp only [mem_setOf_eq, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod,
      mem_Ioo, mem_Icc]
    tauto
  rw [e, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- **`Re(ξ'/ξ) ≥ 0` on more than half of the right half of the critical strip.** For all large
`V` the set of `s` with `½ < Re s < 1`, `0 ≤ Im s ≤ V`, `ξ(s) ≠ 0` and `Re(ξ'/ξ)(s) ≥ 0` has area at
least `(29/100) V − 21/200`, against the total area `V/2`. -/
theorem eventually_volume_hadamardSign_ge :
    ∀ᶠ V in atTop, ENNReal.ofReal (29 / 100 * V - 21 / 200) ≤
      volume {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ V ∧
        xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} := by
  have h := (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) tendsto_id).eventually
    ZetaGateProductAFE.eventually_offLineMoment_le
  filter_upwards [h, eventually_ge_atTop 0] with V hV hV0
  simp only [id] at hV
  set Ω := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ V}
  set F := {s : ℂ | 1 / 2 < s.re ∧ 0 ≤ s.im ∧ s.im ≤ V ∧ ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)}
  have hF : volume F ≤ ENNReal.ofReal (21 / 100 * (V + 1 / 2)) :=
    (volume_hadamardFail_le V).trans (ENNReal.ofReal_le_ofReal hV)
  have hsub : Ω \ F ⊆ {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ V ∧
      xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} := by
    intro s ⟨⟨h1, h2, h3, h4⟩, hnF⟩
    have hg : xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re := by
      by_contra hc
      exact hnF ⟨h1, h3, h4, hc⟩
    exact ⟨h1, h2, h3, h4, hg.1, hg.2⟩
  calc ENNReal.ofReal (29 / 100 * V - 21 / 200)
      = ENNReal.ofReal (V / 2) - ENNReal.ofReal (21 / 100 * (V + 1 / 2)) := by
        rw [← ENNReal.ofReal_sub _ (by positivity)]
        congr 1
        ring
    _ ≤ volume Ω - volume F := by
        rw [volume_rightHalfStrip V]
        exact tsub_le_tsub_left hF _
    _ ≤ volume (Ω \ F) := le_measure_sdiff
    _ ≤ _ := measure_mono hsub

end

end RHTower.DeBruijn
