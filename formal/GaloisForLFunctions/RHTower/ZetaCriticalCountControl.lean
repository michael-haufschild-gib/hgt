import GaloisForLFunctions.RHTower.ZetaNarrowCountControl
import GaloisForLFunctions.RHTower.SelbergVonMangoldtPolyTypical
import GaloisForLFunctions.RHTower.ZetaCriticalWindowStructure
import GaloisForLFunctions.HTGeometry.BoxPartitionSums

/-!
# Count control from the explicit formula, off a small bad set

Write `D(t) = D_x(½ + τ + it)` for Selberg's smoothed von Mangoldt polynomial. The pointwise
explicit formula `exists_abs_narrowMass_sub_le` bounds the narrow mass by
`|M_τ(p) − τℓ_p/2| ≤ τ‖D‖ + κM_τ(p) + 2τ + 4τw`.

* `countControl_of_bound`: if `‖D‖ ≤ Θ ≤ δℓ/4`, `κ ≤ δ/8`, `w ≤ 1/4`, `|ℓ_p − ℓ| ≤ 1` and
  `ℓ ≥ 28/δ`, this is two-sided count control `(1 ∓ δ)τℓ/2`.
* `narrowMass_le_of_bound`: in general (`κ ≤ 1/2`, `w ≤ 1/4`, `ℓ_p ≤ L`),
  `M_τ(p) ≤ τL + 6τ + 2τ‖D‖`.
* `criticalBadSet`: the heights `t ∈ [A, B]` at which `‖D‖ > Θ` at one of the grid points
  `t + 2jτ₂`, `|j| ≤ 6`, at scale `τ₁` or `τ₂`. By Chebyshev and the mean square of `D`
  (`volume_criticalBadSet_le`), its measure is at most
  `26 (B − A + E_x) · 5/(τ₁²Θ²)` with `E_x = 8N_x(1 + log N_x)`.
* `lintegral_bad_le`: `∫⁻ 1_Bad (a + b‖D‖²) ≤ a |Bad| + b ∫_A^B ‖D‖²`.
-/

noncomputable section

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry (volume_Icc_inter_lt_norm_le)

namespace RHTower

/-- **Count control from the explicit formula bound.** -/
theorem countControl_of_bound {τ ℓ ℓp δ Θ κ w p : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : κ ≤ δ / 8) (hΘ : Θ ≤ δ * ℓ / 4) (hw : w ≤ 1 / 4)
    (hℓp : |ℓp - ℓ| ≤ 1) (hℓ : 28 / δ ≤ ℓ)
    (hb : |narrowMass τ p - τ * ℓp / 2| ≤ τ * Θ + κ * narrowMass τ p + 2 * τ + 4 * τ * w) :
    CountControl τ ℓ δ p := by
  set M := narrowMass τ p with hM
  have hM0 : 0 ≤ M := narrowMass_nonneg τ p
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ
  have hδℓ : 28 ≤ δ * ℓ := by rwa [div_le_iff₀ hδ, mul_comm] at hℓ
  rw [abs_le] at hb hℓp
  have hw' : 4 * τ * w ≤ τ := by nlinarith
  have hκM : κ * M ≤ δ / 8 * M := mul_le_mul_of_nonneg_right hκ hM0
  have hτℓp1 : τ * (ℓ - 1) ≤ τ * ℓp := mul_le_mul_of_nonneg_left (by linarith) hτ.le
  have hτℓp2 : τ * ℓp ≤ τ * (ℓ + 1) := mul_le_mul_of_nonneg_left (by linarith) hτ.le
  have hτδℓ : τ * 28 ≤ τ * (δ * ℓ) := mul_le_mul_of_nonneg_left hδℓ hτ.le
  constructor
  · -- `(1 + κ) M ≥ τℓ/2 − τδℓ/4 − 3.5τ`
    have h1 : τ * ℓ / 2 - τ * (δ * ℓ / 4) - 7 / 2 * τ ≤ (1 + κ) * M := by
      have : τ * Θ ≤ τ * (δ * ℓ / 4) := mul_le_mul_of_nonneg_left hΘ hτ.le
      nlinarith
    by_contra hcon
    push Not at hcon
    have h2 : (1 + κ) * M ≤ (1 + δ / 8) * M := by nlinarith
    have h3 : (1 + δ / 8) * M < (1 + δ / 8) * ((1 - δ) * (τ * ℓ / 2)) :=
      mul_lt_mul_of_pos_left hcon (by positivity)
    have h4 : 0 ≤ τ * ℓ * δ * δ := by positivity
    nlinarith
  · have h1 : (1 - κ) * M ≤ τ * ℓ / 2 + τ * (δ * ℓ / 4) + 7 / 2 * τ := by
      have : τ * Θ ≤ τ * (δ * ℓ / 4) := mul_le_mul_of_nonneg_left hΘ hτ.le
      nlinarith
    by_contra hcon
    push Not at hcon
    have h2 : (1 - δ / 8) * M ≤ (1 - κ) * M := by nlinarith
    have h3 : (1 - δ / 8) * ((1 + δ) * (τ * ℓ / 2)) < (1 - δ / 8) * M :=
      mul_lt_mul_of_pos_left hcon (by linarith)
    have h4 : 0 ≤ τ * ℓ * δ * (1 - δ) := by
      have : 0 ≤ 1 - δ := by linarith
      positivity
    nlinarith


/-- **The crude majorant** `M_τ(p) ≤ τL + 6τ + 2τ‖D‖`. -/
theorem narrowMass_le_of_bound {τ ℓp L Dn κ w p : ℝ} (hτ : 0 < τ) (hκ : κ ≤ 1 / 2)
    (hw : w ≤ 1 / 4) (hℓp : ℓp ≤ L)
    (hb : |narrowMass τ p - τ * ℓp / 2| ≤ τ * Dn + κ * narrowMass τ p + 2 * τ + 4 * τ * w) :
    narrowMass τ p ≤ τ * L + 6 * τ + 2 * τ * Dn := by
  have hM0 := narrowMass_nonneg τ p
  rw [abs_le] at hb
  have h1 : τ * ℓp ≤ τ * L := mul_le_mul_of_nonneg_left hℓp hτ.le
  have h2 : κ * narrowMass τ p ≤ 1 / 2 * narrowMass τ p := mul_le_mul_of_nonneg_right hκ hM0
  have h3 : 4 * τ * w ≤ τ := by nlinarith
  linarith

/-- The polynomial `t ↦ D_x(½ + τ + i(t + s))` is continuous. -/
theorem continuous_selbergVonMangoldtPoly_narrow {x : ℝ} (hx : 1 < x) (τ s : ℝ) :
    Continuous fun t : ℝ => selbergVonMangoldtPoly x (narrowPoint τ (t + s)) := by
  refine (differentiable_selbergVonMangoldtPoly hx).continuous.comp ?_
  unfold narrowPoint
  fun_prop

/-- **Shifted mean square.** -/
theorem integral_normSq_selbergNarrow_shift_le {x τ : ℝ} (hx : 1 < x) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {A B : ℝ} (hAB : A ≤ B) (s : ℝ) :
    ∫ t in A..B, ‖selbergVonMangoldtPoly x (narrowPoint τ (t + s))‖ ^ 2 ≤
      (B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x))) * (5 / τ ^ 2) := by
  rw [intervalIntegral.integral_comp_add_right
    (fun u => ‖selbergVonMangoldtPoly x (narrowPoint τ u)‖ ^ 2) s]
  have h := integral_normSq_selbergVonMangoldtPoly_le hx hτ hτ1 (show A + s ≤ B + s by linarith)
  rw [show B + s - (A + s) = B - A by ring] at h
  exact h

/-- The bad heights: `t ∈ [A, B]` with `‖D‖ > Θ` at some grid point `t + 2jτ₂`, `|j| ≤ 6`, at
scale `τ₁` or `τ₂`. -/
def criticalBadSet (x τ₁ τ₂ Θ A B : ℝ) : Set ℝ :=
  Icc A B ∩ {t | ∃ j : ℤ, |j| ≤ 6 ∧
    (Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₁ (t + 2 * j * τ₂))‖ ∨
      Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₂ (t + 2 * j * τ₂))‖)}

/-- **The bad set is small.** -/
theorem volume_criticalBadSet_le {x τ₁ τ₂ Θ A B : ℝ} (hx : 1 < x) (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ ≤ τ₂)
    (hτ₂1 : τ₂ ≤ 1) (hΘ : 0 < Θ) (hAB : A ≤ B) :
    volume (criticalBadSet x τ₁ τ₂ Θ A B) ≤ ENNReal.ofReal (26 *
      ((B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x))) * (5 / τ₁ ^ 2) /
        Θ ^ 2)) := by
  set E := (B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x))) *
    (5 / τ₁ ^ 2) with hE
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ₁₂
  have hlen : 0 ≤ B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) := by
    have h1 : (1 : ℝ) ≤ selbergPolyLength x := by
      have : 1 ≤ selbergPolyLength x := by
        unfold selbergPolyLength
        exact Nat.one_le_iff_ne_zero.mpr (by
          rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
      exact_mod_cast this
    have : 0 ≤ Real.log (selbergPolyLength x) := Real.log_nonneg h1
    nlinarith
  have hpiece : ∀ τ : ℝ, 0 < τ → τ₁ ≤ τ → τ ≤ 1 → ∀ s : ℝ,
      volume (Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ (t + s))‖}) ≤
        ENNReal.ofReal (E / Θ ^ 2) := by
    intro τ hτ hτ₁τ hτ1 s
    refine (volume_Icc_inter_lt_norm_le (continuous_selbergVonMangoldtPoly_narrow hx τ s) hAB
      hΘ).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    refine (integral_normSq_selbergNarrow_shift_le hx hτ hτ1 hAB s).trans ?_
    rw [hE]
    gcongr
  have hsub : criticalBadSet x τ₁ τ₂ Θ A B ⊆ ⋃ j ∈ Finset.Icc (-6 : ℤ) 6,
      ((Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₁ (t + 2 * j * τ₂))‖}) ∪
        (Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₂ (t + 2 * j * τ₂))‖})) := by
    rintro t ⟨ht, j, hj, hj'⟩
    rw [Set.mem_iUnion₂]
    refine ⟨j, by rw [Finset.mem_Icc]; exact abs_le.mp hj, ?_⟩
    rcases hj' with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, h⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ j ∈ Finset.Icc (-6 : ℤ) 6, volume
        ((Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₁ (t + 2 * j * τ₂))‖}) ∪
          (Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₂ (t + 2 * j * τ₂))‖}))
      ≤ ∑ _j ∈ Finset.Icc (-6 : ℤ) 6, (ENNReal.ofReal (E / Θ ^ 2) + ENNReal.ofReal (E / Θ ^ 2)) :=
        Finset.sum_le_sum fun j _ => (measure_union_le _ _).trans
          (add_le_add (hpiece τ₁ hτ₁ le_rfl (hτ₁₂.trans hτ₂1) _) (hpiece τ₂ hτ₂ hτ₁₂ hτ₂1 _))
    _ = ENNReal.ofReal (26 * (E / Θ ^ 2)) := by
        rw [Finset.sum_const, show (Finset.Icc (-6 : ℤ) 6).card = 13 by rfl,
          ← ENNReal.ofReal_add (by positivity) (by positivity), nsmul_eq_mul,
          show ((13 : ℕ) : ENNReal) = ENNReal.ofReal 13 by simp,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

/-- **The bad integral.** -/
theorem lintegral_bad_le {x τ₁ a b A B : ℝ} (hx : 1 < x) (ha : 0 ≤ a) (hb : 0 ≤ b) (hAB : A ≤ B)
    (Bad : Set ℝ) (hBad : Bad ⊆ Icc A B) :
    ∫⁻ t, Bad.indicator (fun t => ENNReal.ofReal
        (a + b * ‖selbergVonMangoldtPoly x (narrowPoint τ₁ t)‖ ^ 2)) t ≤
      ENNReal.ofReal a * volume Bad +
        ENNReal.ofReal (b * ∫ t in A..B, ‖selbergVonMangoldtPoly x (narrowPoint τ₁ t)‖ ^ 2) := by
  set g : ℝ → ℝ := fun t => b * ‖selbergVonMangoldtPoly x (narrowPoint τ₁ t)‖ ^ 2 with hg
  have hgc : Continuous g := by
    have := continuous_selbergVonMangoldtPoly_narrow hx τ₁ 0
    simp only [add_zero] at this
    exact continuous_const.mul (this.norm.pow 2)
  have hpt : (fun t => Bad.indicator (fun t => ENNReal.ofReal (a + g t)) t) ≤
      fun t => Bad.indicator (fun _ => ENNReal.ofReal a) t +
        (Icc A B).indicator (fun t => ENNReal.ofReal (g t)) t := by
    intro t
    by_cases ht : t ∈ Bad
    · simp only [Set.indicator_of_mem ht, Set.indicator_of_mem (hBad ht)]
      rw [← ENNReal.ofReal_add ha (by positivity)]
    · simp only [Set.indicator_of_notMem ht, zero_add]
      exact zero_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_right _ ((hgc.measurable.ennreal_ofReal).indicator measurableSet_Icc)]
  refine add_le_add (lintegral_indicator_const_le _ _) (le_of_eq ?_)
  rw [lintegral_indicator measurableSet_Icc, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le hAB, ← integral_Icc_eq_integral_Ioc]
  exact (ofReal_integral_eq_lintegral_ofReal (hgc.integrableOn_Icc)
    (Filter.Eventually.of_forall fun t => by simp only [Pi.zero_apply, hg]; positivity)).symm

end RHTower
