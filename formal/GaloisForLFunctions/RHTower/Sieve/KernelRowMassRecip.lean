import GaloisForLFunctions.RHTower.Sieve.KernelDoubleIntegral

/-!
# The row mass of a kernel with reciprocal decay

`Sieve/KernelDoubleIntegral.setIntegral_norm_kernel_le` pays a *uniform* far bound, so a kernel of
size `N` at unit frequency contributes `N·|E|` and Halász–Montgomery gains nothing once `|E| ≥ 1`.
A far bound of the shape `A + B/|v|` is integrable against the window: the near-diagonal band still
costs `2N` whatever `E` is, the constant part costs `A·|E|`, and the reciprocal part costs only
`B·log T` — because `∫_{|v| ≤ 2T} dv/(1 + |v|)` is logarithmic, not linear.
-/

namespace RHTower.Sieve

open MeasureTheory intervalIntegral

noncomputable section

/-- The continuous majorant `2/(1 + |x|)` of `1/|x|` above unit frequency. -/
def recipMajorant (x : ℝ) : ℝ := 2 / (1 + |x|)

theorem recipMajorant_pos (x : ℝ) : 0 < recipMajorant x := by
  have h : (0 : ℝ) < 1 + |x| := by positivity
  rw [recipMajorant]
  positivity

theorem continuous_recipMajorant : Continuous recipMajorant := by
  refine continuous_const.div (continuous_const.add continuous_abs) fun x => ?_
  have : (0 : ℝ) < 1 + |x| := by positivity
  linarith

theorem recipMajorant_neg (x : ℝ) : recipMajorant (-x) = recipMajorant x := by
  rw [recipMajorant, recipMajorant, abs_neg]

theorem one_div_abs_le_recipMajorant {x : ℝ} (hx : 1 ≤ |x|) : 1 / |x| ≤ recipMajorant x := by
  have h1 : (0 : ℝ) < |x| := by linarith
  have h2 : (0 : ℝ) < 1 + |x| := by linarith
  have key : recipMajorant x - 1 / |x| = (|x| - 1) / (|x| * (1 + |x|)) := by
    rw [recipMajorant]
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (|x| - 1) / (|x| * (1 + |x|)) :=
    div_nonneg (by linarith) (by positivity)
  rw [← key] at hnn
  linarith

/-- **The symmetric integral of the reciprocal majorant is logarithmic.** -/
theorem integral_recipMajorant_symm {c : ℝ} (hc : 0 ≤ c) :
    (∫ x in (-c)..c, recipMajorant x) = 4 * Real.log (1 + c) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable recipMajorant volume a b := fun a b =>
    continuous_recipMajorant.intervalIntegrable a b
  have hsplit : (∫ x in (-c)..(0 : ℝ), recipMajorant x) + ∫ x in (0 : ℝ)..c, recipMajorant x
      = ∫ x in (-c)..c, recipMajorant x :=
    integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hrefl : (∫ x in (-c)..(0 : ℝ), recipMajorant x) = ∫ x in (0 : ℝ)..c, recipMajorant x := by
    have h := integral_comp_neg (a := (0 : ℝ)) (b := c) recipMajorant
    simp only [neg_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun x _ => recipMajorant_neg x
  have hhalf : (∫ x in (0 : ℝ)..c, recipMajorant x) = 2 * Real.log (1 + c) := by
    have hcongr : (∫ x in (0 : ℝ)..c, recipMajorant x)
        = ∫ x in (0 : ℝ)..c, 2 * (x + 1)⁻¹ := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hc, Set.mem_Icc] at hx
      rw [recipMajorant, abs_of_nonneg hx.1]
      field_simp
      ring
    rw [hcongr, intervalIntegral.integral_const_mul,
      integral_comp_add_right (fun y : ℝ => y⁻¹) 1, zero_add,
      integral_inv_of_pos one_pos (by linarith : (0 : ℝ) < c + 1)]
    rw [div_one]
    ring_nf
  rw [← hsplit, hrefl, hhalf]
  ring

/-- **The reciprocal majorant over a set inside the window is logarithmic.** -/
theorem setIntegral_recipMajorant_le {t T : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc (-T) T)
    {E : Set ℝ} (_hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    (∫ u in E, recipMajorant (t - u)) ≤ 4 * Real.log (2 + 2 * T) := by
  set c : ℝ := 2 * T + 1 with hc
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; linarith
  have hcont : Continuous fun u : ℝ => recipMajorant (t - u) :=
    continuous_recipMajorant.comp (continuous_const.sub continuous_id)
  have hEsub : E ⊆ Set.Ioc (t - c) (t + c) := by
    intro u hu
    have hu' : u ∈ Set.Icc (-T) T := hEs hu
    rw [Set.mem_Icc] at hu' ht
    rw [Set.mem_Ioc, hc]
    constructor
    · linarith [hu'.2, ht.1]
    · linarith [hu'.1, ht.2]
  have hmono : (∫ u in E, recipMajorant (t - u))
      ≤ ∫ u in Set.Ioc (t - c) (t + c), recipMajorant (t - u) := by
    refine MeasureTheory.setIntegral_mono_set
      ((hcont.integrableOn_Icc (a := t - c) (b := t + c)).mono_set (fun u hu => ⟨hu.1.le, hu.2⟩))
      (Filter.Eventually.of_forall fun u => (recipMajorant_pos _).le)
      (Filter.Eventually.of_forall hEsub)
  refine hmono.trans (le_of_eq ?_)
  have hle : t - c ≤ t + c := by linarith
  rw [← intervalIntegral.integral_of_le hle,
    integral_comp_sub_left recipMajorant t]
  have hids : t - (t + c) = -c := by ring
  have hidt : t - (t - c) = c := by ring
  rw [hids, hidt, integral_recipMajorant_symm hc0, hc]
  ring_nf

/-- **The row mass with a reciprocal far bound.** -/
theorem setIntegral_norm_kernel_le_recip {K : ℝ → ℂ} (hK : Continuous K) {E : Set ℝ}
    {T Nb A B : ℝ} (hEs : E ⊆ Set.Icc (-T) T) (hEm : MeasurableSet E) (hT : 1 ≤ T)
    (hNb : 0 ≤ Nb) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnear : ∀ v, ‖K v‖ ≤ Nb)
    (hfar : ∀ v : ℝ, 1 ≤ |v| → |v| ≤ 2 * T → ‖K v‖ ≤ A + B / |v|)
    {t : ℝ} (ht : t ∈ Set.Icc (-T) T) :
    (∫ u in E, ‖K (t - u)‖) ≤ 2 * Nb + A * volume.real E + 4 * B * Real.log (2 + 2 * T) := by
  classical
  set D : Set ℝ := Set.Ioo (t - 1) (t + 1) with hD
  have hDm : MeasurableSet D := measurableSet_Ioo
  have hcontF : Continuous fun u : ℝ => ‖K (t - u)‖ :=
    (hK.comp (continuous_const.sub continuous_id)).norm
  have hintF : IntegrableOn (fun u : ℝ => ‖K (t - u)‖) E volume :=
    (hcontF.integrableOn_Icc (a := -T) (b := T)).mono_set hEs
  have hsplit := MeasureTheory.integral_inter_add_sdiff (μ := volume) hDm hintF
  -- the near band
  have hnearInt : (∫ u in E ∩ D, ‖K (t - u)‖) ≤ 2 * Nb := by
    have hsub : E ∩ D ⊆ D := Set.inter_subset_right
    have hvol : volume.real D = 2 := by
      rw [hD, MeasureTheory.measureReal_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t + 1 - (t - 1))]
      ring
    have hvolle : volume.real (E ∩ D) ≤ 2 := by
      rw [← hvol]
      exact MeasureTheory.measureReal_mono hsub (by
        rw [hD, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hbd : ∀ u ∈ E ∩ D, ‖K (t - u)‖ ≤ Nb := fun u _ => hnear _
    have hmono := MeasureTheory.setIntegral_mono_on
      (hintF.mono_set Set.inter_subset_left)
      (integrableOn_const (by
        refine ne_of_lt (lt_of_le_of_lt (measure_mono hsub) ?_)
        rw [hD, Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top))
      (hEm.inter hDm) hbd
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hmono
    have : volume.real (E ∩ D) * Nb ≤ 2 * Nb := by nlinarith [hvolle, hNb]
    linarith
  -- the far part
  have hfarInt : (∫ u in E \ D, ‖K (t - u)‖)
      ≤ A * volume.real E + 4 * B * Real.log (2 + 2 * T) := by
    have hFDm : MeasurableSet (E \ D) := hEm.diff hDm
    have hFDs : E \ D ⊆ Set.Icc (-T) T := fun u hu => hEs hu.1
    have hbd : ∀ u ∈ E \ D, ‖K (t - u)‖ ≤ A + B * recipMajorant (t - u) := by
      intro u hu
      have hnotD : u ∉ D := hu.2
      have habs : 1 ≤ |t - u| := by
        rw [hD, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hnotD
        rcases hnotD with h | h
        · rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith)]; linarith
      have hbig : |t - u| ≤ 2 * T := by
        have hu' : u ∈ Set.Icc (-T) T := hEs hu.1
        rw [Set.mem_Icc] at hu' ht
        rw [abs_le]
        constructor
        · linarith [hu'.2, ht.1]
        · linarith [hu'.1, ht.2]
      have h1 := hfar (t - u) habs hbig
      have h2 : B / |t - u| ≤ B * recipMajorant (t - u) := by
        have := one_div_abs_le_recipMajorant habs
        have hdiv : B / |t - u| = B * (1 / |t - u|) := by ring
        rw [hdiv]
        exact mul_le_mul_of_nonneg_left this hB
      linarith
    have hcontMaj : Continuous fun u : ℝ => A + B * recipMajorant (t - u) :=
      continuous_const.add ((continuous_recipMajorant.comp
        (continuous_const.sub continuous_id)).const_mul B)
    have hmono := MeasureTheory.setIntegral_mono_on
      (hintF.mono_set Set.sdiff_subset)
      ((hcontMaj.integrableOn_Icc (a := -T) (b := T)).mono_set hFDs) hFDm hbd
    have hcontR : Continuous fun u : ℝ => recipMajorant (t - u) :=
      continuous_recipMajorant.comp (continuous_const.sub continuous_id)
    have hintR : IntegrableOn (fun u : ℝ => recipMajorant (t - u)) (E \ D) volume :=
      (hcontR.integrableOn_Icc (a := -T) (b := T)).mono_set hFDs
    have hexp : (∫ u in E \ D, (A + B * recipMajorant (t - u)))
        = A * volume.real (E \ D) + B * ∫ u in E \ D, recipMajorant (t - u) := by
      have hfin : volume (E \ D) ≠ ⊤ := by
        refine ne_of_lt (lt_of_le_of_lt (measure_mono hFDs) ?_)
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_lt_top
      have hcA : IntegrableOn (fun _ : ℝ => A) (E \ D) volume := integrableOn_const hfin
      rw [MeasureTheory.integral_add hcA (hintR.const_mul _),
        MeasureTheory.setIntegral_const, MeasureTheory.integral_const_mul, smul_eq_mul]
      ring
    rw [hexp] at hmono
    have hlogpart : (∫ u in E \ D, recipMajorant (t - u)) ≤ 4 * Real.log (2 + 2 * T) :=
      setIntegral_recipMajorant_le hT ht hFDm hFDs
    have hvolle : volume.real (E \ D) ≤ volume.real E :=
      MeasureTheory.measureReal_mono Set.sdiff_subset (by
        refine ne_of_lt (lt_of_le_of_lt (measure_mono hEs) ?_)
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_lt_top)
    nlinarith [hmono, hlogpart, hvolle, hA, hB]
  linarith [hsplit, hnearInt, hfarInt]

end

end RHTower.Sieve
