import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.ScalePacking

/-! # Joint physical clock forecasts at square-root dimension cost -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
noncomputable section

private theorem scale_window_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : (ι→ℝ)→ℝ) (hf : Measurable f) (hscale : ∀ a>0, ∀ x, a*f (a • x)=f x)
    {t w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.real (f ⁻¹' Ioc t (t+w)) ≤ 1024*sqrt (Fintype.card ι)*w/t := by
  intro μ
  rcases hw.eq_or_lt with he|hpos
  · subst w; simp
  let L := sqrt (Fintype.card ι)
  have hl : 0 < L := sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  let h := 256*L*w
  have hh : 0 < h := mul_pos (mul_pos (by norm_num) hl) hpos
  let u := t/h
  have hu : 0 < u := div_pos ht hh
  have hut : u*h=t := div_mul_cancel₀ _ hh.ne'
  by_cases hlarge : 2 ≤ u
  · let q := ⌊u⌋₊
    have hq : (q:ℝ) ≤ u := Nat.floor_le hu.le
    have hq' : u < (q:ℝ)+1 := Nat.lt_floor_add_one _
    have hq₀ : 0 < (q:ℝ) := by linarith only [hlarge,hq']
    have hroom : 256*(q:ℝ)*L*w ≤ t := by
      have h₁ := mul_le_mul_of_nonneg_right hq hh.le
      change (q:ℝ)*h ≤ u*h at h₁
      rw [hut] at h₁
      dsimp only [h] at h₁
      linarith only [h₁]
    have hcount := scale_grid_bound f hf hscale q ht hpos hroom
    have hmass : μ.real (f ⁻¹' Ioc t (t+w)) ≤ 2/(q:ℝ) :=
      (le_div_iff₀ hq₀).mpr (by simpa only [mul_comm] using hcount)
    refine hmass.trans ((div_le_div_iff₀ hq₀ ht).mpr ?_)
    have hh' := mul_le_mul_of_nonneg_right (show u ≤ 2*(q:ℝ) by linarith only [hlarge,hq']) hh.le
    rw [hut] at hh'
    dsimp only [h,L] at hh'
    linarith only [hh']
  · refine measureReal_le_one.trans ((one_le_div ht).mpr ?_)
    have hh' := mul_lt_mul_of_pos_right (lt_of_not_ge hlarge) hh
    rw [hut] at hh'
    dsimp only [h,L] at hh'
    linarith only [hh',ht]

/-- Every fixed linear combination of onset and subsequent first wait has
at most square-root-dimension times relative interval width in probability.
This includes their sum, the absolute first-return date, and offsets from
a multiple of the observed crossing. -/
theorem gaussian_first_passage_affine_window (n j s : ℕ) (a b : ℝ) {t w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j s
    μ.real {x | a*σ x+b*Δ x ∈ Ioc t (t+w)} ≤ 1024*sqrt (Fintype.card (ChainLabel (n+2)))*w/t := by
  intro μ σ Δ
  let i := ((pathCoeffEquiv n).symm (Sum.inl (0,0)))
  letI : Nonempty (PrefixIndex n) := ⟨i⟩
  let f (x : PrefixIndex n→ℝ) := a*σ x+b*Δ x
  have hf : Measurable f := ((measurable_crossingOrigin ..).const_mul a).add ((measurable_crossingWait ..).const_mul b)
  have hscale (z : ℝ) (hz : 0 < z) (x : PrefixIndex n→ℝ) : z*f (z • x)=f x := by
    change z*(a*σ (z • x)+b*Δ (z • x))=a*σ x+b*Δ x
    rw [mul_add,mul_left_comm z a,mul_left_comm z b,smul_crossingOrigin n j (9/80) hz,smul_crossingWait n j s hz]
  have he : f ⁻¹' Ioc t (t+w) = {x | a*σ x+b*Δ x ∈ Ioc t (t+w)} := by
    ext x
    rfl
  rw [←he]
  simpa only [Fintype.card_fin] using scale_window_bound f hf hscale ht hw

theorem first_wait_window (n j s : ℕ) {t w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    μ.real {x | crossingWait n j s x ∈ Ioc t (t+w)} ≤ 1024*sqrt (Fintype.card (ChainLabel (n+2)))*w/t := by
  simpa only [zero_mul,one_mul,zero_add] using gaussian_first_passage_affine_window n j s 0 1 ht hw

#print axioms gaussian_first_passage_affine_window

/-- A return forecast may inspect the whole coefficient direction. If it
uses no information about the radius, the same square-root dimension bound
holds for success in a relative window about its chosen date. -/
theorem gaussian_first_wait_angular_forecast (n j s : ℕ) (g : (PrefixIndex n → ℝ) → ℝ)
    (hg : Measurable g) (hang : ∀ a > (0:ℝ), ∀ x, g (a • x)=g x) {w : ℝ} (hw : 0 ≤ w) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let Δ := crossingWait n j s
    μ.real {x | g x < Δ x ∧ Δ x ≤ (1+w)*g x} ≤ 1024*sqrt (Fintype.card (ChainLabel (n+2)))*w := by
  intro μ Δ
  letI : Nonempty (PrefixIndex n) := ⟨(pathCoeffEquiv n).symm (Sum.inl (0,0))⟩
  let f (x : PrefixIndex n → ℝ) := Δ x/g x
  have hf : Measurable f := (measurable_crossingWait ..).div hg
  have hscale (a : ℝ) (ha : 0 < a) (x : PrefixIndex n → ℝ) : a*f (a • x)=f x := by
    dsimp only [f]
    rw [hang a ha,←mul_div_assoc,smul_crossingWait n j s ha]
  have hsub : {x | g x < Δ x ∧ Δ x ≤ (1+w)*g x} ⊆ f ⁻¹' Ioc 1 (1+w) := by
    rintro x ⟨hl,hu⟩
    have hp : 0 < g x := by
      by_contra! hh
      have hn := mul_nonpos_of_nonneg_of_nonpos hw hh
      linarith only [hl,hu,hn]
    exact ⟨(one_lt_div hp).mpr hl,(div_le_iff₀ hp).mpr hu⟩
  exact (measureReal_mono (μ:=μ) hsub).trans (by
    simpa only [div_one,Fintype.card_fin] using scale_window_bound f hf hscale zero_lt_one hw)

#print axioms gaussian_first_wait_angular_forecast
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
