import GaloisForLFunctions.RHTower.ThetaCoordinateCanonicalFlux

/-! Global positivity of the literal confluent coordinate residual.
The canonical transport integral is identified with the actual mixed-row derivative. -/

noncomputable section
open Set Filter Topology MeasureTheory
namespace RHTower.ThetaCoordinate
open ThetaConfluent

local notation "k" => thetaCuspFullSource
local notation "k₁" => deriv thetaCuspFullSource
local notation "k₂" => deriv (deriv thetaCuspFullSource)
private abbrev s := thetaCuspSchwartzReal
private abbrev d := SchwartzMap.derivCLM ℝ ℝ s
private abbrev dd := SchwartzMap.derivCLM ℝ ℝ d

private theorem source_coe : (s : ℝ → ℝ) = k := funext thetaCuspSchwartzReal_apply

private theorem source_hasDerivAt (t : ℝ) : HasDerivAt k (k₁ t) t := s.hasDerivAt t

private def weighted (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

private theorem weighted_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) : weighted f t = t*f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

private def corr (f g : SchwartzMap ℝ ℝ) (y : ℝ) : ℝ := ∫ t in Ioi 0, f t*g (y+t)

private theorem corr_hasDerivAt (f g : SchwartzMap ℝ ℝ) (y : ℝ) :
    HasDerivAt (corr f g) (corr f (SchwartzMap.derivCLM ℝ ℝ g) y) y :=
  schwartzCorrelation_hasDerivAt f g y

private def rawRow (y : ℝ) : ℝ := ∫ t in Ioi 0, canonicalRawMoment t y
private def firstIntegrand (t y : ℝ) : ℝ :=
  k₁ t*k (t+y)+(t+y)*k₁ t*k₁ (t+y)-t*k t*k₂ (t+y)
private def rawRowFirst (y : ℝ) : ℝ := ∫ t in Ioi 0, firstIntegrand t y

private theorem rawRow_eq (y : ℝ) :
    rawRow y = corr (weighted d) s y+y*corr d s y-corr (weighted s) d y := by
  have h1 := (schwartzCorrelation_integrable (weighted d) s y).integrableOn (s := Ioi 0)
  have h2 := ((schwartzCorrelation_integrable d s y).const_mul y).integrableOn (s := Ioi 0)
  have h3 := (schwartzCorrelation_integrable (weighted s) d y).integrableOn (s := Ioi 0)
  have h12 : IntegrableOn (fun t => weighted d t*s (y+t)+y*(d t*s (y+t))) (Ioi 0) := h1.add h2
  unfold rawRow corr
  rw [← integral_const_mul, ← integral_add h1 h2, ← integral_sub h12 h3]
  apply integral_congr_ae
  filter_upwards with t
  simp only [weighted_apply]
  change (t+y)*k₁ t*k (t+y)-t*k t*k₁ (t+y) =
    t*k₁ t*k (y+t)+y*(k₁ t*k (y+t))-t*k t*k₁ (y+t)
  rw [add_comm y t]
  ring

private theorem firstIntegrand_expansion (t y : ℝ) :
    firstIntegrand t y = d t*s (y+t)+weighted d t*d (y+t)+
      y*(d t*d (y+t))-weighted s t*dd (y+t) := by
  simp only [weighted_apply]
  change k₁ t*k (t+y)+(t+y)*k₁ t*k₁ (t+y)-t*k t*k₂ (t+y) =
    k₁ t*k (y+t)+t*k₁ t*k₁ (y+t)+y*(k₁ t*k₁ (y+t))-t*k t*k₂ (y+t)
  rw [add_comm y t]
  ring

private theorem firstIntegrand_integrable (y : ℝ) : Integrable (fun t => firstIntegrand t y) := by
  simp_rw [firstIntegrand_expansion]
  exact (((schwartzCorrelation_integrable d s y).add
    (schwartzCorrelation_integrable (weighted d) d y)).add
      ((schwartzCorrelation_integrable d d y).const_mul y)).sub
        (schwartzCorrelation_integrable (weighted s) dd y)

private theorem rawRowFirst_eq (y : ℝ) :
    rawRowFirst y = corr d s y+corr (weighted d) d y+
      y*corr d d y-corr (weighted s) dd y := by
  have h1 := (schwartzCorrelation_integrable d s y).integrableOn (s := Ioi 0)
  have h2 := (schwartzCorrelation_integrable (weighted d) d y).integrableOn (s := Ioi 0)
  have h3 := ((schwartzCorrelation_integrable d d y).const_mul y).integrableOn (s := Ioi 0)
  have h4 := (schwartzCorrelation_integrable (weighted s) dd y).integrableOn (s := Ioi 0)
  have h12 : IntegrableOn (fun t => d t*s (y+t)+weighted d t*d (y+t)) (Ioi 0) := h1.add h2
  have h123 : IntegrableOn (fun t => d t*s (y+t)+weighted d t*d (y+t)+y*(d t*d (y+t)))
      (Ioi 0) := h12.add h3
  unfold rawRowFirst corr
  simp_rw [firstIntegrand_expansion]
  rw [integral_sub h123 h4, integral_add h12 h3,
    integral_add h1 h2, integral_const_mul]

private theorem rawRow_hasDerivAt (y : ℝ) : HasDerivAt rawRow (rawRowFirst y) y := by
  rw [show rawRow = fun y => corr (weighted d) s y+y*corr d s y-corr (weighted s) d y
    from funext rawRow_eq, rawRowFirst_eq]
  convert! ((corr_hasDerivAt (weighted d) s y).add
    ((hasDerivAt_id y).mul (corr_hasDerivAt d s y))).sub
      (corr_hasDerivAt (weighted s) d y) using 1
  simp only [one_mul, id_eq]
  ring

/-- The canonical raw moment is exactly the literal center mixed row. -/
theorem centerMixedRow_eq_rawMoment (y : ℝ) :
    centerMixedRow y = ∫ t in Ioi 0, canonicalRawMoment t y := by
  have h0 : Integrable (fun t => k t*k (y+t)) := schwartzCorrelation_integrable s s y
  have h1 : Integrable (fun t => t*k₁ t*k (y+t)) := by
    have h := schwartzCorrelation_integrable (weighted d) s y
    simp only [weighted_apply, d, SchwartzMap.derivCLM_apply, source_coe] at h
    exact h
  have h2 : Integrable (fun t => t*k t*k₁ (y+t)) := by
    have h := schwartzCorrelation_integrable (weighted s) d y
    simp only [weighted_apply, d, SchwartzMap.derivCLM_apply, source_coe] at h
    exact h
  have hD : Integrable (fun t => k t*k (y+t)+t*k₁ t*k (y+t)+t*k t*k₁ (y+t)) :=
    (h0.add h1).add h2
  have hiD := hD.integrableOn (s := Ioi 0)
  have hiL := (canonicalRawMoment_integrable y).integrableOn (s := Ioi 0)
  have hd (t : ℝ) : HasDerivAt (fun t => t*k t*k (y+t))
      (k t*k (y+t)+t*k₁ t*k (y+t)+t*k t*k₁ (y+t)) t := by
    have hz := (source_hasDerivAt (y+t)).comp t ((hasDerivAt_id t).const_add y)
    convert! ((hasDerivAt_id t).mul (source_hasDerivAt t)).mul hz using 1
    dsimp
    ring
  have hl : Tendsto (fun t : ℝ => t*k t*k (y+t)) atTop (𝓝 0) := by
    have h := schwartzShiftedProduct_limit (weighted s) s y
    simp only [weighted_apply, source_coe] at h
    exact h
  have hb : (∫ t in Ioi 0, k t*k (y+t)+t*k₁ t*k (y+t)+t*k t*k₁ (y+t)) = 0 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
      (fun t _ => hd t) hiD hl
    simpa only [zero_mul, sub_zero] using h
  have he : centerMixedRow y = (∫ t in Ioi 0, canonicalRawMoment t y)+
      (∫ t in Ioi 0, k t*k (y+t)+t*k₁ t*k (y+t)+t*k t*k₁ (y+t)) := by
    rw [← integral_add hiL hiD]
    unfold centerMixedRow
    apply integral_congr_ae
    filter_upwards with t
    unfold canonicalRawMoment
    rw [add_comm t y]
    ring
  rw [he, hb, add_zero]

private theorem rawDerivative_integral_eq (y : ℝ) :
    (∫ t in Ioi 0, canonicalRawDerivative t y) =
      (rawRowFirst y-(1/y+k₁ y/k y)*rawRow y)/(y*k 0*k y) := by
  change (∫ t in Ioi 0,
    (firstIntegrand t y-(1/y+k₁ y/k y)*canonicalRawMoment t y)/(y*k 0*k y)) = _
  rw [integral_div, integral_sub (firstIntegrand_integrable y).integrableOn
    ((canonicalRawMoment_integrable y).const_mul (1/y+k₁ y/k y)).integrableOn,
    integral_const_mul]
  rfl

/-- The actual mixed row, normalized by its center-scale source factor. -/
def normalizedMixedRow (y : ℝ) : ℝ := centerMixedRow y/(y*k 0*k y)

/-- The strict negative transport integral is the literal normalized-row derivative. -/
theorem normalizedMixedRow_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt normalizedMixedRow (∫ t in Ioi 0, canonicalRawDerivative t y) y := by
  have hrow : HasDerivAt centerMixedRow (rawRowFirst y) y := by
    rw [show centerMixedRow = rawRow from funext centerMixedRow_eq_rawMoment]
    exact rawRow_hasDerivAt y
  have hden : HasDerivAt (fun u => u*k 0*k u) (k 0*k y+y*k 0*k₁ y) y := by
    convert! ((hasDerivAt_id y).mul_const (k 0)).mul (source_hasDerivAt y) using 1
    dsimp
    ring
  convert! hrow.div hden
    (mul_pos (mul_pos hy (thetaCuspFullSource_pos_all 0)) (thetaCuspFullSource_pos_all y)).ne'
    using 1
  rw [rawDerivative_integral_eq]
  change (rawRowFirst y-(1/y+k₁ y/k y)*(∫ t in Ioi 0, canonicalRawMoment t y))/(y*k 0*k y) = _
  rw [← centerMixedRow_eq_rawMoment]
  field_simp [hy.ne', (thetaCuspFullSource_pos_all 0).ne', (thetaCuspFullSource_pos_all y).ne']

theorem normalizedMixedRow_strictAnti : StrictAntiOn normalizedMixedRow (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro y hy; exact (normalizedMixedRow_hasDerivAt hy).continuousAt.continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := by simpa only [interior_Ioi, mem_Ioi] using hy
    rw [(normalizedMixedRow_hasDerivAt hy0).deriv]
    exact integral_canonicalRawDerivative_neg hy0

private theorem normalizedMixedRow_eq_residual {y : ℝ} (hy : 0 < y) :
    normalizedMixedRow y = centerEntry/k 0^2*(1-confluentCoordinateResidual y/(y*k y)) := by
  unfold normalizedMixedRow confluentCoordinateResidual
  field_simp [hy.ne', (thetaCuspFullSource_pos_all 0).ne', (thetaCuspFullSource_pos_all y).ne',
    centerEntry_pos.ne']
  ring

/-- Exact center value of the decreasing normalized mixed row. -/
theorem normalizedMixedRow_limit :
    Tendsto normalizedMixedRow (𝓝[>] 0) (𝓝 (centerEntry/k 0^2)) := by
  have hid : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hk : Tendsto k (𝓝[>] 0) (𝓝 (k 0)) :=
    s.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun y => confluentCoordinateResidual y/(y*k y)) (𝓝[>] 0) (𝓝 0) := by
    have h := (confluentCoordinateResidual_cubic_limit.mul (hid.pow 2)).div hk
      (thetaCuspFullSource_pos_all 0).ne'
    have h' : Tendsto (fun y => (confluentCoordinateResidual y/y^3*y^2)/k y)
        (𝓝[>] 0) (𝓝 0) := by
      convert! h using 1
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
    apply h'.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hypos : 0 < y := hy
    field_simp [hypos.ne', (thetaCuspFullSource_pos_all y).ne']
  have h := (hb.const_sub 1).const_mul (centerEntry/k 0^2)
  have h' : Tendsto (fun y => centerEntry/k 0^2*(1-confluentCoordinateResidual y/(y*k y)))
      (𝓝[>] 0) (𝓝 (centerEntry/k 0^2)) := by simpa only [sub_zero, mul_one] using h
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (normalizedMixedRow_eq_residual hy).symm

theorem normalizedMixedRow_lt_center {y : ℝ} (hy : 0 < y) :
    normalizedMixedRow y < centerEntry/k 0^2 := by
  have hh : 0 < y/2 := by linarith
  have hxy : y/2 < y := by linarith
  have hle : normalizedMixedRow (y/2) ≤ centerEntry/k 0^2 := by
    apply ge_of_tendsto normalizedMixedRow_limit
    have hid : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    filter_upwards [(tendsto_order.1 hid).2 (y/2) hh, self_mem_nhdsWithin] with z hz hz0
    exact (normalizedMixedRow_strictAnti hz0 hh hz).le
  exact (normalizedMixedRow_strictAnti hh hy hxy).trans_le hle

/-- Every positive spacing has a strictly positive literal confluent coordinate residual. -/
theorem confluentCoordinateResidual_pos {y : ℝ} (hy : 0 < y) :
    0 < confluentCoordinateResidual y := by
  have hn := (lt_div_iff₀ (sq_pos_of_pos (thetaCuspFullSource_pos_all 0))).mp
    (normalizedMixedRow_lt_center hy)
  have hp : 0 < 1-k 0^2*normalizedMixedRow y/centerEntry := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ centerEntry_pos).mpr
    nlinarith only [hn]
  have he : confluentCoordinateResidual y =
      y*k y*(1-k 0^2*normalizedMixedRow y/centerEntry) := by
    unfold confluentCoordinateResidual normalizedMixedRow
    field_simp [hy.ne', (thetaCuspFullSource_pos_all 0).ne', (thetaCuspFullSource_pos_all y).ne',
      centerEntry_pos.ne']
  rw [he]
  exact mul_pos (mul_pos hy (thetaCuspFullSource_pos_all y)) hp

/-- At every fixed positive spacing, both actual ports are positive for small old-node separation. -/
theorem eventually_actual_ports_pos_at {y : ℝ} (hy : 0 < y) :
    ∀ᶠ z : ℝ in 𝓝[>] 0, z < y ∧ 0 < sourceResidual z y ∧ 0 < coordinateResidual z y := by
  have hb := (tendsto_order.1 (coordinateResidual_limit y)).1 0 (confluentCoordinateResidual_pos hy)
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  filter_upwards [(tendsto_order.1 hid).2 y hy, eventually_sourceResidual_pos hy, hb] with z hz ha hb
  exact ⟨hz,ha,hb⟩

end RHTower.ThetaCoordinate
