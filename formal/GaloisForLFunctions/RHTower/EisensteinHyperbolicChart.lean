import GaloisForLFunctions.RHTower.SelbergMaassCurvatureTransport
import GaloisForLFunctions.RHTower.EisensteinLineSourceMeanSquare
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

/-!
# Hyperbolic integrals in coordinates: the cusp rectangle and the strip slab

For a measurable `A ⊆ {(x, y) | 0 < y}` and `S = {z ∈ ℍ | (Re z, Im z) ∈ A}`,
`∫_S F(Re z, Im z) dμ = ∫_A F(x, y) y⁻² dx dy`.  Two sets are used by the Maass–Selberg
unfolding: the cusp rectangle `[−½, ½] × (Y, ∞)`, which for `Y ≥ 1` is the part of the fundamental
domain above height `Y`, and the strip slab `[0, 1) × (0, Y]`, the part of the translation strip
below height `Y`.  Product Fubini turns both into iterated integrals.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCurvatureTransport

namespace RHTower

noncomputable section

/-- Complex-valued version of `integral_height_sq_chart`. -/
theorem integral_height_sq_chart_complex (F : ℂ → ℂ) :
    (∫ z : ℍ, ((z.im : ℝ) : ℂ) ^ 2 * F z) = ∫ z in {z : ℂ | 0 < z.im}, F z := by
  have hm : Measurable chartDensity := by unfold chartDensity; fun_prop
  have hi (G : ℂ → ℂ) : (∫ z : ℍ, G z) =
      ∫ z in {z : ℂ | 0 < z.im}, chartDensity z • G z := by
    rw [← UpperHalfPlane.measurableEmbedding_coe.integral_map, map_volume_chart,
      integral_withDensity_eq_integral_smul hm]
  change (∫ z : ℍ, (((z : ℂ).im : ℝ) : ℂ) ^ 2 * F z) = _
  rw [hi (fun z => ((z.im : ℝ) : ℂ) ^ 2 * F z)]
  apply setIntegral_congr_fun isOpen_upperHalfPlaneSet.measurableSet
  intro z hz
  change 0 < z.im at hz
  have hy : ((z.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  simp only [chartDensity, NNReal.smul_def, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    coe_nnnorm, Real.norm_eq_abs, abs_of_pos hz, Complex.real_smul, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_one]
  field_simp

/-- The coordinate map `z ↦ (Re z, Im z)`. -/
theorem measurable_coordMap : Measurable (fun z : ℍ => (z.re, z.im)) :=
  (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im).measurable

/-- **Hyperbolic integrals in coordinates.**  For measurable `A ⊆ {0 < y}`,
`∫_{(Re,Im) ∈ A} F(Re z, Im z) dμ = ∫_A F(p) / p₂² dp`. -/
theorem setIntegral_coord_eq {A : Set (ℝ × ℝ)} (hA : MeasurableSet A)
    (hpos : ∀ p ∈ A, 0 < p.2) (F : ℝ × ℝ → ℂ) :
    ∫ z in {z : ℍ | (z.re, z.im) ∈ A}, F (z.re, z.im) =
      ∫ p in A, F p / ((p.2 : ℝ) : ℂ) ^ 2 := by
  let G : ℂ → ℂ := fun w => A.indicator (fun p => F p / ((p.2 : ℝ) : ℂ) ^ 2) (w.re, w.im)
  have hS : MeasurableSet {z : ℍ | (z.re, z.im) ∈ A} := measurable_coordMap hA
  have he : (∫ z in {z : ℍ | (z.re, z.im) ∈ A}, F (z.re, z.im)) =
      ∫ z : ℍ, ((z.im : ℝ) : ℂ) ^ 2 * G z := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : (z.re, z.im) ∈ A
    · rw [Set.indicator_of_mem (show z ∈ {z : ℍ | (z.re, z.im) ∈ A} from hz)]
      simp only [G, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Set.indicator_of_mem hz]
      have hy : ((z.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
      field_simp
    · rw [Set.indicator_of_notMem (show z ∉ {z : ℍ | (z.re, z.im) ∈ A} from hz)]
      simp only [G, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Set.indicator_of_notMem hz,
        mul_zero]
  rw [he, integral_height_sq_chart_complex]
  calc
    (∫ z in {z : ℂ | 0 < z.im}, G z) = ∫ z : ℂ, G z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      change A.indicator (fun p => F p / ((p.2 : ℝ) : ℂ) ^ 2) (z.re, z.im) = 0
      exact Set.indicator_of_notMem (fun (hp : (z.re, z.im) ∈ A) => hz (hpos _ hp)) _
    _ = ∫ p : ℝ × ℝ, A.indicator (fun p => F p / ((p.2 : ℝ) : ℂ) ^ 2) p := by
      rw [← Complex.volume_preserving_equiv_real_prod.integral_comp
        Complex.measurableEquivRealProd.measurableEmbedding]
      simp only [G, Complex.measurableEquivRealProd_apply]
    _ = _ := integral_indicator hA

/-- Real-valued form of hyperbolic coordinate transport. -/
theorem setIntegral_coord_eq_real {A : Set (ℝ × ℝ)} (hA : MeasurableSet A)
    (hpos : ∀ p ∈ A, 0 < p.2) (F : ℝ × ℝ → ℝ) :
    ∫ z in {z : ℍ | (z.re, z.im) ∈ A}, F (z.re, z.im) =
      ∫ p in A, F p / p.2 ^ 2 := by
  apply Complex.ofReal_injective
  calc
    ((∫ z in {z : ℍ | (z.re, z.im) ∈ A}, F (z.re, z.im) : ℝ) : ℂ) =
        ∫ z in {z : ℍ | (z.re, z.im) ∈ A}, (F (z.re, z.im) : ℂ) := by
          exact (integral_ofReal (𝕜 := ℂ)
            (μ := volume.restrict {z : ℍ | (z.re, z.im) ∈ A})).symm
    _ = ∫ p in A, (F p : ℂ) / ((p.2 : ℝ) : ℂ) ^ 2 :=
      setIntegral_coord_eq hA hpos (fun p => (F p : ℂ))
    _ = ∫ p in A, ((F p / p.2 ^ 2 : ℝ) : ℂ) := by
      apply setIntegral_congr_fun hA
      intro p _
      change (F p : ℂ) / ((p.2 : ℝ) : ℂ) ^ 2 = ((F p / p.2 ^ 2 : ℝ) : ℂ)
      rw [← Complex.ofReal_pow, ← Complex.ofReal_div]
    _ = ((∫ p in A, F p / p.2 ^ 2 : ℝ) : ℂ) := by
      exact integral_ofReal (𝕜 := ℂ)

/-! ## The cusp rectangle -/

/-- The cusp rectangle `[−½, ½] × (Y, ∞)`. -/
def cuspRect (Y : ℝ) : Set (ℝ × ℝ) := unitIcc ×ˢ Ioi Y

theorem measurableSet_cuspRect (Y : ℝ) : MeasurableSet (cuspRect Y) :=
  measurableSet_Icc.prod measurableSet_Ioi

theorem cuspRect_pos {Y : ℝ} (hY : 0 ≤ Y) {p : ℝ × ℝ} (hp : p ∈ cuspRect Y) : 0 < p.2 :=
  lt_of_le_of_lt hY hp.2

/-- Above height `Y ≥ 1` the fundamental domain is the cusp rectangle. -/
theorem coord_mem_cuspRect_iff {Y : ℝ} (hY : 1 ≤ Y) (z : ℍ) :
    (z.re, z.im) ∈ cuspRect Y ↔ z ∈ fd ∧ Y < z.im := by
  constructor
  · rintro ⟨hx, hy⟩
    simp only [unitIcc, mem_Icc] at hx
    simp only [mem_Ioi] at hy
    refine ⟨⟨?_, ?_⟩, hy⟩
    · rw [Complex.normSq_apply]
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      nlinarith [hx.1, hx.2]
    · rw [abs_le]; exact hx
  · rintro ⟨hz, hy⟩
    refine ⟨?_, hy⟩
    have := hz.2
    rw [abs_le] at this
    exact this

theorem setOf_coord_cuspRect {Y : ℝ} (hY : 1 ≤ Y) :
    {z : ℍ | (z.re, z.im) ∈ cuspRect Y} = fd ∩ {z : ℍ | Y < z.im} := by
  ext z
  simp only [mem_setOf_eq, mem_inter_iff]
  exact coord_mem_cuspRect_iff hY z

theorem measurableSet_fd_inter_above (Y : ℝ) : MeasurableSet (fd ∩ {z : ℍ | Y < z.im}) :=
  isClosed_fd.measurableSet.inter (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)

/-- **The cusp part of the fundamental domain in coordinates.** -/
theorem setIntegral_fd_above_eq {Y : ℝ} (hY : 1 ≤ Y) (F : ℝ × ℝ → ℂ) :
    ∫ z in fd ∩ {z : ℍ | Y < z.im}, F (z.re, z.im) =
      ∫ p in cuspRect Y, F p / ((p.2 : ℝ) : ℂ) ^ 2 := by
  rw [← setOf_coord_cuspRect hY]
  exact setIntegral_coord_eq (measurableSet_cuspRect Y) (fun p hp => cuspRect_pos (by linarith) hp) F

/-! ## The strip slab -/

/-- The strip slab `[0, 1) × (0, Y]`. -/
def stripSlab (Y : ℝ) : Set (ℝ × ℝ) := Ico (0 : ℝ) 1 ×ˢ Ioc 0 Y

theorem measurableSet_stripSlab (Y : ℝ) : MeasurableSet (stripSlab Y) :=
  measurableSet_Ico.prod measurableSet_Ioc

theorem stripSlab_pos {Y : ℝ} {p : ℝ × ℝ} (hp : p ∈ stripSlab Y) : 0 < p.2 := hp.2.1

theorem setOf_coord_stripSlab (Y : ℝ) :
    {z : ℍ | (z.re, z.im) ∈ stripSlab Y} = modularStrip ∩ {z : ℍ | z.im ≤ Y} := by
  ext z
  simp only [mem_setOf_eq, mem_inter_iff, stripSlab, mem_prod, mem_Ico, mem_Ioc, modularStrip]
  constructor
  · rintro ⟨⟨h0, h1⟩, ⟨_, hY⟩⟩
    exact ⟨⟨h0, h1⟩, hY⟩
  · rintro ⟨⟨h0, h1⟩, hY⟩
    exact ⟨⟨h0, h1⟩, ⟨z.im_pos, hY⟩⟩

theorem measurableSet_strip_inter_below (Y : ℝ) :
    MeasurableSet (modularStrip ∩ {z : ℍ | z.im ≤ Y}) :=
  measurableSet_modularStrip.inter
    (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const)

/-- **The strip below height `Y` in coordinates.** -/
theorem setIntegral_strip_below_eq (Y : ℝ) (F : ℝ × ℝ → ℂ) :
    ∫ z in modularStrip ∩ {z : ℍ | z.im ≤ Y}, F (z.re, z.im) =
      ∫ p in stripSlab Y, F p / ((p.2 : ℝ) : ℂ) ^ 2 := by
  rw [← setOf_coord_stripSlab Y]
  exact setIntegral_coord_eq (measurableSet_stripSlab Y) (fun _ hp => stripSlab_pos hp) F

/-! ## Product Fubini -/

/-- Fubini on a product set, `y` outside. -/
theorem setIntegral_prod_eq_iterated {I S : Set ℝ} {f : ℝ × ℝ → ℂ}
    (hf : IntegrableOn f (I ×ˢ S)) :
    ∫ p in I ×ˢ S, f p = ∫ y in S, ∫ x in I, f (x, y) := by
  have hprod : Integrable f ((volume.restrict I).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hf
  have h := integral_prod_symm f hprod
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

theorem integrableOn_slice_of_prod {I S : Set ℝ} {f : ℝ × ℝ → ℂ}
    (hf : IntegrableOn f (I ×ˢ S)) :
    IntegrableOn (fun y => ∫ x in I, f (x, y)) S := by
  have hprod : Integrable f ((volume.restrict I).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hf
  exact hprod.integral_prod_right

end

end RHTower
