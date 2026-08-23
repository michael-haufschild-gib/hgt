import GaloisForLFunctions.RHTower.MellinHeadHardyEquiv
import GaloisForLFunctions.RHTower.SoninExtendedMellinExtension
import GaloisForLFunctions.RHTower.SoninExtendedMellinPole
import GaloisForLFunctions.RHTower.L2FourierReflection

/-!
# The vector attached to a constant head and a square-integrable tail

Burnol's description of `L̂_a` is in terms of the pair `(c, g)` — the constant value on the aperture
head `(0,a)` and the `L²` datum on the tail `(a,∞)`.  This module builds the corresponding *even*
vector of `L²(ℝ)` and records what its right Mellin transform is on the strip `1/2 < Re s < 1`.

## Main results

* `headTailFun`, `headTailVector`
* `headTailVector_mem_evenSubspace`, `headTailVector_ae_band`
* `soninMellinIntegral_headTailVector`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The even function on the line which is `c` on `[-a,a]` and `g(|t|)` outside. -/
def headTailFun (a : ℝ) (c : ℂ) (g : ℝ → ℂ) : ℝ → ℂ := fun x =>
  (centralInterval a).indicator (fun _ => c) x
    + ((Ioi a).indicator g x + (Ioi a).indicator g (-x))

theorem headTailFun_neg (a : ℝ) (c : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    headTailFun a c g (-x) = headTailFun a c g x := by
  have hsymm : (centralInterval a).indicator (fun _ => c) (-x)
      = (centralInterval a).indicator (fun _ => c) x := by
    by_cases hx : x ∈ centralInterval a
    · have hx' : -x ∈ centralInterval a := by
        rcases hx with ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : -x ∉ centralInterval a := by
        intro hcon
        rcases hcon with ⟨h1, h2⟩
        exact hx ⟨by linarith, by linarith⟩
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  rw [headTailFun, headTailFun, hsymm, neg_neg]
  ring

theorem memLp_headTailFun {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) :
    MemLp (headTailFun a c g) 2 (volume : Measure ℝ) := by
  have h1 : MemLp ((centralInterval a).indicator (fun _ => c)) 2 (volume : Measure ℝ) := by
    refine memLp_indicator_const 2 (measurableSet_centralInterval a) c (Or.inr ?_)
    rw [centralInterval]
    exact measure_Icc_lt_top.ne
  have h2 : MemLp ((Ioi a).indicator g) 2 (volume : Measure ℝ) :=
    (memLp_indicator_iff_restrict measurableSet_Ioi).2 hg
  have h3 : MemLp (fun x : ℝ => (Ioi a).indicator g (-x)) 2 (volume : Measure ℝ) :=
    MemLp.comp_measurePreserving h2 (Measure.measurePreserving_neg (volume : Measure ℝ))
  exact h1.add (h2.add h3)

/-- The vector of `L²(ℝ)` attached to a constant head and a square-integrable tail. -/
def headTailVector {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) : SoninL2 :=
  (memLp_headTailFun ha c hg).toLp (headTailFun a c g)

theorem headTailVector_coeFn {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) :
    ((headTailVector ha c hg : SoninL2) : ℝ → ℂ) =ᵐ[volume] headTailFun a c g :=
  (memLp_headTailFun ha c hg).coeFn_toLp

theorem headTailVector_mem_evenSubspace {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) :
    headTailVector ha c hg ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  refine Lp.ext ?_
  have hneg := (headTailVector_coeFn ha c hg).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hrefl : ((l2Reflection (headTailVector ha c hg) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] fun x => ((headTailVector ha c hg : SoninL2) : ℝ → ℂ) (-x) :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving (headTailVector ha c hg)
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  filter_upwards [hrefl, hneg, headTailVector_coeFn ha c hg] with x hx hx' hx''
  have hx2 : ((headTailVector ha c hg : SoninL2) : ℝ → ℂ) (-x) = headTailFun a c g (-x) := hx'
  rw [hx, hx2, hx'', headTailFun_neg]

theorem headTailVector_ae_band {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a →
      ((headTailVector ha c hg : SoninL2) : ℝ → ℂ) t = c := by
  filter_upwards [headTailVector_coeFn ha c hg] with t ht hmem
  rw [ht, headTailFun, Set.indicator_of_mem hmem]
  have h1 : t ∉ Ioi a := by
    rcases hmem with ⟨_, h2⟩
    simp only [Set.mem_Ioi, not_lt]
    exact h2
  have h2 : -t ∉ Ioi a := by
    rcases hmem with ⟨h1, _⟩
    simp only [Set.mem_Ioi, not_lt]
    linarith
  rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  ring

theorem headTailVector_ae_tail {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) :
    ∀ᵐ t ∂(volume.restrict (Ioi a)),
      ((headTailVector ha c hg : SoninL2) : ℝ → ℂ) t = g t := by
  filter_upwards [ae_restrict_of_ae (headTailVector_coeFn ha c hg),
    self_mem_ae_restrict (measurableSet_Ioi (a := a))] with t ht hmem
  have hta : a < t := hmem
  rw [ht, headTailFun]
  have h1 : t ∉ centralInterval a := by
    intro hcon
    rcases hcon with ⟨_, h2⟩
    linarith
  have h2 : -t ∉ Ioi a := by
    simp only [Set.mem_Ioi, not_lt]
    linarith
  rw [Set.indicator_of_notMem h1, Set.indicator_of_mem hmem, Set.indicator_of_notMem h2]
  ring

theorem headTailVector_ae_head {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) a)),
      ((headTailVector ha c hg : SoninL2) : ℝ → ℂ) t = c := by
  filter_upwards [ae_restrict_of_ae (headTailVector_ae_band ha c hg),
    self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := a))] with t ht hmem
  refine ht ?_
  rcases hmem with ⟨h1, h2⟩
  exact ⟨by linarith, h2⟩

/-! ## The Mellin transform of the vector -/

/-- **The right Mellin transform of the head/tail vector is `headTailMellin`.** -/
theorem soninMellinIntegral_headTailVector {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) {z : ℂ} (hz1 : 1 / 2 < z.re) (hz2 : z.re < 1) :
    soninMellinIntegral (headTailVector ha c hg) z = headTailMellin a c g z := by
  set v : SoninL2 := headTailVector ha c hg with hv
  have hdisj : Disjoint (Ioc (0 : ℝ) a) (Ioi a) := Ioc_disjoint_Ioi le_rfl
  have hint1 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-z) * (v : ℝ → ℂ) t)
      (Ioc (0 : ℝ) a) volume := by
    refine (integrableOn_head_cpow ha hz2 c).congr_fun_ae ?_
    filter_upwards [headTailVector_ae_head ha c hg] with t ht
    rw [ht]
  have hint2 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-z) * (v : ℝ → ℂ) t)
      (Ioi a) volume := integrableOn_cpow_mul_Ioi ha v hz1
  have hsplit : soninMellinIntegral v z
      = (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-z) * (v : ℝ → ℂ) t)
        + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-z) * (v : ℝ → ℂ) t := by
    rw [soninMellinIntegral, ← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union hdisj measurableSet_Ioi hint1 hint2
  have hhead : (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-z) * (v : ℝ → ℂ) t)
      = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - z) / (1 - z) := by
    rw [← integral_head_cpow_Ioc ha hz2 c]
    refine integral_congr_ae ?_
    filter_upwards [headTailVector_ae_head ha c hg] with t ht
    rw [ht]
  have htail : (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-z) * (v : ℝ → ℂ) t)
      = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-z) * g t := by
    refine integral_congr_ae ?_
    filter_upwards [headTailVector_ae_tail ha c hg] with t ht
    rw [ht]
  rw [hsplit, hhead, htail, headTailMellin]

end

end RHTower
