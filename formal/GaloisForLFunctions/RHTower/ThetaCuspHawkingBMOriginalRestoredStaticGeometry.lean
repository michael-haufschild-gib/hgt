import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalRestoredTemporalContacts

/-! Exact physical static-window mass and two-corner decomposition. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalRestoredStaticGeometry
open D4BMOriginalRestoredTemporalContacts
noncomputable section
set_option autoImplicit false

def staticWindow (A B T p : ℝ) : ℝ := max (min B (2*(T-p))-A) 0/2

private theorem window_positive_parts (A B T p : ℝ) (hAB : A ≤ B) :
    staticWindow A B T p=max (T-A/2-p) 0-max (T-B/2-p) 0 := by
  unfold staticWindow
  by_cases h1 : p ≤ T-B/2
  · rw [min_eq_left (by linarith),max_eq_left (by linarith),
      max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · by_cases h2 : p ≤ T-A/2
    · rw [min_eq_right (by linarith),max_eq_left (by linarith),
        max_eq_left (by linarith),max_eq_right (by linarith)]
      ring
    · rw [min_eq_right (by linarith),max_eq_right (by linarith),
        max_eq_right (by linarith),max_eq_right (by linarith)]
      ring

private theorem clamp_positive_part (a x p : ℝ) (hap : a ≤ p) :
    max (max a x-p) 0=max (x-p) 0 := by
  by_cases h : a ≤ x
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h),max_eq_right (sub_nonpos.mpr hap),
      max_eq_right (by linarith)]

private theorem positive_parts_difference (r s p : ℝ) :
    max (s-p) 0-max (r-p) 0=(s-r)-max (p-r) 0+max (p-s) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- The unchanged static clock gives the exact two-endpoint weight, including
empty and crossing-cutoff cases. -/
theorem static_window_decomposition (a A B T p : ℝ) (hAB : A ≤ B) (hap : a ≤ p) :
    staticWindow A B T p=
      (max a (T-A/2)-max a (T-B/2))-max (p-max a (T-B/2)) 0+max (p-max a (T-A/2)) 0 := by
  rw [window_positive_parts A B T p hAB,
    ← clamp_positive_part a (T-A/2) p hap,← clamp_positive_part a (T-B/2) p hap]
  exact positive_parts_difference _ _ _

private theorem shifted_positive_integral (U : ℝ→ℂ) (a r : ℝ) (har : a ≤ r) :
    (∫ p in Ioi a,((max (p-r) 0:ℝ):ℂ)*U p)=∫ p in Ioi r,((p-r:ℝ):ℂ)*U p := by
  have he : (fun p : ℝ => ((max (p-r) 0:ℝ):ℂ)*U p)=
      (Ioi r).indicator (fun p => ((p-r:ℝ):ℂ)*U p) := by
    funext p
    by_cases hp : r<p
    · simp [hp,max_eq_left (sub_nonneg.mpr hp.le)]
    · simp [hp,max_eq_right (sub_nonpos.mpr (le_of_not_gt hp))]
  rw [he,setIntegral_indicator measurableSet_Ioi]
  have hi : Ioi a ∩ Ioi r=Ioi r := by
    ext p
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨har.trans_lt h,h⟩
  rw [hi]

/-- The complete physical window integral equals its finite-onset mass and
both admitted mass-tail corners. No relation between horizon and time cutoffs
is used. -/
theorem static_window_two_corners (U : ℝ→ℂ) (hU : IntegrableOn U (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*U p) (Ioi (0:ℝ)))
    (a A B T : ℝ) (ha : 0 ≤ a) (hAB : A ≤ B) :
    IntegrableOn (fun p => (staticWindow A B T p:ℂ)*U p) (Ioi a) ∧
      (∫ p in Ioi a,(staticWindow A B T p:ℂ)*U p)=
        ((max a (T-A/2)-max a (T-B/2):ℝ):ℂ)*tailMass U a+
          tailCorner U (max a (T-A/2))-tailCorner U (max a (T-B/2)) := by
  let R := max a (T-B/2)
  let S := max a (T-A/2)
  have haR : a ≤ R := le_max_left _ _
  have haS : a ≤ S := le_max_left _ _
  have hUa := hU.mono_set (Ioi_subset_Ioi ha)
  have hRi := (moment_corner_integrable U hU hM R (ha.trans haR)).mono_set (Ioi_subset_Ioi ha)
  have hSi := (moment_corner_integrable U hU hM S (ha.trans haS)).mono_set (Ioi_subset_Ioi ha)
  have hRe : (∫ p in Ioi a,((max (p-R) 0:ℝ):ℂ)*U p)=tailCorner U R :=
    (shifted_positive_integral U a R haR).trans (tail_corner_moment U hU hM R (ha.trans haR)).2.symm
  have hSe : (∫ p in Ioi a,((max (p-S) 0:ℝ):ℂ)*U p)=tailCorner U S :=
    (shifted_positive_integral U a S haS).trans (tail_corner_moment U hU hM S (ha.trans haS)).2.symm
  have he (p : ℝ) (hp : a<p) : (staticWindow A B T p:ℂ)*U p=
      ((S-R:ℝ):ℂ)*U p-((max (p-R) 0:ℝ):ℂ)*U p+((max (p-S) 0:ℝ):ℂ)*U p := by
    rw [static_window_decomposition a A B T p hAB hp.le]
    dsimp [R,S]
    push_cast
    ring
  have hi := (((hUa.const_mul ((S-R:ℝ):ℂ)).sub hRi).add hSi)
  constructor
  · apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact (he p hp).symm
  · calc
      _ = ∫ p in Ioi a,((S-R:ℝ):ℂ)*U p-((max (p-R) 0:ℝ):ℂ)*U p+((max (p-S) 0:ℝ):ℂ)*U p := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
        exact he p hp
      _ = _ := by
        have hAdd := integral_add ((hUa.const_mul ((S-R:ℝ):ℂ)).sub hRi) hSi
        have hSub := integral_sub (hUa.const_mul ((S-R:ℝ):ℂ)) hRi
        dsimp only [Pi.sub_apply,Pi.add_apply] at hAdd hSub
        rw [hAdd,hSub,integral_const_mul,hRe,hSe]
        dsimp [tailMass,R,S]
        ring

/-- The original static radial/time triangle, retaining its finite onset. -/
def staticTriangle (F : ℝ×ℝ→ℂ) (a A B T : ℝ) : ℂ :=
  (∫ L in A..B,∫ p in a..max a (T-L/2),F (L,p))/2

private theorem clipped_time_integral (F : ℝ→ℂ) (a c : ℝ) :
    (∫ p in Ioi a,(Iic c).indicator F p)=∫ p in a..max a c,F p := by
  rw [setIntegral_indicator measurableSet_Iic]
  change (∫ p in Ioc a c,F p)=_
  by_cases h : a ≤ c
  · rw [max_eq_right h,intervalIntegral.integral_of_le h]
  · rw [max_eq_left (le_of_not_ge h),intervalIntegral.integral_same,
      Ioc_eq_empty (not_lt.mpr (le_of_not_ge h))]
    simp

/-- Fubini on the literal static triangle, with product and radial admission
established before using either iterated integral. -/
theorem static_triangle_fubini (F : ℝ×ℝ→ℂ) (a A B T : ℝ) (hAB : A ≤ B)
    (hF : IntegrableOn F (Ioc A B ×ˢ Ioi a)) :
    IntervalIntegrable (fun L => ∫ p in a..max a (T-L/2),F (L,p)) volume A B ∧
      staticTriangle F a A B T=
        (∫ v in Ioc A B ×ˢ Ioi a,
          {v : ℝ×ℝ | v.2+v.1/2 ≤ T}.indicator F v)/2 := by
  let E := {v : ℝ×ℝ | v.2+v.1/2 ≤ T}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator F)
      ((volume.restrict (Ioc A B)).prod (volume.restrict (Ioi a))) := by
    simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod] using hF.indicator hE
  have hrow (L : ℝ) : (∫ p in Ioi a,E.indicator F (L,p))=
      ∫ p in a..max a (T-L/2),F (L,p) := by
    have he : (fun p => E.indicator F (L,p))=(Iic (T-L/2)).indicator (fun p => F (L,p)) := by
      funext p
      have hh : p+L/2 ≤ T ↔ p ≤ T-L/2 := by constructor <;> intro h <;> linarith
      simp only [E,Set.indicator,mem_setOf_eq,mem_Iic,hh]
    rw [he]
    exact clipped_time_integral _ _ _
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).mpr
    (hi.integral_prod_left.congr (ae_of_all _ hrow)),?_⟩
  unfold staticTriangle
  rw [intervalIntegral.integral_of_le hAB]
  congr 1
  have hp := integral_prod (E.indicator F) hi
  rw [Measure.prod_restrict,← Measure.volume_eq_prod] at hp
  rw [hp]
  exact integral_congr_ae (ae_of_all _ (fun L => (hrow L).symm))

/-- The horizon contribution in the original radial integral is the exact
static window of its actual time density. -/
theorem static_triangle_window (U : ℝ→ℂ) (hU : IntegrableOn U (Ioi (0:ℝ)))
    (a A B T : ℝ) (ha : 0 ≤ a) (hAB : A ≤ B) :
    IntervalIntegrable (fun L => ∫ p in a..max a (T-L/2),U p) volume A B ∧
      staticTriangle (fun v => U v.2) a A B T=
        ∫ p in Ioi a,(staticWindow A B T p:ℂ)*U p := by
  have hUa := hU.mono_set (Ioi_subset_Ioi ha)
  have h1 : IntegrableOn (fun _ : ℝ => (1:ℂ)) (Ioc A B) :=
    integrableOn_const (by simp [Real.volume_Ioc])
  have hbase : IntegrableOn (fun v : ℝ×ℝ => U v.2) (Ioc A B ×ˢ Ioi a) := by
    simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod,one_mul] using h1.mul_prod hUa
  obtain ⟨hi,he⟩ := static_triangle_fubini (fun v => U v.2) a A B T hAB hbase
  refine ⟨hi,?_⟩
  rw [he]
  let E := {v : ℝ×ℝ | v.2+v.1/2 ≤ T}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hprod : Integrable (E.indicator (fun v => U v.2))
      ((volume.restrict (Ioc A B)).prod (volume.restrict (Ioi a))) := by
    simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod] using hbase.indicator hE
  have hcol (p : ℝ) : (∫ L in Ioc A B,E.indicator (fun v => U v.2) (L,p))=
      ((max (min B (2*(T-p))-A) 0:ℝ):ℂ)*U p := by
    have he : (fun L => E.indicator (fun v => U v.2) (L,p))=
        (Iic (2*(T-p))).indicator (fun _ => U p) := by
      funext L
      have hh : p+L/2 ≤ T ↔ L ≤ 2*(T-p) := by constructor <;> intro h <;> linarith
      simp only [E,Set.indicator,mem_setOf_eq,mem_Iic,hh]
    rw [he,setIntegral_indicator measurableSet_Iic]
    have hs : Ioc A B ∩ Iic (2*(T-p))=Ioc A (min B (2*(T-p))) := by
      ext L
      simp only [mem_inter_iff,mem_Ioc,mem_Iic,le_min_iff]
      tauto
    rw [hs,setIntegral_const,Real.volume_real_Ioc,Complex.real_smul]
  have hp := integral_prod_symm (E.indicator (fun v => U v.2)) hprod
  rw [Measure.prod_restrict,← Measure.volume_eq_prod] at hp
  rw [hp,← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    dsimp only
    have heq := hcol p
    convert! congrArg (fun z : ℂ => z/2) heq using 1
    dsimp [staticWindow]
    push_cast
    ring)

/-- The original horizon triangle has precisely its mass and two moving
mass-tail corners, with arbitrary independent finite cutoffs. -/
theorem static_triangle_two_corners (U : ℝ→ℂ) (hU : IntegrableOn U (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*U p) (Ioi (0:ℝ)))
    (a A B T : ℝ) (ha : 0 ≤ a) (hAB : A ≤ B) :
    staticTriangle (fun v => U v.2) a A B T=
      ((max a (T-A/2)-max a (T-B/2):ℝ):ℂ)*tailMass U a+
        tailCorner U (max a (T-A/2))-tailCorner U (max a (T-B/2)) :=
  (static_triangle_window U hU a A B T ha hAB).2.trans
    (static_window_two_corners U hU hM a A B T ha hAB).2

end
end RHTower.D4BMOriginalRestoredStaticGeometry
