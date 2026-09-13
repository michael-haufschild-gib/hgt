import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalAngularCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSpacetimeRegularity

/-!
# Original Einstein angular current with parameter derivatives transferred to its boundaries

For the actual causal source U = R Z and the unchanged left scalar W, every
radial and temporal source derivative in the angular Einstein current is a
parameter divergence plus an explicit transfer involving only derivatives of
W. The inverse-square weight is differentiated. Both ordered mixed reader
derivatives and all four temporal/radial edges remain.

The original current integrated on a compact interior rectangle equals its
four oriented endpoint terms minus the unchanged-reader remainder. All
regularity and integrability are supplied by the original fields. No cusp
limit is differentiated, and no endpoint value or extinction is assumed.
-/

open Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalGreenBoundary
open GaloisForLFunctions.HTGeometry ScalarTwoJet D4BMOriginalAngularCurrent
private abbrev P := Fin 4 → ℝ
private abbrev F := P → ℂ

private theorem smooth_partial {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x) (i : Fin 4) :
    ContDiffAt ℝ ∞ (coordDeriv i f) x := coordDeriv_contDiffAt hf (by simp) i

private theorem smooth_two {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ 2 f x := hf.of_le (WithTop.coe_le_coe.mpr le_top)

private theorem partial_coordinate (x : P) (i k : Fin 4) :
    coordDeriv i (fun y : P => (y k:ℂ)) x=if i=k then 1 else 0 := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply k x)
  change fderiv ℝ (Complex.ofRealCLM ∘ (fun y : P => y k)) x (Pi.single i 1)=_
  rw [h.fderiv]
  by_cases hi : i=k
  · subst i; simp
  · simp [hi,Ne.symm hi]

private theorem partial_triple {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x) (i k : Fin 4) :
    coordDeriv i (coordDeriv k (coordDeriv k f)) x=
      coordDeriv k (coordDeriv k (coordDeriv i f)) x := by
  rw [coordDeriv_comm (smooth_two (smooth_partial hf k)) i k]
  have he : coordDeriv i (coordDeriv k f) =ᶠ[𝓝 x] coordDeriv k (coordDeriv i f) := by
    filter_upwards [(smooth_two hf).eventually (by norm_num)] with z hz
    exact coordDeriv_comm hz i k
  change fderiv ℝ (coordDeriv i (coordDeriv k f)) x (Pi.single k 1)=_
  rw [he.fderiv_eq]

private theorem angularLap_smooth {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (angularLap f) x := by
  have hY : ContDiffAt ℝ ∞ (fun z : P => (z 3:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (3:Fin 4))).contDiffAt
  exact (hY.pow 2).mul ((smooth_partial (smooth_partial hf 2) 2).add
    (smooth_partial (smooth_partial hf 3) 3))

private theorem angularLap_partial {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x)
    (i : Fin 4) (hi : i≠3) :
    coordDeriv i (angularLap f) x=angularLap (coordDeriv i f) x := by
  have hYs : ContDiff ℝ ∞ (fun z : P => (z 3:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (3:Fin 4))
  have hY := hYs.differentiable (by simp) x
  have h2 := (smooth_partial (smooth_partial hf 2) 2).differentiableAt (by simp)
  have h3 := (smooth_partial (smooth_partial hf 3) 3).differentiableAt (by simp)
  change coordDeriv i (fun z => (z 3:ℂ)^2*
    (coordDeriv 2 (coordDeriv 2 f) z+coordDeriv 3 (coordDeriv 3 f) z)) x=_
  simp only [pow_two]
  have hYY : DifferentiableAt ℝ (fun z : P => (z 3:ℂ)*(z 3:ℂ)) x := hY.mul hY
  have hsum : DifferentiableAt ℝ (fun z => coordDeriv 2 (coordDeriv 2 f) z+
    coordDeriv 3 (coordDeriv 3 f) z) x := h2.add h3
  rw [coordDeriv_mul hYY hsum,coordDeriv_mul hY hY,
    partial_coordinate,if_neg hi,coordDeriv_add h2 h3,
    partial_triple hf i 2,partial_triple hf i 3]
  dsimp only [angularLap]
  ring

/-- The original bilinear Green transfer is smooth as a field. -/
theorem greenPair_smooth {u v : F} {x : P} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (j : Fin 2) :
    ContDiffAt ℝ ∞ (fun z => greenPair u v j z) x :=
  ((angularLap_smooth hu).mul (smooth_partial hv (angularIndex j))).sub
    ((angularLap_smooth hv).mul (smooth_partial hu (angularIndex j)))

/-- Parameter differentiation obeys the actual bilinear rule; no independent jets occur. -/
theorem greenPair_partial {u v : F} {x : P} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (i : Fin 4) (hi : i≠3) (j : Fin 2) :
    coordDeriv i (fun z => greenPair u v j z) x=
      greenPair (coordDeriv i u) v j x+greenPair u (coordDeriv i v) j x := by
  have hLu := (angularLap_smooth hu).differentiableAt (by simp)
  have hLv := (angularLap_smooth hv).differentiableAt (by simp)
  have hdu := (smooth_partial hu (angularIndex j)).differentiableAt (by simp)
  have hdv := (smooth_partial hv (angularIndex j)).differentiableAt (by simp)
  change coordDeriv i (fun z => angularLap u z*coordDeriv (angularIndex j) v z-
    angularLap v z*coordDeriv (angularIndex j) u z) x=_
  have h1 : DifferentiableAt ℝ (fun z => angularLap u z*coordDeriv (angularIndex j) v z) x := hLu.mul hdv
  have h2 : DifferentiableAt ℝ (fun z => angularLap v z*coordDeriv (angularIndex j) u z) x := hLv.mul hdu
  rw [coordDeriv_sub h1 h2,coordDeriv_mul hLu hdv,
    coordDeriv_mul hLv hdu,angularLap_partial hu i hi,angularLap_partial hv i hi,
    coordDeriv_comm (smooth_two hu) i (angularIndex j),
    coordDeriv_comm (smooth_two hv) i (angularIndex j)]
  dsimp only [greenPair]
  ring

def inverseSquare (x : P) : ℂ := 1/(x 1:ℂ)^2
def radialCoefficient (x : P) : ℂ := 1-inverseSquare x
def weightDerivative (x : P) : ℂ := -2/(x 1:ℂ)^3

private theorem inverseSquare_smooth {x : P} (hr : x 1≠0) :
    ContDiffAt ℝ ∞ inverseSquare x := by
  have hR : ContDiffAt ℝ ∞ (fun z : P => z 1) x :=
    (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  have h := Complex.ofRealCLM.contDiff.contDiffAt.comp x
    ((hR.pow 2).inv (pow_ne_zero 2 hr))
  convert! h using 1
  funext z
  simp [inverseSquare]

private theorem radialCoefficient_smooth {x : P} (hr : x 1≠0) :
    ContDiffAt ℝ ∞ radialCoefficient x := contDiffAt_const.sub (inverseSquare_smooth hr)

private theorem inverseSquare_partial {x : P} (hr : x 1≠0) (i : Fin 4) :
    coordDeriv i inverseSquare x=if i=1 then weightDerivative x else 0 := by
  have hd : HasDerivAt (fun r : ℝ => 1/r^2) (-2/(x 1)^3) (x 1) := by
    have h := (hasDerivAt_const (x 1) (1:ℝ)).div
      ((hasDerivAt_id (x 1)).pow 2) (pow_ne_zero 2 hr)
    apply h.congr_deriv
    simp only [Pi.pow_apply,id_eq,mul_one,zero_mul,zero_sub,one_mul]
    field_simp
    ring
  have hc := HasDerivAt.comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ)
    (f := fun z : P => z 1) x hd (hasFDerivAt_apply 1 x)
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hc
  have he : inverseSquare=Complex.ofRealCLM ∘ ((fun r : ℝ => 1/r^2) ∘ (fun z : P => z 1)) := by
    funext z
    simp [inverseSquare,Function.comp_def]
  rw [he]
  change fderiv ℝ _ x (Pi.single i 1)=_
  rw [h.fderiv]
  by_cases hi : i=1
  · subst i; simp [weightDerivative]
  · simp [hi,Ne.symm hi]

private theorem radialCoefficient_partial {x : P} (hr : x 1≠0) :
    coordDeriv 1 radialCoefficient x= -weightDerivative x := by
  change coordDeriv 1 (fun z => (1:ℂ)-inverseSquare z) x=_
  rw [coordDeriv_sub (differentiableAt_const (c := (1:ℂ)))
    ((inverseSquare_smooth hr).differentiableAt (by simp)),inverseSquare_partial hr]
  simp [coordDeriv]

/-- Exact radial endpoint current before any limit. -/
def radialBoundary (u v : F) (j : Fin 2) (x : P) : ℂ :=
  radialCoefficient x*greenPair u (coordDeriv 1 v) j x+
    inverseSquare x*greenPair u (coordDeriv 0 v) j x

/-- Exact temporal endpoint current before any limit. -/
def timeBoundary (u v : F) (j : Fin 2) (x : P) : ℂ :=
  inverseSquare x*greenPair u (coordDeriv 1 v) j x

/-- The surviving interior transfer contains no temporal or radial source derivative.
Both ordered mixed derivatives of the unchanged reader remain. -/
def readerRemainder (u v : F) (j : Fin 2) (x : P) : ℂ :=
  -weightDerivative x*greenPair u (coordDeriv 1 v) j x+
    weightDerivative x*greenPair u (coordDeriv 0 v) j x+
    radialCoefficient x*greenPair u (coordDeriv 1 (coordDeriv 1 v)) j x+
    inverseSquare x*greenPair u (coordDeriv 1 (coordDeriv 0 v)) j x+
    inverseSquare x*greenPair u (coordDeriv 0 (coordDeriv 1 v)) j x

private theorem radialBoundary_smooth {u v : F} {x : P} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (hr : x 1≠0) (j : Fin 2) :
    ContDiffAt ℝ ∞ (radialBoundary u v j) x :=
  ((radialCoefficient_smooth hr).mul (greenPair_smooth hu (smooth_partial hv 1) j)).add
    ((inverseSquare_smooth hr).mul (greenPair_smooth hu (smooth_partial hv 0) j))

private theorem timeBoundary_smooth {u v : F} {x : P} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (hr : x 1≠0) (j : Fin 2) :
    ContDiffAt ℝ ∞ (timeBoundary u v j) x :=
  (inverseSquare_smooth hr).mul (greenPair_smooth hu (smooth_partial hv 1) j)

private theorem radialBoundary_partial {u v : F} {x : P} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (hr : x 1≠0) (j : Fin 2) :
    coordDeriv 1 (radialBoundary u v j) x=
      -weightDerivative x*greenPair u (coordDeriv 1 v) j x+
      radialCoefficient x*(greenPair (coordDeriv 1 u) (coordDeriv 1 v) j x+
        greenPair u (coordDeriv 1 (coordDeriv 1 v)) j x)+
      (weightDerivative x*greenPair u (coordDeriv 0 v) j x+
      inverseSquare x*(greenPair (coordDeriv 1 u) (coordDeriv 0 v) j x+
        greenPair u (coordDeriv 1 (coordDeriv 0 v)) j x)) := by
  have hA := (radialCoefficient_smooth hr).differentiableAt (by simp)
  have hC := (inverseSquare_smooth hr).differentiableAt (by simp)
  have hB1 := (greenPair_smooth hu (smooth_partial hv 1) j).differentiableAt (by simp)
  have hB0 := (greenPair_smooth hu (smooth_partial hv 0) j).differentiableAt (by simp)
  have h1 : DifferentiableAt ℝ (fun z => radialCoefficient z*greenPair u (coordDeriv 1 v) j z) x := hA.mul hB1
  have h0 : DifferentiableAt ℝ (fun z => inverseSquare z*greenPair u (coordDeriv 0 v) j z) x := hC.mul hB0
  change coordDeriv 1 (fun z => radialCoefficient z*greenPair u (coordDeriv 1 v) j z+
    inverseSquare z*greenPair u (coordDeriv 0 v) j z) x=_
  rw [coordDeriv_add h1 h0,coordDeriv_mul hA hB1,coordDeriv_mul hC hB0,
    radialCoefficient_partial hr,inverseSquare_partial hr,
    greenPair_partial hu (smooth_partial hv 1) 1 (by simp [Fin.ext_iff]),
    greenPair_partial hu (smooth_partial hv 0) 1 (by simp [Fin.ext_iff])]
  rfl

private theorem timeBoundary_partial {u v : F} {x : P} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (hr : x 1≠0) (j : Fin 2) :
    coordDeriv 0 (timeBoundary u v j) x=
      inverseSquare x*(greenPair (coordDeriv 0 u) (coordDeriv 1 v) j x+
        greenPair u (coordDeriv 0 (coordDeriv 1 v)) j x) := by
  have hC := (inverseSquare_smooth hr).differentiableAt (by simp)
  have hB := (greenPair_smooth hu (smooth_partial hv 1) j).differentiableAt (by simp)
  change coordDeriv 0 (fun z => inverseSquare z*greenPair u (coordDeriv 1 v) j z) x=_
  rw [coordDeriv_mul hC hB,inverseSquare_partial hr,
    greenPair_partial hu (smooth_partial hv 1) 0 (by simp [Fin.ext_iff])]
  simp

/-- All source parameter derivatives move to the two retained endpoint currents. -/
theorem green_triple_boundary {u v : F} {x : P} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (hr : x 1≠0) (j : Fin 2) :
    1/(x 1:ℂ)^2*(((x 1:ℂ)^2-1)*greenPair (coordDeriv 1 u) (coordDeriv 1 v) j x+
      greenPair (coordDeriv 1 u) (coordDeriv 0 v) j x+
      greenPair (coordDeriv 0 u) (coordDeriv 1 v) j x)=
    coordDeriv 1 (radialBoundary u v j) x+coordDeriv 0 (timeBoundary u v j) x-
      readerRemainder u v j x := by
  rw [radialBoundary_partial hu hv hr,timeBoundary_partial hu hv hr]
  have hrC : (x 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  dsimp only [readerRemainder,radialCoefficient,inverseSquare,weightDerivative]
  field_simp
  ring

open MeasureTheory

private def rectanglePoint (X Y : ℝ) (z : ℝ × ℝ) : P := ![z.1,z.2,X,Y]

private theorem rectanglePoint_smooth (X Y : ℝ) : ContDiff ℝ ∞ (rectanglePoint X Y) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_snd
  · exact contDiff_const
  · exact contDiff_const

private theorem radius_slice_derivative {g : F} (p r X Y : ℝ)
    (hg : DifferentiableAt ℝ g (rectanglePoint X Y (p,r))) :
    HasDerivAt (fun s => g (rectanglePoint X Y (p,s)))
      (coordDeriv 1 g (rectanglePoint X Y (p,r))) r := by
  have hc : HasDerivAt (fun s => rectanglePoint X Y (p,s)) (Pi.single 1 1) r := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [rectanglePoint,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const r p
    · simpa [rectanglePoint,Pi.single_apply,Fin.ext_iff] using! hasDerivAt_id r
    · simpa [rectanglePoint,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const r X
    · simpa [rectanglePoint,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const r Y
  exact hg.hasFDerivAt.comp_hasDerivAt r hc

private theorem time_slice_derivative {g : F} (p r X Y : ℝ)
    (hg : DifferentiableAt ℝ g (rectanglePoint X Y (p,r))) :
    HasDerivAt (fun s => g (rectanglePoint X Y (s,r)))
      (coordDeriv 0 g (rectanglePoint X Y (p,r))) p := by
  have hc : HasDerivAt (fun s => rectanglePoint X Y (s,r)) (Pi.single 0 1) p := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [rectanglePoint,Pi.single_apply,Fin.ext_iff] using! hasDerivAt_id p
    · simpa [rectanglePoint,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const p r
    · simpa [rectanglePoint,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const p X
    · simpa [rectanglePoint,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const p Y
  exact hg.hasFDerivAt.comp_hasDerivAt p hc

private theorem rectangle_inner_integrable {H : ℝ × ℝ → ℂ} {a b c d : ℝ}
    (hH : ContinuousOn H (Icc a b ×ˢ Icc c d)) (hcd : c≤d) {p : ℝ} (hp : p∈Icc a b) :
    IntervalIntegrable (fun r => H (p,r)) volume c d := by
  have h : ContinuousOn (fun r => H (p,r)) (Icc c d) :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hr => ⟨hp,hr⟩)
  exact h.intervalIntegrable_of_Icc hcd

private theorem rectangle_outer_integrable {H : ℝ × ℝ → ℂ} {a b c d : ℝ}
    (hH : ContinuousOn H (Icc a b ×ˢ Icc c d)) (hab : a≤b) (hcd : c≤d) :
    IntervalIntegrable (fun p => ∫ r in c..d,H (p,r)) volume a b := by
  have h : Integrable H ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hH.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  simpa only [intervalIntegral.integral_of_le hcd,IntegrableOn] using! h.integral_prod_left

private theorem rectangle_add {H K : ℝ × ℝ → ℂ} {a b c d : ℝ}
    (hH : ContinuousOn H (Icc a b ×ˢ Icc c d))
    (hK : ContinuousOn K (Icc a b ×ˢ Icc c d)) (hab : a≤b) (hcd : c≤d) :
    (∫ p in a..b,∫ r in c..d,H (p,r)+K (p,r))=
      (∫ p in a..b,∫ r in c..d,H (p,r))+(∫ p in a..b,∫ r in c..d,K (p,r)) := by
  calc
    _ = ∫ p in a..b,((∫ r in c..d,H (p,r))+(∫ r in c..d,K (p,r))) := by
      apply intervalIntegral.integral_congr
      intro p hp
      have hp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hp
      exact intervalIntegral.integral_add (rectangle_inner_integrable hH hcd hp')
        (rectangle_inner_integrable hK hcd hp')
    _ = _ := intervalIntegral.integral_add (rectangle_outer_integrable hH hab hcd)
      (rectangle_outer_integrable hK hab hcd)

private theorem rectangle_swap {H : ℝ × ℝ → ℂ} {a b c d : ℝ}
    (hH : ContinuousOn H (Icc a b ×ˢ Icc c d)) (hab : a≤b) (hcd : c≤d) :
    (∫ p in a..b,∫ r in c..d,H (p,r))=∫ r in c..d,∫ p in a..b,H (p,r) := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  rw [uIoc_of_le hab,uIoc_of_le hcd]
  exact (hH.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The two parameter derivatives integrate to all four original oriented edges. -/
theorem rectangle_divergence (A B : F) (a b c d X Y : ℝ) (hab : a≤b) (hcd : c≤d)
    (hA : ∀ z∈Icc a b ×ˢ Icc c d,ContDiffAt ℝ ∞ A (rectanglePoint X Y z))
    (hB : ∀ z∈Icc a b ×ˢ Icc c d,ContDiffAt ℝ ∞ B (rectanglePoint X Y z)) :
    (∫ p in a..b,∫ r in c..d,
      coordDeriv 1 A (rectanglePoint X Y (p,r))+coordDeriv 0 B (rectanglePoint X Y (p,r)))=
    (∫ p in a..b,A (rectanglePoint X Y (p,d))-A (rectanglePoint X Y (p,c)))+
      ∫ r in c..d,B (rectanglePoint X Y (b,r))-B (rectanglePoint X Y (a,r)) := by
  have h1 : ContinuousOn (fun z => coordDeriv 1 A (rectanglePoint X Y z)) (Icc a b ×ˢ Icc c d) := by
    intro z hz
    exact ((smooth_partial (hA z hz) 1).continuousAt.comp
      (rectanglePoint_smooth X Y).continuous.continuousAt).continuousWithinAt
  have h0 : ContinuousOn (fun z => coordDeriv 0 B (rectanglePoint X Y z)) (Icc a b ×ˢ Icc c d) := by
    intro z hz
    exact ((smooth_partial (hB z hz) 0).continuousAt.comp
      (rectanglePoint_smooth X Y).continuous.continuousAt).continuousWithinAt
  rw [rectangle_add h1 h0 hab hcd]
  congr 1
  · apply intervalIntegral.integral_congr
    intro p hp
    have hp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hp
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro r hr
      have hr' : r∈Icc c d := by simpa only [uIcc_of_le hcd] using hr
      exact radius_slice_derivative p r X Y ((hA (p,r) ⟨hp',hr'⟩).differentiableAt (by simp))
    · exact rectangle_inner_integrable h1 hcd hp'
  · rw [rectangle_swap h0 hab hcd]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc c d := by simpa only [uIcc_of_le hcd] using hr
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro p hp
      have hp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hp
      exact time_slice_derivative p r X Y ((hB (p,r) ⟨hp',hr'⟩).differentiableAt (by simp))
    · have hs : ContinuousOn (fun z : ℝ × ℝ => coordDeriv 0 B (rectanglePoint X Y (z.2,z.1)))
          (Icc c d ×ˢ Icc a b) :=
        h0.comp continuous_swap.continuousOn (fun _ hz => ⟨hz.2,hz.1⟩)
      exact rectangle_inner_integrable hs hab hr'

private theorem weightDerivative_smooth {x : P} (hr : x 1≠0) :
    ContDiffAt ℝ ∞ weightDerivative x := by
  have hR : ContDiffAt ℝ ∞ (fun z : P => z 1) x := (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x ((hR.pow 3).inv (pow_ne_zero 3 hr))
  have h := (contDiffAt_const (c := (-2:ℂ))).mul hc
  convert! h using 1
  funext z
  simp [weightDerivative,div_eq_mul_inv]

private theorem readerRemainder_smooth {u v : F} {x : P} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (hr : x 1≠0) (j : Fin 2) :
    ContDiffAt ℝ ∞ (readerRemainder u v j) x := by
  have hD := weightDerivative_smooth hr
  have hC := inverseSquare_smooth hr
  have hA := radialCoefficient_smooth hr
  have h := ((((hD.neg.mul (greenPair_smooth hu (smooth_partial hv 1) j)).add
    (hD.mul (greenPair_smooth hu (smooth_partial hv 0) j))).add
    (hA.mul (greenPair_smooth hu (smooth_partial (smooth_partial hv 1) 1) j))).add
    (hC.mul (greenPair_smooth hu (smooth_partial (smooth_partial hv 0) 1) j))).add
    (hC.mul (greenPair_smooth hu (smooth_partial (smooth_partial hv 1) 0) j))
  exact h

private theorem rectangle_sub {H K : ℝ × ℝ → ℂ} {a b c d : ℝ}
    (hH : ContinuousOn H (Icc a b ×ˢ Icc c d))
    (hK : ContinuousOn K (Icc a b ×ˢ Icc c d)) (hab : a≤b) (hcd : c≤d) :
    (∫ p in a..b,∫ r in c..d,H (p,r)-K (p,r))=
      (∫ p in a..b,∫ r in c..d,H (p,r))-(∫ p in a..b,∫ r in c..d,K (p,r)) := by
  simpa only [sub_eq_add_neg,Pi.neg_apply,intervalIntegral.integral_neg] using rectangle_add hH hK.neg hab hcd

/-- Original causal source paired against the original physical left stream in ingoing coordinates. -/
def originalAngularCurrent (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (j : Fin 2) (x : P) : ℂ :=
  D4BMIngoingFullCurrent.current (x 1) (x 3)
    (fun a => ofField (D4BMActualIngoingCurrent.originalStream q branch amp a) x)
    (fun a => ofField (leftStream r side outer a) x) (angularIndex j)

private theorem tortoise_smooth {R : ℝ} (hR : 1<R) :
    ContDiffAt ℝ ∞ D4BMIngoingCoordinates.tortoise R := by
  have hm : R-1≠0 := by linarith
  have hp : R+1≠0 := by linarith
  unfold D4BMIngoingCoordinates.tortoise
  fun_prop

/-- The original causal integral is smooth throughout the positive-time physical exterior. -/
theorem originalPotential_exterior_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    ContDiffAt ℝ ∞ (D4BMActualIngoingCurrent.originalIngoingPotential q branch amp) x := by
  let C : P → P := fun z =>
    ![z 0,z 0-2*D4BMIngoingCoordinates.tortoise (z 1),z 2,Real.log (z 3)]
  have ht : D4BMIngoingCoordinates.tortoise (x 1)<0 := by
    have h := Real.log_lt_log (show 0<x 1-1 by linarith) (show x 1-1<x 1+1 by linarith)
    dsimp [D4BMIngoingCoordinates.tortoise]
    linarith
  have hc : ContDiffAt ℝ ∞ C x := by
    have hT := (tortoise_smooth hr).comp x (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ (0:Fin 4)).contDiffAt
    · exact (contDiff_apply ℝ ℝ (0:Fin 4)).contDiffAt.sub (contDiffAt_const.mul hT)
    · exact (contDiff_apply ℝ ℝ (2:Fin 4)).contDiffAt
    · exact (contDiff_apply ℝ ℝ (3:Fin 4)).contDiffAt.log hy.ne'
  exact (D4BMOriginalSpacetimeRegularity.originalPotential_smooth q branch amp (C x)
    hp (by change x 0<x 0-2*D4BMIngoingCoordinates.tortoise (x 1);linarith)).comp x hc

/-- The reconstruction scalar R Z has actual derivatives on the entire physical exterior. -/
theorem sourceScalar_exterior_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    ContDiffAt ℝ ∞ (sourceScalar q branch amp) x :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 4))).contDiffAt.mul
    (originalPotential_exterior_smooth q branch amp x hp hr hy)

private theorem source_exterior_germ (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    coexactField (sourceScalar q branch amp) j =ᶠ[𝓝 x]
      D4BMActualIngoingCurrent.originalStream q branch amp j := by
  have hZ : ContDiffAt ℝ 1 (D4BMActualIngoingCurrent.originalIngoingPotential q branch amp) x :=
    (originalPotential_exterior_smooth q branch amp x hp hr hy).of_le (by simp)
  filter_upwards [hZ.eventually (by norm_num)] with z hz
  exact source_coexact q branch amp z (hz.differentiableAt (by norm_num)) j

private theorem coexact_smooth {u : F} {x : P} (hu : ContDiffAt ℝ ∞ u x) (j : Fin 2) :
    ContDiffAt ℝ ∞ (coexactField u j) x := by
  fin_cases j
  · exact smooth_partial hu 3
  · exact (smooth_partial hu 2).neg

/-- All ordered derivatives of the original reconstructed stream exist for every R > 1. -/
theorem originalStream_exterior_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    ContDiffAt ℝ ∞ (D4BMActualIngoingCurrent.originalStream q branch amp j) x :=
  (coexact_smooth (sourceScalar_exterior_smooth q branch amp x hp hr hy) j).congr_of_eventuallyEq
    (source_exterior_germ q branch amp x hp hr hy j).symm

private theorem ingoing_smooth (x : P) (hr : 1<x 1) :
    ContDiffAt ℝ ∞ D4BMActualIngoingCurrent.ingoingPoint x := by
  have ht := (tortoise_smooth hr).comp x (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_apply ℝ ℝ (0:Fin 4)).contDiffAt.add ht
  · exact (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  · exact (contDiff_apply ℝ ℝ (2:Fin 4)).contDiffAt
  · exact (contDiff_apply ℝ ℝ (3:Fin 4)).contDiffAt

/-- The full original reconstructed metric current equals the actual ingoing current
throughout the exterior, with no upper radial cutoff and the unchanged physical left field. -/
theorem original_metric_current_eq (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (x : D4BMBackground.ExteriorPoint) (hp : 0<D4BMActualIngoingCurrent.ingoingPoint x.val 0) :
    D4BMActualIngoingCurrent.metricIngoingCurrent x
      (D4BMActualIngoingCurrent.originalStaticStream q branch amp)
      (D4BMPhysicalModeAction.physicalLeftModeStream r
        (D4BMLeftModeRadialEquation.frequency r side) outer)=
    D4BMIngoingFullCurrent.current (x.val 1) (x.val 3)
      (fun a => ofField (D4BMActualIngoingCurrent.originalStream q branch amp a)
        (D4BMActualIngoingCurrent.ingoingPoint x.val))
      (fun a => ofField (leftStream r side outer a)
        (D4BMActualIngoingCurrent.ingoingPoint x.val)) := by
  have hP (a : Fin 2) := smooth_two (originalStream_exterior_smooth q branch amp
    (D4BMActualIngoingCurrent.ingoingPoint x.val) hp x.property.1 x.property.2 a)
  have hQ (a : Fin 2) := leftStream_smooth r side outer
    (D4BMActualIngoingCurrent.ingoingPoint x.val) x.property.1 x.property.2 a
  have hs := (ingoing_smooth x.val x.property.1).of_le
    (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have he : (fun a z => leftStream r side outer a (D4BMActualIngoingCurrent.ingoingPoint z))=
      D4BMPhysicalModeAction.physicalLeftModeStream r
        (D4BMLeftModeRadialEquation.frequency r side) outer := funext (leftStream_static r side outer)
  have hPs (a : Fin 2) : ContDiffAt ℝ 2
      (D4BMActualIngoingCurrent.originalStaticStream q branch amp a) x.val :=
    (hP a).comp x.val hs
  have hQs (a : Fin 2) : ContDiffAt ℝ 2
      (fun z => leftStream r side outer a (D4BMActualIngoingCurrent.ingoingPoint z)) x.val :=
    (hQ a).comp x.val hs
  rw [← he,D4BMActualIngoingCurrent.metricIngoingCurrent_eq _ _ x hPs hQs]
  change D4BMPhysicalLiftCurrent.ingoingAction x
    (fun a => ofField (fun z => D4BMActualIngoingCurrent.originalStream q branch amp a
      (D4BMActualIngoingCurrent.ingoingPoint z)) x.val) _=_
  simp_rw [D4BMActualIngoingCurrent.ofField_ingoing_comp x.property.1 (hP _),
    D4BMActualIngoingCurrent.ofField_ingoing_comp x.property.1 (hQ _)]
  exact D4BMIngoingFullCurrent.original_ingoing_current x _ _

/-- Actual source and original physical reader throughout the exterior,
with every parameter endpoint retained. -/
theorem original_current_boundary (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    originalAngularCurrent q r branch side outer amp j x=
      coordDeriv 1 (radialBoundary (sourceScalar q branch amp) (leftScalar r side outer) j) x+
      coordDeriv 0 (timeBoundary (sourceScalar q branch amp) (leftScalar r side outer) j) x-
      readerRemainder (sourceScalar q branch amp) (leftScalar r side outer) j x := by
  have hu := sourceScalar_exterior_smooth q branch amp x hp hr hy
  have hv := leftScalar_smooth r side outer x hr hy
  have he (a : Fin 2) := ofField_germ (source_exterior_germ q branch amp x hp hr hy a)
  have hf (a : Fin 2) := ofField_germ (left_coexact_germ r side outer x hr hy a)
  unfold originalAngularCurrent
  simp_rw [← he,← hf]
  exact (coexact_current _ _ x (hu.of_le (WithTop.coe_le_coe.mpr le_top))
    (hv.of_le (WithTop.coe_le_coe.mpr le_top)) j).trans
    (green_triple_boundary hu hv (by linarith) j)

/-- The boundary transfer for the actual reconstructed metric current at every R > 1. -/
theorem original_metric_boundary (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (x : D4BMBackground.ExteriorPoint) (hp : 0<D4BMActualIngoingCurrent.ingoingPoint x.val 0)
    (j : Fin 2) :
    D4BMActualIngoingCurrent.metricIngoingCurrent x
      (D4BMActualIngoingCurrent.originalStaticStream q branch amp)
      (D4BMPhysicalModeAction.physicalLeftModeStream r
        (D4BMLeftModeRadialEquation.frequency r side) outer) (angularIndex j)=
      coordDeriv 1 (radialBoundary (sourceScalar q branch amp) (leftScalar r side outer) j)
        (D4BMActualIngoingCurrent.ingoingPoint x.val)+
      coordDeriv 0 (timeBoundary (sourceScalar q branch amp) (leftScalar r side outer) j)
        (D4BMActualIngoingCurrent.ingoingPoint x.val)-
      readerRemainder (sourceScalar q branch amp) (leftScalar r side outer) j
        (D4BMActualIngoingCurrent.ingoingPoint x.val) := by
  rw [original_metric_current_eq q r branch side outer amp x hp]
  exact original_current_boundary q r branch side outer amp
    (D4BMActualIngoingCurrent.ingoingPoint x.val) hp x.property.1 x.property.2 j

/-- The actual physical angular current integrated on any compact interior time/radius
rectangle equals all four original edges minus the explicit unchanged-reader remainder.
No derivative of a cusp limit or analytic-admission hypothesis is used. -/
theorem original_rectangle_boundary (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p0 p1 R0 R1 X Y : ℝ) (hp : 0<p0) (hp01 : p0≤p1)
    (hR0 : 1<R0) (hR01 : R0≤R1) (hY : 0<Y) (j : Fin 2) :
    (∫ p in p0..p1,∫ R in R0..R1,
      originalAngularCurrent q r branch side outer amp j ![p,R,X,Y])=
      (∫ p in p0..p1,
        radialBoundary (sourceScalar q branch amp) (leftScalar r side outer) j ![p,R1,X,Y]-
        radialBoundary (sourceScalar q branch amp) (leftScalar r side outer) j ![p,R0,X,Y])+
      (∫ R in R0..R1,
        timeBoundary (sourceScalar q branch amp) (leftScalar r side outer) j ![p1,R,X,Y]-
        timeBoundary (sourceScalar q branch amp) (leftScalar r side outer) j ![p0,R,X,Y])-
      ∫ p in p0..p1,∫ R in R0..R1,
        readerRemainder (sourceScalar q branch amp) (leftScalar r side outer) j ![p,R,X,Y] := by
  let U := sourceScalar q branch amp
  let V := leftScalar r side outer
  let A := radialBoundary U V j
  let B := timeBoundary U V j
  let K := readerRemainder U V j
  have hgeom (z : ℝ × ℝ) (hz : z∈Icc p0 p1 ×ˢ Icc R0 R1) :
      0<z.1 ∧ 1<z.2 :=
    ⟨hp.trans_le hz.1.1,hR0.trans_le hz.2.1⟩
  have hUV (z : ℝ × ℝ) (hz : z∈Icc p0 p1 ×ˢ Icc R0 R1) :
      ContDiffAt ℝ ∞ U (rectanglePoint X Y z) ∧
      ContDiffAt ℝ ∞ V (rectanglePoint X Y z) := by
    obtain ⟨hpz,hRz⟩ := hgeom z hz
    exact ⟨sourceScalar_exterior_smooth q branch amp (rectanglePoint X Y z) hpz hRz hY,
      leftScalar_smooth r side outer (rectanglePoint X Y z) hRz hY⟩
  have hA (z : ℝ × ℝ) (hz : z∈Icc p0 p1 ×ˢ Icc R0 R1) :
      ContDiffAt ℝ ∞ A (rectanglePoint X Y z) :=
    radialBoundary_smooth (hUV z hz).1 (hUV z hz).2
      (show z.2≠0 by linarith [(hgeom z hz).2]) j
  have hB (z : ℝ × ℝ) (hz : z∈Icc p0 p1 ×ˢ Icc R0 R1) :
      ContDiffAt ℝ ∞ B (rectanglePoint X Y z) :=
    timeBoundary_smooth (hUV z hz).1 (hUV z hz).2
      (show z.2≠0 by linarith [(hgeom z hz).2]) j
  have hK (z : ℝ × ℝ) (hz : z∈Icc p0 p1 ×ˢ Icc R0 R1) :
      ContDiffAt ℝ ∞ K (rectanglePoint X Y z) :=
    readerRemainder_smooth (hUV z hz).1 (hUV z hz).2
      (show z.2≠0 by linarith [(hgeom z hz).2]) j
  have hD : ContinuousOn (fun z => coordDeriv 1 A (rectanglePoint X Y z)+
      coordDeriv 0 B (rectanglePoint X Y z)) (Icc p0 p1 ×ˢ Icc R0 R1) := by
    intro z hz
    exact (((smooth_partial (hA z hz) 1).continuousAt.add
      (smooth_partial (hB z hz) 0).continuousAt).comp
      (rectanglePoint_smooth X Y).continuous.continuousAt).continuousWithinAt
  have hKC : ContinuousOn (fun z => K (rectanglePoint X Y z)) (Icc p0 p1 ×ˢ Icc R0 R1) := by
    intro z hz
    exact ((hK z hz).continuousAt.comp (rectanglePoint_smooth X Y).continuous.continuousAt).continuousWithinAt
  calc
    _ = ∫ p in p0..p1,∫ R in R0..R1,
        (coordDeriv 1 A (rectanglePoint X Y (p,R))+coordDeriv 0 B (rectanglePoint X Y (p,R)))-
          K (rectanglePoint X Y (p,R)) := by
      apply intervalIntegral.integral_congr
      intro p hpi
      apply intervalIntegral.integral_congr
      intro R hRi
      have hz : (p,R)∈Icc p0 p1 ×ˢ Icc R0 R1 := by
        simpa only [mem_prod,uIcc_of_le hp01,uIcc_of_le hR01] using And.intro hpi hRi
      obtain ⟨hpz,hRz⟩ := hgeom (p,R) hz
      exact original_current_boundary q r branch side outer amp
        (rectanglePoint X Y (p,R)) hpz hRz hY j
    _ = _ := by
      rw [rectangle_sub hD hKC hp01 hR01,rectangle_divergence A B p0 p1 R0 R1 X Y hp01 hR01 hA hB]
      rfl

end RHTower.D4BMOriginalGreenBoundary
