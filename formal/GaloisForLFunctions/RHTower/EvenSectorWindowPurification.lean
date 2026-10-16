import GaloisForLFunctions.HTGeometry.EvenEntireWindowSource
import GaloisForLFunctions.RHTower.EvenSectorSmoothSourceScalarization

/-!
# Exact purification inside each EWU source window

The actual autocorrelation image of smooth even pole-free sources in any
fixed interval is already a convex cone. Every finite positive mixture has
one source in that same interval with its complete profile. In particular,
rank removal preserves every profile constraint, mass, and Weil energy
without changing the aperture.
-/

open Complex Filter Topology Set MeasureTheory Finsupp Zeta23
open scoped ComplexConjugate NNReal ContDiff
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

theorem paperFT_subquadratic (f : WeilTestFn) : SubquadraticType (paperFT f.1) := by
  obtain ⟨R,hR⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  have hs (u : ℝ) (hu : |R| < |u|) : f.1 u=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh := hR hm
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
    linarith [le_abs_self R]
  refine ⟨1,le_rfl,by norm_num,∫ u : ℝ,‖f.1 u‖,|R|,
    integral_nonneg (fun _ => norm_nonneg _),abs_nonneg _,fun z => ?_⟩
  have hh := norm_testTransform_le_exp f.2.1.continuous f.2.2 (abs_nonneg R) hs z
    (Complex.abs_im_le_norm z)
  simpa only [testTransform,paperFT,Real.rpow_one,mul_comm] using hh

/-- On the imaginary axis a positive even mixture has the common source
type, independently of its rank. -/
theorem factor_common_window (c : WeilEvenPolarTestFn →₀ ℝ≥0) (a : ℝ≥0)
    (hw : ∀ f ∈ c.support,tsupport f.1.1 ⊆ Icc (-(a : ℝ)) a)
    {q : ℂ → ℂ} (he : Function.Even q)
    (hi : ∀ z,evenPolarMixtureSpectrum c z=q z*conj (q (conj z))) :
    ∃ R : ℝ,0≤R ∧ ∀ y : ℝ,0≤y → ‖q ((y : ℂ)*I)‖≤R*Real.exp ((a : ℝ)*y) := by
  classical
  let M (f : WeilEvenPolarTestFn) := ∫ u : ℝ,‖f.1.1 u‖
  let D := c.sum fun f t => (t : ℝ)*(M f)^2
  have hD : 0≤D := Finset.sum_nonneg fun f _ => mul_nonneg (c f).coe_nonneg (sq_nonneg _)
  refine ⟨Real.sqrt D,Real.sqrt_nonneg _,fun y hy => ?_⟩
  have hb (f : WeilEvenPolarTestFn) (hf : f ∈ c.support) :
      ‖paperFT f.1.1 ((y : ℂ)*I)‖≤M f*Real.exp ((a : ℝ)*y) := by
    have hs (u : ℝ) (hu : (a : ℝ) < |u|) : f.1.1 u=0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact (not_le_of_gt hu) (abs_le.mpr (hw f hf hm))
    have hh := norm_testTransform_le_exp f.1.2.1.continuous f.1.2.2 a.coe_nonneg hs
      ((y : ℂ)*I) (K := y) (by simp [abs_of_nonneg hy])
    simpa only [testTransform,paperFT,M,mul_comm] using hh
  have hs : ‖q ((y : ℂ)*I)‖^2≤D*(Real.exp ((a : ℝ)*y))^2 := by
    rw [factor_axis_norm_sq c he hi _ (Or.inl (by simp))]
    dsimp only [D,Finsupp.sum]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro f hf
    calc
      _ ≤ (c f : ℝ)*(M f*Real.exp ((a : ℝ)*y))^2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hb f hf) 2) (c f).coe_nonneg
      _ = _ := by ring
  have hsq : (Real.sqrt D*Real.exp ((a : ℝ)*y))^2=D*(Real.exp ((a : ℝ)*y))^2 := by
    rw [mul_pow,Real.sq_sqrt hD]
  have hpos : 0≤Real.sqrt D*Real.exp ((a : ℝ)*y) := by positivity
  nlinarith [norm_nonneg (q ((y : ℂ)*I))]

/-- Whole-profile equality forces any smooth even scalarization to stay in
the original common window. No support choice for the factor is assumed. -/
theorem scalarization_tsupport_subset (c : SmoothEvenPolarTestFn →₀ ℝ≥0) (a : ℝ≥0)
    (hw : ∀ f ∈ c.support,tsupport f.1.1.1 ⊆ Icc (-(a : ℝ)) a)
    (f : SmoothEvenPolarTestFn)
    (hp : EF.weilTest f.1.1.1 f.1.1.1=polarMixtureProfile (smoothPolarCoefficients c)) :
    tsupport f.1.1.1 ⊆ Icc (-(a : ℝ)) a := by
  let d := smoothPolarCoefficients c
  have hd : ∀ g ∈ d.support,tsupport g.1.1 ⊆ Icc (-(a : ℝ)) a := by
    intro g hg
    let e : SmoothEvenPolarTestFn ↪ WeilEvenPolarTestFn := ⟨Subtype.val,Subtype.val_injective⟩
    change g ∈ (c.mapDomain e).support at hg
    rw [Finsupp.support_mapDomain_embedding] at hg
    obtain ⟨h,hh,rfl⟩ := Finset.mem_map.mp hg
    exact hw h hh
  let q := paperFT f.1.1.1
  have he : Function.Even q := paperFT_neg_of_even f.1.2.1
  have hi (z : ℂ) : evenPolarMixtureSpectrum d z=q z*conj (q (conj z)) := by
    rw [← polarMixtureProfile_transform,← hp]
    exact EF.paperFT_weilTest f.1.1.2.1.continuous f.1.1.2.1.continuous f.1.1.2.2 f.1.1.2.2 z
  obtain ⟨R,hR,him⟩ := factor_common_window d a hd he hi
  obtain ⟨M,hM⟩ := factor_real_decay d (smoothPolarCoefficients_smooth c) he hi 2
  have hs := compactInverse_tsupport_subset_axis_window
    (differentiable_paperFT_of_compact f.1.1.2.1.continuous f.1.1.2.2)
    he (paperFT_subquadratic f.1.1) hR hM him
  rwa [compactInverse_eq_of_paperFT f.1.1.2.1 f.1.1.2.2 he (fun _ => rfl)] at hs

/-- Compact interior supports have a common strict margin, and exact
scalarization retains that margin. -/
theorem scalarization_tsupport_subset_interior (c : SmoothEvenPolarTestFn →₀ ℝ≥0)
    (a : {r : ℝ // 0<r})
    (hw : ∀ f ∈ c.support,tsupport f.1.1.1 ⊆ Ioo (-a.1) a.1)
    (f : SmoothEvenPolarTestFn)
    (hp : EF.weilTest f.1.1.1 f.1.1.1=polarMixtureProfile (smoothPolarCoefficients c)) :
    tsupport f.1.1.1 ⊆ Ioo (-a.1) a.1 := by
  let K := insert (0 : ℝ) (⋃ g ∈ c.support,tsupport g.1.1.1)
  have hK : IsCompact K :=
    (c.support.isCompact_biUnion fun g _ => g.1.1.2.2.isCompact).insert 0
  obtain ⟨x,hx,hm⟩ := hK.exists_isMaxOn ⟨0,mem_insert _ _⟩ continuous_abs.continuousOn
  have hxa : |x| < a.1 := by
    rcases mem_insert_iff.mp hx with rfl | hx
    · simpa only [abs_zero] using a.2
    · obtain ⟨g,hg,hx⟩ := mem_iUnion₂.mp hx
      exact abs_lt.mpr (hw g hg hx)
  have hs : ∀ g ∈ c.support,tsupport g.1.1.1 ⊆ Icc (-|x|) |x| := by
    intro g hg u hu
    exact abs_le.mp (hm (mem_insert_of_mem 0 (mem_iUnion₂.mpr ⟨g,hg,hu⟩)))
  have hf := scalarization_tsupport_subset c ⟨|x|,abs_nonneg x⟩ hs f hp
  intro u hu
  exact ⟨lt_of_lt_of_le (neg_lt_neg hxa) (hf hu).1,lt_of_le_of_lt (hf hu).2 hxa⟩

private theorem profile_map_sources {ι : Type*} (F : ι → SmoothEvenPolarTestFn)
    (c : ι →₀ ℝ≥0) :
    polarMixtureProfile (smoothPolarCoefficients (c.mapDomain F))=
      c.sum (fun i t => (t : ℝ) • EF.weilTest (F i).1.1.1 (F i).1.1.1) := by
  funext u
  unfold polarMixtureProfile smoothPolarCoefficients
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ s t => by push_cast; ring)]
  erw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ s t => by push_cast; ring)]
  simp only [Finsupp.sum,Finset.sum_apply,Pi.smul_apply,Complex.real_smul]

/-- An actual smooth even pole-free source in the prescribed closed window. -/
def WindowedSmoothEvenPolarTestFn (a : ℝ≥0) : Type :=
  {f : SmoothEvenPolarTestFn // tsupport f.1.1.1 ⊆ Icc (-(a : ℝ)) a}

def windowProfile {a : ℝ≥0} (f : WindowedSmoothEvenPolarTestFn a) : ℝ → ℂ :=
  EF.weilTest f.1.1.1.1 f.1.1.1.1

def windowMixtureProfile (a : ℝ≥0) (c : WindowedSmoothEvenPolarTestFn a →₀ ℝ≥0) : ℝ → ℂ :=
  c.sum fun f t => (t : ℝ) • windowProfile f

/-- **Fixed-window purification.** Every positive finite mixture of actual
smooth even pole-free sources has one such source in the same window with
exactly its entire autocorrelation. Coefficients and sources are input data;
there are no positivity, RH, or factor-admission premises. -/
theorem exists_window_purification (a : ℝ≥0) (c : WindowedSmoothEvenPolarTestFn a →₀ ℝ≥0) :
    ∃ f : WindowedSmoothEvenPolarTestFn a,windowProfile f=windowMixtureProfile a c := by
  let d : SmoothEvenPolarTestFn →₀ ℝ≥0 := c.mapDomain Subtype.val
  have hd : ∀ f ∈ d.support,tsupport f.1.1.1 ⊆ Icc (-(a : ℝ)) a := by
    intro f hf
    let e : WindowedSmoothEvenPolarTestFn a ↪ SmoothEvenPolarTestFn :=
      ⟨Subtype.val,Subtype.val_injective⟩
    change f ∈ (c.mapDomain e).support at hf
    rw [Finsupp.support_mapDomain_embedding] at hf
    obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hf
    exact g.2
  obtain ⟨f,hf⟩ := exists_smoothPolar_exact_autocorrelation d
  refine ⟨⟨f,scalarization_tsupport_subset d a hd f hf⟩,hf.trans ?_⟩
  exact profile_map_sources Subtype.val c

@[simp] theorem windowMixtureProfile_single (a : ℝ≥0)
    (f : WindowedSmoothEvenPolarTestFn a) (t : ℝ≥0) :
    windowMixtureProfile a (Finsupp.single f t)=(t : ℝ) • windowProfile f := by
  classical
  simp [windowMixtureProfile]

theorem windowMixtureProfile_add (a : ℝ≥0)
    (c d : WindowedSmoothEvenPolarTestFn a →₀ ℝ≥0) :
    windowMixtureProfile a (c+d)=windowMixtureProfile a c+windowMixtureProfile a d := by
  classical
  unfold windowMixtureProfile
  exact Finsupp.sum_add_index (fun _ => by simp) (fun _ s t => by simp [add_smul])

/-- The actual fixed-window source image already equals its finite positive
mixture image. No closure, limiting aperture, or rank relaxation is needed. -/
theorem window_profile_range_eq_mixture_range (a : ℝ≥0) :
    Set.range (windowProfile (a := a))=Set.range (windowMixtureProfile a) := by
  ext P
  constructor
  · rintro ⟨f,rfl⟩
    exact ⟨Finsupp.single f 1,by simp⟩
  · rintro ⟨c,rfl⟩
    exact exists_window_purification a c

/-- A fixed aperture has a convex actual profile image, so imposing any
affine profile constraints does not create a finite-mixture rank gap. -/
theorem convex_window_profile_range (a : ℝ≥0) :
    Convex ℝ (Set.range (windowProfile (a := a))) := by
  rintro P ⟨f,rfl⟩ Q ⟨g,rfl⟩ s t hs ht _
  obtain ⟨h,hh⟩ := exists_window_purification a
    (Finsupp.single f ⟨s,hs⟩+Finsupp.single g ⟨t,ht⟩)
  rw [windowMixtureProfile_add,windowMixtureProfile_single,windowMixtureProfile_single] at hh
  exact ⟨h,hh⟩

/-- The compact interior domain used by aperture variational problems. -/
def InteriorWindowedSmoothEvenPolarTestFn (a : {r : ℝ // 0<r}) : Type :=
  {f : SmoothEvenPolarTestFn // tsupport f.1.1.1 ⊆ Ioo (-a.1) a.1}

/-- **Interior-domain purification.** Exact rank removal also preserves
strict interior support, so it stays within the original compact smooth core. -/
theorem exists_interior_window_purification (a : {r : ℝ // 0<r})
    (c : InteriorWindowedSmoothEvenPolarTestFn a →₀ ℝ≥0) :
    ∃ f : InteriorWindowedSmoothEvenPolarTestFn a,
      EF.weilTest f.1.1.1.1 f.1.1.1.1=
        c.sum (fun g t => (t : ℝ) • EF.weilTest g.1.1.1.1 g.1.1.1.1) := by
  let d : SmoothEvenPolarTestFn →₀ ℝ≥0 := c.mapDomain Subtype.val
  have hd : ∀ f ∈ d.support,tsupport f.1.1.1 ⊆ Ioo (-a.1) a.1 := by
    intro f hf
    let e : InteriorWindowedSmoothEvenPolarTestFn a ↪ SmoothEvenPolarTestFn :=
      ⟨Subtype.val,Subtype.val_injective⟩
    change f ∈ (c.mapDomain e).support at hf
    rw [Finsupp.support_mapDomain_embedding] at hf
    obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hf
    exact g.2
  obtain ⟨f,hf⟩ := exists_smoothPolar_exact_autocorrelation d
  exact ⟨⟨f,scalarization_tsupport_subset_interior d a hd f hf⟩,
    hf.trans (profile_map_sources Subtype.val c)⟩

end RHTower.EvenSector
