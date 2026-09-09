import GaloisForLFunctions.RHTower.GomesClarkObservationReconstruction

/-!
# Reconstruction across collapse of the movable Clark anchor

Experimental corpus application of arXiv:2607.24901's reconstruction / invisible-sector
viewpoint to `clarkSquaredKernel`. A nonzero anchor has a parameter at which its compactified
kernel is identically one, so its own observations supply total mass. Away from that parameter
they recover the Stieltjes bank; continuity fills the omitted value. At zero anchor the exact
endpoint-one ambiguity returns. The sign of the anchor remains invisible because the corpus
kernel depends on its square.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- Continuous extension of the movable squared Clark kernel to the compact source space. -/
def gomesClarkAnchorTest (c : ℝ) (t : Set.Ioi (-1 : ℝ)) : C(HausdorffSourceSpace, ℝ) :=
  ⟨fun y => 1 + (c ^ 2 - 1 - (t : ℝ)) * stieltjesKernel t y,
    continuous_const.add (continuous_const.mul (gomesHausdorffStieltjesTest t).continuous)⟩

/-- The movable-anchor observation bank, including its compactification endpoint. -/
def gomesClarkAnchorRecord (c : ℝ) (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) : ℝ :=
  ∫ y, (1 + (c ^ 2 - 1 - (t : ℝ)) * stieltjesKernel t y) ∂(μ : Measure HausdorffSourceSpace)

/-- Exact rational form of the compactified movable-anchor test. -/
theorem gomesClarkAnchorTest_fraction (c : ℝ) (t : Set.Ioi (-1 : ℝ)) (y : HausdorffSourceSpace) :
    gomesClarkAnchorTest c t y =
      (1 + (c ^ 2 - 1) * (y : ℝ)) / (1 + (t : ℝ) * (y : ℝ)) := by
  have hd := ne_of_gt (gomesHausdorffStieltjes_denominator_pos t y)
  dsimp [gomesClarkAnchorTest, stieltjesKernel]
  field_simp [hd]
  ring

/-- The extension agrees with the corpus's literal squared Clark kernel at every positive coordinate. -/
theorem gomesClarkAnchorTest_existingKernel (c : ℝ) (t : Set.Ioi (-1 : ℝ))
    (y : GomesHausdorffVisibleSpace) :
    clarkSquaredKernel c (1 + (t : ℝ)) ((1 - (y.val : ℝ)) / (y.val : ℝ)) =
      gomesClarkAnchorTest c t y := by
  have hy : (y.val : ℝ) ≠ 0 := by
    intro h
    exact y.property (Subtype.ext h)
  have hd := ne_of_gt (gomesHausdorffStieltjes_denominator_pos t y.val)
  have he : (1 - (y.val : ℝ)) / (y.val : ℝ) + (1 + (t : ℝ)) =
      (1 + (t : ℝ) * (y.val : ℝ)) / (y.val : ℝ) := by
    field_simp [hy]
    ring
  rw [clarkSquaredKernel, he, gomesClarkAnchorTest_fraction]
  field_simp [hy, hd]
  ring

/-- Collapsing the anchor gives exactly the existing fixed Clark bank. -/
theorem gomesClarkAnchorRecord_zero (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord 0 μ = gomesClarkFixedRecord μ := by
  funext t
  unfold gomesClarkAnchorRecord gomesClarkFixedRecord
  congr 1
  funext y
  ring

/-- The movable bank separates into total mass and one Stieltjes value at each parameter. -/
theorem gomesClarkAnchorRecord_mass_split (c : ℝ) (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkAnchorRecord c μ t = (μ.mass : ℝ) +
      (c ^ 2 - 1 - (t : ℝ)) * gomesHausdorffStieltjesRecord μ t := by
  have hk : Integrable (stieltjesKernel (t : ℝ)) (μ : Measure HausdorffSourceSpace) :=
    integrable_of_continuous _ (gomesHausdorffStieltjesTest t).continuous
  rw [gomesClarkAnchorRecord, integral_add (integrable_const 1) (hk.const_mul _),
    integral_const_mul, integral_const]
  simp only [smul_eq_mul, mul_one]
  rfl

/-- Every nonzero anchor has an admissible parameter measuring precisely the total source mass. -/
def gomesClarkAnchorBaseParameter (c : {c : ℝ // c ≠ 0}) : Set.Ioi (-1 : ℝ) :=
  ⟨(c : ℝ) ^ 2 - 1, by
    change (-1 : ℝ) < (c : ℝ) ^ 2 - 1
    have hc := sq_pos_of_ne_zero c.property
    linarith⟩

/-- At its own base parameter, a nonzero anchor reads the entire source mass. -/
theorem gomesClarkAnchorRecord_base (c : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord c μ (gomesClarkAnchorBaseParameter c) = μ.mass := by
  rw [gomesClarkAnchorRecord_mass_split]
  simp [gomesClarkAnchorBaseParameter]

/-- Exact reconstruction boundary: only a zero anchor permits an invisible endpoint-one sector. -/
theorem gomesClarkAnchorRecord_classification (c : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord c ν ↔
      μ = ν ∨ (c = 0 ∧ gomesClarkFixedRecord μ = gomesClarkFixedRecord ν) := by
  constructor
  · intro h
    by_cases hc : c = 0
    · right
      refine ⟨hc, ?_⟩
      simpa only [hc, gomesClarkAnchorRecord_zero] using h
    · left
      let a := gomesClarkAnchorBaseParameter ⟨c, hc⟩
      have hm : (μ.mass : ℝ) = (ν.mass : ℝ) := by
        have ha := congrFun h a
        rw [gomesClarkAnchorRecord_mass_split, gomesClarkAnchorRecord_mass_split] at ha
        simpa [a, gomesClarkAnchorBaseParameter] using ha
      apply (gomesHausdorffStieltjes_mass_reconstruction μ ν).mp
      refine ⟨?_, by exact_mod_cast hm⟩
      apply (gomesHausdorffStieltjesRecord_eq_iff_offPoint μ ν a).mpr
      intro t
      have ht : c ^ 2 - 1 - (t.val : ℝ) ≠ 0 := by
        intro hz
        apply t.property
        apply Subtype.ext
        exact (sub_eq_zero.mp hz).symm
      have hv := congrFun h t.val
      rw [gomesClarkAnchorRecord_mass_split, gomesClarkAnchorRecord_mass_split, hm] at hv
      exact mul_left_cancel₀ ht (add_left_cancel hv)
  · rintro (rfl | ⟨rfl, h⟩)
    · rfl
    · simpa only [gomesClarkAnchorRecord_zero] using h

/-- The movable bank is injective on all finite sources exactly when the anchor is nonzero. -/
theorem gomesClarkAnchorRecord_injective_iff (c : ℝ) :
    Function.Injective (gomesClarkAnchorRecord c) ↔ c ≠ 0 := by
  constructor
  · intro hi hc
    subst c
    have hz : gomesClarkAnchorRecord 0 (0 : FiniteMeasure HausdorffSourceSpace) =
        gomesClarkAnchorRecord 0 gomesHausdorffOneAtom := by
      rw [gomesClarkAnchorRecord_zero, gomesClarkAnchorRecord_zero]
      simpa using (gomesClarkFixedRecord_oneCompletion
        (0 : FiniteMeasure HausdorffSourceSpace) 1).symm
    have he := hi hz
    have hu := congrArg (fun μ : FiniteMeasure HausdorffSourceSpace =>
      (μ : Measure HausdorffSourceSpace) Set.univ) he
    simp [gomesHausdorffOneAtom] at hu
  · intro hc μ ν h
    rcases (gomesClarkAnchorRecord_classification c μ ν).mp h with he | ⟨hz, _⟩
    · exact he
    · exact False.elim (hc hz)

/-- The formerly invisible endpoint-one atom is measured with exact strength `c²/(1+t)`. -/
theorem gomesClarkAnchorRecord_oneAtom (c : ℝ) (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkAnchorRecord c gomesHausdorffOneAtom t = c ^ 2 / (1 + (t : ℝ)) := by
  change (∫ y, (1 + (c ^ 2 - 1 - (t : ℝ)) * stieltjesKernel t y)
    ∂Measure.dirac gomesHausdorffOne) = _
  rw [integral_dirac]
  change gomesClarkAnchorTest c t gomesHausdorffOne = _
  rw [gomesClarkAnchorTest_fraction]
  simp [gomesHausdorffOne]

/-- Reversing the anchor sign preserves every source observation. -/
theorem gomesClarkAnchorRecord_neg (c : ℝ) (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord (-c) μ = gomesClarkAnchorRecord c μ := by
  funext t
  simp only [gomesClarkAnchorRecord, neg_sq]

/-- Across all sources, the exact surviving anchor ambiguity is its sign. -/
theorem gomesClarkAnchorRecord_parameter_classification (c d : ℝ) :
    (∀ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord d μ) ↔ c = d ∨ c = -d := by
  constructor
  · intro h
    have hp := congrFun (h gomesHausdorffOneAtom) (⟨0, by change (-1 : ℝ) < 0; linarith⟩ : Set.Ioi (-1 : ℝ))
    rw [gomesClarkAnchorRecord_oneAtom, gomesClarkAnchorRecord_oneAtom] at hp
    have hs : c ^ 2 = d ^ 2 := by simpa using hp
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hs
  · rintro (rfl | rfl) μ
    · rfl
    · exact gomesClarkAnchorRecord_neg d μ

/-- The entire movable bank is continuous, including its mass-reading parameter. -/
theorem gomesClarkAnchorRecord_continuous (c : ℝ) (μ : FiniteMeasure HausdorffSourceSpace) :
    Continuous (gomesClarkAnchorRecord c μ) := by
  have he : gomesClarkAnchorRecord c μ = fun (t : Set.Ioi (-1 : ℝ)) => (μ.mass : ℝ) +
      (c ^ 2 - 1 - (t : ℝ)) * gomesHausdorffStieltjesRecord μ t :=
    funext (gomesClarkAnchorRecord_mass_split c μ)
  rw [he]
  exact continuous_const.add ((continuous_const.sub continuous_subtype_val).mul
    (gomesHausdorffStieltjesRecord_continuous μ))

/-- Deleting any one anchor-bank sample preserves its exact observation equivalence. -/
theorem gomesClarkAnchorRecord_eq_iff_offPoint (c : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) (p : Set.Ioi (-1 : ℝ)) :
    gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord c ν ↔
      ∀ t : {t : Set.Ioi (-1 : ℝ) // t ≠ p},
        gomesClarkAnchorRecord c μ t = gomesClarkAnchorRecord c ν t := by
  constructor
  · intro h t
    exact congrFun h t
  · intro h
    apply Continuous.ext_on (dense_compl_singleton p)
      (gomesClarkAnchorRecord_continuous c μ) (gomesClarkAnchorRecord_continuous c ν)
    intro t ht
    exact h ⟨t, ht⟩

end RHTower
