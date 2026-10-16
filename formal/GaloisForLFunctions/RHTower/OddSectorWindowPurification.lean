import GaloisForLFunctions.RHTower.OddSectorSmoothSourceScalarization

/-!
# Exact purification in the original odd source window

Finite positive odd autocorrelation mixtures are single actual odd sources
without aperture enlargement. Closed windows and strict interior windows are
both retained. Consequently the fixed-window profile image is already convex;
all linear profile constraints and energies survive rank removal exactly.
-/

open Complex Set MeasureTheory Zeta23
open scoped NNReal

noncomputable section
namespace RHTower.OddSector

def WindowedSmoothOddTestFn (R : ℝ≥0) : Type :=
  {f : SmoothOddTestFn // tsupport f.1.1.1 ⊆ Icc (-(R : ℝ)) R}

def windowProfile {R : ℝ≥0} (f : WindowedSmoothOddTestFn R) : ℝ → ℂ :=
  EF.weilTest f.1.1.1.1 f.1.1.1.1

/-- Exact finite-mixture rank removal inside the prescribed closed interval. -/
theorem exists_window_purification {N : ℕ} (R : ℝ≥0)
    (F : Fin N → WindowedSmoothOddTestFn R) (a : Fin N → ℝ≥0) :
    ∃ f : WindowedSmoothOddTestFn R,
      windowProfile f=oddMixtureProfile (fun i => (F i).1) a := by
  obtain ⟨f,hf,hw⟩ := exists_smoothOdd_exact_autocorrelation_with_window
    (fun i => (F i).1) a
  exact ⟨⟨f,hw R (fun i => (F i).2)⟩,hf⟩

/-- The actual odd-source image has no finite-mixture convexification gap. -/
theorem convex_window_profile_range (R : ℝ≥0) :
    Convex ℝ (Set.range (windowProfile (R := R))) := by
  rintro P ⟨f,rfl⟩ Q ⟨g,rfl⟩ s t hs ht _
  obtain ⟨h,hh⟩ := exists_window_purification R ![f,g] ![⟨s,hs⟩,⟨t,ht⟩]
  refine ⟨h,hh.trans ?_⟩
  funext u
  simp only [oddMixtureProfile,Fin.sum_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Pi.add_apply,Pi.smul_apply,
    Complex.real_smul,windowProfile]
  rfl

def InteriorWindowedSmoothOddTestFn (R : {r : ℝ // 0<r}) : Type :=
  {f : SmoothOddTestFn // tsupport f.1.1.1 ⊆ Ioo (-R.1) R.1}

/-- Compact interior mixtures retain a common strict support margin. -/
theorem exists_interior_window_purification {N : ℕ} (R : {r : ℝ // 0<r})
    (F : Fin N → InteriorWindowedSmoothOddTestFn R) (a : Fin N → ℝ≥0) :
    ∃ f : InteriorWindowedSmoothOddTestFn R,
      EF.weilTest f.1.1.1.1 f.1.1.1.1=oddMixtureProfile (fun i => (F i).1) a := by
  classical
  let K := insert (0 : ℝ) (⋃ i ∈ (Finset.univ : Finset (Fin N)),tsupport (F i).1.1.1.1)
  have hK : IsCompact K :=
    (Finset.univ.isCompact_biUnion fun i _ => (F i).1.1.1.2.2.isCompact).insert 0
  obtain ⟨x,hx,hm⟩ := hK.exists_isMaxOn ⟨0,mem_insert _ _⟩ continuous_abs.continuousOn
  have hxa : |x|<R.1 := by
    rcases mem_insert_iff.mp hx with rfl | hx
    · simpa only [abs_zero] using R.2
    · obtain ⟨i,-,hi⟩ := mem_iUnion₂.mp hx
      exact abs_lt.mpr ((F i).2 hi)
  have hs (i : Fin N) : tsupport (F i).1.1.1.1 ⊆ Icc (-|x|) |x| := by
    intro u hu
    exact abs_le.mp (hm (mem_insert_of_mem 0
      (mem_iUnion₂.mpr ⟨i,Finset.mem_univ i,hu⟩)))
  obtain ⟨f,hf,hw⟩ := exists_smoothOdd_exact_autocorrelation_with_window
    (fun i => (F i).1) a
  have hfw := hw ⟨|x|,abs_nonneg x⟩ hs
  refine ⟨⟨f,?_⟩,hf⟩
  intro u hu
  exact ⟨lt_of_lt_of_le (neg_lt_neg hxa) (hfw hu).1,
    lt_of_le_of_lt (hfw hu).2 hxa⟩

end RHTower.OddSector
