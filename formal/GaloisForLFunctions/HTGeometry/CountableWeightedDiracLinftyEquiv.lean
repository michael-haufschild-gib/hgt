import GaloisForLFunctions.HTGeometry.CountableWeightedDirac
import Mathlib.Analysis.Normed.Lp.LpEquiv

/-!
# Bounded sequences as `L∞` classes on a countable weighted Dirac support

For an injective sequence of atoms with strictly positive weights, restriction to the atoms and
extension by zero are inverse real-linear isometries between literal bounded real sequences and
`L∞` classes for the corresponding weighted Dirac measure.  Strict positivity is essential:
it upgrades almost-everywhere identities and bounds to pointwise statements at every listed atom.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal bounded real sequences with the supremum norm. -/
abbrev BoundedRealSequence := lp (fun _ : ℕ => ℝ) ∞

variable {ε atoms : ℕ → ℝ}

private noncomputable def weightedDiracExtension
    (atoms : ℕ → ℝ) (u : BoundedRealSequence) (x : ℝ) : ℝ := by
  classical
  exact if hx : x ∈ Set.range atoms then u (Function.invFun atoms x) else 0

private theorem weightedDiracExtension_at (hinj : Function.Injective atoms)
    (u : BoundedRealSequence) (n : ℕ) :
    weightedDiracExtension (atoms := atoms) u (atoms n) = u n := by
  simp [weightedDiracExtension, Function.leftInverse_invFun hinj n]

private theorem measurable_weightedDiracExtension (u : BoundedRealSequence) :
    Measurable (weightedDiracExtension (atoms := atoms) u) := by
  refine measurable_zero.measurable_of_countable_ne ?_
  refine (Set.countable_range atoms).mono ?_
  intro x hx
  by_contra hxr
  apply hx
  simp [weightedDiracExtension, hxr]

private theorem norm_weightedDiracExtension_le (u : BoundedRealSequence) (x : ℝ) :
    ‖weightedDiracExtension (atoms := atoms) u x‖ ≤ ‖u‖ := by
  by_cases hx : x ∈ Set.range atoms
  · simp only [weightedDiracExtension, dif_pos hx]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero u _
  · simp [weightedDiracExtension, hx]

private theorem memLp_weightedDiracExtension (u : BoundedRealSequence) :
    MemLp (weightedDiracExtension (atoms := atoms) u) ∞
      (HTGeometry.countableWeightedDirac ε atoms) :=
  memLp_top_of_bound (measurable_weightedDiracExtension (atoms := atoms) u).aestronglyMeasurable
    ‖u‖ (Filter.Eventually.of_forall (norm_weightedDiracExtension_le (atoms := atoms) u))

private def boundedSequenceToDiracLp (u : BoundedRealSequence) :
    Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms) :=
  (memLp_weightedDiracExtension (ε := ε) (atoms := atoms) u).toLp
    (weightedDiracExtension (atoms := atoms) u)

private theorem ae_property_at_positive_atom
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    {P : ℝ → Prop} (hP : ∀ᵐ x ∂(HTGeometry.countableWeightedDirac ε atoms), P x)
    (n : ℕ) : P (atoms n) := by
  rw [ae_iff] at hP
  by_contra hn
  have hsingle : HTGeometry.countableWeightedDirac ε atoms {atoms n} = 0 :=
    measure_mono_null (by rintro x rfl; exact hn) hP
  rw [HTGeometry.countableWeightedDirac_singleton ε hinj n] at hsingle
  exact (ENNReal.ofReal_pos.mpr (hε n)).ne' hsingle

private theorem boundedSequenceToDiracLp_at
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    (u : BoundedRealSequence) (n : ℕ) :
    boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u (atoms n) = u n := by
  have hae := (memLp_weightedDiracExtension (ε := ε) (atoms := atoms) u).coeFn_toLp
  exact (ae_property_at_positive_atom hinj hε hae n).trans
    (weightedDiracExtension_at hinj u n)

private theorem diracLp_ae_norm_le (f : Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms)) :
    ∀ᵐ x ∂(HTGeometry.countableWeightedDirac ε atoms), ‖f x‖ ≤ ‖f‖ := by
  simpa only [Lp.norm_def, lpNorm, if_pos (Lp.memLp f).1] using
    ae_le_lpNorm_exponent_top (Lp.memLp f)

private theorem diracLp_norm_at_le
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    (f : Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms)) (n : ℕ) :
    ‖f (atoms n)‖ ≤ ‖f‖ :=
  ae_property_at_positive_atom hinj hε (diracLp_ae_norm_le f) n

private def diracLpToBoundedSequence
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    (f : Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms)) :
    BoundedRealSequence :=
  ⟨fun n => f (atoms n), memℓp_infty_iff.mpr
    ⟨‖f‖, by rintro _ ⟨n, rfl⟩; exact diracLp_norm_at_le hinj hε f n⟩⟩

private theorem countableWeightedDirac_compl_range
    (ε atoms : ℕ → ℝ) :
    HTGeometry.countableWeightedDirac ε atoms (Set.range atoms)ᶜ = 0 := by
  rw [HTGeometry.countableWeightedDirac_apply ε atoms
    ((Set.countable_range atoms).measurableSet.compl)]
  simp

private theorem boundedSequenceToDiracLp_diracLpToBoundedSequence
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    (f : Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms)) :
    boundedSequenceToDiracLp (ε := ε) (atoms := atoms)
      (diracLpToBoundedSequence hinj hε f) = f := by
  apply Lp.ext
  have hrange : ∀ᵐ x ∂(HTGeometry.countableWeightedDirac ε atoms), x ∈ Set.range atoms :=
    ae_iff.mpr (by
      change HTGeometry.countableWeightedDirac ε atoms (Set.range atoms)ᶜ = 0
      exact countableWeightedDirac_compl_range ε atoms)
  filter_upwards [
    (memLp_weightedDiracExtension (ε := ε) (atoms := atoms)
      (diracLpToBoundedSequence hinj hε f)).coeFn_toLp,
    hrange
  ] with x hx hxr
  have hx' :
      boundedSequenceToDiracLp (ε := ε) (atoms := atoms)
          (diracLpToBoundedSequence hinj hε f) x =
        weightedDiracExtension atoms (diracLpToBoundedSequence hinj hε f) x := by
    simpa only [boundedSequenceToDiracLp] using hx
  rw [hx']
  simp only [weightedDiracExtension, dif_pos hxr]
  change f (atoms (Function.invFun atoms x)) = f x
  rw [Function.invFun_eq hxr]

private theorem diracLpToBoundedSequence_boundedSequenceToDiracLp
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    (u : BoundedRealSequence) :
    diracLpToBoundedSequence hinj hε
      (boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u) = u := by
  refine Subtype.ext (funext fun n => ?_)
  exact boundedSequenceToDiracLp_at hinj hε u n

private theorem boundedSequenceToDiracLp_add (u v : BoundedRealSequence) :
    boundedSequenceToDiracLp (ε := ε) (atoms := atoms) (u + v) =
      boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u +
        boundedSequenceToDiracLp (ε := ε) (atoms := atoms) v := by
  apply Lp.ext
  filter_upwards [
    (memLp_weightedDiracExtension (ε := ε) (atoms := atoms) (u + v)).coeFn_toLp,
    (memLp_weightedDiracExtension (ε := ε) (atoms := atoms) u).coeFn_toLp,
    (memLp_weightedDiracExtension (ε := ε) (atoms := atoms) v).coeFn_toLp,
    Lp.coeFn_add
      (boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u)
      (boundedSequenceToDiracLp (ε := ε) (atoms := atoms) v)
  ] with x huv hu hv hadd
  have huv' :
      boundedSequenceToDiracLp (ε := ε) (atoms := atoms) (u + v) x =
        weightedDiracExtension atoms (u + v) x := by
    simpa only [boundedSequenceToDiracLp] using huv
  have hu' :
      boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u x =
        weightedDiracExtension atoms u x := by
    simpa only [boundedSequenceToDiracLp] using hu
  have hv' :
      boundedSequenceToDiracLp (ε := ε) (atoms := atoms) v x =
        weightedDiracExtension atoms v x := by
    simpa only [boundedSequenceToDiracLp] using hv
  rw [huv', hadd, Pi.add_apply, hu', hv']
  by_cases hxr : x ∈ Set.range atoms
  · simp [weightedDiracExtension, hxr]
  · simp [weightedDiracExtension, hxr]

private theorem boundedSequenceToDiracLp_smul (c : ℝ) (u : BoundedRealSequence) :
    boundedSequenceToDiracLp (ε := ε) (atoms := atoms) (c • u) =
      c • boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u := by
  apply Lp.ext
  filter_upwards [
    (memLp_weightedDiracExtension (ε := ε) (atoms := atoms) (c • u)).coeFn_toLp,
    (memLp_weightedDiracExtension (ε := ε) (atoms := atoms) u).coeFn_toLp,
    Lp.coeFn_smul c (boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u)
  ] with x hcu hu hsmul
  have hcu' :
      boundedSequenceToDiracLp (ε := ε) (atoms := atoms) (c • u) x =
        weightedDiracExtension atoms (c • u) x := by
    simpa only [boundedSequenceToDiracLp] using hcu
  have hu' :
      boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u x =
        weightedDiracExtension atoms u x := by
    simpa only [boundedSequenceToDiracLp] using hu
  rw [hcu', hsmul, Pi.smul_apply, hu']
  by_cases hxr : x ∈ Set.range atoms
  · simp [weightedDiracExtension, hxr, lp.coeFn_smul]
  · simp [weightedDiracExtension, hxr]

private def boundedSequenceDiracLpLinearEquiv
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n) :
    BoundedRealSequence ≃ₗ[ℝ] Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms) where
  toFun := boundedSequenceToDiracLp
  invFun := diracLpToBoundedSequence hinj hε
  left_inv := diracLpToBoundedSequence_boundedSequenceToDiracLp hinj hε
  right_inv := boundedSequenceToDiracLp_diracLpToBoundedSequence hinj hε
  map_add' := boundedSequenceToDiracLp_add
  map_smul' := boundedSequenceToDiracLp_smul

private theorem norm_boundedSequenceToDiracLp_le (u : BoundedRealSequence) :
    ‖boundedSequenceToDiracLp (ε := ε) (atoms := atoms) u‖ ≤ ‖u‖ := by
  unfold boundedSequenceToDiracLp
  rw [MeasureTheory.Lp.norm_toLp]
  have hbound :
      eLpNorm (weightedDiracExtension atoms u) ∞
          (HTGeometry.countableWeightedDirac ε atoms) ≤ ENNReal.ofReal ‖u‖ := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall (norm_weightedDiracExtension_le (atoms := atoms) u))
  simpa [ENNReal.toReal_ofReal (norm_nonneg u)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

private theorem norm_diracLpToBoundedSequence_le
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    (f : Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms)) :
    ‖diracLpToBoundedSequence hinj hε f‖ ≤ ‖f‖ := by
  rw [lp.norm_eq_ciSup]
  exact Real.iSup_le (fun n => diracLp_norm_at_le hinj hε f n) (norm_nonneg f)

/-- Positive weighted point masses identify literal bounded real sequences isometrically with
`L∞` classes on their countable support. -/
noncomputable def countableWeightedDiracLinftyEquiv
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n) :
    BoundedRealSequence ≃ₗᵢ[ℝ] Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms) :=
  LinearIsometryEquiv.ofBounds
    (boundedSequenceDiracLpLinearEquiv hinj hε)
    norm_boundedSequenceToDiracLp_le
    (norm_diracLpToBoundedSequence_le hinj hε)

@[simp]
theorem countableWeightedDiracLinftyEquiv_apply_at
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    (u : BoundedRealSequence) (n : ℕ) :
    countableWeightedDiracLinftyEquiv hinj hε u (atoms n) = u n :=
  boundedSequenceToDiracLp_at hinj hε u n

@[simp]
theorem countableWeightedDiracLinftyEquiv_symm_apply
    (hinj : Function.Injective atoms) (hε : ∀ n, 0 < ε n)
    (f : Lp ℝ ∞ (HTGeometry.countableWeightedDirac ε atoms)) (n : ℕ) :
    ((countableWeightedDiracLinftyEquiv hinj hε).symm f : ℕ → ℝ) n = f (atoms n) :=
  rfl

end

end GaloisForLFunctions.HTGeometry
