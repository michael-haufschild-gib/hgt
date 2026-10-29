import GaloisForLFunctions.HTGeometry.NumberFieldIdealCovolume
import GaloisForLFunctions.HTGeometry.IntrinsicLatticeTheta

/-!
# Gaussian theta inversion for fractional ideals

The theta series sums over actual fractional-ideal elements in trace-normalized
Minkowski coordinates. The weighted embedding identifies these elements with the
lattice points, while its conjugate identifies the arithmetic trace dual with the
intrinsic integer dual. Conjugation preserves the Gaussian, so intrinsic lattice
inversion gives the exact ideal-norm, discriminant, and field-degree constants.
-/

noncomputable section
open NumberField NumberField.InfinitePlace Module
open scoped Classical NumberField

namespace GaloisForLFunctions.HTGeometry
open IntegerLatticePoisson

variable {K : Type*} [Field K] [NumberField K]
local notation "ι" => numberFieldMixedRealCoordinateIndex K
local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- An actual ideal element is equivalent to its weighted lattice point. -/
def numberFieldIdealLatticeEquiv (I : FIˣ) : (I : FI) ≃ numberFieldTraceLattice I :=
  Equiv.ofBijective
    (fun a => ⟨numberFieldTraceRealCoordinates (mixedEmbedding K (a : K)),
      (mem_numberFieldTraceLattice I).mpr ⟨a, a.property, rfl⟩⟩)
    ⟨by
      intro a b h
      apply Subtype.ext
      apply NumberField.mixedEmbedding_injective K
      apply (numberFieldTraceRealCoordinates (K := K)).injective
      exact congrArg Subtype.val h,
    by
      intro x
      rcases (mem_numberFieldTraceLattice I).mp x.property with ⟨a, ha, hax⟩
      exact ⟨⟨a, ha⟩, Subtype.ext hax⟩⟩

/-- Trace-dual ideal elements correspond to intrinsic dual-lattice points. -/
def numberFieldDualIdealLatticeEquiv (I : FIˣ) :
    FractionalIdeal.dual ℤ ℚ (I : FI) ≃ DualZLattice.dual (numberFieldTraceLattice I) :=
  Equiv.ofBijective
    (fun a => ⟨numberFieldTraceRealCoordinates
      (numberFieldMixedConjugation (mixedEmbedding K (a : K))),
      (mem_dual_numberFieldTraceLattice I).mpr ⟨a, a.property, rfl⟩⟩)
    ⟨by
      intro a b h
      apply Subtype.ext
      apply NumberField.mixedEmbedding_injective K
      apply (numberFieldMixedConjugation (K := K)).injective
      apply (numberFieldTraceRealCoordinates (K := K)).injective
      exact congrArg Subtype.val h,
    by
      intro x
      rcases (mem_dual_numberFieldTraceLattice I).mp x.property with ⟨a, ha, hax⟩
      exact ⟨⟨a, ha⟩, Subtype.ext hax⟩⟩

/-- Complex conjugation preserves the trace-normalized Euclidean squared norm. -/
theorem norm_sq_traceCoordinates_conjugation (z : mixedEmbedding.mixedSpace K) :
    ‖numberFieldTraceCoordinates (numberFieldMixedConjugation z)‖ ^ 2 =
      ‖numberFieldTraceCoordinates z‖ ^ 2 := by
  have hinv : numberFieldMixedConjugation (numberFieldMixedConjugation z) = z :=
    (numberFieldMixedConjugation (K := K)).apply_symm_apply z
  have h := inner_numberFieldTraceCoordinates_conjugate (numberFieldMixedConjugation z) z
  have h' := inner_numberFieldTraceCoordinates_conjugate z (numberFieldMixedConjugation z)
  rw [real_inner_self_eq_norm_sq] at h
  rw [hinv, real_inner_self_eq_norm_sq] at h'
  calc
    _ = numberFieldMixedTrace (numberFieldMixedConjugation z * z) := h
    _ = numberFieldMixedTrace (z * numberFieldMixedConjugation z) := congrArg _ (mul_comm _ _)
    _ = _ := h'.symm

/-- Real dimension of the weighted coordinate space equals the field degree. -/
theorem numberFieldTraceCoordinates_finrank : Module.finrank ℝ E = Module.finrank ℚ K :=
  (numberFieldTraceCoordinates (K := K)).toLinearEquiv.finrank_eq.symm.trans
    (mixedEmbedding.finrank K)

/-- The trace-normalized Gaussian theta series of a fractional ideal. -/
def numberFieldIdealTheta (I : FI) (t : ℝ) : ℝ :=
  ∑' a : I, Real.exp (-(Real.pi * t) *
    ‖numberFieldTraceCoordinates (mixedEmbedding K (a : K))‖ ^ 2)

theorem numberFieldIdealTheta_eq_intrinsic (I : FIˣ) (t : ℝ) :
    numberFieldIdealTheta (I : FI) t = intrinsicLatticeTheta (numberFieldTraceLattice I) t := by
  unfold numberFieldIdealTheta intrinsicLatticeTheta
  exact (numberFieldIdealLatticeEquiv I).tsum_eq
    (fun x : numberFieldTraceLattice I =>
      Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (x : X)‖ ^ 2))

theorem intrinsicLatticeTheta_dual_eq_idealTheta (I : FIˣ) (t : ℝ) :
    intrinsicLatticeTheta (DualZLattice.dual (numberFieldTraceLattice I)) t =
      numberFieldIdealTheta (FractionalIdeal.dual ℤ ℚ (I : FI)) t := by
  calc
    _ = ∑' a : FractionalIdeal.dual ℤ ℚ (I : FI), Real.exp (-(Real.pi * t) *
        ‖numberFieldTraceCoordinates (numberFieldMixedConjugation
          (mixedEmbedding K (a : K)))‖ ^ 2) := by
      exact ((numberFieldDualIdealLatticeEquiv I).tsum_eq
        (fun x => Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (x : X)‖ ^ 2))).symm
    _ = _ := by
      apply tsum_congr
      intro a
      rw [norm_sq_traceCoordinates_conjugation]

private theorem span_trace_basis_reindex (I : FIˣ)
    (e : Free.ChooseBasisIndex ℤ I ≃ ι) :
    Submodule.span ℤ (Set.range ((numberFieldTraceLatticeBasis I).reindex e)) =
      numberFieldTraceLattice I := by
  have hrange : Set.range ((numberFieldTraceLatticeBasis I).reindex e) =
      Set.range (numberFieldTraceLatticeBasis I) := by
    ext x
    simp only [Basis.coe_reindex, Function.comp_apply, Set.mem_range]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩
  rw [hrange, span_numberFieldTraceLatticeBasis]

private theorem summable_idealTheta_of_indexEquiv (I : FIˣ)
    (e : Free.ChooseBasisIndex ℤ I ≃ ι) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : (I : FI) => Real.exp (-(Real.pi * t) *
      ‖numberFieldTraceCoordinates (mixedEmbedding K (a : K))‖ ^ 2)) := by
  have h := summable_intrinsicLatticeTheta_basis ((numberFieldTraceLatticeBasis I).reindex e) ht
  rw [span_trace_basis_reindex] at h
  exact (numberFieldIdealLatticeEquiv I).summable_iff.mpr h

/-- The actual fractional-ideal Gaussian series converges for every positive parameter. -/
theorem summable_numberFieldIdealTheta (I : FIˣ) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : (I : FI) => Real.exp (-(Real.pi * t) *
      ‖numberFieldTraceCoordinates (mixedEmbedding K (a : K))‖ ^ 2)) :=
  summable_idealTheta_of_indexEquiv I
    ((numberFieldTraceLatticeBasis I).indexEquiv (Pi.basisFun ℝ ι)) ht

private theorem idealTheta_inversion_of_indexEquiv (I : FIˣ)
    (e : Free.ChooseBasisIndex ℤ I ≃ ι) {t : ℝ} (ht : 0 < t) :
    numberFieldIdealTheta (I : FI) t =
      ((FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹ *
        t ^ (-((Module.finrank ℚ K : ℝ) / 2)) *
          numberFieldIdealTheta (FractionalIdeal.dual ℤ ℚ (I : FI)) (1 / t) := by
  have h := intrinsicLatticeTheta_basis_inversion ((numberFieldTraceLatticeBasis I).reindex e) ht
  rw [span_trace_basis_reindex, covolume_numberFieldTraceLattice,
    ← numberFieldIdealTheta_eq_intrinsic, intrinsicLatticeTheta_dual_eq_idealTheta,
    numberFieldTraceCoordinates_finrank] at h
  exact h

/-- Gaussian theta inversion on actual fractional-ideal elements with arithmetic constants. -/
theorem numberFieldIdealTheta_inversion (I : FIˣ) {t : ℝ} (ht : 0 < t) :
    numberFieldIdealTheta (I : FI) t =
      ((FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹ *
        t ^ (-((Module.finrank ℚ K : ℝ) / 2)) *
          numberFieldIdealTheta (FractionalIdeal.dual ℤ ℚ (I : FI)) (1 / t) :=
  idealTheta_inversion_of_indexEquiv I
    ((numberFieldTraceLatticeBasis I).indexEquiv (Pi.basisFun ℝ ι)) ht

end GaloisForLFunctions.HTGeometry
