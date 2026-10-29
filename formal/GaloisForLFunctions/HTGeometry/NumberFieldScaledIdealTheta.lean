import GaloisForLFunctions.HTGeometry.NumberFieldIdealTheta
import GaloisForLFunctions.HTGeometry.DiagonalLatticeScaling
import GaloisForLFunctions.HTGeometry.NumberFieldUnitPlaceLog

/-!
# Fractional-ideal theta with archimedean place parameters

Placewise exponential scaling deforms the trace-normalized ideal lattice by a
positive diagonal map. Its dual has reciprocal scales, and its covolume gains
the exponential of the negative weighted place sum. Poisson inversion therefore
has exact ideal-norm, discriminant, and degree constants. Multiplication by a
global unit cancels translation of the profile by that unit's place logarithms.
-/

noncomputable section
open NumberField NumberField.InfinitePlace Module
open scoped Classical NumberField ComplexConjugate

namespace GaloisForLFunctions.HTGeometry
open IntegerLatticePoisson

variable {K : Type*} [Field K] [NumberField K]
local notation "ι" => numberFieldMixedRealCoordinateIndex K
local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- The actual ideal lattice basis indexed by the mixed real coordinate set. -/
def numberFieldTraceCoordinateBasis (I : FIˣ) : Basis ι ℝ X :=
  (numberFieldTraceLatticeBasis I).reindex
    ((numberFieldTraceLatticeBasis I).indexEquiv (Pi.basisFun ℝ ι))

theorem span_numberFieldTraceCoordinateBasis (I : FIˣ) :
    Submodule.span ℤ (Set.range (numberFieldTraceCoordinateBasis I)) =
      numberFieldTraceLattice I := by
  have hr := EquivLike.range_comp (⇑(numberFieldTraceLatticeBasis I))
    (((numberFieldTraceLatticeBasis I).indexEquiv (Pi.basisFun ℝ ι)).symm)
  rw [numberFieldTraceCoordinateBasis, Basis.coe_reindex, hr, span_numberFieldTraceLatticeBasis]

/-- Positive diagonal place scaling on weighted real coordinates. -/
def numberFieldPlaceDiagonal (y : InfinitePlace K → ℝ) : X ≃ₗ[ℝ] X :=
  positiveDiagonalLinearEquiv (numberFieldMixedCoordinateScale y)
    (numberFieldMixedCoordinateScale_pos y)

theorem numberFieldPlaceDiagonal_apply (y : InfinitePlace K → ℝ) (x : X) :
    numberFieldPlaceDiagonal y x = fun i => numberFieldMixedCoordinateScale y i * x i :=
  positiveDiagonalLinearEquiv_apply _ _ x

theorem numberFieldTraceRealCoordinates_placeScale (y : InfinitePlace K → ℝ)
    (z : mixedEmbedding.mixedSpace K) :
    numberFieldTraceRealCoordinates (numberFieldMixedPlaceScale y z) =
      numberFieldPlaceDiagonal y (numberFieldTraceRealCoordinates z) := by
  rw [numberFieldTraceRealCoordinates_apply, numberFieldPlaceDiagonal_apply,
    numberFieldTraceRealCoordinates_apply, numberFieldMixedRealCoordinates_placeScale]
  funext i
  dsimp only
  ring

omit [NumberField K] in
theorem numberFieldMixedCoordinateScale_neg (y : InfinitePlace K → ℝ) (i : ι) :
    numberFieldMixedCoordinateScale (-y) i = (numberFieldMixedCoordinateScale y i)⁻¹ := by
  rcases i with w | ⟨w, j⟩ <;>
    simp only [numberFieldMixedCoordinateScale, Pi.neg_apply, neg_neg, Real.exp_neg, inv_inv]

theorem numberFieldPlaceDiagonal_reciprocal (y : InfinitePlace K → ℝ) :
    positiveDiagonalLinearEquiv (fun i => (numberFieldMixedCoordinateScale y i)⁻¹)
      (fun i => inv_pos.mpr (numberFieldMixedCoordinateScale_pos y i)) =
        numberFieldPlaceDiagonal (-y) := by
  apply LinearEquiv.ext
  intro x
  rw [positiveDiagonalLinearEquiv_apply, numberFieldPlaceDiagonal_apply]
  funext i
  rw [numberFieldMixedCoordinateScale_neg]

theorem prod_numberFieldMixedCoordinateScale_eq_exp (y : InfinitePlace K → ℝ) :
    ∏ i : ι, numberFieldMixedCoordinateScale y i =
      Real.exp (-(∑ w : InfinitePlace K, (mult w : ℝ) * y w)) := by
  have hscale (i : ι) : numberFieldMixedCoordinateScale y i =
      Real.exp (numberFieldMixedCoordinateLogScale y i) := by
    rcases i with w | ⟨w, j⟩ <;> rfl
  simp_rw [hscale, ← Real.exp_sum]
  rw [sum_numberFieldMixedCoordinateLogScale]

/-- The actual weighted ideal lattice after placewise exponential scaling. -/
def numberFieldScaledTraceLattice (I : FIˣ) (y : InfinitePlace K → ℝ) : Submodule ℤ X :=
  DualZLattice.linearImage (numberFieldPlaceDiagonal y) (numberFieldTraceLattice I)

/-- Restriction of place scaling to an integer lattice and its image. -/
def numberFieldPlaceLatticeEquiv (L : Submodule ℤ X) (y : InfinitePlace K → ℝ) :
    L ≃ₗ[ℤ] DualZLattice.linearImage (numberFieldPlaceDiagonal y) L :=
  ((numberFieldPlaceDiagonal y).restrictScalars ℤ).submoduleMap L

/-- Actual fractional-ideal elements parametrize the scaled lattice bijectively. -/
def numberFieldScaledIdealLatticeEquiv (I : FIˣ) (y : InfinitePlace K → ℝ) :
    (I : FI) ≃ numberFieldScaledTraceLattice I y :=
  (numberFieldIdealLatticeEquiv I).trans
    (numberFieldPlaceLatticeEquiv (numberFieldTraceLattice I) y).toEquiv

theorem toLp_numberFieldScaledIdealLatticeEquiv (I : FIˣ) (y : InfinitePlace K → ℝ)
    (a : (I : FI)) :
    WithLp.toLp 2 (numberFieldScaledIdealLatticeEquiv I y a : X) =
      numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))) := by
  change WithLp.toLp 2 (numberFieldPlaceDiagonal y
    (numberFieldTraceRealCoordinates (mixedEmbedding K (a : K)))) =
      WithLp.toLp 2 (numberFieldTraceRealCoordinates
        (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K))))
  rw [numberFieldTraceRealCoordinates_placeScale]

/-- The mapped ideal basis generates the scaled integer lattice. -/
def numberFieldScaledTraceBasis (I : FIˣ) (y : InfinitePlace K → ℝ) : Basis ι ℝ X :=
  (numberFieldTraceCoordinateBasis I).map (numberFieldPlaceDiagonal y)

theorem span_numberFieldScaledTraceBasis (I : FIˣ) (y : InfinitePlace K → ℝ) :
    Submodule.span ℤ (Set.range (numberFieldScaledTraceBasis I y)) =
      numberFieldScaledTraceLattice I y := by
  rw [numberFieldScaledTraceBasis, ← DualZLattice.linearImage_span,
    span_numberFieldTraceCoordinateBasis]
  rfl

theorem dual_numberFieldScaledTraceLattice (I : FIˣ) (y : InfinitePlace K → ℝ) :
    DualZLattice.dual (numberFieldScaledTraceLattice I y) =
      DualZLattice.linearImage (numberFieldPlaceDiagonal (-y))
        (DualZLattice.dual (numberFieldTraceLattice I)) := by
  change DualZLattice.dual (DualZLattice.linearImage
    (positiveDiagonalLinearEquiv (numberFieldMixedCoordinateScale y)
      (numberFieldMixedCoordinateScale_pos y)) (numberFieldTraceLattice I)) = _
  rw [DualZLattice.dual_positiveDiagonal, numberFieldPlaceDiagonal_reciprocal]

/-- Place scaling multiplies the arithmetic ideal covolume by its exponential determinant. -/
theorem covolume_numberFieldScaledTraceLattice (I : FIˣ) (y : InfinitePlace K → ℝ) :
    ZLattice.covolume (numberFieldScaledTraceLattice I y) =
      Real.exp (-(∑ w : InfinitePlace K, (mult w : ℝ) * y w)) *
        ((FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|) := by
  have h := DualZLattice.covolume_positiveDiagonal_span (numberFieldMixedCoordinateScale y)
    (numberFieldMixedCoordinateScale_pos y) (numberFieldTraceCoordinateBasis I)
  rw [span_numberFieldTraceCoordinateBasis, covolume_numberFieldTraceLattice,
    prod_numberFieldMixedCoordinateScale_eq_exp] at h
  exact h

theorem mem_numberFieldScaledTraceLattice (I : FIˣ) (y : InfinitePlace K → ℝ) {x : X} :
    x ∈ numberFieldScaledTraceLattice I y ↔ ∃ a : K, a ∈ (I : Set K) ∧
      numberFieldTraceRealCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K a)) = x := by
  change (∃ z, z ∈ numberFieldTraceLattice I ∧ numberFieldPlaceDiagonal y z = x) ↔ _
  constructor
  · rintro ⟨z, hz, hzx⟩
    rcases (mem_numberFieldTraceLattice I).mp hz with ⟨a, ha, rfl⟩
    exact ⟨a, ha, by rw [numberFieldTraceRealCoordinates_placeScale]; exact hzx⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨numberFieldTraceRealCoordinates (mixedEmbedding K a),
      (mem_numberFieldTraceLattice I).mpr ⟨a, ha, rfl⟩, ?_⟩
    rwa [numberFieldTraceRealCoordinates_placeScale] at hax

omit [NumberField K] in
theorem numberFieldMixedConjugation_placeScale (y : InfinitePlace K → ℝ)
    (z : mixedEmbedding.mixedSpace K) :
    numberFieldMixedConjugation (numberFieldMixedPlaceScale y z) =
      numberFieldMixedPlaceScale y (numberFieldMixedConjugation z) := by
  apply Prod.ext
  · rfl
  · funext w
    change conj ((Real.exp (-y w.1) : ℂ) * z.2 w) =
      (Real.exp (-y w.1) : ℂ) * conj (z.2 w)
    simp only [map_mul, Complex.conj_ofReal]

/-- Trace-dual ideal elements parametrize the reciprocally scaled conjugate lattice. -/
def numberFieldScaledDualIdealLatticeEquiv (I : FIˣ) (y : InfinitePlace K → ℝ) :
    FractionalIdeal.dual ℤ ℚ (I : FI) ≃
      DualZLattice.linearImage (numberFieldPlaceDiagonal (-y))
        (DualZLattice.dual (numberFieldTraceLattice I)) :=
  (numberFieldDualIdealLatticeEquiv I).trans
    (numberFieldPlaceLatticeEquiv (DualZLattice.dual (numberFieldTraceLattice I)) (-y)).toEquiv

theorem toLp_numberFieldScaledDualIdealLatticeEquiv (I : FIˣ) (y : InfinitePlace K → ℝ)
    (a : FractionalIdeal.dual ℤ ℚ (I : FI)) :
    WithLp.toLp 2 (numberFieldScaledDualIdealLatticeEquiv I y a : X) =
      numberFieldTraceCoordinates (numberFieldMixedConjugation
        (numberFieldMixedPlaceScale (-y) (mixedEmbedding K (a : K)))) := by
  change WithLp.toLp 2 (numberFieldPlaceDiagonal (-y)
    (numberFieldTraceRealCoordinates (numberFieldMixedConjugation (mixedEmbedding K (a : K))))) =
      WithLp.toLp 2 (numberFieldTraceRealCoordinates
        (numberFieldMixedConjugation (numberFieldMixedPlaceScale (-y) (mixedEmbedding K (a : K)))))
  rw [numberFieldMixedConjugation_placeScale, numberFieldTraceRealCoordinates_placeScale]

/-- Gaussian theta with an independent logarithmic scale at each archimedean place. -/
def numberFieldScaledIdealTheta (I : FI) (y : InfinitePlace K → ℝ) (t : ℝ) : ℝ :=
  ∑' a : I, Real.exp (-(Real.pi * t) * ‖numberFieldTraceCoordinates
    (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖ ^ 2)

theorem numberFieldScaledIdealTheta_eq_intrinsic (I : FIˣ) (y : InfinitePlace K → ℝ) (t : ℝ) :
    numberFieldScaledIdealTheta (I : FI) y t =
      intrinsicLatticeTheta (numberFieldScaledTraceLattice I y) t := by
  unfold numberFieldScaledIdealTheta intrinsicLatticeTheta
  calc
    _ = ∑' a : (I : FI), Real.exp (-(Real.pi * t) *
        ‖WithLp.toLp 2 (numberFieldScaledIdealLatticeEquiv I y a : X)‖ ^ 2) := by
      apply tsum_congr
      intro a
      rw [toLp_numberFieldScaledIdealLatticeEquiv]
    _ = _ := (numberFieldScaledIdealLatticeEquiv I y).tsum_eq
      (fun x : numberFieldScaledTraceLattice I y =>
        Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (x : X)‖ ^ 2))

theorem intrinsicLatticeTheta_scaledDual_eq (I : FIˣ) (y : InfinitePlace K → ℝ) (t : ℝ) :
    intrinsicLatticeTheta (DualZLattice.dual (numberFieldScaledTraceLattice I y)) t =
      numberFieldScaledIdealTheta (FractionalIdeal.dual ℤ ℚ (I : FI)) (-y) t := by
  rw [dual_numberFieldScaledTraceLattice]
  have h := (numberFieldScaledDualIdealLatticeEquiv I y).tsum_eq
    (fun x : DualZLattice.linearImage (numberFieldPlaceDiagonal (-y))
        (DualZLattice.dual (numberFieldTraceLattice I)) =>
      Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (x : X)‖ ^ 2))
  simp only [toLp_numberFieldScaledDualIdealLatticeEquiv, norm_sq_traceCoordinates_conjugation] at h
  exact h.symm

/-- The place-scaled Gaussian sum converges for every positive theta parameter. -/
theorem summable_numberFieldScaledIdealTheta (I : FIˣ) (y : InfinitePlace K → ℝ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun a : (I : FI) => Real.exp (-(Real.pi * t) * ‖numberFieldTraceCoordinates
      (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖ ^ 2)) := by
  have h := summable_intrinsicLatticeTheta_basis (numberFieldScaledTraceBasis I y) ht
  rw [span_numberFieldScaledTraceBasis] at h
  have hh := (numberFieldScaledIdealLatticeEquiv I y).summable_iff.mpr h
  refine hh.congr (fun a => ?_)
  simp only [Function.comp_def, toLp_numberFieldScaledIdealLatticeEquiv]

/-- Poisson inversion for actual ideals with independent logarithmic place scales. -/
theorem numberFieldScaledIdealTheta_inversion (I : FIˣ) (y : InfinitePlace K → ℝ)
    {t : ℝ} (ht : 0 < t) :
    numberFieldScaledIdealTheta (I : FI) y t =
      Real.exp (∑ w : InfinitePlace K, (mult w : ℝ) * y w) *
        ((FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹ *
          t ^ (-((Module.finrank ℚ K : ℝ) / 2)) *
            numberFieldScaledIdealTheta (FractionalIdeal.dual ℤ ℚ (I : FI)) (-y) (1 / t) := by
  have h := intrinsicLatticeTheta_basis_inversion (numberFieldScaledTraceBasis I y) ht
  rw [span_numberFieldScaledTraceBasis, covolume_numberFieldScaledTraceLattice,
    ← numberFieldScaledIdealTheta_eq_intrinsic, intrinsicLatticeTheta_scaledDual_eq,
    numberFieldTraceCoordinates_finrank, mul_inv_rev, Real.exp_neg, inv_inv] at h
  rw [mul_comm
    (((FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹)
    (Real.exp (∑ w : InfinitePlace K, (mult w : ℝ) * y w))] at h
  exact h

/-- The trace-normalized squared norm is the multiplicity-weighted place sum. -/
theorem norm_sq_numberFieldTraceCoordinates (z : mixedEmbedding.mixedSpace K) :
    ‖numberFieldTraceCoordinates z‖ ^ 2 =
      ∑ w : InfinitePlace K, (mult w : ℝ) * (mixedEmbedding.normAtPlace w z) ^ 2 := by
  have hinv : numberFieldMixedConjugation (numberFieldMixedConjugation z) = z :=
    (numberFieldMixedConjugation (K := K)).apply_symm_apply z
  have h := inner_numberFieldTraceCoordinates_conjugate z (numberFieldMixedConjugation z)
  rw [hinv, real_inner_self_eq_norm_sq] at h
  rw [h, numberFieldMixedTrace, sum_infinitePlaces_eq_real_add_complex, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    rw [mixedEmbedding.normAtPlace_apply_of_isReal w.2]
    change z.1 w * z.1 w = (mult w.1 : ℝ) * ‖z.1 w‖ ^ 2
    simp only [mult, w.2, if_pos, Nat.cast_one, one_mul, Real.norm_eq_abs]
    rw [sq_abs, pow_two]
  · apply Finset.sum_congr rfl
    intro w _
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex w.2]
    change 2 * (z.2 w * conj (z.2 w)).re = (mult w.1 : ℝ) * ‖z.2 w‖ ^ 2
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    simp only [mult, not_isReal_iff_isComplex.mpr w.2, if_false, Nat.cast_ofNat]

omit [NumberField K] in
theorem normAtPlace_numberFieldMixedPlaceScale (y : InfinitePlace K → ℝ)
    (z : mixedEmbedding.mixedSpace K) (w : InfinitePlace K) :
    mixedEmbedding.normAtPlace w (numberFieldMixedPlaceScale y z) =
      Real.exp (-y w) * mixedEmbedding.normAtPlace w z := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw,
      mixedEmbedding.normAtPlace_apply_of_isReal hw]
    change ‖Real.exp (-y w) * z.1 ⟨w, hw⟩‖ = _
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw,
      mixedEmbedding.normAtPlace_apply_of_isComplex hw]
    change ‖(Real.exp (-y w) : ℂ) * z.2 ⟨w, hw⟩‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Unit-log translation is canceled by multiplying the embedded field element by the unit. -/
theorem norm_sq_numberFieldPlaceScale_unit (y : InfinitePlace K → ℝ)
    (u : (𝓞 K)ˣ) (a : K) :
    ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale
      (y + numberFieldUnitPlaceLogEmbeddings u) (mixedEmbedding K ((u : 𝓞 K) * a)))‖ ^ 2 =
        ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K a))‖ ^ 2 := by
  rw [norm_sq_numberFieldTraceCoordinates, norm_sq_numberFieldTraceCoordinates]
  apply Finset.sum_congr rfl
  intro w _
  rw [normAtPlace_numberFieldMixedPlaceScale, normAtPlace_numberFieldMixedPlaceScale,
    mixedEmbedding.normAtPlace_apply, mixedEmbedding.normAtPlace_apply, map_mul]
  have hu : 0 < w ((u : 𝓞 K) : K) := by
    rw [InfinitePlace.pos_iff]
    norm_cast
    exact u.ne_zero
  simp only [Pi.add_apply, numberFieldUnitPlaceLogEmbeddings, neg_add_rev,
    Real.exp_add, Real.exp_neg, Real.exp_log hu]
  congr 2
  field_simp

/-- A global unit acts bijectively on every fractional ideal. -/
def numberFieldIdealUnitEquiv (I : FI) (u : (𝓞 K)ˣ) : I ≃ I :=
  MulAction.toPerm u

omit [NumberField K] in
theorem numberFieldIdealUnitEquiv_apply (I : FI) (u : (𝓞 K)ˣ) (a : I) :
    (numberFieldIdealUnitEquiv I u a : K) = ((u : 𝓞 K) : K) * (a : K) := rfl

theorem sum_mult_placeProfile_add_unitLog (y : InfinitePlace K → ℝ) (u : (𝓞 K)ˣ) :
    (∑ w : InfinitePlace K, (mult w : ℝ) * (y + numberFieldUnitPlaceLogEmbeddings u) w) =
      ∑ w : InfinitePlace K, (mult w : ℝ) * y w := by
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
    sum_mult_numberFieldUnitPlaceLogEmbeddings, add_zero]

/-- Reindexing by a global unit makes the theta family periodic in its place logarithm. -/
theorem numberFieldScaledIdealTheta_unit (I : FI) (y : InfinitePlace K → ℝ)
    (u : (𝓞 K)ˣ) (t : ℝ) :
    numberFieldScaledIdealTheta I (y + numberFieldUnitPlaceLogEmbeddings u) t =
      numberFieldScaledIdealTheta I y t := by
  unfold numberFieldScaledIdealTheta
  have h := (numberFieldIdealUnitEquiv I u).tsum_eq (fun a : I =>
    Real.exp (-(Real.pi * t) * ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale
      (y + numberFieldUnitPlaceLogEmbeddings u) (mixedEmbedding K (a : K)))‖ ^ 2))
  calc
    _ = ∑' a : I, Real.exp (-(Real.pi * t) * ‖numberFieldTraceCoordinates
        (numberFieldMixedPlaceScale (y + numberFieldUnitPlaceLogEmbeddings u)
          (mixedEmbedding K (numberFieldIdealUnitEquiv I u a : K)))‖ ^ 2) := h.symm
    _ = _ := by
      apply tsum_congr
      intro a
      rw [numberFieldIdealUnitEquiv_apply, norm_sq_numberFieldPlaceScale_unit]

end GaloisForLFunctions.HTGeometry
