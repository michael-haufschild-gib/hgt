import GaloisForLFunctions.HTGeometry.TorusCharacterMean
import GaloisForLFunctions.HTGeometry.PhaseJetRelationTransfer
import GaloisForLFunctions.HTGeometry.TorusTrigPolynomial
import GaloisForLFunctions.HTGeometry.TorusDerivationLeibniz

/-!
# The linear phase observable

The phase observable `z ↦ ∑_j a_j z_j` is the exponential sum
`t ↦ ∑_j a_j e^{i ω_j t}`.  It is a continuous linear map, so its coordinate
derivatives are the coefficients and each torus derivative multiplies the
coefficients by the corresponding frequency: every phase jet is again a linear
observable.

Its active characters are the standard basis vectors whose coefficient does not
vanish, so with all coefficients nonzero the active lattice is the whole
character lattice, of rank the number of frequencies.
-/

open Complex Set Filter Topology MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance isProbabilityMeasureCircleLinearPhase : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance isAddHaarMeasureCircleLinearPhase : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### The observable and its derivatives -/

/-- The linear phase observable with prescribed coefficients. -/
def linearObservable (a : d → ℂ) : (d → ℂ) → ℂ := fun z => ∑ j, a j * z j

/-- The same map, bundled as a continuous linear map. -/
def linearObservableCLM (a : d → ℂ) : (d → ℂ) →L[ℂ] ℂ :=
  ∑ j, a j • ContinuousLinearMap.proj j

omit [DecidableEq d] in
theorem coe_linearObservableCLM (a : d → ℂ) :
    ⇑(linearObservableCLM a) = linearObservable a := by
  funext z
  rw [linearObservableCLM, FunLike.coe_sum, Finset.sum_apply,
    linearObservable]
  exact Finset.sum_congr rfl fun j _ => by
    rw [FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]

omit [DecidableEq d] in
theorem analyticOnNhd_linearObservable (a : d → ℂ) (s : Set (d → ℂ)) :
    AnalyticOnNhd ℂ (linearObservable a) s := by
  have h := ContinuousLinearMap.analyticOnNhd (linearObservableCLM a) s
  rwa [coe_linearObservableCLM] at h

theorem coordDeriv_linearObservable (a : d → ℂ) (j : d) (z : d → ℂ) :
    coordDeriv (linearObservable a) j z = a j := by
  rw [coordDeriv, ← coe_linearObservableCLM, ContinuousLinearMap.fderiv,
    coe_linearObservableCLM, linearObservable]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem torusDerivation_linearObservable (omega : d → ℝ) (a : d → ℂ) :
    torusDerivation omega (linearObservable a)
      = linearObservable fun j => Complex.I * (omega j : ℂ) * a j := by
  funext z
  rw [torusDerivation, linearObservable]
  exact Finset.sum_congr rfl fun j _ => by
    rw [coordDeriv_linearObservable]
    ring

/-- **Every phase jet of a linear observable is a linear observable.** -/
theorem phaseJet_linearObservable (omega : d → ℝ) (a : d → ℂ) (k : ℕ) :
    phaseJet omega (linearObservable a) k
      = linearObservable fun j => (Complex.I * (omega j : ℂ)) ^ k * a j := by
  induction k with
  | zero =>
      have hfun : (fun j => (Complex.I * (omega j : ℂ)) ^ (0 : ℕ) * a j) = a := by
        funext j
        rw [pow_zero, one_mul]
      rw [hfun]
      rfl
  | succ m ih =>
      rw [← torusDerivation_phaseJet, ih, torusDerivation_linearObservable]
      congr 1
      funext j
      ring

/-! ### The active characters -/

theorem torusRestriction_linearObservable (a : d → ℂ) :
    torusRestriction (linearObservable a)
      = fun x => ∑ j, a j * UnitAddTorus.mFourier (Pi.single j 1) x := by
  funext x
  rw [torusRestriction, linearObservable]
  exact Finset.sum_congr rfl fun j _ => by
    rw [UnitAddTorus.mFourier_single]
    rfl

omit [DecidableEq d] in
theorem mFourierCoeff_fintype_sum (a : d → ℂ) (e : d → (d → ℤ)) (m : d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (fun x => ∑ j, a j * UnitAddTorus.mFourier (e j) x) m
      = ∑ j, a j * (if m = e j then 1 else 0) := by
  classical
  have hsplit : (fun x : UnitAddTorus d =>
      UnitAddTorus.mFourier (-m) x • ∑ j, a j * UnitAddTorus.mFourier (e j) x)
      = fun x => ∑ j, a j •
        (UnitAddTorus.mFourier (-m) x • UnitAddTorus.mFourier (e j) x) := by
    funext x
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [UnitAddTorus.mFourierCoeff, hsplit, integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul, smul_eq_mul, ← UnitAddTorus.mFourierCoeff,
      mFourierCoeff_mFourier]
  · intro j _
    exact integrable_torus_of_continuous (by fun_prop)

omit [Fintype d] in
theorem single_injective (i j : d) (h : (Pi.single i 1 : d → ℤ) = Pi.single j 1) :
    i = j := by
  by_contra hij
  have := congrFun h i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
  exact one_ne_zero this

/-- **The active coefficient at a standard character is the corresponding
coefficient.** -/
theorem activeCoeff_linearObservable_single (a : d → ℂ) (i : d) :
    activeCoeff (linearObservable a) (Pi.single i 1) = a i := by
  classical
  rw [activeCoeff, torusRestriction_linearObservable, mFourierCoeff_fintype_sum]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one]
  · intro j _ hji
    rw [if_neg fun hc => hji (single_injective i j hc).symm, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ### The active lattice -/

theorem activeLattice_linearObservable_eq_top {a : d → ℂ} (ha : ∀ j, a j ≠ 0) :
    activeLattice (linearObservable a) = ⊤ := by
  classical
  refine top_unique ?_
  have hbasis : Submodule.span ℤ (Set.range fun j : d => (Pi.single j 1 : d → ℤ))
      = ⊤ := by
    have hspan := (Pi.basisFun ℤ d).span_eq
    have hfun : (Set.range fun j : d => (Pi.single j 1 : d → ℤ))
        = Set.range ⇑(Pi.basisFun ℤ d) := by
      refine congrArg Set.range ?_
      funext j
      rw [Pi.basisFun_apply]
    rwa [hfun]
  rw [← hbasis]
  refine Submodule.span_mono ?_
  rintro - ⟨j, rfl⟩
  show activeCoeff (linearObservable a) (Pi.single j 1) ≠ 0
  rw [activeCoeff_linearObservable_single]
  exact ha j

/-- **The active lattice of an exponential sum has rank the number of
frequencies.** -/
theorem rank_activeLattice_linearObservable {a : d → ℂ} (ha : ∀ j, a j ≠ 0) :
    Module.rank ℤ (activeLattice (linearObservable a))
      = (Fintype.card d : Cardinal) := by
  rw [activeLattice_linearObservable_eq_top ha, rank_top, rank_fun']

end

end GaloisForLFunctions.HTGeometry
