import GaloisForLFunctions.RHTower.JointAncestryPrimeCoordinateToggleDenseRangeNoGo
import GaloisForLFunctions.HTGeometry.WeightedDensityL2
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# JAS Haar-bilateral dilation source superselection

The canonical oriented completion of a Boolean creator is a bilateral unitary shift.  Its joint
vacuum spectral law is Haar, whereas the literal JAS source carries the prime-Poisson law.  This
module proves the exact closed source-linear landing threshold between those two multiplication
representations:

`NonzeroClosedSourceLinearSewing (continuousL2Mul primePoisson) (continuousL2Mul torusHaar)`
exists if and only if `1 / 2 < sigma`.

The positive direction is not postulated.  We repair the Radon--Nikodym derivative on its null
exceptional set, use the corpus positive-density `L²` unitary, prove that it intertwines every
continuous multiplier, and take its closed graph.  The negative direction uses the corpus
prime-Poisson/Haar singularity wall and closed-relation splitting.

Consequently the unweighted Haar bilateral completion is impossible exactly at the critical wall.
Any surviving oriented JAS completion there must retain the prime-Poisson measure class rather than
transport through the open-right-half Haar equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- Graph of a bounded linear map, as a Hilbert-space relation. -/
def hilbertContinuousGraphRelation (U : H₁ →L[ℂ] H₂) :
    Submodule ℂ (HilbertSum H₁ H₂) :=
  LinearMap.ker ((hilbertSumSnd - U.comp hilbertSumFst).toLinearMap)

theorem mem_hilbertContinuousGraphRelation (U : H₁ →L[ℂ] H₂)
    (z : HilbertSum H₁ H₂) :
    z ∈ hilbertContinuousGraphRelation U ↔ hilbertSumSnd z = U (hilbertSumFst z) := by
  change hilbertSumSnd z - U (hilbertSumFst z) = 0 ↔ _
  exact sub_eq_zero

theorem isClosed_hilbertContinuousGraphRelation (U : H₁ →L[ℂ] H₂) :
    IsClosed (hilbertContinuousGraphRelation U : Set (HilbertSum H₁ H₂)) :=
  ContinuousLinearMap.isClosed_ker _

theorem hilbertContinuousGraphRelation_domain_eq_top (U : H₁ →L[ℂ] H₂) :
    hilbertRelationDomain (hilbertContinuousGraphRelation U) = ⊤ := by
  apply top_unique
  intro x _
  rw [hilbertRelationDomain, Submodule.mem_map]
  refine ⟨hilbertSumInl x + hilbertSumInr (U x), ?_, ?_⟩
  · rw [mem_hilbertContinuousGraphRelation, map_add, map_add]
    change (0 : H₂) + U x = U (x + 0)
    simp
  · change x + 0 = x
    simp

theorem hilbertContinuousGraphRelation_singleValued (U : H₁ →L[ℂ] H₂) :
    HilbertRelationSingleValued (hilbertContinuousGraphRelation U) := by
  intro y hy
  rw [mem_hilbertContinuousGraphRelation] at hy
  change y = U 0 at hy
  simpa using hy

/-- A bounded intertwiner with one nonzero output produces a genuinely coupled closed,
dense-domain, single-valued source-linear sewing. -/
theorem nonzeroClosedSourceLinearSewing_of_continuousLinearMap_intertwines
    {I : Type*} (A : I → H₁ →L[ℂ] H₁) (B : I → H₂ →L[ℂ] H₂)
    (U : H₁ →L[ℂ] H₂) (hU : ∀ i, U.comp (A i) = (B i).comp U)
    (u : H₁) (hu : U u ≠ 0) :
    NonzeroClosedSourceLinearSewing A B := by
  refine ⟨hilbertContinuousGraphRelation U,
    isClosed_hilbertContinuousGraphRelation U, ?_,
    hilbertContinuousGraphRelation_singleValued U, ?_, ?_⟩
  · rw [hilbertContinuousGraphRelation_domain_eq_top]
    exact dense_univ
  · intro i z hz
    rw [mem_hilbertContinuousGraphRelation] at hz ⊢
    rw [hilbertBlockDiagonal_snd, hilbertBlockDiagonal_fst, hz]
    exact DFunLike.congr_fun (hU i).symm (hilbertSumFst z)
  · refine ⟨hilbertSumInl u + hilbertSumInr (U u), ?_, ?_⟩
    · rw [mem_hilbertContinuousGraphRelation, map_add, map_add]
      change (0 : H₂) + U u = U (u + 0)
      simp
    · rw [map_add]
      change (0 : H₂) + U u ≠ 0
      simpa using hu

variable {X : Type*} [MeasurableSpace X]

/-- An everywhere positive finite representative of a Radon--Nikodym derivative.  The values zero
and infinity occur only on null exceptional sets under mutual absolute continuity, so replacing
them by one preserves the weighted measure and makes square-root division globally defined. -/
def repairedRnDensity (μ ν : Measure X) (x : X) : ℝ :=
  let d := μ.rnDeriv ν x
  if d = 0 ∨ d = ∞ then 1 else d.toReal

theorem measurable_repairedRnDensity (μ ν : Measure X) :
    Measurable (repairedRnDensity μ ν) := by
  let d : X → ℝ≥0∞ := μ.rnDeriv ν
  let bad : Set X := {x | d x = 0} ∪ {x | d x = ∞}
  change Measurable (bad.piecewise (fun _ => (1 : ℝ)) (fun x => (d x).toReal))
  apply Measurable.piecewise
  · exact (measurableSet_eq_fun (Measure.measurable_rnDeriv μ ν) measurable_const).union
      (measurableSet_eq_fun (Measure.measurable_rnDeriv μ ν) measurable_const)
  · exact measurable_const
  · exact ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv μ ν)

theorem repairedRnDensity_pos (μ ν : Measure X) (x : X) :
    0 < repairedRnDensity μ ν x := by
  rw [repairedRnDensity]
  split_ifs with h
  · norm_num
  · exact ENNReal.toReal_pos (not_or.mp h).1 (not_or.mp h).2

theorem realDensity_repairedRnDensity_ae
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    realDensity (repairedRnDensity μ ν) =ᵐ[ν] μ.rnDeriv ν := by
  have hposμ : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := Measure.rnDeriv_pos hμν
  have hposν : ∀ᵐ x ∂ν, 0 < μ.rnDeriv ν x := hνμ.ae_le hposμ
  filter_upwards [hposν, Measure.rnDeriv_lt_top μ ν] with x hx htop
  rw [realDensity, repairedRnDensity]
  simp only [if_neg (not_or_intro hx.ne' htop.ne)]
  exact ENNReal.ofReal_toReal htop.ne

/-- Mutual absolute continuity gives an exact positive real-density presentation, with no
pointwise zero or infinity left in the chosen representative. -/
theorem withDensity_repairedRnDensity_eq
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    ν.withDensity (realDensity (repairedRnDensity μ ν)) = μ := by
  calc
    ν.withDensity (realDensity (repairedRnDensity μ ν)) =
        ν.withDensity (μ.rnDeriv ν) := by
      ext s hs
      rw [withDensity_apply _ hs, withDensity_apply _ hs]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae
        (realDensity_repairedRnDensity_ae μ ν hμν hνμ)] with x hx
      simp only [hx]
    _ = μ := Measure.withDensity_rnDeriv_eq μ ν hμν

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [SecondCountableTopologyEither X ℂ]

omit [SecondCountableTopologyEither X ℂ] in
/-- The positive-density unitary commutes with every continuous multiplication operator. -/
theorem weightedDensityUnitary_continuousL2Mul
    (ν : Measure X) [IsFiniteMeasure ν]
    (w : X → ℝ) (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    [IsFiniteMeasure (ν.withDensity (realDensity w))]
    (f : C(X, ℂ)) (u : WeightedL2 (μ := ν) w) :
    weightedDensityUnitary w hw hpos
        (continuousL2Mul (ν.withDensity (realDensity w)) f u) =
      continuousL2Mul ν f (weightedDensityUnitary w hw hpos u) := by
  change densityMul w hw hpos
      (continuousL2Mul (ν.withDensity (realDensity w)) f u) =
    continuousL2Mul ν f (densityMul w hw hpos u)
  apply Lp.ext
  have hmulSource := (withDensity_realDensity_ae_eq hw hpos).mp
    (continuousL2Mul_coeFn (ν.withDensity (realDensity w)) f u)
  filter_upwards [densityMul_ae w hw hpos
      (continuousL2Mul (ν.withDensity (realDensity w)) f u),
    hmulSource,
    continuousL2Mul_coeFn ν f (densityMul w hw hpos u),
    densityMul_ae w hw hpos u] with x hleft hsource hright hu
  rw [hleft, hright, hsource, hu]
  ring

omit [SecondCountableTopologyEither X ℂ] in
/-- An exact positive-density presentation yields a nonzero closed source-linear sewing. -/
theorem continuousL2Mul_nonzeroClosedSourceLinearSewing_of_withDensity_eq
    (ν : Measure X) [IsFiniteMeasure ν]
    (w : X → ℝ) (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (μ : Measure X) [IsFiniteMeasure μ]
    (hmeasure : ν.withDensity (realDensity w) = μ)
    (v : Lp ℂ 2 ν) (hv : v ≠ 0) :
    NonzeroClosedSourceLinearSewing (continuousL2Mul μ) (continuousL2Mul ν) := by
  subst μ
  let U := weightedDensityUnitary (μ := ν) w hw hpos
  let Uc : WeightedL2 (μ := ν) w →L[ℂ] Lp ℂ 2 ν :=
    U.toContinuousLinearEquiv.toContinuousLinearMap
  refine nonzeroClosedSourceLinearSewing_of_continuousLinearMap_intertwines
    (continuousL2Mul (ν.withDensity (realDensity w))) (continuousL2Mul ν)
    Uc ?_ (U.symm v) ?_
  · intro f
    apply ContinuousLinearMap.ext
    intro u
    exact weightedDensityUnitary_continuousL2Mul ν w hw hpos f u
  · change U (U.symm v) ≠ 0
    simpa using hv

omit [SecondCountableTopologyEither X ℂ] in
/-- Equivalent finite measures have a nonzero closed source-linear sewing between their
continuous multiplication representations, constructed by Radon--Nikodym half-density. -/
theorem continuousL2Mul_nonzeroClosedSourceLinearSewing_of_mutuallyAbsolutelyContinuous
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (v : Lp ℂ 2 ν) (hv : v ≠ 0) :
    NonzeroClosedSourceLinearSewing (continuousL2Mul μ) (continuousL2Mul ν) := by
  let w : X → ℝ := repairedRnDensity μ ν
  have hw : Measurable w := measurable_repairedRnDensity μ ν
  have hpos : ∀ x, 0 < w x := repairedRnDensity_pos μ ν
  have hmeasure : ν.withDensity (realDensity w) = μ :=
    withDensity_repairedRnDensity_eq μ ν hμν hνμ
  exact continuousL2Mul_nonzeroClosedSourceLinearSewing_of_withDensity_eq
    ν w hw hpos μ hmeasure v hv

/-- The constant Haar vacuum is nonzero in prime-torus `L²`. -/
theorem torusHaar_primeTorus_continuousOne_toLp_ne_zero :
    ContinuousMap.toLp 2 (torusHaar Nat.Primes) ℂ
      (1 : C(PrimeTorus, ℂ)) ≠ 0 := by
  let ν := torusHaar Nat.Primes
  let v : Lp ℂ 2 ν := ContinuousMap.toLp 2 ν ℂ (1 : C(PrimeTorus, ℂ))
  change v ≠ 0
  intro hzero
  have hnorm : ‖v‖ ^ 2 = 1 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hcoe : ((v : Lp ℂ 2 ν) : PrimeTorus → ℂ) =ᵐ[ν]
        fun _ => (1 : ℂ) := by
      filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) ν
        (1 : C(PrimeTorus, ℂ))] with x hx
      simpa [v] using hx
    calc
      (∫ x, ‖((v : Lp ℂ 2 ν) : PrimeTorus → ℂ) x‖ ^ 2 ∂ν) =
          ∫ _x : PrimeTorus, (1 : ℝ) ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with x hx
        rw [hx]
        norm_num
      _ = 1 := by simp [ν]
  rw [hzero, norm_zero, zero_pow (by norm_num)] at hnorm
  norm_num at hnorm

/-- **Sharp Haar-bilateral JAS landing wall.**  The prime-Poisson multiplication source admits a
nonzero closed densely defined single-valued source-linear sewing into the unweighted Haar
bilateral representation exactly in the open right half-plane. -/
theorem primePoisson_haar_nonzeroClosedSourceLinearSewing_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    NonzeroClosedSourceLinearSewing
      (continuousL2Mul (primePoissonMeasure sigma t hsigma))
      (continuousL2Mul (torusHaar Nat.Primes)) ↔
      1 / 2 < sigma := by
  constructor
  · intro hsew
    by_contra hright
    have hwall : sigma ≤ 1 / 2 := le_of_not_gt hright
    have hdisj : OperatorFamiliesDisjoint
        (continuousL2Mul (primePoissonMeasure sigma t hsigma))
        (continuousL2Mul (torusHaar Nat.Primes)) :=
      continuousL2Mul_operatorFamiliesDisjoint_of_mutuallySingular
        (primePoissonMeasure_mutuallySingular_torusHaar_of_le_half
          sigma t hsigma hwall)
    rcases hsew with ⟨R, hclosed, hdense, hsingle, hinv, z, hz, hout⟩
    have hzero := (closedDenseSingleValuedRelation_mem_iff_output_eq_zero_of_disjoint
      (continuousL2Mul (primePoissonMeasure sigma t hsigma))
      (continuousL2Mul (torusHaar Nat.Primes)) hdisj R hclosed hdense hsingle hinv
      (fun f w hw => by
        rw [adjoint_continuousL2Mul, adjoint_continuousL2Mul]
        exact hinv (star f) w hw) z).mp hz
    exact hout hzero
  · intro hright
    have hmac := (primePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff
      sigma t hsigma).mpr hright
    let v : Lp ℂ 2 (torusHaar Nat.Primes) :=
      ContinuousMap.toLp 2 (torusHaar Nat.Primes) ℂ (1 : C(PrimeTorus, ℂ))
    exact continuousL2Mul_nonzeroClosedSourceLinearSewing_of_mutuallyAbsolutelyContinuous
      (primePoissonMeasure sigma t hsigma) (torusHaar Nat.Primes)
      hmac.1 hmac.2 v (by
        simpa only [v] using torusHaar_primeTorus_continuousOne_toLp_ne_zero)

end

end GaloisForLFunctions.HTGeometry
