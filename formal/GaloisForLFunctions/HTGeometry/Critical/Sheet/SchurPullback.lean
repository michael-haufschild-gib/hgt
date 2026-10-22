import GaloisForLFunctions.HTGeometry.Critical.Sheet.ChartIntegrality
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.UniqueRamifiedPrime
import GaloisForLFunctions.HTGeometry.Critical.Schur.NormalRamifies
import GaloisForLFunctions.HTGeometry.Critical.Chart.CentreHeight

/-!
# A singular sheet pulls the Schur place back to the Schur place

Pulling the chosen normal-closure Schur valuation back along a geometric sheet gives a prime of
the chart algebra lying over the centre of the Schur place.  If the sheet is *singular* — that is,
if the ramification element lands in the maximal ideal — then that prime is ramified, so `(D-1)`
identifies it with the centre of the Schur place itself.

Consequently the sheet lifts to a ring map of the source Schur valuation ring into the
normal-closure one, and nonvanishing residues are preserved.  This is what makes the corank-one
statement at the Schur place apply at *every* singular point of the reduced fibre.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- A sheet, restricted to the chart algebra and corestricted to the normal-closure Schur
valuation ring. -/
noncomputable def criticalSheetChartToNormalSchur (σ : criticalGeometricSheet K m n) :
    criticalSourceChartAlgebra K (m := m) (n := n) →+*
      criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) where
  toFun t := ⟨σ (t : criticalSourceField K m n),
    criticalSourceChartAlgebra_sheet_mem_normalClosureSchur K
      (Fact.out : 1 < m) (Fact.out : 1 < n) σ t.2⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _

@[simp] theorem criticalSheetChartToNormalSchur_coe (σ : criticalGeometricSheet K m n)
    (t : criticalSourceChartAlgebra K (m := m) (n := n)) :
    (criticalSheetChartToNormalSchur K σ t : criticalNormalClosure K m n)
      = σ (t : criticalSourceField K m n) := rfl

/-- The centre on the chart algebra of the Schur place pulled back along a sheet. -/
noncomputable def criticalSheetChartPrime (σ : criticalGeometricSheet K m n) :
    Ideal (criticalSourceChartAlgebra K (m := m) (n := n)) :=
  (maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
    (Fact.out : 0 < n))).comap (criticalSheetChartToNormalSchur K σ)

instance criticalSheetChartPrime_isPrime (σ : criticalGeometricSheet K m n) :
    (criticalSheetChartPrime K σ).IsPrime := Ideal.comap_isPrime _ _

theorem mem_criticalSheetChartPrime_iff (σ : criticalGeometricSheet K m n)
    (t : criticalSourceChartAlgebra K (m := m) (n := n)) :
    t ∈ criticalSheetChartPrime K σ ↔
      criticalSheetChartToNormalSchur K σ t ∈ maximalIdeal
        (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)) := Iff.rfl

/-- Membership in the maximal ideal is detected upstairs. -/
theorem mem_maximalIdeal_normalUpper_iff
    (x : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    criticalSchurSourceToNormalUpper K (m := m) (n := n) x
        ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))
      ↔ x ∈ maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)) := by
  constructor
  · intro h
    by_contra hx
    exact (IsLocalRing.notMem_maximalIdeal.mpr
      ((IsLocalRing.notMem_maximalIdeal.mp hx).map _)) h
  · intro h
    by_contra hy
    exact (IsLocalRing.notMem_maximalIdeal.mpr
      (IsLocalHom.map_nonunit (f := criticalSchurSourceToNormalUpper K (m := m) (n := n)) x
        (IsLocalRing.notMem_maximalIdeal.mp hy))) h

/-- Every sheet agrees with the canonical embedding on the observation field. -/
theorem sheet_eq_embedding_of_observationRange (σ : criticalGeometricSheet K m n)
    (y : criticalObservationField K m n) :
    σ (algebraMap (criticalObservationField K m n) (criticalSourceField K m n) y)
      = criticalSourceNormalClosureEmbedding K m n
          (algebraMap (criticalObservationField K m n) (criticalSourceField K m n) y) := by
  rw [σ.commutes, (criticalSourceNormalClosureEmbedding K m n).commutes]

/-- The sheet-pulled-back centre lies over the centre of the Schur place on the chart ring. -/
instance criticalSheetChartPrime_liesOver (σ : criticalGeometricSheet K m n) :
    (criticalSheetChartPrime K σ).LiesOver
      (criticalSchurChartUnder K (m := m) (n := n)) := by
  constructor
  refine Ideal.ext fun c => ?_
  obtain ⟨y, hy⟩ := algebraMap_chartRing_mem_observationRange K c
  have hxB : algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) c
      ∈ criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
    chartRing_mem_schur K (Fact.out : 1 < m) (Fact.out : 1 < n) c
  set xB : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
    ⟨algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) c, hxB⟩
    with hxBdef
  have hsheet : criticalSheetChartToNormalSchur K σ
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartAlgebra K (m := m) (n := n)) c)
      = criticalSchurSourceToNormalUpper K (m := m) (n := n) xB := by
    apply Subtype.ext
    show σ _ = _
    rw [show ((algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartAlgebra K (m := m) (n := n)) c :
          criticalSourceChartAlgebra K (m := m) (n := n)) :
        criticalSourceField K m n)
        = algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) c from rfl,
      ← hy, sheet_eq_embedding_of_observationRange K σ y, hy]
    rfl
  have hchart : chartAlgebraToSchur K
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartAlgebra K (m := m) (n := n)) c) = xB := rfl
  show c ∈ criticalSchurChartUnder K (m := m) (n := n)
    ↔ c ∈ (criticalSheetChartPrime K σ).under (criticalObservationChartRing K m n)
  rw [criticalSchurChartUnder, Ideal.mem_under, Ideal.mem_under, criticalSchurChartPrime,
    Ideal.mem_comap, mem_criticalSheetChartPrime_iff, hsheet]
  show chartAlgebraToSchur K _ ∈ _ ↔ _
  rw [hchart, ← mem_maximalIdeal_normalUpper_iff K xB]

/-- **A singular sheet pulls the Schur place back to the Schur place.**  This is `(D-1)` in the
form the reduced fibre needs. -/
theorem criticalSheetChartPrime_eq_of_singular (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    criticalSheetChartPrime K σ = criticalSchurChartPrime K (m := m) (n := n) :=
  criticalSchurChartPrime_eq_of_mem K (criticalSheetChartPrime K σ) hsing

/-- The lift of a singular sheet to the source Schur valuation ring. -/
noncomputable def criticalSheetSourceSchurLift (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) →+*
      criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
  IsLocalization.lift (M := (criticalSchurChartPrime K (m := m) (n := n)).primeCompl)
    (g := criticalSheetChartToNormalSchur K σ) (fun y => by
      have hy : (y : criticalSourceChartAlgebra K (m := m) (n := n))
          ∉ criticalSheetChartPrime K σ := by
        rw [criticalSheetChartPrime_eq_of_singular K σ hsing]
        exact y.2
      exact IsLocalRing.notMem_maximalIdeal.mp hy)

theorem criticalSheetSourceSchurLift_comp (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    ((criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)).subtype).comp (criticalSheetSourceSchurLift K σ hsing)
      = (σ.toRingHom).comp
        ((criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)).subtype) := by
  refine IsLocalization.ringHom_ext
    (M := (criticalSchurChartPrime K (m := m) (n := n)).primeCompl) ?_
  refine RingHom.ext fun t => ?_
  show ((criticalSheetSourceSchurLift K σ hsing)
      (algebraMap (criticalSourceChartAlgebra K (m := m) (n := n))
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) t) :
      criticalNormalClosure K m n) = _
  rw [criticalSheetSourceSchurLift, IsLocalization.lift_eq]
  rfl

/-- The underlying source-field element of a lifted sheet is the sheet image. -/
theorem criticalSheetSourceSchurLift_coe (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    (x : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    ((criticalSheetSourceSchurLift K σ hsing x : criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)) : criticalNormalClosure K m n)
      = σ (x : criticalSourceField K m n) :=
  congrArg (fun f : criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n) →+* criticalNormalClosure K m n => f x)
    (criticalSheetSourceSchurLift_comp K σ hsing)

/-- **Nonvanishing residues survive a singular sheet.** -/
theorem residue_criticalSheetSourceSchurLift_ne_zero (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    {x : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)}
    (hx : IsLocalRing.residue _ x ≠ 0) :
    IsLocalRing.residue _ (criticalSheetSourceSchurLift K σ hsing x) ≠ 0 := by
  intro hcon
  have hunit : IsUnit x :=
    IsLocalRing.notMem_maximalIdeal.mp fun hmem => hx ((IsLocalRing.residue_eq_zero_iff _).mpr hmem)
  exact (IsLocalRing.notMem_maximalIdeal.mpr (hunit.map _))
    ((IsLocalRing.residue_eq_zero_iff _).mp hcon)

end

end GaloisForLFunctions.HTGeometry
