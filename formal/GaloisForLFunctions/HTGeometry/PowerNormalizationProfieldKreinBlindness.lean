import GaloisForLFunctions.HTGeometry.ArbitraryFamilyPowerQuotientResidue
import GaloisForLFunctions.HTGeometry.KreinEscapePowerFieldInvariance
import GaloisForLFunctions.HTGeometry.MovingCanonicalTranslationExistence
import GaloisForLFunctions.HTGeometry.EvenSurgeryPoleSeparationWitnesses

/-!
# Power-normalization pro-field Krein blindness

Exact global canonical-product realizations show that every algebraic power-translation level,
their complete divisibility-tower intersection, and maximal translation differential independence
are simultaneously blind to finite Krein index. The Schwarz-real even construction realizes every
even index while preserving the scalar functional equation.
-/

open Complex Filter Polynomial
open scoped Differential ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance testUpperDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance testUpperAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance testRatDiff : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance testUpperDiff : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance testUpperDiffAlg : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

local instance testUpperCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) upperEndMeroField).injective

theorem baseSurgeryProductTranslateFamily_logDeriv
    (θ : BoundedRealSequence) (h : ℂ) :
    Differential.logDeriv
        (surgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h) =
      -movingCanonicalSurgeryTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h := by
  let a : upperEndAnalyticSubring :=
    analyticUpperEndElement
      (fun z => movingCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)) 0
      (analyticOnNhd_translate_upperTail
        (movingCanonicalSurgeryProduct_analytic θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)) h)
  let c : upperEndAnalyticSubring :=
    upperEndTranslationAnalyticEquiv h
      (movingCanonicalSurgeryCarrierUpperEndAnalytic θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i))
  have ha : surgeryProductTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h =
      algebraMap upperEndAnalyticSubring upperEndMeroField a := rfl
  have hc : movingCanonicalSurgeryTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h =
      algebraMap upperEndAnalyticSubring upperEndMeroField c := by
    rw [movingCanonicalSurgeryTranslateFamily,
      movingCanonicalSurgeryUpperEndMero,
      upperEndTranslationMeroEquiv_algebraMap]
  have hane : a ≠ 0 := by
    intro hzero
    have hzeroGerm :
        ((fun z => movingCanonicalSurgeryProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) (z + h)) :
            Germ upperEndFilter ℂ) = 0 := by
      change (a : Germ upperEndFilter ℂ) = 0
      rw [hzero]
      rfl
    have hzEventually : ∀ᶠ z in upperEndFilter,
        movingCanonicalSurgeryProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) (z + h) = 0 := by
      apply Filter.Germ.coe_eq.mp
      exact hzeroGerm.trans Filter.Germ.coe_zero.symm
    have hneEventually : ∀ᶠ z in upperEndFilter,
        movingCanonicalSurgeryProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) (z + h) ≠ 0 := by
      rw [upperEndFilter_basis.eventually_iff]
      refine ⟨-h.im + 1, trivial, fun z hz => ?_⟩
      apply movingCanonicalSurgeryProduct_ne_zero_of_upper θ
      · change -h.im + 1 < z.im at hz
        simp only [Complex.add_im]
        linarith
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
    rcases (hzEventually.and hneEventually).exists with ⟨z, hz, hne⟩
    exact hne hz
  rw [ha, hc, Differential.logDeriv,
    upperEndMeroFieldDifferential_algebraMap]
  have hmapne : algebraMap upperEndAnalyticSubring upperEndMeroField a ≠ 0 := by
    intro hzero
    apply hane
    apply IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
    simpa using hzero
  rw [div_eq_iff hmapne, ← map_neg, ← map_mul]
  apply congrArg (algebraMap upperEndAnalyticSubring upperEndMeroField)
  apply Subtype.ext
  rw [upperEndAnalyticDeriv_coe]
  change upperEndGermDeriv (a : Germ upperEndFilter ℂ) =
    ((-c * a : upperEndAnalyticSubring) : Germ upperEndFilter ℂ)
  change
    (deriv (fun z => movingCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ) =
    -(c : Germ upperEndFilter ℂ) * (a : Germ upperEndFilter ℂ)
  rw [upperEndTranslationAnalyticEquiv_coe,
    movingCanonicalSurgeryCarrierUpperEndAnalytic_coe,
    upperEndTranslateGerm_coe]
  change
    (deriv (fun z => movingCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ) =
    ((fun z => -movingCanonicalSurgeryCarrier θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ) *
    ((fun z => movingCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ)
  rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter,
    deriv (fun w => movingCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (w + h)) z =
      (-movingCanonicalSurgeryCarrier θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)) *
      movingCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨-h.im + 1, trivial, fun z hz => ?_⟩
  have hpos : 0 < (z + h).im := by
    change -h.im + 1 < z.im at hz
    simp only [Complex.add_im]
    linarith
  have hrel := neg_logDeriv_movingCanonicalSurgeryProduct_eq θ
    (fun i : Fin 0 => Fin.elim0 i)
    (fun i : Fin 0 => Fin.elim0 i)
    (fun i : Fin 0 => Fin.elim0 i) hpos
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hne := movingCanonicalSurgeryProduct_ne_zero_of_upper θ
    (fun i : Fin 0 => Fin.elim0 i)
    (fun i : Fin 0 => Fin.elim0 i)
    (fun i : Fin 0 => Fin.elim0 i) hpos
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rw [deriv_comp_add_const]
  change -(deriv (movingCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)) (z + h) /
      movingCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)) = _ at hrel
  field_simp [hne] at hrel
  linear_combination -hrel

theorem exists_baseSurgeryProductTranslateFamily_differentialIndependent :
    ∃ θ : BoundedRealSequence,
      DifferentialIndependent (RatFunc ℂ)
        (surgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)) := by
  obtain ⟨θ, hθ⟩ :=
    exists_movingCanonicalTranslation_upperEnd_differentialIndependent
  have hcarrier : DifferentialIndependent (RatFunc ℂ)
      (movingCanonicalSurgeryTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)) :=
    (movingCanonicalSurgeryTranslateFamily_differentialIndependent_iff θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)).2 hθ
  have hneg : DifferentialIndependent (RatFunc ℂ)
      (fun h : ℂ => -movingCanonicalSurgeryTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h) := by
    have h := (_root_.GaloisForLFunctions.differentialIndependent_affineBase_iff
      (F := RatFunc ℂ) (K := upperEndMeroField)
      (movingCanonicalSurgeryTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i))
      (fun _ : ℂ => (-1 : RatFunc ℂ))
      (fun _ : ℂ => (0 : RatFunc ℂ)) (by simp)).2 hcarrier
    simpa using h
  have hlog : DifferentialIndependent (RatFunc ℂ)
      (fun h : ℂ => Differential.logDeriv
        (surgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h)) := by
    simpa only [baseSurgeryProductTranslateFamily_logDeriv] using hneg
  refine ⟨θ, ?_⟩
  exact (differentialIndependent_deriv_div_self_iff
    (F := RatFunc ℂ)
    (surgeryProductTranslateFamily θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i))).2 hlog

/-- Canonical distinct points on the positive imaginary axis. -/
def finiteKreinCenters (k : ℕ) (q : Fin k) : ℂ :=
  ((q.val + 1 : ℕ) : ℂ) * Complex.I

@[simp] theorem finiteKreinCenters_im (k : ℕ) (q : Fin k) :
    (finiteKreinCenters k q).im = (q.val + 1 : ℕ) := by
  simp [finiteKreinCenters]

theorem finiteKreinCenters_im_pos (k : ℕ) (q : Fin k) :
    0 < (finiteKreinCenters k q).im := by
  rw [finiteKreinCenters_im]
  exact_mod_cast Nat.zero_lt_succ q.val

theorem finiteKreinCenters_ne_zero (k : ℕ) (q : Fin k) :
    finiteKreinCenters k q ≠ 0 := by
  intro h
  have hp := finiteKreinCenters_im_pos k q
  rw [h] at hp
  simp at hp

theorem finiteKreinCenters_injective (k : ℕ) :
    Function.Injective (finiteKreinCenters k) := by
  intro i j h
  apply Fin.ext
  have him := congrArg Complex.im h
  simp only [finiteKreinCenters_im] at him
  have hn : i.val + 1 = j.val + 1 := by exact_mod_cast him
  exact Nat.add_right_cancel hn

/-- Literal exact negative-square index predicate for a meromorphic Pick carrier. -/
def HasExactKreinIndex (k m : ℕ)
    (poles : Fin m → ℂ) (M : ℂ → ℂ) : Prop :=
  m = k ∧
    (∀ {N : ℕ} (z : Fin N → ℂ),
      (∀ j, 0 < (z j).im) →
      (∀ i j, z j ≠ poles i) →
      ∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ x ∈ W, x ≠ 0 →
          (star x ⬝ᵥ (carrierPickMatrix M z).mulVec x).re < 0) →
        Module.finrank ℂ W ≤ k) ∧
    ∃ z : Fin m → ℂ,
      (∀ j, 0 < (z j).im) ∧
      (∀ i j, z j ≠ poles i) ∧
      Function.Injective z ∧
      ∀ x : Fin m → ℂ, x ≠ 0 →
        (star x ⬝ᵥ (carrierPickMatrix M z).mulVec x).re < 0

theorem kreinEscapeCarrier_finiteKreinCenters_exact
    (θ : BoundedRealSequence) (k : ℕ) :
    HasExactKreinIndex k (0 + k)
      (Fin.append (fun i : Fin 0 => Fin.elim0 i)
        (finiteKreinCenters k))
      (kreinEscapeCarrier θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (finiteKreinCenters k)) := by
  unfold HasExactKreinIndex
  refine ⟨by simp, ?_⟩
  simpa only [Nat.zero_add] using
    (kreinEscapeCarrier_exact_negativeSquares
      (k := 0) (r := k) θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (finiteKreinCenters k)
      (by
        intro i
        simpa using finiteKreinCenters_im_pos k
          (Fin.cast (Nat.zero_add k) i))
      (by
        intro i j hij
        apply Fin.ext
        have hij' :
            finiteKreinCenters k (Fin.cast (Nat.zero_add k) i) =
              finiteKreinCenters k (Fin.cast (Nat.zero_add k) j) := by
          simpa using hij
        have hc := finiteKreinCenters_injective k hij'
        simpa using congrArg Fin.val hc))

/-- Baseline power-translation field of the canonically free zero-surgery product. -/
def basePowerTranslationField (θ : BoundedRealSequence) (N : ℕ) :
    IntermediateField (RatFunc ℂ) upperEndMeroField :=
  differentialAdjoin (RatFunc ℂ)
    (Set.range fun h : ℂ =>
      (surgeryProductTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h) ^ N)

/-- Power-translation field after inserting `k` positive-half-plane conjugate pairs. -/
def finiteKreinPowerTranslationField
    (θ : BoundedRealSequence) (k N : ℕ) :
    IntermediateField (RatFunc ℂ) upperEndMeroField :=
  differentialAdjoin (RatFunc ℂ)
    (Set.range fun h : ℂ =>
      (kreinEscapeTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (finiteKreinCenters k) h) ^ N)

/-- Logarithmic-residue field after inserting `k` conjugate pairs. -/
def finiteKreinLogResidue
    (θ : BoundedRealSequence) (k : ℕ) :
    IntermediateField (RatFunc ℂ) upperEndMeroField :=
  differentialAdjoin (RatFunc ℂ)
    (Set.range fun h : ℂ => Differential.logDeriv
      (kreinEscapeTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (finiteKreinCenters k) h))

/-- One power-normalization pro-field and its exact logarithmic residue realize every finite Krein
index. -/
theorem exists_powerNormalizationProfield_allFiniteKreinIndex
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    ∃ θ : BoundedRealSequence, ∀ k : ℕ,
      HasExactKreinIndex k (0 + k)
        (Fin.append (fun i : Fin 0 => Fin.elim0 i)
          (finiteKreinCenters k))
        (kreinEscapeCarrier θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (finiteKreinCenters k)) ∧
      AnalyticOnNhd ℂ
        (kreinEscapeProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (finiteKreinCenters k)) Set.univ ∧
      (∀ z, kreinEscapeProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (finiteKreinCenters k) (star z) =
        star (kreinEscapeProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (finiteKreinCenters k) z)) ∧
      OrderOneEnvelope
        (kreinEscapeProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (finiteKreinCenters k)) ∧
      (∀ N, finiteKreinPowerTranslationField θ k N =
        basePowerTranslationField θ N) ∧
      ({z : upperEndMeroField | ∀ n,
          z ∈ finiteKreinPowerTranslationField θ k (D n)} =
        (finiteKreinLogResidue θ k : Set upperEndMeroField)) ∧
      ({z : upperEndMeroField | ∀ n,
          z ∈ finiteKreinPowerTranslationField θ k (D n)} =
        {z : upperEndMeroField | ∀ n,
          z ∈ basePowerTranslationField θ (D n)}) ∧
      DifferentialIndependent (RatFunc ℂ)
        (fun h : ℂ => Differential.logDeriv
          (kreinEscapeTranslateFamily θ
            (fun i : Fin 0 => Fin.elim0 i)
            (fun i : Fin 0 => Fin.elim0 i)
            (fun i : Fin 0 => Fin.elim0 i)
            (finiteKreinCenters k) h)) := by
  obtain ⟨θ, hbase⟩ :=
    exists_baseSurgeryProductTranslateFamily_differentialIndependent
  refine ⟨θ, fun k => ?_⟩
  have hlevel : ∀ N, finiteKreinPowerTranslationField θ k N =
      basePowerTranslationField θ N := by
    intro N
    exact kreinEscapeTranslateFamily_differentialAdjoin_pow_eq θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun q => finiteKreinCenters_ne_zero k q) N
  have hindexed : DifferentialIndependent (RatFunc ℂ)
      (kreinEscapeTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (finiteKreinCenters k)) :=
    (kreinEscapeTranslateFamily_differentialIndependent_iff θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun q => finiteKreinCenters_ne_zero k q)).2 hbase
  have hintersection :=
    arbitraryFamily_strictDivisibility_iInter_eq_logDeriv_embedded_of_roots
      (F := RatFunc ℂ) (E := upperEndMeroField)
      ratFunc_containsAllRootsOfUnity
      (kreinEscapeTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (finiteKreinCenters k))
      hindexed D hD0 hdiv hlt
  have hcommon :
      {z : upperEndMeroField | ∀ n,
          z ∈ finiteKreinPowerTranslationField θ k (D n)} =
        {z : upperEndMeroField | ∀ n,
          z ∈ basePowerTranslationField θ (D n)} := by
    ext z
    simp only [Set.mem_setOf_eq]
    apply forall_congr'
    intro n
    rw [hlevel (D n)]
  refine ⟨kreinEscapeCarrier_finiteKreinCenters_exact θ k,
    kreinEscapeProduct_analytic θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (finiteKreinCenters k),
    kreinEscapeProduct_conj θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (finiteKreinCenters k),
    kreinEscapeProduct_orderOneEnvelope θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (finiteKreinCenters k),
    hlevel, ?_, hcommon, ?_⟩
  · exact hintersection
  · exact arbitraryFamily_logDeriv_differentialIndependent _ hindexed

/-! ## Functional-equation-even amplitude orbit -/

/-- Full complex translation orbit of an even canonical surgery product. -/
def evenSurgeryProductTranslateFamily {k : ℕ}
    (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ)
    (t : Fin k → ℂ) (h : ℂ) : upperEndMeroField :=
  analyticUpperEndMero
    (fun z => movingEvenCanonicalSurgeryProduct θ aIdx bIdx t (z + h)) 0
    (analyticOnNhd_translate_upperTail
      (movingEvenCanonicalSurgeryProduct_analytic θ aIdx bIdx t) h)

theorem baseEvenSurgeryProductTranslateFamily_logDeriv
    (θ : BoundedRealSequence) (h : ℂ) :
    Differential.logDeriv
        (evenSurgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h) =
      -movingEvenCanonicalSurgeryTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h := by
  let a : upperEndAnalyticSubring :=
    analyticUpperEndElement
      (fun z => movingEvenCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)) 0
      (analyticOnNhd_translate_upperTail
        (movingEvenCanonicalSurgeryProduct_analytic θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)) h)
  let c : upperEndAnalyticSubring :=
    upperEndTranslationAnalyticEquiv h
      (movingEvenCanonicalSurgeryCarrierUpperEndAnalytic θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i))
  have ha : evenSurgeryProductTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h =
      algebraMap upperEndAnalyticSubring upperEndMeroField a := rfl
  have hc : movingEvenCanonicalSurgeryTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h =
      algebraMap upperEndAnalyticSubring upperEndMeroField c := by
    rw [movingEvenCanonicalSurgeryTranslateFamily,
      movingEvenCanonicalSurgeryUpperEndMero,
      upperEndTranslationMeroEquiv_algebraMap]
  have hane : a ≠ 0 := by
    intro hzero
    have hzeroGerm :
        ((fun z => movingEvenCanonicalSurgeryProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) (z + h)) :
            Germ upperEndFilter ℂ) = 0 := by
      change (a : Germ upperEndFilter ℂ) = 0
      rw [hzero]
      rfl
    have hzEventually : ∀ᶠ z in upperEndFilter,
        movingEvenCanonicalSurgeryProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) (z + h) = 0 := by
      apply Filter.Germ.coe_eq.mp
      exact hzeroGerm.trans Filter.Germ.coe_zero.symm
    have hneEventually : ∀ᶠ z in upperEndFilter,
        movingEvenCanonicalSurgeryProduct θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) (z + h) ≠ 0 := by
      rw [upperEndFilter_basis.eventually_iff]
      refine ⟨-h.im + 1, trivial, fun z hz => ?_⟩
      have hpos : 0 < (z + h).im := by
        change -h.im + 1 < z.im at hz
        simp only [Complex.add_im]
        linarith
      rw [movingEvenCanonicalSurgeryProduct]
      exact mul_ne_zero
        (movingCanonicalSurgeryProduct_ne_zero_of_nonreal θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (ne_of_gt hpos) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i))
        (movingCanonicalSurgeryProduct_ne_zero_of_nonreal θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (by simpa using neg_ne_zero.mpr (ne_of_gt hpos))
          (fun i => Fin.elim0 i) (fun i => Fin.elim0 i))
    rcases (hzEventually.and hneEventually).exists with ⟨z, hz, hne⟩
    exact hne hz
  rw [ha, hc, Differential.logDeriv,
    upperEndMeroFieldDifferential_algebraMap]
  have hmapne : algebraMap upperEndAnalyticSubring upperEndMeroField a ≠ 0 := by
    intro hzero
    apply hane
    apply IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
    simpa using hzero
  rw [div_eq_iff hmapne, ← map_neg, ← map_mul]
  apply congrArg (algebraMap upperEndAnalyticSubring upperEndMeroField)
  apply Subtype.ext
  rw [upperEndAnalyticDeriv_coe]
  change upperEndGermDeriv (a : Germ upperEndFilter ℂ) =
    ((-c * a : upperEndAnalyticSubring) : Germ upperEndFilter ℂ)
  change
    (deriv (fun z => movingEvenCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ) =
    -(c : Germ upperEndFilter ℂ) * (a : Germ upperEndFilter ℂ)
  rw [upperEndTranslationAnalyticEquiv_coe,
    movingEvenCanonicalSurgeryCarrierUpperEndAnalytic_coe,
    upperEndTranslateGerm_coe]
  change
    (deriv (fun z => movingEvenCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ) =
    ((fun z => -movingEvenCanonicalSurgeryCarrier θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ) *
    ((fun z => movingEvenCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ)
  rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter,
    deriv (fun w => movingEvenCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (w + h)) z =
      (-movingEvenCanonicalSurgeryCarrier θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)) *
      movingEvenCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨-h.im + 1, trivial, fun z hz => ?_⟩
  have hpos : 0 < (z + h).im := by
    change -h.im + 1 < z.im at hz
    simp only [Complex.add_im]
    linarith
  have hrel := neg_logDeriv_movingEvenCanonicalSurgeryProduct_eq θ
    (fun i : Fin 0 => Fin.elim0 i)
    (fun i : Fin 0 => Fin.elim0 i)
    (fun i : Fin 0 => Fin.elim0 i) hpos
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hne : movingEvenCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (z + h) ≠ 0 := by
    rw [movingEvenCanonicalSurgeryProduct]
    exact mul_ne_zero
      (movingCanonicalSurgeryProduct_ne_zero_of_nonreal θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (ne_of_gt hpos) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i))
      (movingCanonicalSurgeryProduct_ne_zero_of_nonreal θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (by simpa using neg_ne_zero.mpr (ne_of_gt hpos))
        (fun i => Fin.elim0 i) (fun i => Fin.elim0 i))
  rw [deriv_comp_add_const]
  change -(deriv (movingEvenCanonicalSurgeryProduct θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)) (z + h) /
      movingEvenCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)) = _ at hrel
  field_simp [hne] at hrel
  linear_combination -hrel

theorem exists_baseEvenSurgeryProductTranslateFamily_differentialIndependent :
    ∃ θ : BoundedRealSequence,
      DifferentialIndependent (RatFunc ℂ)
        (evenSurgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)) := by
  have hdense :=
    movingEvenCanonical_fullTranslationUpperEndDifferentialIndependence_denseResidual
  dsimp only at hdense
  obtain ⟨θ, hθ⟩ := hdense.1.nonempty
  have hbase := hdense.2.2 θ hθ
  have hcarrier : DifferentialIndependent (RatFunc ℂ)
      (movingEvenCanonicalSurgeryTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)) :=
    (movingEvenCanonicalSurgeryTranslateFamily_differentialIndependent_iff θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)).2 hbase
  have hneg : DifferentialIndependent (RatFunc ℂ)
      (fun h : ℂ => -movingEvenCanonicalSurgeryTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h) := by
    have h := (_root_.GaloisForLFunctions.differentialIndependent_affineBase_iff
      (F := RatFunc ℂ) (K := upperEndMeroField)
      (movingEvenCanonicalSurgeryTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i))
      (fun _ : ℂ => (-1 : RatFunc ℂ))
      (fun _ : ℂ => (0 : RatFunc ℂ)) (by simp)).2 hcarrier
    simpa using h
  have hlog : DifferentialIndependent (RatFunc ℂ)
      (fun h : ℂ => Differential.logDeriv
        (evenSurgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h)) := by
    simpa only [baseEvenSurgeryProductTranslateFamily_logDeriv] using hneg
  refine ⟨θ, ?_⟩
  exact (differentialIndependent_deriv_div_self_iff
    (F := RatFunc ℂ)
    (evenSurgeryProductTranslateFamily θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i))).2 hlog

/-! ## Explicit even index packet and rational amplitude gauge -/

def evenSurgeryAIdx {k : ℕ} (q : Fin k) : ℕ := 2 * q.val

def evenSurgeryBIdx {k : ℕ} (q : Fin k) : ℕ := 2 * q.val + 1

theorem evenSurgeryIndexFamily_injective (k : ℕ) :
    Function.Injective
      (movingCanonicalSurgeryIndexFamily
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)) := by
  rintro (i | i) (j | j) h
  · apply congrArg Sum.inl
    apply Fin.ext
    simp only [movingCanonicalSurgeryIndexFamily, Sum.elim_inl,
      evenSurgeryAIdx] at h
    omega
  · simp only [movingCanonicalSurgeryIndexFamily, Sum.elim_inl,
      Sum.elim_inr, evenSurgeryAIdx, evenSurgeryBIdx] at h
    omega
  · simp only [movingCanonicalSurgeryIndexFamily, Sum.elim_inl,
      Sum.elim_inr, evenSurgeryAIdx, evenSurgeryBIdx] at h
    omega
  · apply congrArg Sum.inr
    apply Fin.ext
    simp only [movingCanonicalSurgeryIndexFamily, Sum.elim_inr,
      evenSurgeryBIdx] at h
    omega

/-- Distinct surgery parameters in the open first quadrant. -/
def evenKreinCenters (k : ℕ) (q : Fin k) : ℂ :=
  ((q.val + 1 : ℕ) : ℂ) + ((q.val + 1 : ℕ) : ℂ) * Complex.I

@[simp] theorem evenKreinCenters_re (k : ℕ) (q : Fin k) :
    (evenKreinCenters k q).re = (q.val + 1 : ℕ) := by
  simp [evenKreinCenters]

@[simp] theorem evenKreinCenters_im (k : ℕ) (q : Fin k) :
    (evenKreinCenters k q).im = (q.val + 1 : ℕ) := by
  simp [evenKreinCenters]

theorem evenKreinCenters_re_pos (k : ℕ) (q : Fin k) :
    0 < (evenKreinCenters k q).re := by
  rw [evenKreinCenters_re]
  exact_mod_cast Nat.zero_lt_succ q.val

theorem evenKreinCenters_im_pos (k : ℕ) (q : Fin k) :
    0 < (evenKreinCenters k q).im := by
  rw [evenKreinCenters_im]
  exact_mod_cast Nat.zero_lt_succ q.val

theorem evenKreinCenters_injective (k : ℕ) :
    Function.Injective (evenKreinCenters k) := by
  intro i j h
  apply Fin.ext
  have hre := congrArg Complex.re h
  simp only [evenKreinCenters_re] at hre
  have hn : i.val + 1 = j.val + 1 := by exact_mod_cast hre
  exact Nat.add_right_cancel hn

theorem evenKreinCenters_separated (k : ℕ) :
    EvenSurgeryPoleSeparated (evenKreinCenters k) :=
  evenSurgeryPoleSeparated_of_injective_of_re_pos
    (evenKreinCenters_injective k)
    (evenKreinCenters_re_pos k)

theorem movingEvenCanonicalSurgeryCarrier_exactIndex
    (θ : BoundedRealSequence) (k : ℕ) :
    HasExactKreinIndex (2 * k) (k + k)
      (movingEvenCanonicalSurgeryPoleFamily (evenKreinCenters k))
      (movingEvenCanonicalSurgeryCarrier θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k)) := by
  unfold HasExactKreinIndex
  refine ⟨by omega, ?_⟩
  simpa only [two_mul] using
    (movingEvenCanonicalSurgeryCarrier_exact_negativeSquares θ
      (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
      (evenKreinCenters k)
      (evenKreinCenters_im_pos k)
      (evenKreinCenters_separated k))

def evenSurgeryAmplitudeNumeratorPoly {k : ℕ}
    (t : Fin k → ℂ) : Polynomial ℂ :=
  ∏ i, ((Polynomial.X ^ (2 : ℕ) - Polynomial.C ((t i) ^ (2 : ℕ))) *
    (Polynomial.X ^ (2 : ℕ) - Polynomial.C ((star (t i)) ^ (2 : ℕ))))

def evenSurgeryAmplitudeDenominatorPoly {k : ℕ}
    (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ) : Polynomial ℂ :=
  ∏ i, ((Polynomial.X ^ (2 : ℕ) -
      Polynomial.C ((movingCanonicalZero θ (aIdx i) : ℂ) ^ (2 : ℕ))) *
    (Polynomial.X ^ (2 : ℕ) -
      Polynomial.C ((movingCanonicalZero θ (bIdx i) : ℂ) ^ (2 : ℕ))))

@[simp] theorem eval_evenSurgeryAmplitudeNumeratorPoly {k : ℕ}
    (t : Fin k → ℂ) (z : ℂ) :
    (evenSurgeryAmplitudeNumeratorPoly t).eval z =
      ∏ i, ((z ^ (2 : ℕ) - (t i) ^ (2 : ℕ)) *
        (z ^ (2 : ℕ) - (star (t i)) ^ (2 : ℕ))) := by
  rw [evenSurgeryAmplitudeNumeratorPoly, eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

@[simp] theorem eval_evenSurgeryAmplitudeDenominatorPoly {k : ℕ}
    (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ) (z : ℂ) :
    (evenSurgeryAmplitudeDenominatorPoly θ aIdx bIdx).eval z =
      ∏ i, ((z ^ (2 : ℕ) - (movingCanonicalZero θ (aIdx i) : ℂ) ^ (2 : ℕ)) *
        (z ^ (2 : ℕ) - (movingCanonicalZero θ (bIdx i) : ℂ) ^ (2 : ℕ))) := by
  rw [evenSurgeryAmplitudeDenominatorPoly, eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

theorem evenSurgeryAmplitudeNumeratorPoly_ne_zero {k : ℕ}
    (t : Fin k → ℂ) :
    evenSurgeryAmplitudeNumeratorPoly t ≠ 0 := by
  rw [evenSurgeryAmplitudeNumeratorPoly]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact mul_ne_zero
    (Polynomial.monic_X_pow_sub_C ((t i) ^ (2 : ℕ)) (by omega)).ne_zero
    (Polynomial.monic_X_pow_sub_C ((star (t i)) ^ (2 : ℕ)) (by omega)).ne_zero

theorem evenSurgeryAmplitudeDenominatorPoly_ne_zero {k : ℕ}
    (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ) :
    evenSurgeryAmplitudeDenominatorPoly θ aIdx bIdx ≠ 0 := by
  rw [evenSurgeryAmplitudeDenominatorPoly]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact mul_ne_zero
    (Polynomial.monic_X_pow_sub_C
      ((movingCanonicalZero θ (aIdx i) : ℂ) ^ (2 : ℕ)) (by omega)).ne_zero
    (Polynomial.monic_X_pow_sub_C
      ((movingCanonicalZero θ (bIdx i) : ℂ) ^ (2 : ℕ)) (by omega)).ne_zero

/-- Rational amplitude gauge after translating the coordinate by `h`. -/
def evenSurgeryAmplitudeGaugeRatFunc {k : ℕ}
    (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ)
    (t : Fin k → ℂ) (h : ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (polyTranslationEquiv h (evenSurgeryAmplitudeNumeratorPoly t)) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (polyTranslationEquiv h
        (evenSurgeryAmplitudeDenominatorPoly θ aIdx bIdx))

theorem evenSurgeryAmplitudeGaugeRatFunc_ne_zero {k : ℕ}
    (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ)
    (t : Fin k → ℂ) (h : ℂ) :
    evenSurgeryAmplitudeGaugeRatFunc θ aIdx bIdx t h ≠ 0 := by
  apply div_ne_zero
  · exact (map_ne_zero_iff
      (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (RatFunc.algebraMap_injective ℂ)).2
      ((map_ne_zero_iff (polyTranslationEquiv h)
        (polyTranslationEquiv h).injective).2
          (evenSurgeryAmplitudeNumeratorPoly_ne_zero t))
  · exact (map_ne_zero_iff
      (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (RatFunc.algebraMap_injective ℂ)).2
      ((map_ne_zero_iff (polyTranslationEquiv h)
        (polyTranslationEquiv h).injective).2
          (evenSurgeryAmplitudeDenominatorPoly_ne_zero θ aIdx bIdx))

theorem movingEvenCanonicalSurgeryProduct_empty
    (θ : BoundedRealSequence) (z : ℂ) :
    movingEvenCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) z =
      movingEvenCanonicalProduct θ z := by
  simpa using
    (movingEvenCanonicalSurgeryProduct_eq_paperQuotient θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (by
        intro i
        rcases i with i | i
        · exact Fin.elim0 i
        · exact Fin.elim0 i)
      (z := z) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i))

theorem evenSurgeryProductTranslateFamily_eq_mul {k : ℕ}
    (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (hidx : Function.Injective (movingCanonicalSurgeryIndexFamily aIdx bIdx))
    (h : ℂ) :
    evenSurgeryProductTranslateFamily θ aIdx bIdx t h =
      algebraMap (RatFunc ℂ) upperEndMeroField
          (evenSurgeryAmplitudeGaugeRatFunc θ aIdx bIdx t h) *
        evenSurgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h := by
  let num := polyTranslationEquiv h
    (evenSurgeryAmplitudeNumeratorPoly t)
  let den := polyTranslationEquiv h
    (evenSurgeryAmplitudeDenominatorPoly θ aIdx bIdx)
  have hden : den ≠ 0 :=
    (map_ne_zero_iff (polyTranslationEquiv h)
      (polyTranslationEquiv h).injective).2
        (evenSurgeryAmplitudeDenominatorPoly_ne_zero θ aIdx bIdx)
  have hdenMero : upperEndPolyToMero den ≠ 0 :=
    (map_ne_zero_iff upperEndPolyToMero upperEndPolyToMero_injective).2 hden
  rw [evenSurgeryAmplitudeGaugeRatFunc,
    map_div₀ (algebraMap (RatFunc ℂ) upperEndMeroField)]
  change evenSurgeryProductTranslateFamily θ aIdx bIdx t h =
    upperEndRatfuncToMero
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (polyTranslationEquiv h
            (evenSurgeryAmplitudeNumeratorPoly t))) /
      upperEndRatfuncToMero
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (polyTranslationEquiv h
            (evenSurgeryAmplitudeDenominatorPoly θ aIdx bIdx))) *
      evenSurgeryProductTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h
  rw [upperEndRatfuncToMero_algebraMap_polynomial,
    upperEndRatfuncToMero_algebraMap_polynomial]
  change evenSurgeryProductTranslateFamily θ aIdx bIdx t h =
    upperEndPolyToMero num / upperEndPolyToMero den *
      evenSurgeryProductTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h
  rw [div_mul_eq_mul_div, eq_div_iff hdenMero]
  rw [evenSurgeryProductTranslateFamily,
    evenSurgeryProductTranslateFamily, analyticUpperEndMero,
    analyticUpperEndMero]
  change algebraMap upperEndAnalyticSubring upperEndMeroField _ *
      upperEndPolyToMero den =
    upperEndPolyToMero num *
      algebraMap upperEndAnalyticSubring upperEndMeroField _
  change algebraMap upperEndAnalyticSubring upperEndMeroField _ *
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndPolyToAnalytic den) =
    algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndPolyToAnalytic num) *
      algebraMap upperEndAnalyticSubring upperEndMeroField _
  rw [← map_mul, ← map_mul]
  apply congrArg (algebraMap upperEndAnalyticSubring upperEndMeroField)
  apply Subtype.ext
  change
    ((fun z => movingEvenCanonicalSurgeryProduct θ aIdx bIdx t (z + h)) :
        Germ upperEndFilter ℂ) *
      ((fun z => den.eval z) : Germ upperEndFilter ℂ) =
    ((fun z => num.eval z) : Germ upperEndFilter ℂ) *
      ((fun z => movingEvenCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)) : Germ upperEndFilter ℂ)
  rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter,
    movingEvenCanonicalSurgeryProduct θ aIdx bIdx t (z + h) * den.eval z =
      num.eval z * movingEvenCanonicalSurgeryProduct θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (z + h)
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨-h.im + 1, trivial, fun z hz => ?_⟩
  have hpos : 0 < (z + h).im := by
    change -h.im + 1 < z.im at hz
    simp only [Complex.add_im]
    linarith
  have hza : ∀ i, z + h ≠ (movingCanonicalZero θ (aIdx i) : ℂ) :=
    fun i => movingCanonicalZero_ne_of_im_ne_zero θ (aIdx i) (ne_of_gt hpos)
  have hzb : ∀ i, z + h ≠ (movingCanonicalZero θ (bIdx i) : ℂ) :=
    fun i => movingCanonicalZero_ne_of_im_ne_zero θ (bIdx i) (ne_of_gt hpos)
  have hnza : ∀ i, z + h ≠ -(movingCanonicalZero θ (aIdx i) : ℂ) := by
    intro i heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im] at him
    rw [Complex.add_im] at hpos
    linarith
  have hnzb : ∀ i, z + h ≠ -(movingCanonicalZero θ (bIdx i) : ℂ) := by
    intro i heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im] at him
    rw [Complex.add_im] at hpos
    linarith
  have hquot := movingEvenCanonicalSurgeryProduct_eq_paperQuotient θ
    aIdx bIdx t hidx hza hzb hnza hnzb
  rw [show den.eval z =
      (evenSurgeryAmplitudeDenominatorPoly θ aIdx bIdx).eval (z + h) by
        exact eval_polyTranslationEquiv h _ z,
    show num.eval z =
      (evenSurgeryAmplitudeNumeratorPoly t).eval (z + h) by
        exact eval_polyTranslationEquiv h _ z,
    eval_evenSurgeryAmplitudeDenominatorPoly,
    eval_evenSurgeryAmplitudeNumeratorPoly,
    movingEvenCanonicalSurgeryProduct_empty]
  rw [Finset.prod_div_distrib] at hquot
  have hdeneval :
      (∏ i, (((z + h) ^ (2 : ℕ) -
          (movingCanonicalZero θ (aIdx i) : ℂ) ^ (2 : ℕ)) *
        ((z + h) ^ (2 : ℕ) -
          (movingCanonicalZero θ (bIdx i) : ℂ) ^ (2 : ℕ)))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply mul_ne_zero
    · intro heq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp heq) with heq | heq
      · exact hza i heq
      · exact hnza i heq
    · intro heq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp heq) with heq | heq
      · exact hzb i heq
      · exact hnzb i heq
  field_simp [hdeneval] at hquot ⊢
  simpa [mul_comm, mul_left_comm, mul_assoc] using hquot

def evenBasePowerTranslationField (θ : BoundedRealSequence) (N : ℕ) :
    IntermediateField (RatFunc ℂ) upperEndMeroField :=
  differentialAdjoin (RatFunc ℂ)
    (Set.range fun h : ℂ =>
      (evenSurgeryProductTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) h) ^ N)

def evenFiniteKreinPowerTranslationField
    (θ : BoundedRealSequence) (k N : ℕ) :
    IntermediateField (RatFunc ℂ) upperEndMeroField :=
  differentialAdjoin (RatFunc ℂ)
    (Set.range fun h : ℂ =>
      (evenSurgeryProductTranslateFamily θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k) h) ^ N)

def evenFiniteKreinLogResidue
    (θ : BoundedRealSequence) (k : ℕ) :
    IntermediateField (RatFunc ℂ) upperEndMeroField :=
  differentialAdjoin (RatFunc ℂ)
    (Set.range fun h : ℂ => Differential.logDeriv
      (evenSurgeryProductTranslateFamily θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k) h))

theorem evenFiniteKreinPowerTranslationField_eq
    (θ : BoundedRealSequence) (k N : ℕ) :
    evenFiniteKreinPowerTranslationField θ k N =
      evenBasePowerTranslationField θ N := by
  rw [evenFiniteKreinPowerTranslationField,
    evenBasePowerTranslationField,
    show evenSurgeryProductTranslateFamily θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k) =
      fun h => algebraMap (RatFunc ℂ) upperEndMeroField
          (evenSurgeryAmplitudeGaugeRatFunc θ
            (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
            (evenKreinCenters k) h) *
        evenSurgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h by
      funext h
      exact evenSurgeryProductTranslateFamily_eq_mul θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k)
        (evenSurgeryIndexFamily_injective k) h]
  exact differentialAdjoin_range_pow_baseGauge_eq
    (evenSurgeryProductTranslateFamily θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i))
    (evenSurgeryAmplitudeGaugeRatFunc θ
      (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
      (evenKreinCenters k))
    (evenSurgeryAmplitudeGaugeRatFunc_ne_zero θ
      (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
      (evenKreinCenters k)) N

theorem evenSurgeryProductTranslateFamily_differentialIndependent
    (θ : BoundedRealSequence)
    (hbase : DifferentialIndependent (RatFunc ℂ)
      (evenSurgeryProductTranslateFamily θ
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)))
    (k : ℕ) :
    DifferentialIndependent (RatFunc ℂ)
      (evenSurgeryProductTranslateFamily θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k)) := by
  rw [show evenSurgeryProductTranslateFamily θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k) =
      fun h => algebraMap (RatFunc ℂ) upperEndMeroField
          (evenSurgeryAmplitudeGaugeRatFunc θ
            (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
            (evenKreinCenters k) h) *
        evenSurgeryProductTranslateFamily θ
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i)
          (fun i : Fin 0 => Fin.elim0 i) h by
      funext h
      exact evenSurgeryProductTranslateFamily_eq_mul θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k)
        (evenSurgeryIndexFamily_injective k) h]
  have h := (_root_.GaloisForLFunctions.differentialIndependent_affineBase_iff
    (F := RatFunc ℂ) (K := upperEndMeroField)
    (evenSurgeryProductTranslateFamily θ
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i))
    (evenSurgeryAmplitudeGaugeRatFunc θ
      (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
      (evenKreinCenters k))
    (fun _ : ℂ => (0 : RatFunc ℂ))
    (evenSurgeryAmplitudeGaugeRatFunc_ne_zero θ
      (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
      (evenKreinCenters k))).2 hbase
  simpa using h

theorem exists_powerNormalizationProfield_allEvenKreinIndex
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    ∃ θ : BoundedRealSequence, ∀ k : ℕ,
      HasExactKreinIndex (2 * k) (k + k)
        (movingEvenCanonicalSurgeryPoleFamily (evenKreinCenters k))
        (movingEvenCanonicalSurgeryCarrier θ
          (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
          (evenKreinCenters k)) ∧
      AnalyticOnNhd ℂ
        (movingEvenCanonicalSurgeryProduct θ
          (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
          (evenKreinCenters k)) Set.univ ∧
      (∀ z, movingEvenCanonicalSurgeryProduct θ
          (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
          (evenKreinCenters k) (-z) =
        movingEvenCanonicalSurgeryProduct θ
          (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
          (evenKreinCenters k) z) ∧
      (∀ z, movingEvenCanonicalSurgeryProduct θ
          (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
          (evenKreinCenters k) (conj z) =
        conj (movingEvenCanonicalSurgeryProduct θ
          (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
          (evenKreinCenters k) z)) ∧
      OrderOneEnvelope
        (movingEvenCanonicalSurgeryProduct θ
          (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
          (evenKreinCenters k)) ∧
      (∀ N, evenFiniteKreinPowerTranslationField θ k N =
        evenBasePowerTranslationField θ N) ∧
      ({z : upperEndMeroField | ∀ n,
          z ∈ evenFiniteKreinPowerTranslationField θ k (D n)} =
        (evenFiniteKreinLogResidue θ k : Set upperEndMeroField)) ∧
      ({z : upperEndMeroField | ∀ n,
          z ∈ evenFiniteKreinPowerTranslationField θ k (D n)} =
        {z : upperEndMeroField | ∀ n,
          z ∈ evenBasePowerTranslationField θ (D n)}) ∧
      DifferentialIndependent (RatFunc ℂ)
        (fun h : ℂ => Differential.logDeriv
          (evenSurgeryProductTranslateFamily θ
            (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
            (evenKreinCenters k) h)) := by
  obtain ⟨θ, hbase⟩ :=
    exists_baseEvenSurgeryProductTranslateFamily_differentialIndependent
  refine ⟨θ, fun k => ?_⟩
  have hlevel : ∀ N, evenFiniteKreinPowerTranslationField θ k N =
      evenBasePowerTranslationField θ N :=
    evenFiniteKreinPowerTranslationField_eq θ k
  have hindexed : DifferentialIndependent (RatFunc ℂ)
      (evenSurgeryProductTranslateFamily θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k)) :=
    evenSurgeryProductTranslateFamily_differentialIndependent θ hbase k
  have hintersection :=
    arbitraryFamily_strictDivisibility_iInter_eq_logDeriv_embedded_of_roots
      (F := RatFunc ℂ) (E := upperEndMeroField)
      ratFunc_containsAllRootsOfUnity
      (evenSurgeryProductTranslateFamily θ
        (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
        (evenKreinCenters k))
      hindexed D hD0 hdiv hlt
  have hcommon :
      {z : upperEndMeroField | ∀ n,
          z ∈ evenFiniteKreinPowerTranslationField θ k (D n)} =
        {z : upperEndMeroField | ∀ n,
          z ∈ evenBasePowerTranslationField θ (D n)} := by
    ext z
    simp only [Set.mem_setOf_eq]
    apply forall_congr'
    intro n
    rw [hlevel (D n)]
  have hpackage := movingEvenCanonicalSurgeryProduct_exactOrderOneDivisor θ
    (@evenSurgeryAIdx k) (@evenSurgeryBIdx k)
    (evenKreinCenters k)
    (evenKreinCenters_im_pos k)
    (evenKreinCenters_separated k)
  refine ⟨movingEvenCanonicalSurgeryCarrier_exactIndex θ k,
    hpackage.1, hpackage.2.1, hpackage.2.2.1, hpackage.2.2.2.1,
    hlevel, ?_, hcommon, ?_⟩
  · exact hintersection
  · exact arbitraryFamily_logDeriv_differentialIndependent _ hindexed

end
end GaloisForLFunctions.HTGeometry
