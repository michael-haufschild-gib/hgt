import GaloisForLFunctions.RHTower.FormationBlowupProjectiveKinkBarrierTransgression
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.PositiveOperatorTraceComparison
import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound
import GaloisForLFunctions.RHTower.SoninResidualApertureHilbertSchmidtContinuity
import GaloisForLFunctions.RHTower.EulerValuationLorentzLog
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry

/-!
# Prime-framed integral--nuclear homotopy defect

The trace-one prime--history state is lifted through its full theta frame.  The resulting
two-channel state retains every prime-mixed matrix entry, is recovered exactly by the common
coframe, closes in trace norm at prime infinity, and exposes the sharp norm discontinuity of the
unobserved frame and projection.

Every statement is unconditional.  No divisor, zero, ordinate, or RH hypothesis occurs here.
-/

open Filter Topology
open scoped InnerProductSpace ComplexOrder

namespace RHTower

open ContinuousLinearMap

noncomputable section

abbrev PrimeFramedDouble :=
  WithLp 2 (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert)

private def primeFramedToProd :
    PrimeFramedDouble →L[ℂ]
      PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
    PrimeHodgeHistoryHilbert).toContinuousLinearMap

private def primeFramedOfProd :
    (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert) →L[ℂ]
      PrimeFramedDouble :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
    PrimeHodgeHistoryHilbert).symm.toContinuousLinearMap

def primeFramedFst : PrimeFramedDouble →L[ℂ] PrimeHodgeHistoryHilbert :=
  ContinuousLinearMap.fst ℂ PrimeHodgeHistoryHilbert PrimeHodgeHistoryHilbert ∘L
    primeFramedToProd

def primeFramedSnd : PrimeFramedDouble →L[ℂ] PrimeHodgeHistoryHilbert :=
  ContinuousLinearMap.snd ℂ PrimeHodgeHistoryHilbert PrimeHodgeHistoryHilbert ∘L
    primeFramedToProd

def primeFramedInl : PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble :=
  primeFramedOfProd ∘L
    (ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert).prod
      (0 : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)

def primeFramedInr : PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble :=
  primeFramedOfProd ∘L
    (0 : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert).prod
      (ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert)

@[simp] theorem primeFramedFst_apply (z : PrimeFramedDouble) :
    primeFramedFst z = z.fst := rfl

@[simp] theorem primeFramedSnd_apply (z : PrimeFramedDouble) :
    primeFramedSnd z = z.snd := rfl

@[simp] theorem primeFramedInl_fst (x : PrimeHodgeHistoryHilbert) :
    (primeFramedInl x).fst = x := rfl

@[simp] theorem primeFramedInl_snd (x : PrimeHodgeHistoryHilbert) :
    (primeFramedInl x).snd = 0 := rfl

@[simp] theorem primeFramedInr_fst (x : PrimeHodgeHistoryHilbert) :
    (primeFramedInr x).fst = 0 := rfl

@[simp] theorem primeFramedInr_snd (x : PrimeHodgeHistoryHilbert) :
    (primeFramedInr x).snd = x := rfl

/-- The full theta block rotation `[[V,-C],[C,V]]`. -/
def primeFramedRotation (a : ℝ) : PrimeFramedDouble →L[ℂ] PrimeFramedDouble :=
  primeFramedOfProd ∘L
    (((primeHodgeVisibilityOp a ∘L primeFramedFst) -
        (primeHodgeContrastOp a ∘L primeFramedSnd)).prod
      ((primeHodgeContrastOp a ∘L primeFramedFst) +
        (primeHodgeVisibilityOp a ∘L primeFramedSnd)))

@[simp] theorem primeFramedRotation_fst (a : ℝ) (z : PrimeFramedDouble) :
    (primeFramedRotation a z).fst =
      primeHodgeVisibilityOp a z.fst - primeHodgeContrastOp a z.snd := rfl

@[simp] theorem primeFramedRotation_snd (a : ℝ) (z : PrimeFramedDouble) :
    (primeFramedRotation a z).snd =
      primeHodgeContrastOp a z.fst + primeHodgeVisibilityOp a z.snd := rfl

theorem primeFramedRotation_neg_comp (a : ℝ) :
    primeFramedRotation (-a) ∘L primeFramedRotation a =
      ContinuousLinearMap.id ℂ PrimeFramedDouble := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
    PrimeHodgeHistoryHilbert).injective
  apply Prod.ext
  · change (primeFramedRotation (-a) (primeFramedRotation a z)).fst = z.fst
    simp only [primeFramedRotation_fst, primeFramedRotation_snd]
    rw [primeHodgeVisibilityOp_neg, primeHodgeContrastOp_neg]
    have hs := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ]
        PrimeHodgeHistoryHilbert => A z.fst)
      (primeHodgeVisibilityOp_sq_add_contrastOp_sq a)
    have hc := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ]
        PrimeHodgeHistoryHilbert => A z.snd)
      (primeHodgeVisibilityOp_contrastOp_comm a)
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.id_apply] at hs hc
    calc
      primeHodgeVisibilityOp a
            (primeHodgeVisibilityOp a z.fst - primeHodgeContrastOp a z.snd) -
          (-primeHodgeContrastOp a)
            (primeHodgeContrastOp a z.fst + primeHodgeVisibilityOp a z.snd) =
          (primeHodgeVisibilityOp a (primeHodgeVisibilityOp a z.fst) +
              primeHodgeContrastOp a (primeHodgeContrastOp a z.fst)) +
            (primeHodgeContrastOp a (primeHodgeVisibilityOp a z.snd) -
              primeHodgeVisibilityOp a (primeHodgeContrastOp a z.snd)) := by
            simp only [map_sub, map_add, neg_apply]
            module
      _ = z.fst := by rw [hs, hc]; simp
  · change (primeFramedRotation (-a) (primeFramedRotation a z)).snd = z.snd
    simp only [primeFramedRotation_fst, primeFramedRotation_snd]
    rw [primeHodgeVisibilityOp_neg, primeHodgeContrastOp_neg]
    have hs := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ]
        PrimeHodgeHistoryHilbert => A z.snd)
      (primeHodgeVisibilityOp_sq_add_contrastOp_sq a)
    have hc := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ]
        PrimeHodgeHistoryHilbert => A z.fst)
      (primeHodgeVisibilityOp_contrastOp_comm a)
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.id_apply] at hs hc
    calc
      (-primeHodgeContrastOp a)
            (primeHodgeVisibilityOp a z.fst - primeHodgeContrastOp a z.snd) +
          primeHodgeVisibilityOp a
            (primeHodgeContrastOp a z.fst + primeHodgeVisibilityOp a z.snd) =
          (primeHodgeVisibilityOp a (primeHodgeContrastOp a z.fst) -
              primeHodgeContrastOp a (primeHodgeVisibilityOp a z.fst)) +
            (primeHodgeContrastOp a (primeHodgeContrastOp a z.snd) +
              primeHodgeVisibilityOp a (primeHodgeVisibilityOp a z.snd)) := by
            simp only [map_sub, map_add, neg_apply]
            module
      _ = z.snd := by
        rw [hc, sub_self, zero_add]
        simpa only [add_comm] using hs

theorem primeFramedRotation_comp_neg (a : ℝ) :
    primeFramedRotation a ∘L primeFramedRotation (-a) =
      ContinuousLinearMap.id ℂ PrimeFramedDouble := by
  simpa only [neg_neg] using primeFramedRotation_neg_comp (-a)

theorem primeFramedRotation_neg_eq_adjoint (a : ℝ) :
    primeFramedRotation (-a) =
      ContinuousLinearMap.adjoint (primeFramedRotation a) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change inner ℂ
        (primeHodgeVisibilityOp (-a) z.fst - primeHodgeContrastOp (-a) z.snd)
        w.fst +
      inner ℂ
        (primeHodgeContrastOp (-a) z.fst + primeHodgeVisibilityOp (-a) z.snd)
        w.snd =
    inner ℂ z.fst
        (primeHodgeVisibilityOp a w.fst - primeHodgeContrastOp a w.snd) +
      inner ℂ z.snd
        (primeHodgeContrastOp a w.fst + primeHodgeVisibilityOp a w.snd)
  rw [primeHodgeVisibilityOp_neg, primeHodgeContrastOp_neg]
  have hv1 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (primeHodgeVisibilityOp_isSelfAdjoint a) z.fst w.fst
  have hv2 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (primeHodgeVisibilityOp_isSelfAdjoint a) z.snd w.snd
  have hc1 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (primeHodgeContrastOp_isSelfAdjoint a) z.fst w.snd
  have hc2 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (primeHodgeContrastOp_isSelfAdjoint a) z.snd w.fst
  have hn1 : (-primeHodgeContrastOp a) z.snd =
      -(primeHodgeContrastOp a z.snd) := rfl
  have hn2 : (-primeHodgeContrastOp a) z.fst =
      -(primeHodgeContrastOp a z.fst) := rfl
  rw [hn1, hn2]
  rw [sub_neg_eq_add]
  change inner ℂ
        (primeHodgeVisibilityOp a z.fst + primeHodgeContrastOp a z.snd) w.fst +
      inner ℂ
        (-(primeHodgeContrastOp a z.fst) + primeHodgeVisibilityOp a z.snd) w.snd =
    inner ℂ z.fst
        (primeHodgeVisibilityOp a w.fst - primeHodgeContrastOp a w.snd) +
      inner ℂ z.snd
        (primeHodgeContrastOp a w.fst + primeHodgeVisibilityOp a w.snd)
  simp only [inner_add_left, inner_neg_left, inner_sub_right, inner_add_right]
  have hfirst := congrArg₂ (· + ·) hv1 hc2
  have hsecond := congrArg₂ (· + ·) (congrArg Neg.neg hc1) hv2
  calc
    _ = (inner ℂ z.fst (primeHodgeVisibilityOp a w.fst) +
          inner ℂ z.snd (primeHodgeContrastOp a w.fst)) +
        (-inner ℂ z.fst (primeHodgeContrastOp a w.snd) +
          inner ℂ z.snd (primeHodgeVisibilityOp a w.snd)) :=
      congrArg₂ (· + ·) hfirst hsecond
    _ = _ := by module

theorem adjoint_primeFramedRotation (a : ℝ) :
    ContinuousLinearMap.adjoint (primeFramedRotation a) =
      primeFramedRotation (-a) :=
  (primeFramedRotation_neg_eq_adjoint a).symm

theorem adjoint_primeFramedRotation_comp_self (a : ℝ) :
    ContinuousLinearMap.adjoint (primeFramedRotation a) ∘L
      primeFramedRotation a = ContinuousLinearMap.id ℂ PrimeFramedDouble := by
  rw [adjoint_primeFramedRotation, primeFramedRotation_neg_comp]

theorem primeFramedRotation_comp_adjoint (a : ℝ) :
    primeFramedRotation a ∘L ContinuousLinearMap.adjoint (primeFramedRotation a) =
      ContinuousLinearMap.id ℂ PrimeFramedDouble := by
  rw [adjoint_primeFramedRotation, primeFramedRotation_comp_neg]

/-- Explicit coframe `W_a* (x,y)=V_a x+C_a y`. -/
def primeHodgeSplitCoframe (a : ℝ) :
    PrimeFramedDouble →L[ℂ] PrimeHodgeHistoryHilbert :=
  (primeHodgeVisibilityOp a ∘L primeFramedFst) +
    (primeHodgeContrastOp a ∘L primeFramedSnd)

@[simp] theorem primeHodgeSplitCoframe_apply (a : ℝ) (z : PrimeFramedDouble) :
    primeHodgeSplitCoframe a z =
      primeHodgeVisibilityOp a z.fst + primeHodgeContrastOp a z.snd := rfl

theorem primeHodgeSplitCoframe_eq_adjoint (a : ℝ) :
    primeHodgeSplitCoframe a =
      ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z x
  rw [primeHodgeSplitCoframe_apply, WithLp.prod_inner_apply]
  change inner ℂ
      (primeHodgeVisibilityOp a z.fst + primeHodgeContrastOp a z.snd) x =
    inner ℂ z.fst (primeHodgeVisibilityOp a x) +
      inner ℂ z.snd (primeHodgeContrastOp a x)
  rw [inner_add_left]
  have hv := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (primeHodgeVisibilityOp_isSelfAdjoint a) z.fst x
  have hc := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (primeHodgeContrastOp_isSelfAdjoint a) z.snd x
  exact congrArg₂ (· + ·) hv hc

theorem adjoint_primeHodgeSplitDilation (a : ℝ) :
    ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) =
      primeHodgeSplitCoframe a :=
  (primeHodgeSplitCoframe_eq_adjoint a).symm

/-- Fixed source in the first channel. -/
def primeFramedSource : PrimeFramedDouble →L[ℂ] PrimeFramedDouble :=
  primeFramedInl ∘L
    (primeHodgeHistoryIntegralNuclearDefectT ∘L primeFramedFst)

/-- Framed projection `P_a=W_aW_a*`. -/
def primeFramedProjection (a : ℝ) : PrimeFramedDouble →L[ℂ] PrimeFramedDouble :=
  primeHodgeSplitDilation a ∘L ContinuousLinearMap.adjoint (primeHodgeSplitDilation a)

/-- Framed nuclear orbit `T_a=W_a T W_a*`. -/
def primeFramedNuclearOrbit (a : ℝ) : PrimeFramedDouble →L[ℂ] PrimeFramedDouble :=
  (primeHodgeSplitDilation a ∘L primeHodgeHistoryIntegralNuclearDefectT) ∘L
    ContinuousLinearMap.adjoint (primeHodgeSplitDilation a)

theorem primeFramedNuclearOrbit_eq_rotation (a : ℝ) :
    primeFramedNuclearOrbit a =
      (primeFramedRotation a ∘L primeFramedSource) ∘L
        ContinuousLinearMap.adjoint (primeFramedRotation a) := by
  rw [primeFramedNuclearOrbit, primeFramedSource,
    adjoint_primeHodgeSplitDilation, adjoint_primeFramedRotation]
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
    PrimeHodgeHistoryHilbert).injective
  apply Prod.ext
  · simp only [ContinuousLinearMap.comp_apply]
    change (primeHodgeSplitDilation a
        (primeHodgeHistoryIntegralNuclearDefectT (primeHodgeSplitCoframe a z))).fst =
      (primeFramedRotation a
        (primeFramedInl (primeHodgeHistoryIntegralNuclearDefectT
          (primeFramedFst (primeFramedRotation (-a) z))))).fst
    rw [primeHodgeSplitDilation_fst, primeFramedRotation_fst,
      primeFramedInl_fst, primeFramedInl_snd, map_zero, sub_zero,
      primeHodgeSplitCoframe_apply, primeFramedFst_apply,
      primeFramedRotation_fst, primeHodgeVisibilityOp_neg,
      primeHodgeContrastOp_neg]
    simp
  · simp only [ContinuousLinearMap.comp_apply]
    change (primeHodgeSplitDilation a
        (primeHodgeHistoryIntegralNuclearDefectT (primeHodgeSplitCoframe a z))).snd =
      (primeFramedRotation a
        (primeFramedInl (primeHodgeHistoryIntegralNuclearDefectT
          (primeFramedFst (primeFramedRotation (-a) z))))).snd
    rw [primeHodgeSplitDilation_snd, primeFramedRotation_snd,
      primeFramedInl_fst, primeFramedInl_snd, map_zero, add_zero,
      primeHodgeSplitCoframe_apply, primeFramedFst_apply,
      primeFramedRotation_fst, primeHodgeVisibilityOp_neg,
      primeHodgeContrastOp_neg]
    simp

theorem primeFramedProjection_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (primeFramedProjection a) := by
  change ContinuousLinearMap.adjoint
      (primeHodgeSplitDilation a ∘L
        ContinuousLinearMap.adjoint (primeHodgeSplitDilation a)) =
    primeHodgeSplitDilation a ∘L
      ContinuousLinearMap.adjoint (primeHodgeSplitDilation a)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem primeFramedProjection_idempotent (a : ℝ) :
    primeFramedProjection a ∘L primeFramedProjection a = primeFramedProjection a := by
  change (primeHodgeSplitDilation a ∘L
      ContinuousLinearMap.adjoint (primeHodgeSplitDilation a)) ∘L
      (primeHodgeSplitDilation a ∘L
        ContinuousLinearMap.adjoint (primeHodgeSplitDilation a)) =
    primeHodgeSplitDilation a ∘L
      ContinuousLinearMap.adjoint (primeHodgeSplitDilation a)
  rw [ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc
    (ContinuousLinearMap.adjoint (primeHodgeSplitDilation a))]
  rw [adjoint_primeHodgeSplitDilation_comp_self]
  ext z
  rfl

theorem primeFramedNuclearOrbit_isPositive (a : ℝ) :
    (primeFramedNuclearOrbit a).IsPositive := by
  have hT : 0 ≤ primeHodgeHistoryIntegralNuclearDefectT := by
    rw [ContinuousLinearMap.le_def, sub_zero]
    exact primeHodgeHistoryIntegralNuclearDefect_closed.1
  have h := GaloisForLFunctions.HTGeometry.traceClassSandwich_nonneg
    (primeHodgeSplitDilation a) primeHodgeHistoryIntegralNuclearDefectT hT
  rw [ContinuousLinearMap.le_def, sub_zero] at h
  exact h

theorem primeFramedNuclearOrbit_memSchattenClass_one (a : ℝ) :
    MemSchattenClass 1 (primeFramedNuclearOrbit a) :=
  GaloisForLFunctions.HTGeometry.memSchattenClass_one_sandwich
    (primeHodgeSplitDilation a) primeHodgeHistoryIntegralNuclearDefect_closed.2.1

theorem opTrace_primeFramedNuclearOrbit (a : ℝ) :
    ContinuousLinearMap.opTrace (primeFramedNuclearOrbit a) = 1 := by
  rw [primeFramedNuclearOrbit,
    GaloisForLFunctions.HTGeometry.opTrace_sandwich
      (primeHodgeSplitDilation a) primeHodgeHistoryIntegralNuclearDefectT
      primeHodgeHistoryIntegralNuclearDefect_closed.2.1]
  rw [adjoint_primeHodgeSplitDilation_comp_self]
  simpa using primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1

theorem traceNorm_primeFramedNuclearOrbit (a : ℝ) :
    traceNorm PrimeFramedDouble (primeFramedNuclearOrbit a) = 1 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive
    (primeFramedNuclearOrbit_memSchattenClass_one a)
    (primeFramedNuclearOrbit_isPositive a), opTrace_primeFramedNuclearOrbit]
  rfl

theorem primeFramedNuclearOrbit_recovery (a : ℝ) :
    (ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) ∘L
      primeFramedNuclearOrbit a) ∘L primeHodgeSplitDilation a =
      primeHodgeHistoryIntegralNuclearDefectT := by
  rw [primeFramedNuclearOrbit]
  change ((ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) ∘L
      primeHodgeSplitDilation a) ∘L
      primeHodgeHistoryIntegralNuclearDefectT) ∘L
      (ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) ∘L
        primeHodgeSplitDilation a) = _
  rw [adjoint_primeHodgeSplitDilation_comp_self]
  ext x
  rfl

/-! ## Exact four-channel block matrix -/

def primeFramedVV (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (primeHodgeVisibilityOp a ∘L primeHodgeHistoryIntegralNuclearDefectT) ∘L
    primeHodgeVisibilityOp a

def primeFramedVC (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (primeHodgeVisibilityOp a ∘L primeHodgeHistoryIntegralNuclearDefectT) ∘L
    primeHodgeContrastOp a

def primeFramedCV (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (primeHodgeContrastOp a ∘L primeHodgeHistoryIntegralNuclearDefectT) ∘L
    primeHodgeVisibilityOp a

def primeFramedCC (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (primeHodgeContrastOp a ∘L primeHodgeHistoryIntegralNuclearDefectT) ∘L
    primeHodgeContrastOp a

theorem primeFramedVV_eq_visibleMarginal (a : ℝ) :
    primeFramedVV a = primeHodgeVisibleMarginal a := by
  rw [primeFramedVV, primeHodgeVisibleMarginal, adjoint_primeHodgeVisibilityOp]

theorem primeFramedCC_eq_contrastMarginal (a : ℝ) :
    primeFramedCC a = primeHodgeContrastMarginal a := by
  rw [primeFramedCC, primeHodgeContrastMarginal, adjoint_primeHodgeContrastOp]

theorem primeFramedNuclearOrbit_fst (a : ℝ) (z : PrimeFramedDouble) :
    (primeFramedNuclearOrbit a z).fst =
      primeFramedVV a z.fst + primeFramedVC a z.snd := by
  rw [primeFramedNuclearOrbit, adjoint_primeHodgeSplitDilation]
  change primeHodgeVisibilityOp a
      (primeHodgeHistoryIntegralNuclearDefectT
        (primeHodgeVisibilityOp a z.fst + primeHodgeContrastOp a z.snd)) = _
  rw [map_add, map_add]
  rfl

theorem primeFramedNuclearOrbit_snd (a : ℝ) (z : PrimeFramedDouble) :
    (primeFramedNuclearOrbit a z).snd =
      primeFramedCV a z.fst + primeFramedCC a z.snd := by
  rw [primeFramedNuclearOrbit, adjoint_primeHodgeSplitDilation]
  change primeHodgeContrastOp a
      (primeHodgeHistoryIntegralNuclearDefectT
        (primeHodgeVisibilityOp a z.fst + primeHodgeContrastOp a z.snd)) = _
  rw [map_add, map_add]
  rfl

theorem primeFramedVC_sameHistory_ne_zero {a : ℝ} (ha : a ≠ 0)
    (n : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (primeFramedVC a
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 := by
  let bp := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)
  let bq := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q)
  have hVp := primeHodgeVisibilityOp_lpBasis a (n, p)
  have hCq := primeHodgeContrastOp_lpBasis a (n, q)
  have hsymm : inner ℂ bp (primeHodgeVisibilityOp a
      (primeHodgeHistoryIntegralNuclearDefectT bq)) =
      inner ℂ (primeHodgeVisibilityOp a bp)
        (primeHodgeHistoryIntegralNuclearDefectT bq) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeHodgeVisibilityOp_isSelfAdjoint a) bp
      (primeHodgeHistoryIntegralNuclearDefectT bq)).symm
  rw [primeFramedVC]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hCq, map_smul, map_smul, inner_smul_right, hsymm, hVp,
    inner_smul_left, inner_lpBasis_primeHodgeHistoryIntegralNuclearDefectT]
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr (primeHodgeContrast_ne_zero ha q)
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr (primeHodgeVisibility_pos a p).ne'
  · exact primeHodgeHistoryDefectKernel_sameHistory_ne_zero zero_lt_one n p q

theorem primeFramedCV_sameHistory_ne_zero {a : ℝ} (ha : a ≠ 0)
    (n : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (primeFramedCV a
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 := by
  let bp := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)
  let bq := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q)
  have hCp := primeHodgeContrastOp_lpBasis a (n, p)
  have hVq := primeHodgeVisibilityOp_lpBasis a (n, q)
  have hsymm : inner ℂ bp (primeHodgeContrastOp a
      (primeHodgeHistoryIntegralNuclearDefectT bq)) =
      inner ℂ (primeHodgeContrastOp a bp)
        (primeHodgeHistoryIntegralNuclearDefectT bq) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeHodgeContrastOp_isSelfAdjoint a) bp
      (primeHodgeHistoryIntegralNuclearDefectT bq)).symm
  rw [primeFramedCV]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hVq, map_smul, map_smul, inner_smul_right, hsymm, hCp,
    inner_smul_left, inner_lpBasis_primeHodgeHistoryIntegralNuclearDefectT]
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr (primeHodgeVisibility_pos a q).ne'
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr (primeHodgeContrast_ne_zero ha p)
  · exact primeHodgeHistoryDefectKernel_sameHistory_ne_zero zero_lt_one n p q

theorem primeFramed_four_blocks_sameHistory_ne_zero {a : ℝ} (ha : a ≠ 0)
    (n : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (primeFramedVV a (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 ∧
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (primeFramedVC a (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 ∧
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (primeFramedCV a (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 ∧
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (primeFramedCC a (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 := by
  refine ⟨?_, primeFramedVC_sameHistory_ne_zero ha n p q,
    primeFramedCV_sameHistory_ne_zero ha n p q, ?_⟩
  · rw [primeFramedVV_eq_visibleMarginal]
    exact inner_lpBasis_primeHodgeVisibleMarginal_sameHistory_ne_zero a n p q
  · rw [primeFramedCC_eq_contrastMarginal]
    exact inner_lpBasis_primeHodgeContrastMarginal_sameHistory_ne_zero ha n p q

/-! ## Strong and trace-norm continuity -/

theorem continuous_primeHodgeVisibility (p : Nat.Primes) :
    Continuous (fun a : ℝ => primeHodgeVisibility a p) := by
  unfold primeHodgeVisibility primeHodgeRapidity
  have hlin : Continuous (fun a : ℝ => a * Real.log (p : ℝ) / 2) := by fun_prop
  exact continuous_const.div (Real.continuous_cosh.comp hlin)
    (fun a => (Real.cosh_pos _).ne')

theorem continuous_primeHodgeContrast (p : Nat.Primes) :
    Continuous (fun a : ℝ => primeHodgeContrast a p) := by
  unfold primeHodgeContrast primeHodgeRapidity
  have hlin : Continuous (fun a : ℝ => a * Real.log (p : ℝ) / 2) := by fun_prop
  have heq : (fun a : ℝ => Real.tanh (a * Real.log (p : ℝ) / 2)) =
      fun a => Real.sinh (a * Real.log (p : ℝ) / 2) /
        Real.cosh (a * Real.log (p : ℝ) / 2) := by
    funext a
    rw [Real.tanh_eq_sinh_div_cosh]
  rw [heq]
  exact (Real.continuous_sinh.comp hlin).div (Real.continuous_cosh.comp hlin)
    (fun a => (Real.cosh_pos _).ne')

private theorem tendsto_primeHodgeVisibilityOp_apply_of_tendsto
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (nhds a))
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun n => primeHodgeVisibilityOp (u n) x) atTop
      (nhds (primeHodgeVisibilityOp a x)) := by
  let f : ℕ → PrimeHodgeHistoryIndex → ℝ := fun n np =>
    ‖(((primeHodgeVisibility (u n) np.2 - primeHodgeVisibility a np.2 : ℝ) : ℂ) * x np)‖ ^ 2
  let bound : PrimeHodgeHistoryIndex → ℝ := fun np => 4 * ‖x np‖ ^ 2
  have hbound : Summable bound := by
    dsimp [bound]
    simpa using ((lp.memℓp x).summable (by norm_num)).mul_left 4
  have hpoint : ∀ np, Tendsto (fun n => f n np) atTop (nhds 0) := by
    intro np
    have hs : Tendsto (fun n =>
        primeHodgeVisibility (u n) np.2 - primeHodgeVisibility a np.2)
        atTop (nhds 0) := by
      simpa using ((continuous_primeHodgeVisibility np.2).continuousAt.tendsto.comp hu).sub_const
        (primeHodgeVisibility a np.2)
    have hc : Tendsto (fun n =>
        (((primeHodgeVisibility (u n) np.2 - primeHodgeVisibility a np.2 : ℝ) : ℂ) * x np))
        atTop (nhds 0) := by
      simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hs).mul_const (x np)
    simpa [f] using (tendsto_norm.comp hc).pow 2
  have hdom : ∀ᶠ n in atTop, ∀ np, ‖f n np‖ ≤ bound np := by
    refine Eventually.of_forall fun n np => ?_
    have hvn := primeHodgeVisibility_le_one (u n) np.2
    have hvn0 := (primeHodgeVisibility_pos (u n) np.2).le
    have hva := primeHodgeVisibility_le_one a np.2
    have hva0 := (primeHodgeVisibility_pos a np.2).le
    have hd : ‖primeHodgeVisibility (u n) np.2 - primeHodgeVisibility a np.2‖ ≤ 2 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    change |‖(((primeHodgeVisibility (u n) np.2 -
      primeHodgeVisibility a np.2 : ℝ) : ℂ) * x np)‖ ^ 2| ≤ 4 * ‖x np‖ ^ 2
    rw [abs_of_nonneg (sq_nonneg _), norm_mul]
    have hdc : ‖((primeHodgeVisibility (u n) np.2 -
        primeHodgeVisibility a np.2 : ℝ) : ℂ)‖ ≤ 2 := by
      simpa only [Complex.norm_real] using hd
    calc
      (‖((primeHodgeVisibility (u n) np.2 -
          primeHodgeVisibility a np.2 : ℝ) : ℂ)‖ * ‖x np‖) ^ 2 ≤
          (2 * ‖x np‖) ^ 2 := by gcongr
      _ = 4 * ‖x np‖ ^ 2 := by ring
  have htsum : Tendsto (fun n => ∑' np, f n np) atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hsq : ∀ n,
      ‖primeHodgeVisibilityOp (u n) x - primeHodgeVisibilityOp a x‖ ^ 2 =
        ∑' np, f n np := by
    intro n
    have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
      (by norm_num) (primeHodgeVisibilityOp (u n) x - primeHodgeVisibilityOp a x)
    norm_num at hnorm
    rw [hnorm]
    apply tsum_congr
    intro np
    rw [← sub_mul]
    change ‖((primeHodgeVisibility (u n) np.2 : ℂ) -
      (primeHodgeVisibility a np.2 : ℂ)) * x np‖ ^ 2 = f n np
    simp only [f, Complex.ofReal_sub]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp htsum
  have hnorm : Tendsto (fun n =>
      ‖primeHodgeVisibilityOp (u n) x - primeHodgeVisibilityOp a x‖)
      atTop (nhds 0) := by
    have hsqrt' : Tendsto (fun n => Real.sqrt (∑' np, f n np))
        atTop (nhds 0) := by simpa [Function.comp_def] using hsqrt
    convert hsqrt' using 1
    · funext n
      rw [← hsq n, Real.sqrt_sq (norm_nonneg _)]
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using hnorm

private theorem tendsto_primeHodgeContrastOp_apply_of_tendsto
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (nhds a))
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun n => primeHodgeContrastOp (u n) x) atTop
      (nhds (primeHodgeContrastOp a x)) := by
  let f : ℕ → PrimeHodgeHistoryIndex → ℝ := fun n np =>
    ‖(((primeHodgeContrast (u n) np.2 - primeHodgeContrast a np.2 : ℝ) : ℂ) * x np)‖ ^ 2
  let bound : PrimeHodgeHistoryIndex → ℝ := fun np => 4 * ‖x np‖ ^ 2
  have hbound : Summable bound := by
    dsimp [bound]
    simpa using ((lp.memℓp x).summable (by norm_num)).mul_left 4
  have hpoint : ∀ np, Tendsto (fun n => f n np) atTop (nhds 0) := by
    intro np
    have hs : Tendsto (fun n =>
        primeHodgeContrast (u n) np.2 - primeHodgeContrast a np.2)
        atTop (nhds 0) := by
      simpa using ((continuous_primeHodgeContrast np.2).continuousAt.tendsto.comp hu).sub_const
        (primeHodgeContrast a np.2)
    have hc : Tendsto (fun n =>
        (((primeHodgeContrast (u n) np.2 - primeHodgeContrast a np.2 : ℝ) : ℂ) * x np))
        atTop (nhds 0) := by
      simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hs).mul_const (x np)
    simpa [f] using (tendsto_norm.comp hc).pow 2
  have hdom : ∀ᶠ n in atTop, ∀ np, ‖f n np‖ ≤ bound np := by
    refine Eventually.of_forall fun n np => ?_
    have hvn := abs_primeHodgeContrast_lt_one (u n) np.2
    have hva := abs_primeHodgeContrast_lt_one a np.2
    have hd : ‖primeHodgeContrast (u n) np.2 - primeHodgeContrast a np.2‖ ≤ 2 := by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by linarith)
    change |‖(((primeHodgeContrast (u n) np.2 -
      primeHodgeContrast a np.2 : ℝ) : ℂ) * x np)‖ ^ 2| ≤ 4 * ‖x np‖ ^ 2
    rw [abs_of_nonneg (sq_nonneg _), norm_mul]
    have hdc : ‖((primeHodgeContrast (u n) np.2 -
        primeHodgeContrast a np.2 : ℝ) : ℂ)‖ ≤ 2 := by
      simpa only [Complex.norm_real] using hd
    calc
      (‖((primeHodgeContrast (u n) np.2 -
          primeHodgeContrast a np.2 : ℝ) : ℂ)‖ * ‖x np‖) ^ 2 ≤
          (2 * ‖x np‖) ^ 2 := by gcongr
      _ = 4 * ‖x np‖ ^ 2 := by ring
  have htsum : Tendsto (fun n => ∑' np, f n np) atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hsq : ∀ n,
      ‖primeHodgeContrastOp (u n) x - primeHodgeContrastOp a x‖ ^ 2 =
        ∑' np, f n np := by
    intro n
    have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
      (by norm_num) (primeHodgeContrastOp (u n) x - primeHodgeContrastOp a x)
    norm_num at hnorm
    rw [hnorm]
    apply tsum_congr
    intro np
    rw [← sub_mul]
    change ‖((primeHodgeContrast (u n) np.2 : ℂ) -
      (primeHodgeContrast a np.2 : ℂ)) * x np‖ ^ 2 = f n np
    simp only [f, Complex.ofReal_sub]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp htsum
  have hnorm : Tendsto (fun n =>
      ‖primeHodgeContrastOp (u n) x - primeHodgeContrastOp a x‖)
      atTop (nhds 0) := by
    have hsqrt' : Tendsto (fun n => Real.sqrt (∑' np, f n np))
        atTop (nhds 0) := by simpa [Function.comp_def] using hsqrt
    convert hsqrt' using 1
    · funext n
      rw [← hsq n, Real.sqrt_sq (norm_nonneg _)]
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using hnorm

theorem tendsto_primeHodgeSplitDilation_apply_of_tendsto
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (nhds a))
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun n => primeHodgeSplitDilation (u n) x) atTop
      (nhds (primeHodgeSplitDilation a x)) := by
  have hv := tendsto_primeHodgeVisibilityOp_apply_of_tendsto hu x
  have hc := tendsto_primeHodgeContrastOp_apply_of_tendsto hu x
  have hprod : Tendsto (fun n =>
      (primeHodgeVisibilityOp (u n) x, primeHodgeContrastOp (u n) x)) atTop
      (nhds (primeHodgeVisibilityOp a x, primeHodgeContrastOp a x)) := by
    simpa only [nhds_prod_eq] using hv.prodMk hc
  have hout := (primeFramedOfProd.continuous.tendsto
    (primeHodgeVisibilityOp a x, primeHodgeContrastOp a x)).comp hprod
  change Tendsto (fun n => primeFramedOfProd
      (primeHodgeVisibilityOp (u n) x, primeHodgeContrastOp (u n) x)) atTop
    (nhds (primeFramedOfProd
      (primeHodgeVisibilityOp a x, primeHodgeContrastOp a x)))
  exact hout

/-- Positive square root of the fixed prime-mixed trace-one state. -/
def primeFramedSourceRoot :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  traceClassRoot primeHodgeHistoryIntegralNuclearDefectT

theorem primeFramedSourceRoot_isHilbertSchmidt :
    primeFramedSourceRoot.IsHilbertSchmidt :=
  traceClassRoot_isHilbertSchmidt
    primeHodgeHistoryIntegralNuclearDefect_closed.2.1

theorem primeFramedSourceRoot_comp_self :
    primeFramedSourceRoot ∘L primeFramedSourceRoot =
      primeHodgeHistoryIntegralNuclearDefectT := by
  rw [primeFramedSourceRoot, traceClassRoot_comp_self]
  apply ContinuousLinearMap.absOp_of_nonneg
  rw [ContinuousLinearMap.le_def, sub_zero]
  exact primeHodgeHistoryIntegralNuclearDefect_closed.1

theorem primeFramedSourceRoot_isSelfAdjoint :
    IsSelfAdjoint primeFramedSourceRoot :=
  isSelfAdjoint_traceClassRoot _

/-- Hilbert--Schmidt lift whose Gram operator is the framed nuclear orbit. -/
def primeFramedRootLift (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble :=
  primeHodgeSplitDilation a ∘L primeFramedSourceRoot

theorem primeFramedRootLift_isHilbertSchmidt (a : ℝ) :
    (primeFramedRootLift a).IsHilbertSchmidt :=
  primeFramedSourceRoot_isHilbertSchmidt.comp_left (primeHodgeSplitDilation a)

theorem hsNormSq_primeFramedRootLift (a : ℝ) :
    (primeFramedRootLift a).hsNormSq = primeFramedSourceRoot.hsNormSq := by
  exact ContinuousLinearMap.hsNormSq_comp_left_eq_of_norm_map
    primeFramedSourceRoot_isHilbertSchmidt
    (primeHodgeSplitDilation a) (norm_primeHodgeSplitDilation a)

theorem hsNorm_primeFramedRootLift (a : ℝ) :
    (primeFramedRootLift a).hsNorm = primeFramedSourceRoot.hsNorm := by
  unfold ContinuousLinearMap.hsNorm
  rw [hsNormSq_primeFramedRootLift]

theorem primeFramedNuclearOrbit_eq_rootGram (a : ℝ) :
    primeFramedNuclearOrbit a =
      primeFramedRootLift a ∘L
        ContinuousLinearMap.adjoint (primeFramedRootLift a) := by
  have hrootAdj : ContinuousLinearMap.adjoint primeFramedSourceRoot =
      primeFramedSourceRoot := primeFramedSourceRoot_isSelfAdjoint
  rw [primeFramedNuclearOrbit, primeFramedRootLift,
    ContinuousLinearMap.adjoint_comp, hrootAdj]
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply]
  have hroot := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ]
      PrimeHodgeHistoryHilbert =>
        A (ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) z))
    primeFramedSourceRoot_comp_self
  simp only [ContinuousLinearMap.comp_apply] at hroot
  rw [hroot]

private theorem tendsto_hsNormSq_primeFramedRootLift_sub_of_tendsto
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (nhds a)) :
    Tendsto (fun n => (primeFramedRootLift (u n) -
      primeFramedRootLift a).hsNormSq) atTop (nhds 0) := by
  let b := ContinuousLinearMap.hsBasis ℂ PrimeHodgeHistoryHilbert
  let D : ℕ → PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble :=
    fun n => primeFramedRootLift (u n) - primeFramedRootLift a
  have hD : ∀ n, (D n).IsHilbertSchmidt := fun n =>
    (primeFramedRootLift_isHilbertSchmidt (u n)).sub
      (primeFramedRootLift_isHilbertSchmidt a)
  have hpoint : ∀ i, Tendsto (fun n => ‖D n (b i)‖ ^ 2) atTop (nhds 0) := by
    intro i
    have hs := tendsto_primeHodgeSplitDilation_apply_of_tendsto hu
      (primeFramedSourceRoot (b i))
    have hz : Tendsto (fun n => D n (b i)) atTop (nhds 0) := by
      simpa [D, primeFramedRootLift, ContinuousLinearMap.comp_apply] using
        hs.sub_const (primeHodgeSplitDilation a (primeFramedSourceRoot (b i)))
    simpa using (tendsto_norm.comp hz).pow 2
  let bound : (exists_hilbertBasis ℂ PrimeHodgeHistoryHilbert).choose → ℝ :=
    fun i => 4 * ‖primeFramedSourceRoot (b i)‖ ^ 2
  have hbound : Summable bound := by
    dsimp [bound, b]
    exact (primeFramedSourceRoot_isHilbertSchmidt.summable
      (ContinuousLinearMap.hsBasis ℂ PrimeHodgeHistoryHilbert)).mul_left 4
  have hdom : ∀ᶠ n in atTop, ∀ i, ‖‖D n (b i)‖ ^ 2‖ ≤ bound i := by
    refine Eventually.of_forall fun n i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have htri := norm_sub_le
      (primeFramedRootLift (u n) (b i)) (primeFramedRootLift a (b i))
    have h1 := norm_primeHodgeSplitDilation (u n) (primeFramedSourceRoot (b i))
    have h2 := norm_primeHodgeSplitDilation a (primeFramedSourceRoot (b i))
    have hle : ‖D n (b i)‖ ≤ 2 * ‖primeFramedSourceRoot (b i)‖ := by
      dsimp [D, primeFramedRootLift]
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      dsimp [primeFramedRootLift] at htri
      rw [h1, h2] at htri
      linarith
    dsimp [bound]
    calc
      ‖D n (b i)‖ ^ 2 ≤ (2 * ‖primeFramedSourceRoot (b i)‖) ^ 2 := by gcongr
      _ = 4 * ‖primeFramedSourceRoot (b i)‖ ^ 2 := by ring
  have ht := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hsum : Tendsto (fun n => ∑' i, ‖D n (b i)‖ ^ 2) atTop (nhds 0) := by
    simpa using ht
  simpa [D, ContinuousLinearMap.hsNormSq_eq (hD _) b] using hsum

private theorem tendsto_hsNorm_primeFramedRootLift_sub_of_tendsto
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (nhds a)) :
    Tendsto (fun n => (primeFramedRootLift (u n) -
      primeFramedRootLift a).hsNorm) atTop (nhds 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_hsNormSq_primeFramedRootLift_sub_of_tendsto hu)
  simpa [ContinuousLinearMap.hsNorm, Function.comp_def] using hs

private theorem adjoint_sub_eq_sub_adjoint
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A B : E →L[ℂ] F) :
    ContinuousLinearMap.adjoint (A - B) =
      ContinuousLinearMap.adjoint A - ContinuousLinearMap.adjoint B := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y x
  simp only [sub_apply, inner_sub_left, inner_sub_right]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]

private theorem primeFramedNuclearOrbit_sub_decomposition (a b : ℝ) :
    primeFramedNuclearOrbit b - primeFramedNuclearOrbit a =
      (primeFramedRootLift b - primeFramedRootLift a) ∘L
          ContinuousLinearMap.adjoint (primeFramedRootLift b) +
        primeFramedRootLift a ∘L
          ContinuousLinearMap.adjoint
            (primeFramedRootLift b - primeFramedRootLift a) := by
  rw [primeFramedNuclearOrbit_eq_rootGram,
    primeFramedNuclearOrbit_eq_rootGram,
    adjoint_sub_eq_sub_adjoint]
  ext z
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

private theorem primeFramedNuclearOrbit_sub_memSchattenClass_one (a b : ℝ) :
    MemSchattenClass 1
      (primeFramedNuclearOrbit b - primeFramedNuclearOrbit a) := by
  let D := primeFramedRootLift b - primeFramedRootLift a
  have hD : D.IsHilbertSchmidt :=
    (primeFramedRootLift_isHilbertSchmidt b).sub
      (primeFramedRootLift_isHilbertSchmidt a)
  have hfirstRect : MemRectSchattenClass 1
      (D ∘L ContinuousLinearMap.adjoint (primeFramedRootLift b)) :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
      (primeFramedRootLift_isHilbertSchmidt b).adjoint hD
  have hsecondRect : MemRectSchattenClass 1
      (primeFramedRootLift a ∘L ContinuousLinearMap.adjoint D) :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
      hD.adjoint (primeFramedRootLift_isHilbertSchmidt a)
  have hfirst : MemSchattenClass 1
      (D ∘L ContinuousLinearMap.adjoint (primeFramedRootLift b)) :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hfirstRect
  have hsecond : MemSchattenClass 1
      (primeFramedRootLift a ∘L ContinuousLinearMap.adjoint D) :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hsecondRect
  rw [primeFramedNuclearOrbit_sub_decomposition]
  change MemSchattenClass 1
    (D ∘L ContinuousLinearMap.adjoint (primeFramedRootLift b) +
      primeFramedRootLift a ∘L ContinuousLinearMap.adjoint D)
  exact memSchattenClass_one_add (hfirst.isCompactOperator one_pos)
    (hsecond.isCompactOperator one_pos)
    hfirst hsecond

/-- Quantitative Hilbert--Schmidt-to-trace-norm control for the framed orbit. -/
theorem traceNorm_primeFramedNuclearOrbit_sub_le (a b : ℝ) :
    traceNorm PrimeFramedDouble
        (primeFramedNuclearOrbit b - primeFramedNuclearOrbit a) ≤
      2 * primeFramedSourceRoot.hsNorm *
        (primeFramedRootLift b - primeFramedRootLift a).hsNorm := by
  let D := primeFramedRootLift b - primeFramedRootLift a
  have hD : D.IsHilbertSchmidt :=
    (primeFramedRootLift_isHilbertSchmidt b).sub
      (primeFramedRootLift_isHilbertSchmidt a)
  let A := D ∘L ContinuousLinearMap.adjoint (primeFramedRootLift b)
  let B := primeFramedRootLift a ∘L ContinuousLinearMap.adjoint D
  have hArect : MemRectSchattenClass 1 A :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
      (primeFramedRootLift_isHilbertSchmidt b).adjoint hD
  have hBrect : MemRectSchattenClass 1 B :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
      hD.adjoint (primeFramedRootLift_isHilbertSchmidt a)
  have hA : MemSchattenClass 1 A :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hArect
  have hB : MemSchattenClass 1 B :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hBrect
  have htri : traceNorm PrimeFramedDouble (A + B) ≤
      traceNorm PrimeFramedDouble A + traceNorm PrimeFramedDouble B :=
    traceNorm_add_le (hA.isCompactOperator one_pos) (hB.isCompactOperator one_pos)
      hA.one_summable_approxNumber hB.one_summable_approxNumber
  have hAbound : traceNorm PrimeFramedDouble A ≤
      D.hsNorm * (primeFramedRootLift b).hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted
      (primeFramedRootLift_isHilbertSchmidt b).adjoint hD
    simpa [A, ContinuousLinearMap.hsNorm,
      (primeFramedRootLift_isHilbertSchmidt b).hsNormSq_adjoint,
      mul_comm] using h
  have hBbound : traceNorm PrimeFramedDouble B ≤
      D.hsNorm * (primeFramedRootLift a).hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted
      hD.adjoint (primeFramedRootLift_isHilbertSchmidt a)
    simpa [ContinuousLinearMap.hsNorm, hD.hsNormSq_adjoint,
      mul_comm] using h
  rw [primeFramedNuclearOrbit_sub_decomposition]
  change traceNorm PrimeFramedDouble (A + B) ≤ _
  calc
    traceNorm PrimeFramedDouble (A + B) ≤
        traceNorm PrimeFramedDouble A + traceNorm PrimeFramedDouble B := htri
    _ ≤ D.hsNorm * (primeFramedRootLift b).hsNorm +
        D.hsNorm * (primeFramedRootLift a).hsNorm := add_le_add hAbound hBbound
    _ = 2 * primeFramedSourceRoot.hsNorm * D.hsNorm := by
      rw [hsNorm_primeFramedRootLift, hsNorm_primeFramedRootLift]
      ring

/-- Sequential trace-norm continuity of the framed nuclear orbit. -/
theorem tendsto_traceNorm_primeFramedNuclearOrbit_sub_of_tendsto
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (nhds a)) :
    Tendsto (fun n => traceNorm PrimeFramedDouble
      (primeFramedNuclearOrbit (u n) - primeFramedNuclearOrbit a))
      atTop (nhds 0) := by
  have hupper : Tendsto (fun n =>
      2 * primeFramedSourceRoot.hsNorm *
        (primeFramedRootLift (u n) - primeFramedRootLift a).hsNorm)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_hsNorm_primeFramedRootLift_sub_of_tendsto hu))
  refine squeeze_zero' (Eventually.of_forall fun n => traceNorm_nonneg _) ?_ hupper
  filter_upwards with n
  exact traceNorm_primeFramedNuclearOrbit_sub_le a (u n)

/-- The orbit is continuous in the nuclear norm, not merely strongly continuous. -/
theorem continuous_primeFramedNuclearOrbit_traceNorm (a : ℝ) :
    Tendsto (fun b => traceNorm PrimeFramedDouble
      (primeFramedNuclearOrbit b - primeFramedNuclearOrbit a))
      (nhds a) (nhds 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  exact tendsto_traceNorm_primeFramedNuclearOrbit_sub_of_tendsto hu

/-! ### Prime-infinity endpoint -/

theorem primeHodgeVisibility_tendsto_atTop (p : Nat.Primes) :
    Tendsto (fun a : ℝ => primeHodgeVisibility a p) atTop (nhds 0) := by
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hscale : Tendsto (fun a : ℝ => a * Real.log (p : ℝ))
      atTop atTop := tendsto_id.atTop_mul_const hp
  simpa [primeHodgeVisibility, primeHodgeRapidity, formationVisibility,
    Function.comp_def] using formationVisibility_tendsto_atTop.comp hscale

theorem primeHodgeVisibility_tendsto_atBot (p : Nat.Primes) :
    Tendsto (fun a : ℝ => primeHodgeVisibility a p) atBot (nhds 0) := by
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hscale : Tendsto (fun a : ℝ => a * Real.log (p : ℝ))
      atBot atBot := tendsto_id.atBot_mul_const hp
  simpa [primeHodgeVisibility, primeHodgeRapidity, formationVisibility,
    Function.comp_def] using formationVisibility_tendsto_atBot.comp hscale

theorem primeHodgeContrast_tendsto_atTop (p : Nat.Primes) :
    Tendsto (fun a : ℝ => primeHodgeContrast a p) atTop (nhds 1) := by
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hscale : Tendsto (fun a : ℝ => a * Real.log (p : ℝ))
      atTop atTop := tendsto_id.atTop_mul_const hp
  simpa [primeHodgeContrast, primeHodgeRapidity, formationContrast,
    Function.comp_def] using formationContrast_tendsto_atTop.comp hscale

theorem primeHodgeContrast_tendsto_atBot (p : Nat.Primes) :
    Tendsto (fun a : ℝ => primeHodgeContrast a p) atBot (nhds (-1)) := by
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hscale : Tendsto (fun a : ℝ => a * Real.log (p : ℝ))
      atBot atBot := tendsto_id.atBot_mul_const hp
  simpa [primeHodgeContrast, primeHodgeRapidity, formationContrast,
    Function.comp_def] using formationContrast_tendsto_atBot.comp hscale

private theorem tendsto_primeHodgeHistoryHilbert_of_pointwise_dominated
    {A : Type*} {l : Filter A}
    (u : A → PrimeHodgeHistoryHilbert) (y : PrimeHodgeHistoryHilbert)
    (bound : PrimeHodgeHistoryIndex → ℝ)
    (hbound : Summable bound)
    (hpoint : ∀ np, Tendsto (fun t => u t np) l (nhds (y np)))
    (hdom : ∀ᶠ t in l, ∀ np, ‖‖u t np - y np‖ ^ 2‖ ≤ bound np) :
    Tendsto u l (nhds y) := by
  let f : A → PrimeHodgeHistoryIndex → ℝ :=
    fun t np => ‖u t np - y np‖ ^ 2
  have hfpoint : ∀ np, Tendsto (fun t => f t np) l (nhds 0) := by
    intro np
    have hz := (hpoint np).sub_const (y np)
    simpa [f] using (tendsto_norm.comp hz).pow 2
  have htsum : Tendsto (fun t => ∑' np, f t np) l (nhds 0) := by
    simpa [f] using tendsto_tsum_of_dominated_convergence hbound hfpoint hdom
  have hsq : ∀ t, ‖u t - y‖ ^ 2 = ∑' np, f t np := by
    intro t
    have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
      (by norm_num) (u t - y)
    norm_num at hnorm
    simpa [f] using hnorm
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp htsum
  have hnorm : Tendsto (fun t => ‖u t - y‖) l (nhds 0) := by
    have hsqrt' : Tendsto (fun t => Real.sqrt (∑' np, f t np)) l (nhds 0) := by
      simpa [Function.comp_def] using hsqrt
    convert hsqrt' using 1
    funext t
    rw [← hsq t, Real.sqrt_sq (norm_nonneg _)]
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using hnorm

private theorem tendsto_primeHodgeVisibilityOp_apply_atTop
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun a : ℝ => primeHodgeVisibilityOp a x) atTop (nhds 0) := by
  let bound : PrimeHodgeHistoryIndex → ℝ := fun np => 4 * ‖x np‖ ^ 2
  have hbound : Summable bound := by
    dsimp [bound]
    simpa using ((lp.memℓp x).summable (by norm_num)).mul_left 4
  apply tendsto_primeHodgeHistoryHilbert_of_pointwise_dominated
    (fun a => primeHodgeVisibilityOp a x) 0 bound hbound
  · intro np
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (primeHodgeVisibility_tendsto_atTop np.2)
    simpa using hs.mul_const (x np)
  · refine Eventually.of_forall fun a np => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖((primeHodgeVisibility a np.2 : ℝ) : ℂ) * x np - 0‖ ^ 2 ≤
      bound np
    rw [sub_zero, norm_mul]
    have hv : ‖((primeHodgeVisibility a np.2 : ℝ) : ℂ)‖ ≤ 1 :=
      norm_primeHodgeVisibility_le_one a np
    dsimp [bound]
    calc
      (‖((primeHodgeVisibility a np.2 : ℝ) : ℂ)‖ * ‖x np‖) ^ 2 ≤
          (1 * ‖x np‖) ^ 2 := by gcongr
      _ ≤ 4 * ‖x np‖ ^ 2 := by nlinarith [sq_nonneg ‖x np‖]

private theorem tendsto_primeHodgeVisibilityOp_apply_atBot
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun a : ℝ => primeHodgeVisibilityOp a x) atBot (nhds 0) := by
  have hneg : Tendsto (fun a : ℝ => -a) atBot atTop :=
    tendsto_neg_atTop_iff.mpr tendsto_id
  simpa [Function.comp_def, primeHodgeVisibilityOp_neg] using
    (tendsto_primeHodgeVisibilityOp_apply_atTop x).comp hneg

private theorem tendsto_primeHodgeContrastOp_apply_atTop
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun a : ℝ => primeHodgeContrastOp a x) atTop (nhds x) := by
  let bound : PrimeHodgeHistoryIndex → ℝ := fun np => 4 * ‖x np‖ ^ 2
  have hbound : Summable bound := by
    dsimp [bound]
    simpa using ((lp.memℓp x).summable (by norm_num)).mul_left 4
  apply tendsto_primeHodgeHistoryHilbert_of_pointwise_dominated
    (fun a => primeHodgeContrastOp a x) x bound hbound
  · intro np
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (primeHodgeContrast_tendsto_atTop np.2)
    simpa using hs.mul_const (x np)
  · refine Eventually.of_forall fun a np => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖((primeHodgeContrast a np.2 : ℝ) : ℂ) * x np - x np‖ ^ 2 ≤
      bound np
    have hc : ‖((primeHodgeContrast a np.2 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_primeHodgeContrast_lt_one a np.2).le
    have htri : ‖((primeHodgeContrast a np.2 : ℝ) : ℂ) * x np - x np‖ ≤
        2 * ‖x np‖ := by
      calc
        ‖((primeHodgeContrast a np.2 : ℝ) : ℂ) * x np - x np‖ ≤
            ‖((primeHodgeContrast a np.2 : ℝ) : ℂ) * x np‖ + ‖x np‖ :=
          norm_sub_le _ _
        _ = ‖((primeHodgeContrast a np.2 : ℝ) : ℂ)‖ * ‖x np‖ +
            ‖x np‖ := by rw [norm_mul]
        _ ≤ 2 * ‖x np‖ := by nlinarith [norm_nonneg (x np)]
    dsimp [bound]
    calc
      ‖((primeHodgeContrast a np.2 : ℝ) : ℂ) * x np - x np‖ ^ 2 ≤
          (2 * ‖x np‖) ^ 2 := by gcongr
      _ = 4 * ‖x np‖ ^ 2 := by ring

private theorem tendsto_primeHodgeContrastOp_apply_atBot
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun a : ℝ => primeHodgeContrastOp a x) atBot (nhds (-x)) := by
  have hneg : Tendsto (fun a : ℝ => -a) atBot atTop :=
    tendsto_neg_atTop_iff.mpr tendsto_id
  have htop := (tendsto_primeHodgeContrastOp_apply_atTop x).comp hneg
  have h := (continuous_neg.tendsto x).comp htop
  simpa [Function.comp_def, primeHodgeContrastOp_neg] using h

def primeFramedEndpointCoframePlus :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble := primeFramedInr

def primeFramedEndpointCoframeMinus :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble := -primeFramedInr

theorem tendsto_primeHodgeSplitDilation_apply_atTop
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun a : ℝ => primeHodgeSplitDilation a x) atTop
      (nhds (primeFramedEndpointCoframePlus x)) := by
  have hv := tendsto_primeHodgeVisibilityOp_apply_atTop x
  have hc := tendsto_primeHodgeContrastOp_apply_atTop x
  have hprod : Tendsto (fun a : ℝ =>
      (primeHodgeVisibilityOp a x, primeHodgeContrastOp a x)) atTop
      (nhds ((0 : PrimeHodgeHistoryHilbert), x)) := by
    simpa only [nhds_prod_eq] using hv.prodMk hc
  have hout := (primeFramedOfProd.continuous.tendsto
    ((0 : PrimeHodgeHistoryHilbert), x)).comp hprod
  change Tendsto (fun a : ℝ => primeFramedOfProd
      (primeHodgeVisibilityOp a x, primeHodgeContrastOp a x)) atTop
    (nhds (primeFramedOfProd ((0 : PrimeHodgeHistoryHilbert), x)))
  simpa only [Function.comp_def] using hout

theorem tendsto_primeHodgeSplitDilation_apply_atBot
    (x : PrimeHodgeHistoryHilbert) :
    Tendsto (fun a : ℝ => primeHodgeSplitDilation a x) atBot
      (nhds (primeFramedEndpointCoframeMinus x)) := by
  have hv := tendsto_primeHodgeVisibilityOp_apply_atBot x
  have hc := tendsto_primeHodgeContrastOp_apply_atBot x
  have hprod : Tendsto (fun a : ℝ =>
      (primeHodgeVisibilityOp a x, primeHodgeContrastOp a x)) atBot
      (nhds ((0 : PrimeHodgeHistoryHilbert), -x)) := by
    simpa only [nhds_prod_eq] using hv.prodMk hc
  have hout := (primeFramedOfProd.continuous.tendsto
    ((0 : PrimeHodgeHistoryHilbert), -x)).comp hprod
  have hend : primeFramedEndpointCoframeMinus x =
      primeFramedOfProd ((0 : PrimeHodgeHistoryHilbert), -x) := by
    change -primeFramedOfProd ((0 : PrimeHodgeHistoryHilbert), x) =
      primeFramedOfProd ((0 : PrimeHodgeHistoryHilbert), -x)
    rw [← map_neg]
    congr 1
    ext <;> simp
  rw [hend]
  change Tendsto (fun a : ℝ => primeFramedOfProd
      (primeHodgeVisibilityOp a x, primeHodgeContrastOp a x)) atBot
    (nhds (primeFramedOfProd ((0 : PrimeHodgeHistoryHilbert), -x)))
  simpa only [Function.comp_def] using hout

theorem norm_primeFramedEndpointCoframePlus
    (x : PrimeHodgeHistoryHilbert) :
    ‖primeFramedEndpointCoframePlus x‖ = ‖x‖ := by
  have hlim := tendsto_norm.comp (tendsto_primeHodgeSplitDilation_apply_atTop x)
  have hconst : Tendsto (fun _ : ℝ => ‖x‖) atTop (nhds ‖x‖) := tendsto_const_nhds
  have hframe : Tendsto (fun a : ℝ => ‖primeHodgeSplitDilation a x‖)
      atTop (nhds ‖x‖) := by
    convert hconst using 1
    funext a
    exact norm_primeHodgeSplitDilation a x
  exact tendsto_nhds_unique hlim hframe

theorem norm_primeFramedEndpointCoframeMinus
    (x : PrimeHodgeHistoryHilbert) :
    ‖primeFramedEndpointCoframeMinus x‖ = ‖x‖ := by
  have hlim := tendsto_norm.comp (tendsto_primeHodgeSplitDilation_apply_atBot x)
  have hconst : Tendsto (fun _ : ℝ => ‖x‖) atBot (nhds ‖x‖) := tendsto_const_nhds
  have hframe : Tendsto (fun a : ℝ => ‖primeHodgeSplitDilation a x‖)
      atBot (nhds ‖x‖) := by
    convert hconst using 1
    funext a
    exact norm_primeHodgeSplitDilation a x
  exact tendsto_nhds_unique hlim hframe

theorem adjoint_primeFramedEndpointCoframePlus :
    ContinuousLinearMap.adjoint primeFramedEndpointCoframePlus = primeFramedSnd := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z x
  rw [WithLp.prod_inner_apply]
  simp [primeFramedEndpointCoframePlus]

theorem adjoint_primeFramedEndpointCoframeMinus :
    ContinuousLinearMap.adjoint primeFramedEndpointCoframeMinus = -primeFramedSnd := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z x
  rw [WithLp.prod_inner_apply]
  simp [primeFramedEndpointCoframeMinus]

def primeFramedEndpointRootPlus :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble :=
  primeFramedEndpointCoframePlus ∘L primeFramedSourceRoot

def primeFramedEndpointRootMinus :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble :=
  primeFramedEndpointCoframeMinus ∘L primeFramedSourceRoot

theorem primeFramedEndpointRootPlus_isHilbertSchmidt :
    primeFramedEndpointRootPlus.IsHilbertSchmidt :=
  primeFramedSourceRoot_isHilbertSchmidt.comp_left primeFramedEndpointCoframePlus

theorem primeFramedEndpointRootMinus_isHilbertSchmidt :
    primeFramedEndpointRootMinus.IsHilbertSchmidt :=
  primeFramedSourceRoot_isHilbertSchmidt.comp_left primeFramedEndpointCoframeMinus

theorem hsNorm_primeFramedEndpointRootPlus :
    primeFramedEndpointRootPlus.hsNorm = primeFramedSourceRoot.hsNorm := by
  unfold ContinuousLinearMap.hsNorm
  rw [primeFramedEndpointRootPlus]
  rw [ContinuousLinearMap.hsNormSq_comp_left_eq_of_norm_map
    primeFramedSourceRoot_isHilbertSchmidt primeFramedEndpointCoframePlus
    norm_primeFramedEndpointCoframePlus]

theorem hsNorm_primeFramedEndpointRootMinus :
    primeFramedEndpointRootMinus.hsNorm = primeFramedSourceRoot.hsNorm := by
  unfold ContinuousLinearMap.hsNorm
  rw [primeFramedEndpointRootMinus]
  rw [ContinuousLinearMap.hsNormSq_comp_left_eq_of_norm_map
    primeFramedSourceRoot_isHilbertSchmidt primeFramedEndpointCoframeMinus
    norm_primeFramedEndpointCoframeMinus]

private theorem tendsto_hsNormSq_primeFramedRootLift_sub_endpoint
    (l : Filter ℝ)
    (Wend : PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble)
    (hWnorm : ∀ x, ‖Wend x‖ = ‖x‖)
    (hW : ∀ x, Tendsto (fun a : ℝ => primeHodgeSplitDilation a x) l
      (nhds (Wend x))) :
    Tendsto (fun a => (primeFramedRootLift a -
      Wend ∘L primeFramedSourceRoot).hsNormSq) l (nhds 0) := by
  let b := ContinuousLinearMap.hsBasis ℂ PrimeHodgeHistoryHilbert
  let Kend := Wend ∘L primeFramedSourceRoot
  let D : ℝ → PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble :=
    fun a => primeFramedRootLift a - Kend
  have hKend : Kend.IsHilbertSchmidt :=
    primeFramedSourceRoot_isHilbertSchmidt.comp_left Wend
  have hD : ∀ a, (D a).IsHilbertSchmidt := fun a =>
    (primeFramedRootLift_isHilbertSchmidt a).sub hKend
  have hpoint : ∀ i, Tendsto (fun a => ‖D a (b i)‖ ^ 2) l (nhds 0) := by
    intro i
    have hs := hW (primeFramedSourceRoot (b i))
    have hz : Tendsto (fun a => D a (b i)) l (nhds 0) := by
      simpa [D, Kend, primeFramedRootLift, ContinuousLinearMap.comp_apply] using
        hs.sub_const (Wend (primeFramedSourceRoot (b i)))
    simpa using (tendsto_norm.comp hz).pow 2
  let bound : (exists_hilbertBasis ℂ PrimeHodgeHistoryHilbert).choose → ℝ :=
    fun i => 4 * ‖primeFramedSourceRoot (b i)‖ ^ 2
  have hbound : Summable bound := by
    dsimp [bound, b]
    exact (primeFramedSourceRoot_isHilbertSchmidt.summable
      (ContinuousLinearMap.hsBasis ℂ PrimeHodgeHistoryHilbert)).mul_left 4
  have hdom : ∀ᶠ a in l, ∀ i, ‖‖D a (b i)‖ ^ 2‖ ≤ bound i := by
    refine Eventually.of_forall fun a i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have htri := norm_sub_le
      (primeFramedRootLift a (b i)) (Kend (b i))
    have h1 := norm_primeHodgeSplitDilation a (primeFramedSourceRoot (b i))
    have h2 := hWnorm (primeFramedSourceRoot (b i))
    have hle : ‖D a (b i)‖ ≤ 2 * ‖primeFramedSourceRoot (b i)‖ := by
      dsimp [D, Kend, primeFramedRootLift]
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      dsimp [D, Kend, primeFramedRootLift] at htri
      rw [h1, h2] at htri
      linarith
    dsimp [bound]
    calc
      ‖D a (b i)‖ ^ 2 ≤ (2 * ‖primeFramedSourceRoot (b i)‖) ^ 2 := by gcongr
      _ = 4 * ‖primeFramedSourceRoot (b i)‖ ^ 2 := by ring
  have ht := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hsum : Tendsto (fun a => ∑' i, ‖D a (b i)‖ ^ 2) l (nhds 0) := by
    simpa using ht
  simpa [D, Kend, ContinuousLinearMap.hsNormSq_eq (hD _) b] using hsum

private theorem tendsto_hsNorm_primeFramedRootLift_sub_endpoint
    (l : Filter ℝ)
    (Wend : PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble)
    (hWnorm : ∀ x, ‖Wend x‖ = ‖x‖)
    (hW : ∀ x, Tendsto (fun a : ℝ => primeHodgeSplitDilation a x) l
      (nhds (Wend x))) :
    Tendsto (fun a => (primeFramedRootLift a -
      Wend ∘L primeFramedSourceRoot).hsNorm) l (nhds 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_hsNormSq_primeFramedRootLift_sub_endpoint l Wend hWnorm hW)
  simpa [ContinuousLinearMap.hsNorm, Function.comp_def] using hs

theorem tendsto_hsNorm_primeFramedRootLift_sub_endpointPlus :
    Tendsto (fun a => (primeFramedRootLift a -
      primeFramedEndpointRootPlus).hsNorm) atTop (nhds 0) := by
  simpa [primeFramedEndpointRootPlus] using
    tendsto_hsNorm_primeFramedRootLift_sub_endpoint atTop
      primeFramedEndpointCoframePlus norm_primeFramedEndpointCoframePlus
      tendsto_primeHodgeSplitDilation_apply_atTop

theorem tendsto_hsNorm_primeFramedRootLift_sub_endpointMinus :
    Tendsto (fun a => (primeFramedRootLift a -
      primeFramedEndpointRootMinus).hsNorm) atBot (nhds 0) := by
  simpa [primeFramedEndpointRootMinus] using
    tendsto_hsNorm_primeFramedRootLift_sub_endpoint atBot
      primeFramedEndpointCoframeMinus norm_primeFramedEndpointCoframeMinus
      tendsto_primeHodgeSplitDilation_apply_atBot

/-- Common prime-infinity endpoint, literally the fixed trace-one source in second channel. -/
def primeFramedEndpoint : PrimeFramedDouble →L[ℂ] PrimeFramedDouble :=
  (primeFramedInr ∘L primeHodgeHistoryIntegralNuclearDefectT) ∘L primeFramedSnd

@[simp] theorem primeFramedEndpoint_fst (z : PrimeFramedDouble) :
    (primeFramedEndpoint z).fst = 0 := rfl

@[simp] theorem primeFramedEndpoint_snd (z : PrimeFramedDouble) :
    (primeFramedEndpoint z).snd =
      primeHodgeHistoryIntegralNuclearDefectT z.snd := rfl

theorem primeFramedEndpoint_eq_rootGramPlus :
    primeFramedEndpoint = primeFramedEndpointRootPlus ∘L
      ContinuousLinearMap.adjoint primeFramedEndpointRootPlus := by
  have hrootAdj : ContinuousLinearMap.adjoint primeFramedSourceRoot =
      primeFramedSourceRoot := primeFramedSourceRoot_isSelfAdjoint
  rw [primeFramedEndpointRootPlus, ContinuousLinearMap.adjoint_comp,
    adjoint_primeFramedEndpointCoframePlus, hrootAdj]
  apply ContinuousLinearMap.ext
  intro z
  simp only [primeFramedEndpoint, ContinuousLinearMap.comp_apply]
  rw [← primeFramedSourceRoot_comp_self]
  rfl

theorem primeFramedEndpoint_eq_rootGramMinus :
    primeFramedEndpoint = primeFramedEndpointRootMinus ∘L
      ContinuousLinearMap.adjoint primeFramedEndpointRootMinus := by
  have hrootAdj : ContinuousLinearMap.adjoint primeFramedSourceRoot =
      primeFramedSourceRoot := primeFramedSourceRoot_isSelfAdjoint
  rw [primeFramedEndpointRootMinus, ContinuousLinearMap.adjoint_comp,
    adjoint_primeFramedEndpointCoframeMinus, hrootAdj]
  apply ContinuousLinearMap.ext
  intro z
  simp only [primeFramedEndpoint, ContinuousLinearMap.comp_apply, neg_apply,
    map_neg]
  rw [← primeFramedSourceRoot_comp_self]
  simp [primeFramedEndpointCoframeMinus]

private theorem traceNorm_gram_sub_le
    {K L : PrimeHodgeHistoryHilbert →L[ℂ] PrimeFramedDouble}
    (hK : K.IsHilbertSchmidt) (hL : L.IsHilbertSchmidt) :
    traceNorm PrimeFramedDouble
        (K ∘L ContinuousLinearMap.adjoint K -
          L ∘L ContinuousLinearMap.adjoint L) ≤
      (K.hsNorm + L.hsNorm) * (K - L).hsNorm := by
  let D := K - L
  let A := D ∘L ContinuousLinearMap.adjoint K
  let B := L ∘L ContinuousLinearMap.adjoint D
  have hD : D.IsHilbertSchmidt := hK.sub hL
  have hArect : MemRectSchattenClass 1 A :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hK.adjoint hD
  have hBrect : MemRectSchattenClass 1 B :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hD.adjoint hL
  have hA : MemSchattenClass 1 A :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hArect
  have hB : MemSchattenClass 1 B :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp hBrect
  have htri : traceNorm PrimeFramedDouble (A + B) ≤
      traceNorm PrimeFramedDouble A + traceNorm PrimeFramedDouble B :=
    traceNorm_add_le (hA.isCompactOperator one_pos) (hB.isCompactOperator one_pos)
      hA.one_summable_approxNumber hB.one_summable_approxNumber
  have hAbound : traceNorm PrimeFramedDouble A ≤ K.hsNorm * D.hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hK.adjoint hD
    simpa [A, ContinuousLinearMap.hsNorm, hK.hsNormSq_adjoint] using h
  have hBbound : traceNorm PrimeFramedDouble B ≤ D.hsNorm * L.hsNorm := by
    rw [← rectTraceNorm_eq_traceNorm]
    have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hD.adjoint hL
    simpa [B, ContinuousLinearMap.hsNorm, hD.hsNormSq_adjoint, mul_comm] using h
  have hdecomp :
      K ∘L ContinuousLinearMap.adjoint K -
          L ∘L ContinuousLinearMap.adjoint L = A + B := by
    dsimp [A, B, D]
    rw [adjoint_sub_eq_sub_adjoint]
    ext z
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hdecomp]
  calc
    traceNorm PrimeFramedDouble (A + B) ≤
        traceNorm PrimeFramedDouble A + traceNorm PrimeFramedDouble B := htri
    _ ≤ K.hsNorm * D.hsNorm + D.hsNorm * L.hsNorm :=
      add_le_add hAbound hBbound
    _ = (K.hsNorm + L.hsNorm) * D.hsNorm := by ring

theorem primeFramedNuclearOrbit_tendsto_endpoint_atTop :
    Tendsto (fun a => traceNorm PrimeFramedDouble
      (primeFramedNuclearOrbit a - primeFramedEndpoint)) atTop (nhds 0) := by
  have hupper : Tendsto (fun a =>
      ((primeFramedRootLift a).hsNorm + primeFramedEndpointRootPlus.hsNorm) *
        (primeFramedRootLift a - primeFramedEndpointRootPlus).hsNorm)
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => 2 * primeFramedSourceRoot.hsNorm)
        atTop (nhds (2 * primeFramedSourceRoot.hsNorm)) := tendsto_const_nhds
    simpa [hsNorm_primeFramedRootLift, hsNorm_primeFramedEndpointRootPlus,
      two_mul] using
      hconst.mul tendsto_hsNorm_primeFramedRootLift_sub_endpointPlus
  refine squeeze_zero' (Eventually.of_forall fun a => traceNorm_nonneg _) ?_ hupper
  refine Eventually.of_forall fun a => ?_
  rw [primeFramedNuclearOrbit_eq_rootGram,
    primeFramedEndpoint_eq_rootGramPlus]
  exact traceNorm_gram_sub_le (primeFramedRootLift_isHilbertSchmidt a)
    primeFramedEndpointRootPlus_isHilbertSchmidt

theorem primeFramedNuclearOrbit_tendsto_endpoint_atBot :
    Tendsto (fun a => traceNorm PrimeFramedDouble
      (primeFramedNuclearOrbit a - primeFramedEndpoint)) atBot (nhds 0) := by
  have hupper : Tendsto (fun a =>
      ((primeFramedRootLift a).hsNorm + primeFramedEndpointRootMinus.hsNorm) *
        (primeFramedRootLift a - primeFramedEndpointRootMinus).hsNorm)
      atBot (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => 2 * primeFramedSourceRoot.hsNorm)
        atBot (nhds (2 * primeFramedSourceRoot.hsNorm)) := tendsto_const_nhds
    simpa [hsNorm_primeFramedRootLift, hsNorm_primeFramedEndpointRootMinus,
      two_mul] using
      hconst.mul tendsto_hsNorm_primeFramedRootLift_sub_endpointMinus
  refine squeeze_zero' (Eventually.of_forall fun a => traceNorm_nonneg _) ?_ hupper
  refine Eventually.of_forall fun a => ?_
  rw [primeFramedNuclearOrbit_eq_rootGram,
    primeFramedEndpoint_eq_rootGramMinus]
  exact traceNorm_gram_sub_le (primeFramedRootLift_isHilbertSchmidt a)
    primeFramedEndpointRootMinus_isHilbertSchmidt

/-! ### Exact strong/operator-norm defect -/

theorem primeHodgeVisibilityOp_isPositive (a : ℝ) :
    (primeHodgeVisibilityOp a).IsPositive := by
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (primeHodgeVisibilityOp_isSelfAdjoint a), fun f => ?_⟩
  have hsum : Summable fun np =>
      inner ℂ ((primeHodgeVisibilityOp a f) np) (f np) := lp.summable_inner _ _
  show (0 : ℝ) ≤ (inner ℂ (primeHodgeVisibilityOp a f) f).re
  rw [lp.inner_eq_tsum, Complex.re_tsum hsum]
  refine tsum_nonneg fun np => ?_
  have hval : inner ℂ ((primeHodgeVisibilityOp a f) np) (f np) =
      ((primeHodgeVisibility a np.2 : ℂ)) *
        ((Complex.normSq (f np) : ℝ) : ℂ) := by
    simp only [primeHodgeVisibilityOp_apply, RCLike.inner_apply, map_mul,
      Complex.conj_ofReal]
    rw [← Complex.mul_conj]
    ring
  rw [hval]
  simp [Complex.normSq_nonneg, mul_nonneg, (primeHodgeVisibility_pos a np.2).le]

private theorem inner_primeHodgeSplitDilation_zero
    (a : ℝ) (x : PrimeHodgeHistoryHilbert) :
    inner ℂ (primeHodgeSplitDilation a x) (primeHodgeSplitDilation 0 x) =
      inner ℂ (primeHodgeVisibilityOp a x) x := by
  rw [WithLp.prod_inner_apply]
  simp [primeHodgeVisibilityOp_zero, primeHodgeContrastOp_zero]

private theorem norm_primeHodgeSplitDilation_sub_zero_apply_le
    (a : ℝ) (x : PrimeHodgeHistoryHilbert) :
    ‖(primeHodgeSplitDilation a - primeHodgeSplitDilation 0) x‖ ≤
      Real.sqrt 2 * ‖x‖ := by
  have hsq : ‖primeHodgeSplitDilation a x - primeHodgeSplitDilation 0 x‖ ^ 2 =
      ‖primeHodgeSplitDilation a x‖ ^ 2 -
        2 * (inner ℂ (primeHodgeSplitDilation a x)
          (primeHodgeSplitDilation 0 x)).re +
        ‖primeHodgeSplitDilation 0 x‖ ^ 2 :=
    @norm_sub_sq ℂ PrimeFramedDouble _ _ _
      (primeHodgeSplitDilation a x) (primeHodgeSplitDilation 0 x)
  rw [norm_primeHodgeSplitDilation, norm_primeHodgeSplitDilation,
    inner_primeHodgeSplitDilation_zero] at hsq
  have hpos := (primeHodgeVisibilityOp_isPositive a).2 x
  change 0 ≤ (inner ℂ (primeHodgeVisibilityOp a x) x).re at hpos
  have hsqrt : (Real.sqrt 2 * ‖x‖) ^ 2 = 2 * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hsqle :
      ‖(primeHodgeSplitDilation a - primeHodgeSplitDilation 0) x‖ ^ 2 ≤
        (Real.sqrt 2 * ‖x‖) ^ 2 := by
    simp only [sub_apply]
    rw [hsq, hsqrt]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsqle

theorem norm_primeHodgeSplitDilation_sub_zero_le (a : ℝ) :
    ‖primeHodgeSplitDilation a - primeHodgeSplitDilation 0‖ ≤ Real.sqrt 2 :=
  (primeHodgeSplitDilation a - primeHodgeSplitDilation 0).opNorm_le_bound
    (Real.sqrt_nonneg 2) (norm_primeHodgeSplitDilation_sub_zero_apply_le a)

theorem primeHodgeVisibility_tendsto_cofinite_zero {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun p : Nat.Primes => primeHodgeVisibility a p)
      cofinite (nhds 0) := by
  have hp := tendsto_primes_cofinite_atTop
  have hlog : Tendsto (fun p : Nat.Primes => Real.log (p : ℝ))
      cofinite atTop := Real.tendsto_log_atTop.comp hp
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hscale : Tendsto (fun p : Nat.Primes => a * Real.log (p : ℝ))
        cofinite atBot := hlog.const_mul_atTop_of_neg haNeg
    simpa [primeHodgeVisibility, primeHodgeRapidity, formationVisibility,
      Function.comp_def] using formationVisibility_tendsto_atBot.comp hscale
  · have hscale : Tendsto (fun p : Nat.Primes => a * Real.log (p : ℝ))
        cofinite atTop := hlog.const_mul_atTop haPos
    simpa [primeHodgeVisibility, primeHodgeRapidity, formationVisibility,
      Function.comp_def] using formationVisibility_tendsto_atTop.comp hscale

private theorem norm_lpBasis_primeHodgeHistoryIndex
    (np : PrimeHodgeHistoryIndex) :
    ‖HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np‖ = 1 := by
  rw [HilbertSchmidt.lpBasis_apply,
    lp.norm_single (E := fun _ : PrimeHodgeHistoryIndex => ℂ)
      (p := 2) (by norm_num) np (1 : ℂ)]
  simp

private theorem norm_primeHodgeSplitDilation_sub_zero_lpBasis_sq
    (a : ℝ) (np : PrimeHodgeHistoryIndex) :
    ‖(primeHodgeSplitDilation a - primeHodgeSplitDilation 0)
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)‖ ^ 2 =
      2 * (1 - primeHodgeVisibility a np.2) := by
  let e := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np
  have he : ‖e‖ = 1 := norm_lpBasis_primeHodgeHistoryIndex np
  have hV := primeHodgeVisibilityOp_lpBasis a np
  have hinter : (inner ℂ (primeHodgeVisibilityOp a e) e).re =
      primeHodgeVisibility a np.2 := by
    rw [hV, inner_smul_left, inner_self_eq_norm_sq_to_K, he]
    simp
  have hsq : ‖primeHodgeSplitDilation a e - primeHodgeSplitDilation 0 e‖ ^ 2 =
      ‖primeHodgeSplitDilation a e‖ ^ 2 -
        2 * (inner ℂ (primeHodgeSplitDilation a e)
          (primeHodgeSplitDilation 0 e)).re +
        ‖primeHodgeSplitDilation 0 e‖ ^ 2 :=
    @norm_sub_sq ℂ PrimeFramedDouble _ _ _
      (primeHodgeSplitDilation a e) (primeHodgeSplitDilation 0 e)
  rw [norm_primeHodgeSplitDilation, norm_primeHodgeSplitDilation,
    inner_primeHodgeSplitDilation_zero, he, hinter] at hsq
  change ‖primeHodgeSplitDilation a e - primeHodgeSplitDilation 0 e‖ ^ 2 = _
  rw [hsq]
  ring

theorem norm_primeHodgeSplitDilation_sub_zero {a : ℝ} (ha : a ≠ 0) :
    ‖primeHodgeSplitDilation a - primeHodgeSplitDilation 0‖ = Real.sqrt 2 := by
  let e : Nat.Primes → PrimeHodgeHistoryHilbert := fun p =>
    HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p)
  have hsquare : Tendsto (fun p : Nat.Primes =>
      ‖(primeHodgeSplitDilation a - primeHodgeSplitDilation 0) (e p)‖ ^ 2)
      cofinite (nhds 2) := by
    have hone : Tendsto (fun _ : Nat.Primes => (1 : ℝ)) cofinite (nhds 1) :=
      tendsto_const_nhds
    have h := (hone.sub
      (primeHodgeVisibility_tendsto_cofinite_zero ha)).const_mul 2
    convert h using 1
    · funext p
      exact norm_primeHodgeSplitDilation_sub_zero_lpBasis_sq a (0, p)
    · norm_num
  have hnorm : Tendsto (fun p : Nat.Primes =>
      ‖(primeHodgeSplitDilation a - primeHodgeSplitDilation 0) (e p)‖)
      cofinite (nhds (Real.sqrt 2)) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    convert hsqrt using 1
    funext p
    change ‖(primeHodgeSplitDilation a - primeHodgeSplitDilation 0) (e p)‖ =
      Real.sqrt (‖(primeHodgeSplitDilation a - primeHodgeSplitDilation 0) (e p)‖ ^ 2)
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hlower : Real.sqrt 2 ≤
      ‖primeHodgeSplitDilation a - primeHodgeSplitDilation 0‖ := by
    apply le_of_tendsto' hnorm
    intro p
    have hop := (primeHodgeSplitDilation a - primeHodgeSplitDilation 0).le_opNorm (e p)
    rw [norm_lpBasis_primeHodgeHistoryIndex] at hop
    simpa [e] using hop
  exact le_antisymm (norm_primeHodgeSplitDilation_sub_zero_le a) hlower

theorem norm_primeFramedProjection_sub_zero_le (a : ℝ) :
    ‖primeFramedProjection a - primeFramedProjection 0‖ ≤ 1 := by
  have hPa : IsIdempotentElem (primeFramedProjection a) := by
    change primeFramedProjection a ∘L primeFramedProjection a =
      primeFramedProjection a
    exact primeFramedProjection_idempotent a
  have hPzero : IsIdempotentElem (primeFramedProjection 0) := by
    change primeFramedProjection 0 ∘L primeFramedProjection 0 =
      primeFramedProjection 0
    exact primeFramedProjection_idempotent 0
  exact HTGeometry.norm_twoProjection_difference_le_one
    (primeFramedProjection a) (primeFramedProjection 0) hPa hPzero
    (primeFramedProjection_isSelfAdjoint a)
    (primeFramedProjection_isSelfAdjoint 0)

private theorem primeFramedProjection_apply_splitDilation
    (a : ℝ) (x : PrimeHodgeHistoryHilbert) :
    primeFramedProjection a (primeHodgeSplitDilation a x) =
      primeHodgeSplitDilation a x := by
  rw [primeFramedProjection]
  simp only [ContinuousLinearMap.comp_apply]
  have h := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ]
      PrimeHodgeHistoryHilbert => A x)
    (adjoint_primeHodgeSplitDilation_comp_self a)
  have h' := congrArg (fun y => primeHodgeSplitDilation a y) h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h'

private theorem norm_primeFramedProjection_sub_zero_splitBasis
    (a : ℝ) (np : PrimeHodgeHistoryIndex) :
    ‖(primeFramedProjection a - primeFramedProjection 0)
        (primeHodgeSplitDilation 0
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np))‖ =
      |primeHodgeContrast a np.2| := by
  let e := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np
  let xzero := primeHodgeSplitDilation 0 e
  let y := primeFramedProjection a xzero
  have he : ‖e‖ = 1 := norm_lpBasis_primeHodgeHistoryIndex np
  have hxzero : ‖xzero‖ = 1 := by
    dsimp [xzero]
    rw [norm_primeHodgeSplitDilation, he]
  have hPzero : primeFramedProjection 0 xzero = xzero := by
    exact primeFramedProjection_apply_splitDilation 0 e
  have hadjApply : ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) xzero =
      primeHodgeVisibilityOp a e := by
    rw [adjoint_primeHodgeSplitDilation]
    simp [xzero, primeHodgeVisibilityOp_zero, primeHodgeContrastOp_zero]
  have hyform : y = primeHodgeSplitDilation a (primeHodgeVisibilityOp a e) := by
    dsimp [y]
    rw [primeFramedProjection]
    simp only [ContinuousLinearMap.comp_apply, hadjApply]
  have hV := primeHodgeVisibilityOp_lpBasis a np
  have hyNorm : ‖y‖ = primeHodgeVisibility a np.2 := by
    rw [hyform, norm_primeHodgeSplitDilation, hV, norm_smul, he, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (primeHodgeVisibility_pos a np.2)]
  have hinner : (inner ℂ y xzero).re = ‖y‖ ^ 2 := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeFramedProjection_isSelfAdjoint a) y xzero
    have hidem := congrArg (fun A : PrimeFramedDouble →L[ℂ] PrimeFramedDouble =>
      A xzero) (primeFramedProjection_idempotent a)
    change primeFramedProjection a (primeFramedProjection a xzero) =
      primeFramedProjection a xzero at hidem
    have hyfixed : primeFramedProjection a y = y := by
      dsimp [y]
      exact hidem
    change inner ℂ (primeFramedProjection a y) xzero =
      inner ℂ y (primeFramedProjection a xzero) at hsym
    rw [hyfixed] at hsym
    change inner ℂ y xzero = inner ℂ y y at hsym
    rw [hsym]
    exact @inner_self_eq_norm_sq ℂ PrimeFramedDouble _ _ _ y
  have hsq : ‖y - xzero‖ ^ 2 = ‖y‖ ^ 2 -
      2 * (inner ℂ y xzero).re + ‖xzero‖ ^ 2 :=
    @norm_sub_sq ℂ PrimeFramedDouble _ _ _ y xzero
  have hcontrast := primeHodgeVisibility_sq_add_contrast_sq a np.2
  have hsqFinal : ‖y - xzero‖ ^ 2 = |primeHodgeContrast a np.2| ^ 2 := by
    rw [hsq, hinner, hxzero, hyNorm]
    nlinarith [sq_abs (primeHodgeContrast a np.2)]
  rw [sub_apply, hPzero]
  change ‖y - xzero‖ = |primeHodgeContrast a np.2|
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hsqFinal

theorem abs_primeHodgeContrast_tendsto_cofinite_one {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun p : Nat.Primes => |primeHodgeContrast a p|)
      cofinite (nhds 1) := by
  have hp := tendsto_primes_cofinite_atTop
  have hlog : Tendsto (fun p : Nat.Primes => Real.log (p : ℝ))
      cofinite atTop := Real.tendsto_log_atTop.comp hp
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hscale : Tendsto (fun p : Nat.Primes => a * Real.log (p : ℝ))
        cofinite atBot := hlog.const_mul_atTop_of_neg haNeg
    have hc : Tendsto (fun p : Nat.Primes => primeHodgeContrast a p)
        cofinite (nhds (-1)) := by
      simpa [primeHodgeContrast, primeHodgeRapidity, formationContrast,
        Function.comp_def] using formationContrast_tendsto_atBot.comp hscale
    have habs := (continuous_abs.tendsto (-1 : ℝ)).comp hc
    simpa [Function.comp_def] using habs
  · have hscale : Tendsto (fun p : Nat.Primes => a * Real.log (p : ℝ))
        cofinite atTop := hlog.const_mul_atTop haPos
    have hc : Tendsto (fun p : Nat.Primes => primeHodgeContrast a p)
        cofinite (nhds 1) := by
      simpa [primeHodgeContrast, primeHodgeRapidity, formationContrast,
        Function.comp_def] using formationContrast_tendsto_atTop.comp hscale
    have habs := (continuous_abs.tendsto (1 : ℝ)).comp hc
    simpa [Function.comp_def] using habs

theorem norm_primeFramedProjection_sub_zero {a : ℝ} (ha : a ≠ 0) :
    ‖primeFramedProjection a - primeFramedProjection 0‖ = 1 := by
  let e : Nat.Primes → PrimeHodgeHistoryHilbert := fun p =>
    HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p)
  let xzero : Nat.Primes → PrimeFramedDouble := fun p =>
    primeHodgeSplitDilation 0 (e p)
  have hxzero : ∀ p, ‖xzero p‖ = 1 := by
    intro p
    dsimp [xzero, e]
    rw [norm_primeHodgeSplitDilation,
      norm_lpBasis_primeHodgeHistoryIndex]
  have hlim : Tendsto (fun p : Nat.Primes =>
      ‖(primeFramedProjection a - primeFramedProjection 0) (xzero p)‖)
      cofinite (nhds 1) := by
    convert abs_primeHodgeContrast_tendsto_cofinite_one ha using 1
    funext p
    exact norm_primeFramedProjection_sub_zero_splitBasis a (0, p)
  have hlower : 1 ≤ ‖primeFramedProjection a - primeFramedProjection 0‖ := by
    apply le_of_tendsto' hlim
    intro p
    have hop := (primeFramedProjection a - primeFramedProjection 0).le_opNorm
      (xzero p)
    rw [hxzero p, mul_one] at hop
    exact hop
  exact le_antisymm (norm_primeFramedProjection_sub_zero_le a) hlower

/-! ## Projective degree, reflection gauge, and closed nuclear contraction -/

/-- Affine slope of the frame line at a fixed prime. -/
def primeFramedProjectiveSlope (p : Nat.Primes) (a : ℝ) : ℝ :=
  formationSlope (a * Real.log (p : ℝ))

theorem primeFramedProjectiveSlope_eq_ratio (p : Nat.Primes) (a : ℝ) :
    primeHodgeContrast a p / primeHodgeVisibility a p =
      primeFramedProjectiveSlope p a := by
  exact formationSlope_eq_contrast_div_visibility
    (a * Real.log (p : ℝ))

theorem primeFramedProjectiveSlope_strictMono (p : Nat.Primes) :
    StrictMono (primeFramedProjectiveSlope p) := by
  intro a b hab
  apply formationSlope_strictMono
  exact mul_lt_mul_of_pos_right hab
    (Real.log_pos (by exact_mod_cast p.property.one_lt))

theorem primeFramedProjectiveSlope_surjective (p : Nat.Primes) :
    Function.Surjective (primeFramedProjectiveSlope p) := by
  intro y
  rcases formationSlope_surjective y with ⟨u, hu⟩
  have hp : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  refine ⟨u / Real.log (p : ℝ), ?_⟩
  simpa [primeFramedProjectiveSlope, div_mul_cancel₀ u hp] using hu

/-- Orientation-preserving affine chart of one fixed prime frame line. -/
def primeFramedProjectiveSlopeOrderIso (p : Nat.Primes) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (primeFramedProjectiveSlope p)
    (primeFramedProjectiveSlope_strictMono p)
    (primeFramedProjectiveSlope_surjective p)

/-- Compactification of the fixed-prime projective frame line. -/
def primeFramedProjectiveHomeomorph (p : Nat.Primes) :
    OnePoint ℝ ≃ₜ OnePoint ℝ :=
  Homeomorph.onePointCongr (primeFramedProjectiveSlopeOrderIso p).toHomeomorph

@[simp] theorem primeFramedProjectiveHomeomorph_coe
    (p : Nat.Primes) (a : ℝ) :
    primeFramedProjectiveHomeomorph p (a : OnePoint ℝ) =
      (primeFramedProjectiveSlope p a : OnePoint ℝ) := by
  simp [primeFramedProjectiveHomeomorph, Homeomorph.onePointCongr,
    primeFramedProjectiveSlopeOrderIso]

@[simp] theorem primeFramedProjectiveHomeomorph_infty (p : Nat.Primes) :
    primeFramedProjectiveHomeomorph p (OnePoint.infty : OnePoint ℝ) =
      OnePoint.infty := by
  simp [primeFramedProjectiveHomeomorph, Homeomorph.onePointCongr]

theorem primeFramedProjectiveDegree_eq_one (p : Nat.Primes) :
    affineProjectiveDegree (primeFramedProjectiveSlope p) = 1 := by
  classical
  simp [affineProjectiveDegree, primeFramedProjectiveSlope_strictMono p]

/-- Fixed reflection gauge `diag(I,-I)`. -/
def primeFramedReflection : PrimeFramedDouble →L[ℂ] PrimeFramedDouble :=
  primeFramedOfProd ∘L (primeFramedFst.prod (-primeFramedSnd))

@[simp] theorem primeFramedReflection_fst (z : PrimeFramedDouble) :
    (primeFramedReflection z).fst = z.fst := rfl

@[simp] theorem primeFramedReflection_snd (z : PrimeFramedDouble) :
    (primeFramedReflection z).snd = -z.snd := rfl

theorem primeFramedReflection_involution :
    primeFramedReflection ∘L primeFramedReflection =
      ContinuousLinearMap.id ℂ PrimeFramedDouble := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
    PrimeHodgeHistoryHilbert).injective
  ext <;> simp

theorem primeFramedReflection_isSelfAdjoint :
    IsSelfAdjoint primeFramedReflection := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro z w
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp

theorem adjoint_primeFramedReflection :
    ContinuousLinearMap.adjoint primeFramedReflection = primeFramedReflection :=
  primeFramedReflection_isSelfAdjoint

theorem primeHodgeSplitDilation_neg_eq_reflection_comp (a : ℝ) :
    primeHodgeSplitDilation (-a) =
      primeFramedReflection ∘L primeHodgeSplitDilation a := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
    PrimeHodgeHistoryHilbert).injective
  apply Prod.ext
  · simp [primeHodgeVisibilityOp_neg]
  · simp [primeHodgeContrastOp_neg]

theorem primeFramedNuclearOrbit_reflection (a : ℝ) :
    primeFramedNuclearOrbit (-a) =
      (primeFramedReflection ∘L primeFramedNuclearOrbit a) ∘L
        primeFramedReflection := by
  rw [primeFramedNuclearOrbit,
    primeHodgeSplitDilation_neg_eq_reflection_comp,
    ContinuousLinearMap.adjoint_comp, adjoint_primeFramedReflection]
  ext z
  rfl

theorem adjoint_primeFramedEndpointCoframePlus_comp_self :
    ContinuousLinearMap.adjoint primeFramedEndpointCoframePlus ∘L
      primeFramedEndpointCoframePlus =
        ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert := by
  rw [adjoint_primeFramedEndpointCoframePlus]
  ext x
  rfl

theorem primeFramedEndpoint_eq_sandwich :
    primeFramedEndpoint =
      (primeFramedEndpointCoframePlus ∘L
          primeHodgeHistoryIntegralNuclearDefectT) ∘L
        ContinuousLinearMap.adjoint primeFramedEndpointCoframePlus := by
  rw [adjoint_primeFramedEndpointCoframePlus]
  rfl

theorem primeFramedEndpoint_isPositive : primeFramedEndpoint.IsPositive := by
  rw [primeFramedEndpoint_eq_sandwich]
  have hT : 0 ≤ primeHodgeHistoryIntegralNuclearDefectT := by
    rw [ContinuousLinearMap.le_def, sub_zero]
    exact primeHodgeHistoryIntegralNuclearDefect_closed.1
  have h := GaloisForLFunctions.HTGeometry.traceClassSandwich_nonneg
    primeFramedEndpointCoframePlus
    primeHodgeHistoryIntegralNuclearDefectT hT
  rw [ContinuousLinearMap.le_def, sub_zero] at h
  exact h

theorem primeFramedEndpoint_memSchattenClass_one :
    MemSchattenClass 1 primeFramedEndpoint := by
  rw [primeFramedEndpoint_eq_sandwich]
  exact GaloisForLFunctions.HTGeometry.memSchattenClass_one_sandwich
    primeFramedEndpointCoframePlus
    primeHodgeHistoryIntegralNuclearDefect_closed.2.1

theorem opTrace_primeFramedEndpoint :
    ContinuousLinearMap.opTrace primeFramedEndpoint = 1 := by
  rw [primeFramedEndpoint_eq_sandwich,
    GaloisForLFunctions.HTGeometry.opTrace_sandwich
      primeFramedEndpointCoframePlus
      primeHodgeHistoryIntegralNuclearDefectT
      primeHodgeHistoryIntegralNuclearDefect_closed.2.1]
  rw [adjoint_primeFramedEndpointCoframePlus_comp_self]
  simpa using primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1

theorem traceNorm_primeFramedEndpoint :
    traceNorm PrimeFramedDouble primeFramedEndpoint = 1 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive
    primeFramedEndpoint_memSchattenClass_one primeFramedEndpoint_isPositive,
    opTrace_primeFramedEndpoint]
  rfl

/-- Literal one-point extension of the nuclear orbit. -/
def primeFramedClosedNuclearLoop :
    OnePoint ℝ → PrimeFramedDouble →L[ℂ] PrimeFramedDouble :=
  OnePoint.rec primeFramedEndpoint primeFramedNuclearOrbit

@[simp] theorem primeFramedClosedNuclearLoop_coe (a : ℝ) :
    primeFramedClosedNuclearLoop (a : OnePoint ℝ) =
      primeFramedNuclearOrbit a := rfl

@[simp] theorem primeFramedClosedNuclearLoop_infty :
    primeFramedClosedNuclearLoop (OnePoint.infty : OnePoint ℝ) =
      primeFramedEndpoint := rfl

theorem primeFramedClosedNuclearLoop_isPositive (z : OnePoint ℝ) :
    (primeFramedClosedNuclearLoop z).IsPositive :=
  OnePoint.rec primeFramedEndpoint_isPositive
    (fun a => primeFramedNuclearOrbit_isPositive a) z

theorem primeFramedClosedNuclearLoop_memSchattenClass_one (z : OnePoint ℝ) :
    MemSchattenClass 1 (primeFramedClosedNuclearLoop z) :=
  OnePoint.rec primeFramedEndpoint_memSchattenClass_one
    (fun a => primeFramedNuclearOrbit_memSchattenClass_one a) z

theorem opTrace_primeFramedClosedNuclearLoop (z : OnePoint ℝ) :
    ContinuousLinearMap.opTrace (primeFramedClosedNuclearLoop z) = 1 :=
  OnePoint.rec opTrace_primeFramedEndpoint
    (fun a => opTrace_primeFramedNuclearOrbit a) z

theorem traceNorm_primeFramedClosedNuclearLoop (z : OnePoint ℝ) :
    traceNorm PrimeFramedDouble (primeFramedClosedNuclearLoop z) = 1 :=
  OnePoint.rec traceNorm_primeFramedEndpoint
    (fun a => traceNorm_primeFramedNuclearOrbit a) z

theorem primeFramedClosedNuclearLoop_traceNormContinuous_coe (a : ℝ) :
    Tendsto (fun b : ℝ => traceNorm PrimeFramedDouble
      (primeFramedClosedNuclearLoop (b : OnePoint ℝ) -
        primeFramedClosedNuclearLoop (a : OnePoint ℝ)))
      (nhds a) (nhds 0) := by
  simpa using continuous_primeFramedNuclearOrbit_traceNorm a

theorem primeFramedClosedNuclearLoop_traceNormContinuous_infty :
    Tendsto (fun a : ℝ => traceNorm PrimeFramedDouble
      (primeFramedClosedNuclearLoop (a : OnePoint ℝ) -
        primeFramedClosedNuclearLoop OnePoint.infty))
      (cocompact ℝ) (nhds 0) := by
  rw [cocompact_eq_atBot_atTop]
  exact primeFramedNuclearOrbit_tendsto_endpoint_atBot.sup
    primeFramedNuclearOrbit_tendsto_endpoint_atTop

/-- Straight-line contraction of the closed nuclear loop inside the trace-one positive cone. -/
def primeFramedNuclearNullHomotopy
    (r : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ) :
    PrimeFramedDouble →L[ℂ] PrimeFramedDouble :=
  (((1 - r.1 : ℝ) : ℂ) • primeFramedClosedNuclearLoop z) +
    (((r.1 : ℝ) : ℂ) • primeFramedEndpoint)

theorem primeFramedNuclearNullHomotopy_zero (z : OnePoint ℝ) :
    primeFramedNuclearNullHomotopy ⟨0, by constructor <;> norm_num⟩ z =
      primeFramedClosedNuclearLoop z := by
  simp only [primeFramedNuclearNullHomotopy]
  module

theorem primeFramedNuclearNullHomotopy_one (z : OnePoint ℝ) :
    primeFramedNuclearNullHomotopy ⟨1, by constructor <;> norm_num⟩ z =
      primeFramedEndpoint := by
  simp only [primeFramedNuclearNullHomotopy]
  module

theorem primeFramedNuclearNullHomotopy_isPositive
    (r : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ) :
    (primeFramedNuclearNullHomotopy r z).IsPositive := by
  let A := primeFramedClosedNuclearLoop z
  let E := primeFramedEndpoint
  have hA := primeFramedClosedNuclearLoop_isPositive z
  have hE := primeFramedEndpoint_isPositive
  change A.IsPositive at hA
  change E.IsPositive at hE
  refine ⟨?_, ?_⟩
  · intro x y
    change inner ℂ
        ((((1 - r.1 : ℝ) : ℂ) • A) x + (((r.1 : ℝ) : ℂ) • E) x) y =
      inner ℂ x
        ((((1 - r.1 : ℝ) : ℂ) • A) y + (((r.1 : ℝ) : ℂ) • E) y)
    simp only [smul_apply, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    exact congrArg₂ (· + ·)
      (congrArg (fun t : ℂ => (((1 - r.1 : ℝ) : ℂ)) * t) (hA.1 x y))
      (congrArg (fun t : ℂ => (((r.1 : ℝ) : ℂ)) * t) (hE.1 x y))
  · intro x
    have hAx := hA.2 x
    have hEx := hE.2 x
    change 0 ≤ (inner ℂ
      ((((1 - r.1 : ℝ) : ℂ) • A) x + (((r.1 : ℝ) : ℂ) • E) x) x).re
    simp only [smul_apply, inner_add_left, inner_smul_left,
      Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change 0 ≤ (inner ℂ (A x) x).re at hAx
    change 0 ≤ (inner ℂ (E x) x).re at hEx
    nlinarith [r.2.1, r.2.2]

theorem primeFramedNuclearNullHomotopy_memSchattenClass_one
    (r : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ) :
    MemSchattenClass 1 (primeFramedNuclearNullHomotopy r z) := by
  have hA := memSchattenClass_one_smul
    (primeFramedClosedNuclearLoop_memSchattenClass_one z)
    (((1 - r.1 : ℝ) : ℂ))
  have hE := memSchattenClass_one_smul
    primeFramedEndpoint_memSchattenClass_one (((r.1 : ℝ) : ℂ))
  exact memSchattenClass_one_add
    (hA.isCompactOperator one_pos) (hE.isCompactOperator one_pos) hA hE

theorem opTrace_primeFramedNuclearNullHomotopy
    (r : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ) :
    ContinuousLinearMap.opTrace (primeFramedNuclearNullHomotopy r z) = 1 := by
  rw [primeFramedNuclearNullHomotopy,
    opTrace_add_of_memSchattenClass_one
      (memSchattenClass_one_smul
        (primeFramedClosedNuclearLoop_memSchattenClass_one z)
        (((1 - r.1 : ℝ) : ℂ)))
      (memSchattenClass_one_smul primeFramedEndpoint_memSchattenClass_one
        (((r.1 : ℝ) : ℂ))),
    opTrace_smul, opTrace_smul,
    opTrace_primeFramedClosedNuclearLoop, opTrace_primeFramedEndpoint]
  push_cast
  ring

theorem traceNorm_primeFramedNuclearNullHomotopy
    (r : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ) :
    traceNorm PrimeFramedDouble (primeFramedNuclearNullHomotopy r z) = 1 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive
    (primeFramedNuclearNullHomotopy_memSchattenClass_one r z)
    (primeFramedNuclearNullHomotopy_isPositive r z),
    opTrace_primeFramedNuclearNullHomotopy]
  rfl

private theorem primeFramedNuclearNullHomotopy_sub_loop
    (r : Set.Icc (0 : ℝ) 1) (z w : OnePoint ℝ) :
    primeFramedNuclearNullHomotopy r w -
        primeFramedNuclearNullHomotopy r z =
      (((1 - r.1 : ℝ) : ℂ) •
        (primeFramedClosedNuclearLoop w - primeFramedClosedNuclearLoop z)) := by
  simp only [primeFramedNuclearNullHomotopy]
  module

theorem primeFramedNuclearNullHomotopy_traceNormContinuous_coe
    (r : Set.Icc (0 : ℝ) 1) (a : ℝ) :
    Tendsto (fun b : ℝ => traceNorm PrimeFramedDouble
      (primeFramedNuclearNullHomotopy r (b : OnePoint ℝ) -
        primeFramedNuclearNullHomotopy r (a : OnePoint ℝ)))
      (nhds a) (nhds 0) := by
  simp_rw [primeFramedNuclearNullHomotopy_sub_loop, traceNorm_smul]
  have hc : Tendsto (fun _ : ℝ => ‖(((1 - r.1 : ℝ) : ℂ))‖)
      (nhds a) (nhds ‖(((1 - r.1 : ℝ) : ℂ))‖) := tendsto_const_nhds
  have h := hc.mul
    (primeFramedClosedNuclearLoop_traceNormContinuous_coe a)
  simpa using h

theorem primeFramedNuclearNullHomotopy_traceNormContinuous_infty
    (r : Set.Icc (0 : ℝ) 1) :
    Tendsto (fun a : ℝ => traceNorm PrimeFramedDouble
      (primeFramedNuclearNullHomotopy r (a : OnePoint ℝ) -
        primeFramedNuclearNullHomotopy r OnePoint.infty))
      (cocompact ℝ) (nhds 0) := by
  simp_rw [primeFramedNuclearNullHomotopy_sub_loop, traceNorm_smul]
  have hc : Tendsto (fun _ : ℝ => ‖(((1 - r.1 : ℝ) : ℂ))‖)
      (cocompact ℝ) (nhds ‖(((1 - r.1 : ℝ) : ℂ))‖) := tendsto_const_nhds
  have h := hc.mul
    primeFramedClosedNuclearLoop_traceNormContinuous_infty
  simpa using h

private theorem primeFramedNuclearNullHomotopy_sub_parameter
    (r s : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ) :
    primeFramedNuclearNullHomotopy s z -
        primeFramedNuclearNullHomotopy r z =
      ((((s.1 - r.1 : ℝ) : ℂ)) •
        (primeFramedEndpoint - primeFramedClosedNuclearLoop z)) := by
  simp only [primeFramedNuclearNullHomotopy]
  module

theorem primeFramedNuclearNullHomotopy_traceNormContinuous_parameter
    (r : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ) :
    Tendsto (fun s => traceNorm PrimeFramedDouble
      (primeFramedNuclearNullHomotopy s z -
        primeFramedNuclearNullHomotopy r z))
      (nhds r) (nhds 0) := by
  simp_rw [primeFramedNuclearNullHomotopy_sub_parameter, traceNorm_smul]
  have hcoeff : Tendsto (fun s : Set.Icc (0 : ℝ) 1 =>
      ‖(((s.1 - r.1 : ℝ) : ℂ))‖) (nhds r) (nhds 0) := by
    have hc : Tendsto (fun s : Set.Icc (0 : ℝ) 1 =>
        (((s.1 - r.1 : ℝ) : ℂ))) (nhds r)
        (nhds ((((r.1 - r.1 : ℝ) : ℂ)))) :=
      (Complex.continuous_ofReal.comp
        (continuous_subtype_val.sub continuous_const)).continuousAt
    convert tendsto_norm.comp hc using 1
    · rfl
    · norm_num
  have hconst : Tendsto (fun _ : Set.Icc (0 : ℝ) 1 =>
      traceNorm PrimeFramedDouble
        (primeFramedEndpoint - primeFramedClosedNuclearLoop z))
      (nhds r) (nhds (traceNorm PrimeFramedDouble
        (primeFramedEndpoint - primeFramedClosedNuclearLoop z))) :=
    tendsto_const_nhds
  have h := hcoeff.mul hconst
  simpa using h

/-- Closed certificate for the complete framed nuclear cycle, including its open norm defect,
projective charge, one-point trace-norm closure, reflection gauge, and positive trace-one null
homotopy. -/
theorem primeFramedIntegralNuclearHomotopyDefect_closed :
    (∀ a : ℝ,
      ContinuousLinearMap.adjoint (primeFramedRotation a) ∘L
          primeFramedRotation a = ContinuousLinearMap.id ℂ PrimeFramedDouble ∧
      primeFramedRotation a ∘L
          ContinuousLinearMap.adjoint (primeFramedRotation a) =
        ContinuousLinearMap.id ℂ PrimeFramedDouble) ∧
    (∀ a : ℝ,
      ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) ∘L
          primeHodgeSplitDilation a =
        ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert) ∧
    (∀ a : ℝ,
      primeFramedNuclearOrbit a =
        (primeFramedRotation a ∘L primeFramedSource) ∘L
          ContinuousLinearMap.adjoint (primeFramedRotation a)) ∧
    (∀ a : ℝ,
      (primeFramedNuclearOrbit a).IsPositive ∧
      MemSchattenClass 1 (primeFramedNuclearOrbit a) ∧
      ContinuousLinearMap.opTrace (primeFramedNuclearOrbit a) = 1 ∧
      traceNorm PrimeFramedDouble (primeFramedNuclearOrbit a) = 1 ∧
      (ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) ∘L
        primeFramedNuclearOrbit a) ∘L primeHodgeSplitDilation a =
          primeHodgeHistoryIntegralNuclearDefectT) ∧
    (∀ (a : ℝ), a ≠ 0 → ∀ (n : ℕ) (p q : Nat.Primes),
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
          (primeFramedVV a
            (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 ∧
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
          (primeFramedVC a
            (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 ∧
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
          (primeFramedCV a
            (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 ∧
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
          (primeFramedCC a
            (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0) ∧
    (∀ a : ℝ, Tendsto (fun b => traceNorm PrimeFramedDouble
      (primeFramedNuclearOrbit b - primeFramedNuclearOrbit a))
        (nhds a) (nhds 0)) ∧
    Tendsto (fun a => traceNorm PrimeFramedDouble
      (primeFramedNuclearOrbit a - primeFramedEndpoint)) atTop (nhds 0) ∧
    Tendsto (fun a => traceNorm PrimeFramedDouble
      (primeFramedNuclearOrbit a - primeFramedEndpoint)) atBot (nhds 0) ∧
    (∀ a : ℝ, primeFramedNuclearOrbit (-a) =
      (primeFramedReflection ∘L primeFramedNuclearOrbit a) ∘L
        primeFramedReflection) ∧
    (∀ a : ℝ, a ≠ 0 →
      ‖primeHodgeSplitDilation a - primeHodgeSplitDilation 0‖ = Real.sqrt 2 ∧
      ‖primeFramedProjection a - primeFramedProjection 0‖ = 1) ∧
    (∀ p : Nat.Primes,
      affineProjectiveDegree (primeFramedProjectiveSlope p) = 1) ∧
    (∀ z : OnePoint ℝ,
      (primeFramedClosedNuclearLoop z).IsPositive ∧
      MemSchattenClass 1 (primeFramedClosedNuclearLoop z) ∧
      ContinuousLinearMap.opTrace (primeFramedClosedNuclearLoop z) = 1 ∧
      traceNorm PrimeFramedDouble (primeFramedClosedNuclearLoop z) = 1) ∧
    Tendsto (fun a : ℝ => traceNorm PrimeFramedDouble
      (primeFramedClosedNuclearLoop (a : OnePoint ℝ) -
        primeFramedClosedNuclearLoop OnePoint.infty))
      (cocompact ℝ) (nhds 0) ∧
    (∀ (r : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ),
      (primeFramedNuclearNullHomotopy r z).IsPositive ∧
      MemSchattenClass 1 (primeFramedNuclearNullHomotopy r z) ∧
      ContinuousLinearMap.opTrace (primeFramedNuclearNullHomotopy r z) = 1 ∧
      traceNorm PrimeFramedDouble (primeFramedNuclearNullHomotopy r z) = 1) ∧
    (∀ (r : Set.Icc (0 : ℝ) 1) (a : ℝ),
      Tendsto (fun b : ℝ => traceNorm PrimeFramedDouble
        (primeFramedNuclearNullHomotopy r (b : OnePoint ℝ) -
          primeFramedNuclearNullHomotopy r (a : OnePoint ℝ)))
        (nhds a) (nhds 0)) ∧
    (∀ r : Set.Icc (0 : ℝ) 1,
      Tendsto (fun a : ℝ => traceNorm PrimeFramedDouble
        (primeFramedNuclearNullHomotopy r (a : OnePoint ℝ) -
          primeFramedNuclearNullHomotopy r OnePoint.infty))
        (cocompact ℝ) (nhds 0)) ∧
    (∀ (r : Set.Icc (0 : ℝ) 1) (z : OnePoint ℝ),
      Tendsto (fun s => traceNorm PrimeFramedDouble
        (primeFramedNuclearNullHomotopy s z -
          primeFramedNuclearNullHomotopy r z))
        (nhds r) (nhds 0)) ∧
    (∀ z : OnePoint ℝ,
      primeFramedNuclearNullHomotopy
          ⟨0, by constructor <;> norm_num⟩ z =
        primeFramedClosedNuclearLoop z ∧
      primeFramedNuclearNullHomotopy
          ⟨1, by constructor <;> norm_num⟩ z = primeFramedEndpoint) := by
  refine ⟨fun a => ⟨adjoint_primeFramedRotation_comp_self a,
      primeFramedRotation_comp_adjoint a⟩,
    adjoint_primeHodgeSplitDilation_comp_self,
    primeFramedNuclearOrbit_eq_rotation, ?_, ?_,
    continuous_primeFramedNuclearOrbit_traceNorm,
    primeFramedNuclearOrbit_tendsto_endpoint_atTop,
    primeFramedNuclearOrbit_tendsto_endpoint_atBot,
    primeFramedNuclearOrbit_reflection, ?_,
    primeFramedProjectiveDegree_eq_one, ?_,
    primeFramedClosedNuclearLoop_traceNormContinuous_infty, ?_,
    primeFramedNuclearNullHomotopy_traceNormContinuous_coe,
    primeFramedNuclearNullHomotopy_traceNormContinuous_infty,
    primeFramedNuclearNullHomotopy_traceNormContinuous_parameter, ?_⟩
  · intro a
    exact ⟨primeFramedNuclearOrbit_isPositive a,
      primeFramedNuclearOrbit_memSchattenClass_one a,
      opTrace_primeFramedNuclearOrbit a,
      traceNorm_primeFramedNuclearOrbit a,
      primeFramedNuclearOrbit_recovery a⟩
  · intro a ha n p q
    exact primeFramed_four_blocks_sameHistory_ne_zero ha n p q
  · intro a ha
    exact ⟨norm_primeHodgeSplitDilation_sub_zero ha,
      norm_primeFramedProjection_sub_zero ha⟩
  · intro z
    exact ⟨primeFramedClosedNuclearLoop_isPositive z,
      primeFramedClosedNuclearLoop_memSchattenClass_one z,
      opTrace_primeFramedClosedNuclearLoop z,
      traceNorm_primeFramedClosedNuclearLoop z⟩
  · intro r z
    exact ⟨primeFramedNuclearNullHomotopy_isPositive r z,
      primeFramedNuclearNullHomotopy_memSchattenClass_one r z,
      opTrace_primeFramedNuclearNullHomotopy r z,
      traceNorm_primeFramedNuclearNullHomotopy r z⟩
  · intro z
    exact ⟨primeFramedNuclearNullHomotopy_zero z,
      primeFramedNuclearNullHomotopy_one z⟩

end
end RHTower
