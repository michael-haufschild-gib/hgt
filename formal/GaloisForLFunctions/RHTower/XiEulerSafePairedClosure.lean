import GaloisForLFunctions.RHTower.XiEulerSafePairedCompleteness
import GaloisForLFunctions.RHTower.XiHurwitzOrientationWeilSector
import GaloisForLFunctions.RHTower.XiHurwitzOrientationSourceSequenceGate

/-!
# The Xi orientation vector lies in the absolute-Euler paired real closure

The Schwarz-fixed fibre-constant vectors form a closed real subspace of the multiplicity-exact Xi
`ell^2` carrier.  It contains every absolute-Euler Schwarz-paired Cauchy vector and the canonical
Xi--Hurwitz orientation vector.  Absolute-Euler paired completeness says that the only vector of
that sector orthogonal to all paired vectors is zero, so the orthogonal projection of the
orientation vector onto the closed real span of the paired vectors is the orientation vector
itself.

Consequently passivity of the unconditional Weil quadratic form on real finite paired packets with
poles in one fixed absolute-Euler quadrant is already equivalent to the Riemann hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

local notation "XiLp" => lp (fun _ : XiZeroCopy => ℂ) 2

/-! ## Coordinate evaluation -/

/-- Coordinate evaluation on the multiplicity-exact Xi carrier as a continuous functional. -/
def xiZeroCopyEval (q : XiZeroCopy) : XiLp →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun v => (v : XiZeroCopy → ℂ) q
      map_add' := fun v w => by simp
      map_smul' := fun a v => by simp } 1
    (fun v => by
      simpa using lp.norm_apply_le_norm (p := (2 : ENNReal)) (by norm_num) v q)

@[simp] theorem xiZeroCopyEval_apply (q : XiZeroCopy) (v : XiLp) :
    xiZeroCopyEval q v = (v : XiZeroCopy → ℂ) q := rfl

theorem continuous_xiZeroCopyCoord (q : XiZeroCopy) :
    Continuous (fun v : XiLp => (v : XiZeroCopy → ℂ) q) :=
  (xiZeroCopyEval q).continuous

/-! ## The Schwarz-fixed fibre-constant sector -/

/-- The real sector `(7)` of Schwarz-fixed fibre-constant divisor vectors. -/
def xiSchwarzFiberSector : Submodule ℝ XiLp where
  carrier := {v : XiLp |
    (∀ q : XiZeroCopy,
        (starRingEnd ℂ) ((v : XiZeroCopy → ℂ) (xiZeroCopyConjEquiv q)) =
          (v : XiZeroCopy → ℂ) q) ∧
    ∀ q q' : XiZeroCopy, q.1 = q'.1 →
      (v : XiZeroCopy → ℂ) q = (v : XiZeroCopy → ℂ) q'}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    refine ⟨fun q => ?_, fun q q' h => ?_⟩
    · simp only [lp.coeFn_add, Pi.add_apply, map_add, hv1 q, hw1 q]
    · simp only [lp.coeFn_add, Pi.add_apply, hv2 q q' h, hw2 q q' h]
  smul_mem' := by
    rintro r v ⟨hv1, hv2⟩
    refine ⟨fun q => ?_, fun q q' h => ?_⟩
    · simp only [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, map_mul,
        Complex.conj_ofReal, hv1 q]
    · simp only [lp.coeFn_smul, Pi.smul_apply, hv2 q q' h]

theorem mem_xiSchwarzFiberSector_iff (v : XiLp) :
    v ∈ xiSchwarzFiberSector ↔ xiWeilSchwarzLp v = v ∧ XiFiberConstant v := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    apply lp.ext
    funext q
    rw [xiWeilSchwarzLp_apply]
    exact h1 q
  · rintro ⟨h1, h2⟩
    refine ⟨fun q => ?_, h2⟩
    have := congrArg (fun u : XiLp => (u : XiZeroCopy → ℂ) q) h1
    simpa using this

theorem isClosed_xiSchwarzFiberSector :
    IsClosed (xiSchwarzFiberSector : Set XiLp) := by
  have hset : (xiSchwarzFiberSector : Set XiLp) =
      (⋂ q : XiZeroCopy, {v : XiLp |
        (starRingEnd ℂ) ((v : XiZeroCopy → ℂ) (xiZeroCopyConjEquiv q)) =
          (v : XiZeroCopy → ℂ) q}) ∩
      (⋂ p : {p : XiZeroCopy × XiZeroCopy // p.1.1 = p.2.1}, {v : XiLp |
        (v : XiZeroCopy → ℂ) p.1.1 = (v : XiZeroCopy → ℂ) p.1.2}) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun p => h2 p.1.1 p.1.2 p.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun q q' h => h2 ⟨(q, q'), h⟩⟩
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun q => ?_) (isClosed_iInter fun p => ?_)
  · exact isClosed_eq (Complex.continuous_conj.comp (continuous_xiZeroCopyCoord _))
      (continuous_xiZeroCopyCoord q)
  · exact isClosed_eq (continuous_xiZeroCopyCoord _) (continuous_xiZeroCopyCoord _)

/-! ## The absolute-Euler paired generators -/

/-- The set of absolute-Euler Schwarz-paired Cauchy vectors, poles in the open quadrant
`Re w > 1/2`, `Im w > 0`. -/
def xiEulerPairedSet : Set XiLp :=
  {v : XiLp | ∃ (w : ℂ) (h : 1 / 2 < w.re), 0 < w.im ∧
    v = xiEulerPairedCauchyLp w (XiC_xiEulerCentered_ne_zero h)
      (XiC_neg_conj_xiEulerCentered_ne_zero h)}

/-- The closed real span of the absolute-Euler paired Cauchy vectors. -/
def xiEulerPairedRealClosure : Submodule ℝ XiLp :=
  (Submodule.span ℝ xiEulerPairedSet).topologicalClosure

theorem xiWeilCauchyLp_fiberConstant (z : XiCRegularPoint) :
    XiFiberConstant (xiWeilCauchyLp z) := by
  intro q q' h
  simp only [xiWeilCauchyLp_apply, xiWeilCauchyTest, xiSpectralPoint, h]

theorem xiEulerPairedSet_subset_sector :
    xiEulerPairedSet ⊆ (xiSchwarzFiberSector : Set XiLp) := by
  rintro v ⟨w, h, _, rfl⟩
  refine (mem_xiSchwarzFiberSector_iff _).mpr ⟨xiWeilSchwarzLp_eulerPaired w _ _, ?_⟩
  intro q q' hq
  have h1 := xiWeilCauchyLp_fiberConstant ⟨xiEulerCentered w, XiC_xiEulerCentered_ne_zero h⟩ q q' hq
  have h2 := xiWeilCauchyLp_fiberConstant
    ⟨-(starRingEnd ℂ) (xiEulerCentered w), XiC_neg_conj_xiEulerCentered_ne_zero h⟩ q q' hq
  simp only [xiEulerPairedCauchyLp, lp.coeFn_sub, Pi.sub_apply, h1, h2]

theorem xiEulerPairedRealClosure_le_sector :
    xiEulerPairedRealClosure ≤ xiSchwarzFiberSector := by
  refine Submodule.topologicalClosure_minimal ?_ isClosed_xiSchwarzFiberSector
  exact Submodule.span_le.mpr xiEulerPairedSet_subset_sector

end

end RHTower
