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

open Complex HurwitzOrbit

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

/-- The real inner product on the Xi carrier is the real part of the Hermitian product. -/
theorem xiLp_real_inner_eq_re (x y : XiLp) :
    (inner ℝ x y : ℝ) = (inner ℂ x y).re := by
  rw [lp.inner_eq_tsum (𝕜 := ℝ), lp.inner_eq_tsum (𝕜 := ℂ),
    Complex.re_tsum (lp.summable_inner x y)]
  exact tsum_congr (fun q => ClosedSubmodule.inner_real_eq_re_inner _ _)

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
  exact Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr xiEulerPairedSet_subset_sector) isClosed_xiSchwarzFiberSector

/-! ## The orientation vector lies in the sector -/

/-- The support point of the conjugated divisor copy is the conjugated point. -/
theorem xiZeroCopyConjEquiv_point' (q : XiZeroCopy) :
    (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ) = (starRingEnd ℂ) ((q.1 : ℂ)) := rfl

/-- Schwarz conjugation inverts the conjugate Hurwitz monodromy character. -/
theorem monoScalar_schwarzConj (s : ℂ) :
    monoScalar ((starRingEnd ℂ) s) = ((starRingEnd ℂ) (monoScalar s))⁻¹ := by
  rw [monoScalar, monoScalar, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_neg, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, neg_neg]
  ring

/-- **The orientation coordinate is Schwarz invariant.**  Conjugating the divisor point inverts
the conjugate character, which leaves the radius-normalized imaginary part unchanged. -/
theorem xiHurwitzOrientationCoordinate_conj (q : XiZeroCopy) :
    xiHurwitzOrientationCoordinate (xiZeroCopyConjEquiv q) =
      xiHurwitzOrientationCoordinate q := by
  have hpt := xiZeroCopyConjEquiv_point' q
  have hm0 : xiHurwitzMonodromyCharacter q.1 ≠ 0 := xiHurwitzMonodromyCharacter_ne_zero q.1
  have hnorm : ‖xiHurwitzMonodromyCharacter q.1‖ ≠ 0 := norm_ne_zero_iff.mpr hm0
  have hchar : xiHurwitzMonodromyCharacter (xiZeroCopyConjEquiv q).1 =
      ((starRingEnd ℂ) (xiHurwitzMonodromyCharacter q.1))⁻¹ := by
    rw [xiHurwitzMonodromyCharacter, xiHurwitzMonodromyCharacter, hpt, monoScalar_schwarzConj]
  have him : (((starRingEnd ℂ) (xiHurwitzMonodromyCharacter q.1))⁻¹).im =
      (xiHurwitzMonodromyCharacter q.1).im / ‖xiHurwitzMonodromyCharacter q.1‖ ^ 2 := by
    rw [Complex.inv_im, Complex.conj_im, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
    ring
  have hnorminv : ‖((starRingEnd ℂ) (xiHurwitzMonodromyCharacter q.1))⁻¹‖ =
      ‖xiHurwitzMonodromyCharacter q.1‖⁻¹ := by
    rw [norm_inv, RCLike.norm_conj]
  have hcent : ‖(((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ) - 1 / 2‖ =
      ‖((q.1 : XiDivisorSupport) : ℂ) - 1 / 2‖ := by
    rw [hpt, show (starRingEnd ℂ) ((q.1 : ℂ)) - 1 / 2 =
      (starRingEnd ℂ) ((q.1 : ℂ) - 1 / 2) by
        rw [map_sub, map_div₀, map_one, map_ofNat], Complex.norm_conj]
  have hcent0 : ‖((q.1 : XiDivisorSupport) : ℂ) - 1 / 2‖ ≠ 0 :=
    (norm_pos_iff.mpr (sub_ne_zero.mpr (xi_divisor_support_ne_half q.1))).ne'
  rw [xiHurwitzOrientationCoordinate, xiHurwitzOrientationCoordinate, hchar]
  congr 1
  rw [him, hnorminv, hcent]
  field_simp [hnorm, hcent0]

theorem xiHurwitzOrientationVector_mem_xiSchwarzFiberSector :
    xiHurwitzOrientationVector ∈ xiSchwarzFiberSector := by
  refine ⟨fun q => ?_, fun q q' h => ?_⟩
  · show (starRingEnd ℂ) (xiHurwitzOrientationCoordinate (xiZeroCopyConjEquiv q)) =
      xiHurwitzOrientationCoordinate q
    rw [xiHurwitzOrientationCoordinate_conj, xiHurwitzOrientationCoordinate,
      Complex.conj_ofReal]
  · show xiHurwitzOrientationCoordinate q = xiHurwitzOrientationCoordinate q'
    rw [xiHurwitzOrientationCoordinate, xiHurwitzOrientationCoordinate, h]

/-! ## Completeness of the absolute-Euler paired quadrant -/

theorem mem_xiEulerPairedRealClosure_of_mem_sector {v : XiLp}
    (hv : v ∈ xiSchwarzFiberSector) : v ∈ xiEulerPairedRealClosure := by
  haveI hcl : IsClosed ((xiEulerPairedRealClosure : Submodule ℝ XiLp) : Set XiLp) :=
    Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace ((xiEulerPairedRealClosure : Submodule ℝ XiLp)) := hcl.completeSpace_coe
  set K : Submodule ℝ XiLp := xiEulerPairedRealClosure with hK
  have hpm : K.starProjection v ∈ K := K.starProjection_apply_mem v
  have horth : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have husec : v - K.starProjection v ∈ xiSchwarzFiberSector :=
    Submodule.sub_mem _ hv (xiEulerPairedRealClosure_le_sector hpm)
  obtain ⟨hs, hf⟩ := (mem_xiSchwarzFiberSector_iff _).mp husec
  have huzero : v - K.starProjection v = 0 := by
    refine eq_zero_of_re_inner_eulerPaired_eq_zero hs hf (fun w hw1 hw2 => ?_)
    have hmem : xiEulerPairedCauchyLp w (XiC_xiEulerCentered_ne_zero hw1)
        (XiC_neg_conj_xiEulerCentered_ne_zero hw1) ∈ K := by
      refine Submodule.le_topologicalClosure _ ?_
      exact Submodule.subset_span ⟨w, hw1, hw2, rfl⟩
    have hzero := (Submodule.mem_orthogonal K _).mp horth _ hmem
    rw [← inner_conj_symm, Complex.conj_re, ← xiLp_real_inner_eq_re]
    exact hzero
  have : v = K.starProjection v := by
    have := sub_eq_zero.mp huzero
    exact this
  rw [this]
  exact hpm

/-- **Equation `(9)`.**  The canonical Xi--Hurwitz orientation vector belongs to the closed real
span of the absolute-Euler Schwarz-paired Cauchy vectors of one open quadrant. -/
theorem xiHurwitzOrientationVector_mem_xiEulerPairedRealClosure :
    xiHurwitzOrientationVector ∈ xiEulerPairedRealClosure :=
  mem_xiEulerPairedRealClosure_of_mem_sector xiHurwitzOrientationVector_mem_xiSchwarzFiberSector

/-! ## The absolute-Euler paired passivity criterion -/

/-- Positivity of the unconditional Weil quadratic form on real finite packets of absolute-Euler
paired Cauchy vectors. -/
def XiEulerSafePairedPassivity : Prop :=
  ∀ v ∈ Submodule.span ℝ xiEulerPairedSet, 0 ≤ xiWeilHilbertQuadratic v

/-- **Equation `(26)`.**  Absolute-Euler paired passivity on one open quadrant is exactly the
Riemann hypothesis. -/
theorem riemannHypothesis_iff_xiEulerSafePairedPassivity :
    RiemannHypothesis ↔ XiEulerSafePairedPassivity := by
  constructor
  · intro hRH _ _
    exact xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH _
  · intro hpos
    refine riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg.mpr ?_
    have hclosed : IsClosed {u : XiLp | 0 ≤ xiWeilHilbertQuadratic u} :=
      isClosed_Ici.preimage continuous_xiWeilHilbertQuadratic
    have hmem : xiHurwitzOrientationVector ∈
        closure ((Submodule.span ℝ xiEulerPairedSet : Submodule ℝ XiLp) : Set XiLp) :=
      xiHurwitzOrientationVector_mem_xiEulerPairedRealClosure
    exact closure_minimal hpos hclosed hmem


end

end RHTower
