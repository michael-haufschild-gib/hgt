import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEPacketPeierlsClassification

/-!
# Complete source-FE classification of arbitrary Peierls packet kernels

HC51 classified only diagonal weights.  This module allows every ordered cross-fibre coefficient
`K(q,r)` and proves that packetwise source-FE covariance is equivalent to one coefficient law on
each ordered pair.  The associated source-kernel conjugation is an anti-linear involution; its
fixed points are exactly Ward kernels, and every fixed point is a Reynolds symmetrization.

This exposes the exact fixed-versus-transported boundary.  Transported mixed-copy forms exist
unconditionally.  But if a kernel is fixed by physical reflection and has a nonzero diagonal at a
copy, Ward covariance forces that copy onto the critical line.  Hence arbitrary off-diagonal
couplings cannot rescue a reflection-real physical form with nonzero diagonal: its full finite-
packet covariance is equivalent to RH.

`[NEW] [ARBITRARY KERNEL] [FIXED-POINT CLASSIFICATION] [CROSS-FIBRE RIGIDITY] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Arbitrary complex-bilinear kernel form on finite Xi packets. -/
def hbXiPeierlsKernelForm
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (x y : HBXiPeierlsPacket) : ℂ :=
  x.sum fun q c => y.sum fun r d => K q r * c * d

@[simp]
theorem hbXiPeierlsKernelForm_zero_left
    (K : XiZeroCopy → XiZeroCopy → ℂ) (y : HBXiPeierlsPacket) :
    hbXiPeierlsKernelForm K 0 y = 0 := by
  simp [hbXiPeierlsKernelForm]

@[simp]
theorem hbXiPeierlsKernelForm_zero_right
    (K : XiZeroCopy → XiZeroCopy → ℂ) (x : HBXiPeierlsPacket) :
    hbXiPeierlsKernelForm K x 0 = 0 := by
  simp [hbXiPeierlsKernelForm]

theorem hbXiPeierlsKernelForm_add_left
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (x y z : HBXiPeierlsPacket) :
    hbXiPeierlsKernelForm K (x + y) z =
      hbXiPeierlsKernelForm K x z + hbXiPeierlsKernelForm K y z := by
  classical
  rw [hbXiPeierlsKernelForm, hbXiPeierlsKernelForm,
    hbXiPeierlsKernelForm, Finsupp.sum_add_index']
  · intro q
    simp
  · intro q a b
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr (fun r _ => ?_)
    ring

theorem hbXiPeierlsKernelForm_add_right
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (x y z : HBXiPeierlsPacket) :
    hbXiPeierlsKernelForm K x (y + z) =
      hbXiPeierlsKernelForm K x y + hbXiPeierlsKernelForm K x z := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [hbXiPeierlsKernelForm_add_left, hbXiPeierlsKernelForm_add_left,
        hbXiPeierlsKernelForm_add_left, hf, hg]
      ring
  | single q c =>
      rw [hbXiPeierlsKernelForm, hbXiPeierlsKernelForm,
        hbXiPeierlsKernelForm]
      rw [Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp)]
      rw [Finsupp.sum_add_index']
      · intro r
        simp
      · intro r a b
        ring

@[simp]
theorem hbXiPeierlsKernelForm_single_single
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (q r : XiZeroCopy) (c d : ℂ) :
    hbXiPeierlsKernelForm K (Finsupp.single q c) (Finsupp.single r d) =
      K q r * c * d := by
  classical
  simp [hbXiPeierlsKernelForm]

/-- Ordered-pair coefficient equation for source-FE covariance of an arbitrary kernel. -/
def HBXiPeierlsUnitSourceFEKernelWard
    (K : XiZeroCopy → XiZeroCopy → ℂ) : Prop :=
  ∀ q r : XiZeroCopy,
    K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv r) *
        hbXiPeierlsUnitSourceFECocycle q *
        hbXiPeierlsUnitSourceFECocycle r =
      (starRingEnd ℂ) (K q r)

theorem hbXiPeierlsKernelForm_packetTransport_of_kernelWard
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hK : HBXiPeierlsUnitSourceFEKernelWard K)
    (x y : HBXiPeierlsPacket) :
    hbXiPeierlsKernelForm K (hbXiPeierlsUnitSourceFEPacketTransport x)
        (hbXiPeierlsUnitSourceFEPacketTransport y) =
      (starRingEnd ℂ) (hbXiPeierlsKernelForm K x y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, hbXiPeierlsKernelForm_add_left, hf, hg,
        hbXiPeierlsKernelForm_add_left, map_add]
  | single q c =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg =>
          rw [map_add, hbXiPeierlsKernelForm_add_right, hf, hg,
            hbXiPeierlsKernelForm_add_right, map_add]
      | single r d =>
          rw [hbXiPeierlsUnitSourceFEPacketTransport_single,
            hbXiPeierlsUnitSourceFEPacketTransport_single,
            hbXiPeierlsKernelForm_single_single,
            hbXiPeierlsKernelForm_single_single, map_mul, map_mul]
          calc
            _ = (K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv r) *
                  hbXiPeierlsUnitSourceFECocycle q *
                  hbXiPeierlsUnitSourceFECocycle r) *
                (starRingEnd ℂ) c * (starRingEnd ℂ) d := by ring
            _ = _ := by rw [hK q r]

theorem forall_hbXiPeierlsKernelForm_packetTransport_iff_kernelWard
    (K : XiZeroCopy → XiZeroCopy → ℂ) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm K (hbXiPeierlsUnitSourceFEPacketTransport x)
          (hbXiPeierlsUnitSourceFEPacketTransport y) =
        (starRingEnd ℂ) (hbXiPeierlsKernelForm K x y)) ↔
      HBXiPeierlsUnitSourceFEKernelWard K := by
  constructor
  · intro h q r
    have hqr := h (Finsupp.single q 1) (Finsupp.single r 1)
    rw [hbXiPeierlsUnitSourceFEPacketTransport_single,
      hbXiPeierlsUnitSourceFEPacketTransport_single,
      hbXiPeierlsKernelForm_single_single,
      hbXiPeierlsKernelForm_single_single] at hqr
    simpa only [mul_one, map_one] using hqr
  · exact hbXiPeierlsKernelForm_packetTransport_of_kernelWard K

/-- Anti-linear conjugation of arbitrary packet kernels forced by the literal source cocycle. -/
def hbXiPeierlsUnitSourceFEKernelConjugation
    (K : XiZeroCopy → XiZeroCopy → ℂ) (q r : XiZeroCopy) : ℂ :=
  (starRingEnd ℂ)
    (K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv r) *
      hbXiPeierlsUnitSourceFECocycle q *
      hbXiPeierlsUnitSourceFECocycle r)

theorem hbXiPeierlsUnitSourceFEKernelConjugation_involutive
    (K : XiZeroCopy → XiZeroCopy → ℂ) :
    hbXiPeierlsUnitSourceFEKernelConjugation
        (hbXiPeierlsUnitSourceFEKernelConjugation K) = K := by
  funext q r
  simp only [hbXiPeierlsUnitSourceFEKernelConjugation,
    xiZeroCopyReflectEquiv_apply_apply, map_mul]
  have hq := hbXiPeierlsUnitSourceFECocycle_involutive q
  have hr := hbXiPeierlsUnitSourceFECocycle_involutive r
  have hcc : (starRingEnd ℂ) ((starRingEnd ℂ) (K q r)) = K q r := by simp
  have hccq :
      (starRingEnd ℂ) ((starRingEnd ℂ)
        (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q))) =
      hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) := by simp
  have hccr :
      (starRingEnd ℂ) ((starRingEnd ℂ)
        (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv r))) =
      hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv r) := by simp
  rw [hcc, hccq, hccr]
  calc
    K q r * hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
          hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv r) *
        (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) *
        (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle r) =
      K q r *
        (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q)) *
        (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv r) *
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle r)) := by ring
    _ = K q r := by rw [hq, hr, mul_one, mul_one]

theorem hbXiPeierlsUnitSourceFEKernelConjugation_add
    (K L : XiZeroCopy → XiZeroCopy → ℂ) :
    hbXiPeierlsUnitSourceFEKernelConjugation (fun q r => K q r + L q r) =
      fun q r => hbXiPeierlsUnitSourceFEKernelConjugation K q r +
        hbXiPeierlsUnitSourceFEKernelConjugation L q r := by
  funext q r
  simp [hbXiPeierlsUnitSourceFEKernelConjugation, add_mul]

theorem kernelWard_iff_kernelConjugation_eq
    (K : XiZeroCopy → XiZeroCopy → ℂ) :
    HBXiPeierlsUnitSourceFEKernelWard K ↔
      hbXiPeierlsUnitSourceFEKernelConjugation K = K := by
  constructor
  · intro h
    funext q r
    rw [hbXiPeierlsUnitSourceFEKernelConjugation, h q r]
    simp
  · intro h q r
    have hqr := congrFun (congrFun h q) r
    rw [hbXiPeierlsUnitSourceFEKernelConjugation] at hqr
    have hc := congrArg (starRingEnd ℂ) hqr
    simpa using hc

/-- Reynolds symmetrization for the source-kernel involution. -/
def hbXiPeierlsUnitSourceFEKernelSymmetrization
    (K : XiZeroCopy → XiZeroCopy → ℂ) (q r : XiZeroCopy) : ℂ :=
  K q r + hbXiPeierlsUnitSourceFEKernelConjugation K q r

theorem hbXiPeierlsUnitSourceFEKernelSymmetrization_kernelWard
    (K : XiZeroCopy → XiZeroCopy → ℂ) :
    HBXiPeierlsUnitSourceFEKernelWard
      (hbXiPeierlsUnitSourceFEKernelSymmetrization K) := by
  rw [kernelWard_iff_kernelConjugation_eq]
  rw [show hbXiPeierlsUnitSourceFEKernelSymmetrization K =
      fun q r => K q r + hbXiPeierlsUnitSourceFEKernelConjugation K q r by rfl,
    hbXiPeierlsUnitSourceFEKernelConjugation_add,
    hbXiPeierlsUnitSourceFEKernelConjugation_involutive]
  funext q r
  simp [add_comm]

/-- Every Ward kernel, and only a Ward kernel, is a source-conjugation symmetrization. -/
theorem kernelWard_iff_exists_kernelSymmetrization
    (K : XiZeroCopy → XiZeroCopy → ℂ) :
    HBXiPeierlsUnitSourceFEKernelWard K ↔
      ∃ A : XiZeroCopy → XiZeroCopy → ℂ,
        hbXiPeierlsUnitSourceFEKernelSymmetrization A = K := by
  constructor
  · intro hK
    refine ⟨fun q r => (1 / 2 : ℂ) * K q r, ?_⟩
    have hfixed := (kernelWard_iff_kernelConjugation_eq K).mp hK
    funext q r
    have hqr := congrFun (congrFun hfixed q) r
    rw [hbXiPeierlsUnitSourceFEKernelConjugation] at hqr
    rw [hbXiPeierlsUnitSourceFEKernelSymmetrization,
      hbXiPeierlsUnitSourceFEKernelConjugation]
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      simpa using (map_ratCast (starRingEnd ℂ) (1 / 2 : ℚ))
    rw [map_mul, map_mul, map_mul, hhalf]
    have hqr' :
        (starRingEnd ℂ)
              (K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv r)) *
            (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) *
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle r) = K q r := by
      simpa only [map_mul] using hqr
    calc
      1 / 2 * K q r + 1 / 2 *
          (starRingEnd ℂ)
              (K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv r)) *
            (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) *
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle r) =
        1 / 2 * K q r + 1 / 2 *
          ((starRingEnd ℂ)
              (K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv r)) *
            (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) *
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle r)) := by ring
      _ =
        1 / 2 * K q r + 1 / 2 * K q r := by rw [hqr']
      _ = K q r := by ring
  · rintro ⟨A, rfl⟩
    exact hbXiPeierlsUnitSourceFEKernelSymmetrization_kernelWard A

/-- A kernel fixed by physical reflection and complex conjugation. -/
def HBXiPeierlsReflectionRealKernel
    (K : XiZeroCopy → XiZeroCopy → ℂ) : Prop :=
  ∀ q r : XiZeroCopy,
    K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv r) =
      (starRingEnd ℂ) (K q r)

theorem criticalLine_of_kernelWard_of_reflectionReal_of_diagonal_ne_zero
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsUnitSourceFEKernelWard K)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (q : XiZeroCopy) (hdiag : K q q ≠ 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  have hq := hward q q
  rw [hreflect q q] at hq
  have hconj : (starRingEnd ℂ) (K q q) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hdiag
  have hsquare : hbXiPeierlsUnitSourceFECocycle q ^ (2 : ℕ) = 1 := by
    apply mul_left_cancel₀ hconj
    simpa only [pow_two, mul_one, mul_assoc] using hq
  exact (hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q).mp hsquare

/-- Sharp fixed-form obstruction: every tilted fibre has zero diagonal in any reflection-real
Ward kernel, regardless of all off-diagonal couplings. -/
theorem kernel_diagonal_eq_zero_of_kernelWard_of_reflectionReal_of_tilt
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsUnitSourceFEKernelWard K)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    K q q = 0 := by
  by_contra hdiag
  exact htilt (criticalLine_of_kernelWard_of_reflectionReal_of_diagonal_ne_zero
    K hward hreflect q hdiag)

theorem forall_hbXiPeierlsKernelForm_packetTransport_iff_rh_of_reflectionReal
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (hdiag : ∀ q : XiZeroCopy, K q q ≠ 0) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm K (hbXiPeierlsUnitSourceFEPacketTransport x)
          (hbXiPeierlsUnitSourceFEPacketTransport y) =
        (starRingEnd ℂ) (hbXiPeierlsKernelForm K x y)) ↔
      RiemannHypothesis := by
  rw [forall_hbXiPeierlsKernelForm_packetTransport_iff_kernelWard]
  constructor
  · intro hward
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact criticalLine_of_kernelWard_of_reflectionReal_of_diagonal_ne_zero K hward
      hreflect q (hdiag q)
  · intro hRH q r
    have hfixed :=
      (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH
    have hq : (q.1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp (hfixed q)
    have hr : (r.1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff r).mp (hfixed r)
    have hkq : hbXiPeierlsUnitSourceFECocycle q = 1 := by
      have hsource :=
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hq
      simp [hbXiPeierlsUnitSourceFECocycle, hsource]
    have hkr : hbXiPeierlsUnitSourceFECocycle r = 1 := by
      have hsource :=
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero r).mpr hr
      simp [hbXiPeierlsUnitSourceFECocycle, hsource]
    rw [hreflect q r, hkq, hkr, mul_one, mul_one]

end

end RHTower
