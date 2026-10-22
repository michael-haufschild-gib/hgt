import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFESpectralLocalKernelRigidity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTopologicalBlackHoleQNMIncidence

/-!
# QNM time-generator classification and source-FE Ward no-go

The literal positive-branch Birmingham--Mokhtari QNM frequency separates distinct Xi divisor
supports.  On arbitrary finite-packet kernel forms, symmetry under its infinitesimal time-
translation generator is therefore equivalent to spectral-fibre locality, with arbitrary mixing
among multiplicity copies over one zero.

The constructed physical identity kernel and global two-channel Peierls pairing have this QNM
conservation unconditionally.  Nevertheless source-FE covariance of the same identity kernel is
equivalent to RH.  Thus stationary QNM conservation derives exactly the locality isolated by HC55,
but cannot by itself supply the missing FE--Schwarz Ward law.

`[NEW] [QNM ORTHOGONALITY] [GENERATOR CLASSIFICATION] [PRODUCER NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Literal positive-branch BM QNM frequency attached to an Xi multiplicity copy. -/
def hbXiPeierlsQNMFrequency (n : ℕ) (q : XiZeroCopy) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)

theorem hbXiPeierlsQNMFrequency_eq (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsQNMFrequency n q =
      -Complex.I / 2 * (q.1 : ℂ) + Complex.I / 2 -
        Complex.I * thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  unfold hbXiPeierlsQNMFrequency
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum, xiSpectralPoint]
  ring

/-- At fixed overtone, the literal BM QNM frequency separates Xi support exactly. -/
theorem hbXiPeierlsQNMFrequency_eq_iff (n : ℕ) (q r : XiZeroCopy) :
    hbXiPeierlsQNMFrequency n q = hbXiPeierlsQNMFrequency n r ↔ q.1 = r.1 := by
  constructor
  · intro h
    apply Subtype.ext
    rw [hbXiPeierlsQNMFrequency_eq, hbXiPeierlsQNMFrequency_eq] at h
    have hcoef : (-Complex.I / 2 : ℂ) ≠ 0 := by
      exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by norm_num)
    apply mul_left_cancel₀ hcoef
    linear_combination h
  · intro h
    rw [hbXiPeierlsQNMFrequency_eq, hbXiPeierlsQNMFrequency_eq, h]

/-- Diagonal infinitesimal time-translation generator on finite Xi source packets. -/
def hbXiPeierlsQNMTimeGenerator (n : ℕ) :
    HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket :=
  hbXiPeierlsWeightedPacketLinear (hbXiPeierlsQNMFrequency n)

@[simp]
theorem hbXiPeierlsQNMTimeGenerator_single
    (n : ℕ) (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsQNMTimeGenerator n (Finsupp.single q c) =
      Finsupp.single q (hbXiPeierlsQNMFrequency n q * c) := by
  exact hbXiPeierlsWeightedPacket_single _ q c

@[simp]
theorem hbXiPeierlsQNMTimeGenerator_apply
    (n : ℕ) (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsQNMTimeGenerator n x q = hbXiPeierlsQNMFrequency n q * x q := by
  exact hbXiPeierlsWeightedPacket_apply _ x q

/-- Ordered-pair coefficient equation for symmetry under the QNM time generator. -/
def HBXiPeierlsQNMGeneratorWard
    (n : ℕ) (K : XiZeroCopy → XiZeroCopy → ℂ) : Prop :=
  ∀ q r : XiZeroCopy,
    K q r * hbXiPeierlsQNMFrequency n q =
      K q r * hbXiPeierlsQNMFrequency n r

/-- Full finite-packet generator symmetry is exactly its ordered-pair coefficient law. -/
theorem forall_hbXiPeierlsKernelForm_qnmGenerator_symmetric_iff_generatorWard
    (n : ℕ) (K : XiZeroCopy → XiZeroCopy → ℂ) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm K (hbXiPeierlsQNMTimeGenerator n x) y =
        hbXiPeierlsKernelForm K x (hbXiPeierlsQNMTimeGenerator n y)) ↔
      HBXiPeierlsQNMGeneratorWard n K := by
  constructor
  · intro h q r
    have hqr := h (Finsupp.single q 1) (Finsupp.single r 1)
    simpa using hqr
  · intro h
    have hsingle (q : XiZeroCopy) (c : ℂ) (y : HBXiPeierlsPacket) :
        hbXiPeierlsKernelForm K
            (hbXiPeierlsQNMTimeGenerator n (Finsupp.single q c)) y =
          hbXiPeierlsKernelForm K (Finsupp.single q c)
            (hbXiPeierlsQNMTimeGenerator n y) := by
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg =>
          rw [map_add, hbXiPeierlsKernelForm_add_right,
            hbXiPeierlsKernelForm_add_right, hf, hg]
      | single r d =>
          simp only [hbXiPeierlsQNMTimeGenerator_single,
            hbXiPeierlsKernelForm_single_single]
          calc
            K q r * (hbXiPeierlsQNMFrequency n q * c) * d =
                (K q r * hbXiPeierlsQNMFrequency n q) * c * d := by ring
            _ = (K q r * hbXiPeierlsQNMFrequency n r) * c * d := by
              rw [h q r]
            _ = K q r * c * (hbXiPeierlsQNMFrequency n r * d) := by ring
    intro x y
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
        rw [map_add, hbXiPeierlsKernelForm_add_left,
          hbXiPeierlsKernelForm_add_left, hf, hg]
    | single q c => exact hsingle q c y

/-- The QNM generator coefficient law is exactly spectral-fibre locality. -/
theorem hbXiPeierlsQNMGeneratorWard_iff_spectralLocal
    (n : ℕ) (K : XiZeroCopy → XiZeroCopy → ℂ) :
    HBXiPeierlsQNMGeneratorWard n K ↔
      HBXiPeierlsSpectralFibreLocalKernel K := by
  constructor
  · intro h q r hqr
    apply (hbXiPeierlsQNMFrequency_eq_iff n q r).mp
    exact mul_left_cancel₀ hqr (h q r)
  · intro h q r
    by_cases hqr : K q r = 0
    · simp [hqr]
    · rw [(hbXiPeierlsQNMFrequency_eq_iff n q r).mpr (h q r hqr)]

/-- Complete QNM orthogonality classification: infinitesimal time-translation symmetry of an
arbitrary finite-packet kernel form is equivalent to support on equal Xi spectral fibres. -/
theorem forall_hbXiPeierlsKernelForm_qnmGenerator_symmetric_iff_spectralLocal
    (n : ℕ) (K : XiZeroCopy → XiZeroCopy → ℂ) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm K (hbXiPeierlsQNMTimeGenerator n x) y =
        hbXiPeierlsKernelForm K x (hbXiPeierlsQNMTimeGenerator n y)) ↔
      HBXiPeierlsSpectralFibreLocalKernel K := by
  rw [forall_hbXiPeierlsKernelForm_qnmGenerator_symmetric_iff_generatorWard,
    hbXiPeierlsQNMGeneratorWard_iff_spectralLocal]

/-- Identity kernel of the physical direct-sum Peierls dot product. -/
def hbXiPeierlsPhysicalIdentityKernel (q r : XiZeroCopy) : ℂ :=
  if q = r then 1 else 0

theorem hbXiPeierlsPhysicalIdentityKernelForm_eq_dot
    (x y : HBXiPeierlsPacket) :
    hbXiPeierlsKernelForm hbXiPeierlsPhysicalIdentityKernel x y =
      hbXiPeierlsDot x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp [hbXiPeierlsDot]
  | add f g hf hg =>
      rw [hbXiPeierlsKernelForm_add_left, hbXiPeierlsDot_add_left, hf, hg]
  | single q c =>
      induction y using Finsupp.induction_linear with
      | zero => simp [hbXiPeierlsDot]
      | add f g hf hg =>
          rw [hbXiPeierlsKernelForm_add_right, hbXiPeierlsDot_add_right, hf, hg]
      | single r d =>
          by_cases hqr : q = r
          · subst r
            simp [hbXiPeierlsPhysicalIdentityKernel,
              hbXiPeierlsKernelForm_single_single, hbXiPeierlsDot_single]
          · simp [hbXiPeierlsPhysicalIdentityKernel,
              hbXiPeierlsKernelForm_single_single, hbXiPeierlsDot_single, hqr]

theorem hbXiPeierlsPhysicalIdentityKernel_spectralLocal :
    HBXiPeierlsSpectralFibreLocalKernel hbXiPeierlsPhysicalIdentityKernel := by
  intro q r hqr
  by_contra hfst
  have hne : q ≠ r := by
    intro h
    exact hfst (congrArg Sigma.fst h)
  exact hqr (by simp [hbXiPeierlsPhysicalIdentityKernel, hne])

theorem hbXiPeierlsPhysicalIdentityKernel_reflectionReal :
    HBXiPeierlsReflectionRealKernel hbXiPeierlsPhysicalIdentityKernel := by
  intro q r
  by_cases hqr : q = r
  · subst r
    simp [hbXiPeierlsPhysicalIdentityKernel]
  · have hreflect : xiZeroCopyReflectEquiv q ≠ xiZeroCopyReflectEquiv r :=
      fun h => hqr (xiZeroCopyReflectEquiv.injective h)
    simp [hbXiPeierlsPhysicalIdentityKernel, hqr, hreflect]

theorem hbXiPeierlsPhysicalIdentityKernelForm_leftNondegenerate :
    HBXiPeierlsKernelFormLeftNondegenerate hbXiPeierlsPhysicalIdentityKernel := by
  intro x hx
  apply Finsupp.ext
  intro q
  have hq := hx (Finsupp.single q 1)
  classical
  simpa [hbXiPeierlsKernelForm, hbXiPeierlsPhysicalIdentityKernel, eq_comm] using hq

/-- The actual physical Peierls dot product is symmetric under the literal BM QNM generator
unconditionally. -/
theorem hbXiPeierlsDot_qnmGenerator_symmetric
    (n : ℕ) (x y : HBXiPeierlsPacket) :
    hbXiPeierlsDot (hbXiPeierlsQNMTimeGenerator n x) y =
      hbXiPeierlsDot x (hbXiPeierlsQNMTimeGenerator n y) := by
  rw [← hbXiPeierlsPhysicalIdentityKernelForm_eq_dot,
    ← hbXiPeierlsPhysicalIdentityKernelForm_eq_dot]
  exact
    (forall_hbXiPeierlsKernelForm_qnmGenerator_symmetric_iff_spectralLocal
      n hbXiPeierlsPhysicalIdentityKernel).mpr
        hbXiPeierlsPhysicalIdentityKernel_spectralLocal x y

/-- Componentwise QNM time generator on the constructed two-channel Peierls carrier. -/
def hbXiPeierlsCarrierQNMTimeGenerator
    (n : ℕ) (x : HBXiPeierlsCarrier) : HBXiPeierlsCarrier :=
  (hbXiPeierlsQNMTimeGenerator n x.1, hbXiPeierlsQNMTimeGenerator n x.2)

/-- The constructed global two-channel physical Peierls pairing is QNM-time-conserved
unconditionally. -/
theorem hbXiPeierlsPairing_qnmGenerator_symmetric
    (n : ℕ) (x y : HBXiPeierlsCarrier) :
    hbXiPeierlsPairing (hbXiPeierlsCarrierQNMTimeGenerator n x) y =
      hbXiPeierlsPairing x (hbXiPeierlsCarrierQNMTimeGenerator n y) := by
  simp only [hbXiPeierlsPairing_apply, hbXiPeierlsCarrierQNMTimeGenerator]
  rw [hbXiPeierlsDot_qnmGenerator_symmetric,
    hbXiPeierlsDot_qnmGenerator_symmetric]

/-- Sharp producer no-go: although the physical identity kernel is QNM-time-conserved and
nondegenerate unconditionally, its literal source-FE covariance remains exactly RH. -/
theorem forall_hbXiPeierlsPhysicalIdentityKernelForm_packetTransport_iff_rh :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm hbXiPeierlsPhysicalIdentityKernel
          (hbXiPeierlsUnitSourceFEPacketTransport x)
          (hbXiPeierlsUnitSourceFEPacketTransport y) =
        (starRingEnd ℂ)
          (hbXiPeierlsKernelForm hbXiPeierlsPhysicalIdentityKernel x y)) ↔
      RiemannHypothesis :=
  forall_hbXiPeierlsKernelForm_packetTransport_iff_rh_of_reflectionReal_of_spectralLocal_of_leftNondegenerate
    hbXiPeierlsPhysicalIdentityKernel
    hbXiPeierlsPhysicalIdentityKernel_reflectionReal
    hbXiPeierlsPhysicalIdentityKernel_spectralLocal
    hbXiPeierlsPhysicalIdentityKernelForm_leftNondegenerate

/-- HC54's canonical line-conjugate survivor has QNM-generator symmetry exactly under RH. -/
theorem forall_hbXiPeierlsLineConjPermutationKernelForm_qnmGenerator_symmetric_iff_rh
    (n : ℕ) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm hbXiPeierlsLineConjPermutationKernel
          (hbXiPeierlsQNMTimeGenerator n x) y =
        hbXiPeierlsKernelForm hbXiPeierlsLineConjPermutationKernel x
          (hbXiPeierlsQNMTimeGenerator n y)) ↔
      RiemannHypothesis := by
  rw [forall_hbXiPeierlsKernelForm_qnmGenerator_symmetric_iff_spectralLocal,
    hbXiPeierlsLineConjPermutationKernel_spectralLocal_iff_rh]

end

end RHTower
