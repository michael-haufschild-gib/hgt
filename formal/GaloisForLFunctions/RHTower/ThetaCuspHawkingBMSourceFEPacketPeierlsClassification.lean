import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFECocycleFixedPairingRigidity

/-!
# Packetwise source-FE transport and diagonal Peierls Ward classification
-/

open Complex

namespace RHTower

noncomputable section

/-- Pointwise multiplication of a finite Xi packet by an arbitrary diagonal weight. -/
def hbXiPeierlsWeightedPacket
    (w : XiZeroCopy → ℂ) (x : HBXiPeierlsPacket) : HBXiPeierlsPacket :=
  Finsupp.onFinset x.support (fun q => w q * x q) (by
    intro q h
    rw [Finsupp.mem_support_iff]
    intro hx
    apply h
    rw [hx, mul_zero])

@[simp]
theorem hbXiPeierlsWeightedPacket_apply
    (w : XiZeroCopy → ℂ) (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsWeightedPacket w x q = w q * x q := by
  rw [hbXiPeierlsWeightedPacket, Finsupp.onFinset_apply]

/-- Diagonal packet multiplication as a linear map. -/
def hbXiPeierlsWeightedPacketLinear (w : XiZeroCopy → ℂ) :
    HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket where
  toFun := hbXiPeierlsWeightedPacket w
  map_add' x y := by
    ext q
    simp [mul_add]
  map_smul' c x := by
    ext q
    simp [smul_eq_mul]
    ring

@[simp]
theorem hbXiPeierlsWeightedPacket_zero (w : XiZeroCopy → ℂ) :
    hbXiPeierlsWeightedPacket w 0 = 0 := by
  exact map_zero (hbXiPeierlsWeightedPacketLinear w)

@[simp]
theorem hbXiPeierlsWeightedPacket_add
    (w : XiZeroCopy → ℂ) (x y : HBXiPeierlsPacket) :
    hbXiPeierlsWeightedPacket w (x + y) =
      hbXiPeierlsWeightedPacket w x + hbXiPeierlsWeightedPacket w y := by
  exact map_add (hbXiPeierlsWeightedPacketLinear w) x y

@[simp]
theorem hbXiPeierlsWeightedPacket_single
    (w : XiZeroCopy → ℂ) (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsWeightedPacket w (Finsupp.single q c) =
      Finsupp.single q (w q * c) := by
  classical
  ext r
  by_cases h : r = q
  · subst r
    simp
  · simp [h]

/-- Full finite-packet anti-linear FE transport forced by the literal unit BM source. -/
def hbXiPeierlsUnitSourceFEPacketTransport :
    HBXiPeierlsPacket →ₗ⋆[ℂ] HBXiPeierlsPacket where
  toFun x :=
    hbXiPeierlsWeightedPacket
      (fun q => hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q))
      ((Finsupp.domCongr xiZeroCopyReflectEquiv)
        (hbXiPeierlsPacketConjugation x))
  map_add' x y := by
    ext q
    simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
    ring
  map_smul' c x := by
    ext q
    simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, smul_eq_mul,
      ]
    ring

private theorem hc51_xiZeroCopyReflectEquiv_symm_apply (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv.symm q = xiZeroCopyReflectEquiv q := by
  apply xiZeroCopyReflectEquiv.injective
  simp

@[simp]
theorem hbXiPeierlsUnitSourceFEPacketTransport_apply
    (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEPacketTransport x q =
      hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
        (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv q)) := by
  simp [hbXiPeierlsUnitSourceFEPacketTransport, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, hc51_xiZeroCopyReflectEquiv_symm_apply]

theorem hbXiPeierlsUnitSourceFEPacketTransport_single
    (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q c) =
      Finsupp.single (xiZeroCopyReflectEquiv q)
        (hbXiPeierlsUnitSourceFECocycle q * (starRingEnd ℂ) c) := by
  classical
  ext r
  by_cases h : r = xiZeroCopyReflectEquiv q
  · subst r
    simp
  · have hRq : xiZeroCopyReflectEquiv r ≠ q := by
      intro heq
      apply h
      rw [← heq, xiZeroCopyReflectEquiv_apply_apply]
    simp [h, hRq]

/-- The source-forced packet FE transport is an anti-linear involution. -/
theorem hbXiPeierlsUnitSourceFEPacketTransport_involutive
    (x : HBXiPeierlsPacket) :
    hbXiPeierlsUnitSourceFEPacketTransport
        (hbXiPeierlsUnitSourceFEPacketTransport x) = x := by
  ext q
  simp only [hbXiPeierlsUnitSourceFEPacketTransport_apply,
    xiZeroCopyReflectEquiv_apply_apply, map_mul]
  have hcocycle := hbXiPeierlsUnitSourceFECocycle_involutive q
  have hcc : (starRingEnd ℂ) ((starRingEnd ℂ) (x q)) = x q := by simp
  rw [hcc, ← mul_assoc, hcocycle, one_mul]

/-- Complex-bilinear diagonal Peierls form with fixed weight `w`. -/
def hbXiPeierlsWeightedDot
    (w : XiZeroCopy → ℂ) (x y : HBXiPeierlsPacket) : ℂ :=
  hbXiPeierlsDot (hbXiPeierlsWeightedPacket w x) y

theorem hbXiPeierlsWeightedDot_add_left
    (w : XiZeroCopy → ℂ) (x y z : HBXiPeierlsPacket) :
    hbXiPeierlsWeightedDot w (x + y) z =
      hbXiPeierlsWeightedDot w x z + hbXiPeierlsWeightedDot w y z := by
  simp [hbXiPeierlsWeightedDot, hbXiPeierlsDot_add_left]

theorem hbXiPeierlsWeightedDot_single
    (w : XiZeroCopy → ℂ) (q : XiZeroCopy) (c : ℂ)
    (y : HBXiPeierlsPacket) :
    hbXiPeierlsWeightedDot w (Finsupp.single q c) y =
      w q * c * y q := by
  rw [hbXiPeierlsWeightedDot, hbXiPeierlsWeightedPacket_single,
    hbXiPeierlsDot_single]

/-- Orbitwise coefficient equation for preservation of a diagonal Peierls form. -/
def HBXiPeierlsUnitSourceFEWeightWard
    (w : XiZeroCopy → ℂ) : Prop :=
  ∀ q : XiZeroCopy,
    w (xiZeroCopyReflectEquiv q) * hbXiPeierlsUnitSourceFECocycle q ^ 2 =
      (starRingEnd ℂ) (w q)

/-- The orbitwise coefficient law is sufficient for full finite-packet Ward covariance. -/
theorem hbXiPeierlsWeightedDot_packetTransport_of_weightWard
    (w : XiZeroCopy → ℂ) (hw : HBXiPeierlsUnitSourceFEWeightWard w)
    (x y : HBXiPeierlsPacket) :
    hbXiPeierlsWeightedDot w (hbXiPeierlsUnitSourceFEPacketTransport x)
        (hbXiPeierlsUnitSourceFEPacketTransport y) =
      (starRingEnd ℂ) (hbXiPeierlsWeightedDot w x y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [hbXiPeierlsWeightedDot, hbXiPeierlsDot,
      Finsupp.linearCombination_apply]
  | add f g hf hg =>
      rw [map_add, hbXiPeierlsWeightedDot_add_left, hf, hg,
        hbXiPeierlsWeightedDot_add_left, map_add]
  | single q c =>
      rw [hbXiPeierlsUnitSourceFEPacketTransport_single,
        hbXiPeierlsWeightedDot_single, hbXiPeierlsWeightedDot_single,
        hbXiPeierlsUnitSourceFEPacketTransport_apply,
        xiZeroCopyReflectEquiv_apply_apply, map_mul, map_mul]
      calc
        _ = (w (xiZeroCopyReflectEquiv q) *
              hbXiPeierlsUnitSourceFECocycle q ^ 2) *
              (starRingEnd ℂ) c * (starRingEnd ℂ) (y q) := by ring
        _ = _ := by rw [hw q]

/-- Exact packet classification: diagonal Ward covariance holds precisely when every reflection
orbit satisfies its source-cocycle coefficient equation. -/
theorem forall_hbXiPeierlsWeightedDot_packetTransport_iff_weightWard
    (w : XiZeroCopy → ℂ) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsWeightedDot w (hbXiPeierlsUnitSourceFEPacketTransport x)
          (hbXiPeierlsUnitSourceFEPacketTransport y) =
        (starRingEnd ℂ) (hbXiPeierlsWeightedDot w x y)) ↔
      HBXiPeierlsUnitSourceFEWeightWard w := by
  constructor
  · intro h q
    have hq := h (Finsupp.single q 1) (Finsupp.single q 1)
    rw [hbXiPeierlsUnitSourceFEPacketTransport_single,
      hbXiPeierlsWeightedDot_single, hbXiPeierlsWeightedDot_single] at hq
    simpa only [Finsupp.single_eq_same, map_mul, map_one, mul_one, pow_two,
      mul_assoc] using hq
  · intro hw x y
    exact hbXiPeierlsWeightedDot_packetTransport_of_weightWard w hw x y

/-- Canonical diagonal weight transported by the literal source FE cocycle. -/
def hbXiPeierlsUnitSourceFETransportedWeight (q : XiZeroCopy) : ℂ :=
  (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q)

/-- The source-transported diagonal weight solves the packet Ward equation unconditionally. -/
theorem hbXiPeierlsUnitSourceFETransportedWeight_weightWard :
    HBXiPeierlsUnitSourceFEWeightWard hbXiPeierlsUnitSourceFETransportedWeight := by
  intro q
  have hcocycle :
      (starRingEnd ℂ)
          (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q)) *
        hbXiPeierlsUnitSourceFECocycle q = 1 := by
    simpa using congrArg (starRingEnd ℂ)
      (hbXiPeierlsUnitSourceFECocycle_involutive q)
  unfold hbXiPeierlsUnitSourceFETransportedWeight
  calc
    (starRingEnd ℂ)
          (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q)) *
        hbXiPeierlsUnitSourceFECocycle q ^ 2 =
      ((starRingEnd ℂ)
          (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q)) *
        hbXiPeierlsUnitSourceFECocycle q) *
          hbXiPeierlsUnitSourceFECocycle q := by ring
    _ = hbXiPeierlsUnitSourceFECocycle q := by rw [hcocycle, one_mul]
    _ = (starRingEnd ℂ)
        ((starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q)) := by simp

/-- Canonical transported Peierls form is FE--Schwarz covariant on every finite packet, without
an RH premise. -/
theorem hbXiPeierlsUnitSourceFETransportedWeightedDot_packetWard
    (x y : HBXiPeierlsPacket) :
    hbXiPeierlsWeightedDot hbXiPeierlsUnitSourceFETransportedWeight
        (hbXiPeierlsUnitSourceFEPacketTransport x)
        (hbXiPeierlsUnitSourceFEPacketTransport y) =
      (starRingEnd ℂ)
        (hbXiPeierlsWeightedDot hbXiPeierlsUnitSourceFETransportedWeight x y) := by
  exact hbXiPeierlsWeightedDot_packetTransport_of_weightWard _
    hbXiPeierlsUnitSourceFETransportedWeight_weightWard x y

/-- The transported source weight agrees with the fixed unit weight on one fibre exactly on the
critical wall. -/
theorem hbXiPeierlsUnitSourceFETransportedWeight_eq_one_iff
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFETransportedWeight q = 1 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hweight
    have hkappa := congrArg (starRingEnd ℂ) hweight
    simp only [hbXiPeierlsUnitSourceFETransportedWeight, map_one] at hkappa
    have hsquare : hbXiPeierlsUnitSourceFECocycle q ^ 2 = 1 := by
      rw [show hbXiPeierlsUnitSourceFECocycle q = 1 by simpa using hkappa]
      norm_num
    exact (hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q).mp hsquare
  · intro hline
    have hsource :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    simp [hbXiPeierlsUnitSourceFETransportedWeight,
      hbXiPeierlsUnitSourceFECocycle, hsource]

theorem hbXiPeierlsWeightedDot_one
    (x y : HBXiPeierlsPacket) :
    hbXiPeierlsWeightedDot (fun _ : XiZeroCopy => (1 : ℂ)) x y =
      hbXiPeierlsDot x y := by
  unfold hbXiPeierlsWeightedDot
  congr 1
  ext q
  simp

/-- Identifying the unconditionally transported source Peierls form with the fixed physical form
on all finite packets is exactly RH. -/
theorem forall_hbXiPeierlsUnitSourceFETransportedWeightedDot_eq_fixed_iff_rh :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsWeightedDot hbXiPeierlsUnitSourceFETransportedWeight x y =
        hbXiPeierlsDot x y) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    apply (hbXiPeierlsUnitSourceFETransportedWeight_eq_one_iff q).mp
    have hq := h (Finsupp.single q 1) (Finsupp.single q 1)
    rw [hbXiPeierlsWeightedDot_single, hbXiPeierlsDot_single] at hq
    simpa using hq
  · intro hRH x y
    have hfixed :=
      (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH
    have hweight : ∀ q : XiZeroCopy,
        hbXiPeierlsUnitSourceFETransportedWeight q = 1 := by
      intro q
      apply (hbXiPeierlsUnitSourceFETransportedWeight_eq_one_iff q).mpr
      exact (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp (hfixed q)
    unfold hbXiPeierlsWeightedDot
    congr 1
    ext q
    simp [hweight q]

/-- The constant fixed physical weight satisfies the packet Ward equation exactly under RH. -/
theorem hbXiPeierlsUnitSourceFE_fixedWeightWard_iff_rh :
    HBXiPeierlsUnitSourceFEWeightWard (fun _ : XiZeroCopy => (1 : ℂ)) ↔
      RiemannHypothesis := by
  constructor
  · intro hw
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    apply (hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q).mp
    simpa [HBXiPeierlsUnitSourceFEWeightWard] using hw q
  · intro hRH q
    have hfixed :=
      (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH q
    have hline :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp hfixed
    have hsquare :=
      (hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q).mpr hline
    simpa only [one_mul, map_one] using hsquare

/-- Full-packet fixed Peierls covariance of the literal source FE transport is exactly RH. -/
theorem forall_hbXiPeierlsDot_unitSourceFEPacketTransport_iff_rh :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsDot (hbXiPeierlsUnitSourceFEPacketTransport x)
          (hbXiPeierlsUnitSourceFEPacketTransport y) =
        (starRingEnd ℂ) (hbXiPeierlsDot x y)) ↔
      RiemannHypothesis := by
  simpa only [← hbXiPeierlsWeightedDot_one] using
    (forall_hbXiPeierlsWeightedDot_packetTransport_iff_weightWard
      (fun _ : XiZeroCopy => (1 : ℂ))).trans
        hbXiPeierlsUnitSourceFE_fixedWeightWard_iff_rh

/-- No nondegenerate reflection-real fixed diagonal reweighting evades the source FE obstruction:
its full-packet Ward covariance is equivalent to RH. -/
theorem forall_hbXiPeierlsWeightedDot_packetTransport_iff_rh_of_reflectionReal
    (w : XiZeroCopy → ℂ)
    (hreflect : ∀ q : XiZeroCopy,
      w (xiZeroCopyReflectEquiv q) = (starRingEnd ℂ) (w q))
    (hnonzero : ∀ q : XiZeroCopy, w q ≠ 0) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsWeightedDot w (hbXiPeierlsUnitSourceFEPacketTransport x)
          (hbXiPeierlsUnitSourceFEPacketTransport y) =
        (starRingEnd ℂ) (hbXiPeierlsWeightedDot w x y)) ↔
      RiemannHypothesis := by
  rw [forall_hbXiPeierlsWeightedDot_packetTransport_iff_weightWard]
  constructor
  · intro hw
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    apply (hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q).mp
    have hq := hw q
    rw [hreflect q] at hq
    apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr (hnonzero q))
    simpa only [mul_one] using hq
  · intro hRH q
    have hfixed :=
      (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH q
    have hline :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp hfixed
    have hsquare :=
      (hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q).mpr hline
    rw [hreflect q, hsquare, mul_one]

end

end RHTower
