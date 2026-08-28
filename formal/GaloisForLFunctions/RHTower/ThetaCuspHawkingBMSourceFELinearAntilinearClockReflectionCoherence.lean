import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEClockChiralAmplitudeTransduction

/-!
# Linear/anti-linear source-FE clock-reflection coherence

The complex-linear reflection used by conserved complex-bilinear QNM currents and the literal
anti-linear source-FE transport have complementary defects.  Removing coefficient conjugation
from literal source transport restores centered-QNM clock anticommutation unconditionally, but its
square retains the phase `kappa(Rq) kappa(q)`.  The actual source cocycle only cancels after
conjugation: `kappa(Rq) conj(kappa(q)) = 1`.

Consequently the linearized transport is an involution exactly when the cocycle is real, hence
exactly on the critical line.  Globally, linear involutivity is RH.  Literal anti-linear transport
is always involutive but its clock anticommutation is RH.  Thus the simultaneous involutive,
clock-odd reflection package is RH in either semilinear realization, while the two transports are
provably distinct on every imaginary unit packet.

`[NEW] [SEMILINEARITY] [REFLECTION COHERENCE] [CONSERVATION NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Complex-linear reflection with the literal source-FE cocycle and no coefficient conjugation. -/
def hbXiPeierlsUnitSourceFELinearizedPacketTransport :
    HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket where
  toFun x :=
    hbXiPeierlsWeightedPacket
      (fun q => hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q))
      ((Finsupp.domCongr xiZeroCopyReflectEquiv) x)
  map_add' x y := by
    ext q
    simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
    ring
  map_smul' c x := by
    ext q
    simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, smul_eq_mul]
    ring

private theorem hc59_xiZeroCopyReflectEquiv_symm_apply (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv.symm q = xiZeroCopyReflectEquiv q := by
  apply xiZeroCopyReflectEquiv.injective
  simp

@[simp]
theorem hbXiPeierlsUnitSourceFELinearizedPacketTransport_apply
    (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELinearizedPacketTransport x q =
      hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
        x (xiZeroCopyReflectEquiv q) := by
  simp [hbXiPeierlsUnitSourceFELinearizedPacketTransport, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, hc59_xiZeroCopyReflectEquiv_symm_apply]

/-- The linearized source transport reflects a basis packet without conjugating its coefficient. -/
theorem hbXiPeierlsUnitSourceFELinearizedPacketTransport_single
    (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsUnitSourceFELinearizedPacketTransport (Finsupp.single q c) =
      Finsupp.single (xiZeroCopyReflectEquiv q)
        (hbXiPeierlsUnitSourceFECocycle q * c) := by
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

/-- Squaring linearized transport leaves the unconjugated source-cocycle phase. -/
theorem hbXiPeierlsUnitSourceFELinearizedPacketTransport_sq_apply
    (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELinearizedPacketTransport
        (hbXiPeierlsUnitSourceFELinearizedPacketTransport x) q =
      (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
        hbXiPeierlsUnitSourceFECocycle q) * x q := by
  simp only [hbXiPeierlsUnitSourceFELinearizedPacketTransport_apply,
    xiZeroCopyReflectEquiv_apply_apply]
  ring

/-- Complex-linear reflection anticommutes with the centered QNM generator unconditionally. -/
theorem hbXiPeierlsUnitSourceFELinearizedPacketTransport_centeredQNMGenerator_anticommute
    (n : ℕ) (x : HBXiPeierlsPacket) :
    hbXiPeierlsUnitSourceFELinearizedPacketTransport
        (hbXiPeierlsCenteredQNMTimeGenerator n x) =
      -(hbXiPeierlsCenteredQNMTimeGenerator n
        (hbXiPeierlsUnitSourceFELinearizedPacketTransport x)) := by
  ext r
  change
    hbXiPeierlsUnitSourceFELinearizedPacketTransport
        (hbXiPeierlsCenteredQNMTimeGenerator n x) r =
      -(hbXiPeierlsCenteredQNMTimeGenerator n
        (hbXiPeierlsUnitSourceFELinearizedPacketTransport x) r)
  simp only [hbXiPeierlsUnitSourceFELinearizedPacketTransport_apply,
    hbXiPeierlsCenteredQNMTimeGenerator_apply]
  rw [hbXiPeierlsCenteredQNMFrequency_reflect]
  ring

/-- The unconjugated cocycle closes exactly when the source cocycle is real: on the critical line. -/
theorem hbXiPeierlsUnitSourceFELinearCocycleProduct_eq_one_iff
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
        hbXiPeierlsUnitSourceFECocycle q = 1 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hlinear
    have hantilinear := hbXiPeierlsUnitSourceFECocycle_involutive q
    have heq :
        hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
            hbXiPeierlsUnitSourceFECocycle q =
          hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
            (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) :=
      hlinear.trans hantilinear.symm
    have hkR : hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) ≠ 0 :=
      hbXiPeierlsUnitSourceFECocycle_ne_zero (xiZeroCopyReflectEquiv q)
    have hkreal :
        hbXiPeierlsUnitSourceFECocycle q =
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) :=
      mul_left_cancel₀ hkR heq
    have him := congrArg Complex.im hkreal
    simp at him
    have himzero : (hbXiPeierlsUnitSourceFECocycle q).im = 0 := by linarith
    exact (hbXiPeierlsUnitSourceFECocycle_im_eq_zero_iff q).mp himzero
  · intro hline
    have himzero := (hbXiPeierlsUnitSourceFECocycle_im_eq_zero_iff q).mpr hline
    have hkreal :
        hbXiPeierlsUnitSourceFECocycle q =
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) := by
      apply Complex.ext
      · simp
      · simp [himzero]
    rw [hkreal]
    exact hbXiPeierlsUnitSourceFECocycle_involutive q

/-- Linearized source reflection is involutive on one unit packet exactly on the critical line. -/
theorem hbXiPeierlsUnitSourceFELinearizedPacketTransport_sq_single_eq_iff
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELinearizedPacketTransport
        (hbXiPeierlsUnitSourceFELinearizedPacketTransport (Finsupp.single q 1)) =
      Finsupp.single q 1 ↔
        (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hq := congrArg (fun x : HBXiPeierlsPacket => x q) h
    rw [hbXiPeierlsUnitSourceFELinearizedPacketTransport_sq_apply] at hq
    simp only [Finsupp.single_eq_same, mul_one] at hq
    exact (hbXiPeierlsUnitSourceFELinearCocycleProduct_eq_one_iff q).mp hq
  · intro hline
    apply Finsupp.ext
    intro r
    rw [hbXiPeierlsUnitSourceFELinearizedPacketTransport_sq_apply]
    by_cases hr : r = q
    · subst r
      rw [(hbXiPeierlsUnitSourceFELinearCocycleProduct_eq_one_iff q).mpr hline]
      simp
    · simp [hr]

/-- Global involutivity of complex-linear literal-source reflection is equivalent to RH. -/
theorem forall_hbXiPeierlsUnitSourceFELinearizedPacketTransport_involutive_iff_rh :
    (∀ x : HBXiPeierlsPacket,
      hbXiPeierlsUnitSourceFELinearizedPacketTransport
          (hbXiPeierlsUnitSourceFELinearizedPacketTransport x) = x) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact (hbXiPeierlsUnitSourceFELinearizedPacketTransport_sq_single_eq_iff q).mp
      (h (Finsupp.single q 1))
  · intro hRH x
    apply Finsupp.ext
    intro q
    rw [hbXiPeierlsUnitSourceFELinearizedPacketTransport_sq_apply]
    have hline : (q.1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp
        ((forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH q)
    rw [(hbXiPeierlsUnitSourceFELinearCocycleProduct_eq_one_iff q).mpr hline, one_mul]

/-- Linearized and literal anti-linear source transports disagree on every imaginary unit packet. -/
theorem hbXiPeierlsUnitSourceFELinearized_ne_antilinear_on_I_single
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELinearizedPacketTransport
        (Finsupp.single q Complex.I) ≠
      hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q Complex.I) := by
  intro h
  have hq := congrArg
    (fun x : HBXiPeierlsPacket => x (xiZeroCopyReflectEquiv q)) h
  rw [hbXiPeierlsUnitSourceFELinearizedPacketTransport_single,
    hbXiPeierlsUnitSourceFEPacketTransport_single] at hq
  simp only [Finsupp.single_eq_same] at hq
  have hI : Complex.I = (starRingEnd ℂ) Complex.I :=
    mul_left_cancel₀ (hbXiPeierlsUnitSourceFECocycle_ne_zero q) hq
  have him := congrArg Complex.im hI
  norm_num at him

/-- Linearized reflection coherence requires both involution and centered-clock oddness. -/
def HBXiPeierlsLinearizedSourceFEClockReflectionCoherent : Prop :=
  (∀ x : HBXiPeierlsPacket,
    hbXiPeierlsUnitSourceFELinearizedPacketTransport
        (hbXiPeierlsUnitSourceFELinearizedPacketTransport x) = x) ∧
  (∀ n : ℕ, ∀ x : HBXiPeierlsPacket,
    hbXiPeierlsUnitSourceFELinearizedPacketTransport
        (hbXiPeierlsCenteredQNMTimeGenerator n x) =
      -(hbXiPeierlsCenteredQNMTimeGenerator n
        (hbXiPeierlsUnitSourceFELinearizedPacketTransport x)))

/-- Complex-linear involutive clock reflection is exactly RH for the literal source cocycle. -/
theorem hbXiPeierlsLinearizedSourceFEClockReflectionCoherent_iff_rh :
    HBXiPeierlsLinearizedSourceFEClockReflectionCoherent ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact forall_hbXiPeierlsUnitSourceFELinearizedPacketTransport_involutive_iff_rh.mp h.1
  · intro hRH
    exact ⟨
      forall_hbXiPeierlsUnitSourceFELinearizedPacketTransport_involutive_iff_rh.mpr hRH,
      fun n x =>
        hbXiPeierlsUnitSourceFELinearizedPacketTransport_centeredQNMGenerator_anticommute n x⟩

/-- Literal anti-linear reflection coherence requires involution and centered-clock oddness. -/
def HBXiPeierlsAntilinearSourceFEClockReflectionCoherent : Prop :=
  (∀ x : HBXiPeierlsPacket,
    hbXiPeierlsUnitSourceFEPacketTransport
        (hbXiPeierlsUnitSourceFEPacketTransport x) = x) ∧
  (∀ n : ℕ, ∀ x : HBXiPeierlsPacket,
    hbXiPeierlsUnitSourceFEPacketTransport
        (hbXiPeierlsCenteredQNMTimeGenerator n x) =
      -(hbXiPeierlsCenteredQNMTimeGenerator n
        (hbXiPeierlsUnitSourceFEPacketTransport x)))

/-- Anti-linear involutive clock reflection is exactly RH for the literal source cocycle. -/
theorem hbXiPeierlsAntilinearSourceFEClockReflectionCoherent_iff_rh :
    HBXiPeierlsAntilinearSourceFEClockReflectionCoherent ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact
      (forall_hbXiPeierlsUnitSourceFETransport_centeredQNMGenerator_anticommute_iff_rh 0).mp
        (h.2 0)
  · intro hRH
    exact ⟨hbXiPeierlsUnitSourceFEPacketTransport_involutive,
      fun n =>
        (forall_hbXiPeierlsUnitSourceFETransport_centeredQNMGenerator_anticommute_iff_rh n).mpr
          hRH⟩

/-- Linear and anti-linear realizations have the same global coherence locus, despite differing
as maps on every imaginary unit packet. -/
theorem hbXiPeierlsLinearized_iff_antilinear_sourceFEClockReflectionCoherent :
    HBXiPeierlsLinearizedSourceFEClockReflectionCoherent ↔
      HBXiPeierlsAntilinearSourceFEClockReflectionCoherent := by
  rw [hbXiPeierlsLinearizedSourceFEClockReflectionCoherent_iff_rh,
    hbXiPeierlsAntilinearSourceFEClockReflectionCoherent_iff_rh]

end

end RHTower
