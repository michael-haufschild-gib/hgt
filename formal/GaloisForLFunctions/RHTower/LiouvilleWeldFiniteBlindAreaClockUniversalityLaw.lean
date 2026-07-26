import GaloisForLFunctions.RHTower.TranscendentalRateObject
import GaloisForLFunctions.RHTower.WeldFiniteChargeBlindAreaReadoutUniversalityLaw

/-!
# Liouville-weld finite-blind area-clock universality

The explicit Liouville power lattice gives an infinite-rank transcendental weld packet. Every
finite-valued additive observer annihilates the packet, while one canonical oriented-area scalar
recovers its exact finite-support coefficient combination and is therefore faithful. The same
non-arithmetic object has a uniquely selected Mahler clock at zero.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Scalar represented by a finite integer packet of powers of the Liouville constant. -/
def liouvilleWeldPacketScalar (c : ℕ →₀ ℤ) : ℝ :=
  c.sum fun n z => z • liouvilleConst ^ n

/-- Liouville polynomial packet represented on the real weld-class line. -/
def liouvilleWeldPacket (c : ℕ →₀ ℤ) : WeldClassLine :=
  weldClassHom.rangeRestrict (liouvilleWeldPacketScalar c)

/-- Native cohomology expansion of the Liouville weld packet. -/
theorem liouvilleWeldPacket_val (c : ℕ →₀ ℤ) :
    (liouvilleWeldPacket c).1 =
      c.sum (fun n z => z • weldClassHom (liouvilleConst ^ n)) := by
  change weldClassHom (liouvilleWeldPacketScalar c) = _
  rw [liouvilleWeldPacketScalar, map_finsuppSum]
  simp_rw [map_zsmul]

/-- Canonical area readout returns the exact Liouville polynomial scalar. -/
theorem liouvilleWeldPacket_areaReadout (c : ℕ →₀ ℤ) :
    weldClassAreaReadout (liouvilleWeldPacket c) = liouvilleWeldPacketScalar c :=
  weldClassAreaReadout_rangeRestrict _

/-- The Liouville packet remains injective after compression to one canonical real area readout. -/
theorem liouvilleWeldPacket_injective :
    Function.Injective liouvilleWeldPacket := by
  classical
  intro c d hcd
  have hscalar : liouvilleWeldPacketScalar c = liouvilleWeldPacketScalar d := by
    simpa only [liouvilleWeldPacket_areaReadout] using
      congrArg weldClassAreaReadout hcd
  have hindependent :
      LinearIndependent ℤ (fun n : ℕ => liouvilleConst ^ n) :=
    liouvilleRateObject.rate_indep
  rw [linearIndependent_iff_injective_finsuppLinearCombination] at hindependent
  apply hindependent
  simpa only [liouvilleWeldPacketScalar, Finsupp.linearCombination_apply] using hscalar

/-- Complete observer/clock certificate for the transcendence-generated Liouville weld packet. -/
structure LiouvilleWeldFiniteBlindAreaClockCertificate : Prop where
  nativeCohomology :
    ∀ c : ℕ →₀ ℤ,
      (liouvilleWeldPacket c).1 =
        c.sum (fun n z => z • weldClassHom (liouvilleConst ^ n))
  finiteBlind :
    ∀ {M : Type*} [AddCommGroup M] [Fintype M] [Nonempty M],
      ∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ M)
        (c : ℕ →₀ ℤ),
        φ (liouvilleWeldPacket c).1 = 0
  scalarRecovery :
    ∀ c : ℕ →₀ ℤ,
      weldClassAreaReadout (liouvilleWeldPacket c) = liouvilleWeldPacketScalar c
  packetInjective : Function.Injective liouvilleWeldPacket
  nativeWeldIndependent :
    ∀ (c : ℕ →₀ ℤ),
      c.sum (fun n z => z • weldClassHom (liouvilleConst ^ n)) = 0 → c = 0
  uniqueMahlerClock :
    ∃! s,
      affineSelect liouvilleRateObject.selLin liouvilleRateObject.selConst s = s
  mahlerClockAtZero :
    affineSelect liouvilleRateObject.selLin liouvilleRateObject.selConst 0 = 0

/-- **Liouville-weld finite-blind area-clock universality.**

The explicit infinite-rank transcendental weld packet is invisible to every finite-valued additive
observer, faithfully classified by one canonical scalar area readout, and governed by a uniquely
selected Mahler clock at zero. -/
theorem liouvilleWeld_finiteBlind_areaClockUniversality :
    LiouvilleWeldFiniteBlindAreaClockCertificate := by
  refine
    { nativeCohomology := liouvilleWeldPacket_val
      finiteBlind := ?_
      scalarRecovery := liouvilleWeldPacket_areaReadout
      packetInjective := liouvilleWeldPacket_injective
      nativeWeldIndependent := liouvilleObject_weld_nontrivial
      uniqueMahlerClock := liouvilleObject_has_clock
      mahlerClockAtZero := liouvilleObject_clock_at_zero }
  intro M _ _ _ φ c
  exact weldClassLine_finiteCharge_invisible φ (liouvilleWeldPacket c)

end

end GaloisForLFunctions.RHTower
