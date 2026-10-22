import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMClockPreservingGaugeConjugacyNoGo

/-!
# Source-fixed linear mixing cannot manufacture HB clock covariance

The remaining HB receiver asks literal anti-linear source-FE transport to commute with one
source-predeclared nonzero centered-QNM physical clock step. Previous no-go theorems eliminated
diagonal source gauges and arbitrary gauges that already preserve the clock. This module removes
the surviving static linear-mixing escape: an arbitrary invertible complex-linear equivalence may
mix every packet coordinate and need not preserve the clock, reflection, pairing, support, norm,
or topology, but it must retain each literal nonlinear source packet.

Fixing one nonzero off-wall source packet forces linearity to fix its entire coordinate line.
Fixing both source packets of a tilted functional-equation orbit therefore makes conjugation
invisible on that orbit. The existing one-orbit clock rigidity then gives the exact classification:
such a source-fixed linear mixing is clock-covariant precisely at zero time or under RH. At unit
time its existence is exactly RH.

This kills static complex-linear eigenspace mixing as a producer of the missing HB identity when
literal source incidence is retained. The sharp positive survivor is local: any nonzero-time
clock-covariant mixing on a tilted orbit must displace at least one of the orbit's two literal
source packets. A surviving producer must therefore be genuinely source-changing, nonlinear, or
time-dependent; it cannot be a static source-preserving change of packet coordinates.

`[NEW] [HB NO-GO] [SOURCE RIGIDITY] [LINEAR MIXING] [EXACT RH ENDPOINT] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- An arbitrary complex-linear packet equivalence fixes the literal unit nonlinear source at one
Xi copy. -/
def HBXiPeierlsUnitSourceLinearGaugeFixedAt
    (g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket) (q : XiZeroCopy) : Prop :=
  g (Finsupp.single q
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)) =
    Finsupp.single q
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)

/-- An arbitrary complex-linear packet equivalence fixes every literal unit nonlinear source
coordinate. -/
def HBXiPeierlsUnitSourceLinearGaugeFixed
    (g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket) : Prop :=
  ∀ q : XiZeroCopy, HBXiPeierlsUnitSourceLinearGaugeFixedAt g q

/-- Literal anti-linear source-FE transport conjugated by an arbitrary complex-linear packet
equivalence. -/
def hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport
    (g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket)
    (x : HBXiPeierlsPacket) : HBXiPeierlsPacket :=
  g.symm (hbXiPeierlsUnitSourceFEPacketTransport (g x))

/-- Covariance of the arbitrarily conjugated source-FE transport with the unchanged physical
clock. -/
def HBXiPeierlsLinearGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant
    (g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket)
    (n : ℕ) (t : ℝ) : Prop :=
  ∀ x : HBXiPeierlsPacket,
    hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport g
        (hbXiPeierlsCenteredQNMPhysicalClockStep n t x) =
      hbXiPeierlsCenteredQNMPhysicalClockStep n t
        (hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport g x)

private theorem finsupp_single_eq_smul_single_one
    (q : XiZeroCopy) (c : ℂ) :
    Finsupp.single q c = c • Finsupp.single q (1 : ℂ) := by
  classical
  ext r
  by_cases h : r = q
  · subst r
    simp [smul_eq_mul]
  · simp [h]

/-- Fixing one nonzero source coordinate forces an arbitrary linear equivalence to fix that unit
basis packet. -/
theorem hbXiPeierlsUnitSourceLinearGaugeFixedAt_single_one_of_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    (q : XiZeroCopy) (hfixed : HBXiPeierlsUnitSourceLinearGaugeFixedAt g q)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    g (Finsupp.single q (1 : ℂ)) = Finsupp.single q 1 := by
  let a := d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q
  have ha : a ≠ 0 :=
    (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).not.mpr hoff
  have hsource := hfixed
  unfold HBXiPeierlsUnitSourceLinearGaugeFixedAt at hsource
  rw [finsupp_single_eq_smul_single_one q a, map_smul] at hsource
  apply Finsupp.ext
  intro r
  have hr := congrArg (fun x : HBXiPeierlsPacket => x r) hsource
  simpa [smul_eq_mul] using mul_left_cancel₀ ha hr

/-- Global source fixing forces every off-wall unit basis packet to be fixed. -/
theorem hbXiPeierlsUnitSourceLinearGaugeFixed_single_one_of_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    (hfixed : HBXiPeierlsUnitSourceLinearGaugeFixed g)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    g (Finsupp.single q (1 : ℂ)) = Finsupp.single q 1 :=
  hbXiPeierlsUnitSourceLinearGaugeFixedAt_single_one_of_offLine
    q (hfixed q) hoff

theorem hbXiPeierlsUnitSourceLinearGaugeFixed_single_of_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    (hfixed : HBXiPeierlsUnitSourceLinearGaugeFixed g)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) (c : ℂ) :
    g (Finsupp.single q c) = Finsupp.single q c := by
  rw [finsupp_single_eq_smul_single_one q c, map_smul,
    hbXiPeierlsUnitSourceLinearGaugeFixed_single_one_of_offLine hfixed q hoff,
    ← finsupp_single_eq_smul_single_one]

theorem hbXiPeierlsUnitSourceLinearGaugeFixedAt_single_of_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    {q : XiZeroCopy} (hfixed : HBXiPeierlsUnitSourceLinearGaugeFixedAt g q)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) (c : ℂ) :
    g (Finsupp.single q c) = Finsupp.single q c := by
  rw [finsupp_single_eq_smul_single_one q c, map_smul,
    hbXiPeierlsUnitSourceLinearGaugeFixedAt_single_one_of_offLine q hfixed hoff,
    ← finsupp_single_eq_smul_single_one]

theorem hbXiPeierlsUnitSourceLinearGaugeFixed_symm_single_of_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    (hfixed : HBXiPeierlsUnitSourceLinearGaugeFixed g)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) (c : ℂ) :
    g.symm (Finsupp.single q c) = Finsupp.single q c := by
  apply g.injective
  rw [g.apply_symm_apply,
    hbXiPeierlsUnitSourceLinearGaugeFixed_single_of_offLine hfixed q hoff c]

theorem hbXiPeierlsUnitSourceLinearGaugeFixedAt_symm_single_of_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    {q : XiZeroCopy} (hfixed : HBXiPeierlsUnitSourceLinearGaugeFixedAt g q)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) (c : ℂ) :
    g.symm (Finsupp.single q c) = Finsupp.single q c := by
  apply g.injective
  rw [g.apply_symm_apply,
    hbXiPeierlsUnitSourceLinearGaugeFixedAt_single_of_offLine hfixed hoff c]

private theorem xiZeroCopyReflect_re_ne_half_of_ne_half
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≠ 1 / 2 := by
  rw [xiZeroCopyReflect_re_eq_one_sub]
  intro h
  apply hoff
  linarith

/-- Fixing both literal source coordinates on one tilted FE orbit makes arbitrary linear
conjugation invisible on that orbit. -/
theorem hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport_single_of_fixedOrbit_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    {q : XiZeroCopy}
    (hq : HBXiPeierlsUnitSourceLinearGaugeFixedAt g q)
    (hRq : HBXiPeierlsUnitSourceLinearGaugeFixedAt g (xiZeroCopyReflectEquiv q))
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) (c : ℂ) :
    hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport g
        (Finsupp.single q c) =
      hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q c) := by
  rw [hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport,
    hbXiPeierlsUnitSourceLinearGaugeFixedAt_single_of_offLine hq hoff c,
    hbXiPeierlsUnitSourceFEPacketTransport_single,
    hbXiPeierlsUnitSourceLinearGaugeFixedAt_symm_single_of_offLine hRq
      (xiZeroCopyReflect_re_ne_half_of_ne_half q hoff)]

/-- On every off-wall FE orbit, arbitrary source-fixed linear conjugation leaves literal transport
unchanged. -/
theorem hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport_single_of_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    (hfixed : HBXiPeierlsUnitSourceLinearGaugeFixed g)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) (c : ℂ) :
    hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport g
        (Finsupp.single q c) =
      hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q c) := by
  exact
    hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport_single_of_fixedOrbit_offLine
      (hfixed q) (hfixed (xiZeroCopyReflectEquiv q)) hoff c

/-- Sharp positive survivor: any arbitrary linear mixing which achieves nonzero-time fixed-clock
covariance on a tilted FE orbit must displace at least one of that orbit's two literal source
packets. -/
theorem hbXiPeierlsLinearGaugeClockCovariant_sourceDisplacement_of_offLine
    {g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket}
    {n : ℕ} {t : ℝ} (ht : t ≠ 0)
    (hcov : HBXiPeierlsLinearGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant g n t)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬(HBXiPeierlsUnitSourceLinearGaugeFixedAt g q ∧
      HBXiPeierlsUnitSourceLinearGaugeFixedAt g (xiZeroCopyReflectEquiv q)) := by
  rintro ⟨hq, hRq⟩
  have hconjClock := hcov (Finsupp.single q (1 : ℂ))
  have hliteral :
      hbXiPeierlsUnitSourceFEPacketTransport
          (hbXiPeierlsCenteredQNMPhysicalClockStep n t
            (Finsupp.single q 1)) =
        hbXiPeierlsCenteredQNMPhysicalClockStep n t
          (hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q 1)) := by
    calc
      _ = hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport g
            (hbXiPeierlsCenteredQNMPhysicalClockStep n t
              (Finsupp.single q 1)) := by
          rw [hbXiPeierlsCenteredQNMPhysicalClockStep_single]
          exact
            (hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport_single_of_fixedOrbit_offLine
              hq hRq hoff _).symm
      _ = hbXiPeierlsCenteredQNMPhysicalClockStep n t
            (hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport g
              (Finsupp.single q 1)) := hconjClock
      _ = _ := by
          rw [hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport_single_of_fixedOrbit_offLine
            hq hRq hoff]
  have hline :=
    (hbXiPeierlsUnitSourceFEPhysicalClockStep_single_commute_iff n t q).mp hliteral
  exact hoff (hline.resolve_left ht)

/-- Existence of any source-fixed linear mixing with fixed-clock covariance. -/
def HBXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant
    (n : ℕ) (t : ℝ) : Prop :=
  ∃ g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket,
    HBXiPeierlsUnitSourceLinearGaugeFixed g ∧
      HBXiPeierlsLinearGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant g n t

/-- Complete arbitrary-linear-mixing classification: a literal-source-fixed packet equivalence
can make the conjugated FE transport commute with the unchanged clock only at zero time or under
RH. -/
theorem hbXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant_iff
    (n : ℕ) (t : ℝ) :
    HBXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant n t ↔
      t = 0 ∨ RiemannHypothesis := by
  constructor
  · rintro ⟨g, hfixed, hcov⟩
    by_cases ht : t = 0
    · exact Or.inl ht
    · right
      apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
      intro q
      apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
      by_contra hoff
      have hconjClock := hcov (Finsupp.single q (1 : ℂ))
      have hliteral :
          hbXiPeierlsUnitSourceFEPacketTransport
              (hbXiPeierlsCenteredQNMPhysicalClockStep n t
                (Finsupp.single q 1)) =
            hbXiPeierlsCenteredQNMPhysicalClockStep n t
              (hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q 1)) := by
        calc
          _ = hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport g
                (hbXiPeierlsCenteredQNMPhysicalClockStep n t
                  (Finsupp.single q 1)) := by
              rw [hbXiPeierlsCenteredQNMPhysicalClockStep_single]
              exact (hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport_single_of_offLine
                hfixed q hoff _).symm
          _ = hbXiPeierlsCenteredQNMPhysicalClockStep n t
                (hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport g
                  (Finsupp.single q 1)) := hconjClock
          _ = _ := by
              rw [hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport_single_of_offLine
                hfixed q hoff]
      have hline :=
        (hbXiPeierlsUnitSourceFEPhysicalClockStep_single_commute_iff n t q).mp hliteral
      exact hoff (hline.resolve_left ht)
  · rintro (ht | hRH)
    · subst t
      refine ⟨LinearEquiv.refl ℂ HBXiPeierlsPacket, ?_, ?_⟩
      · intro q
        rfl
      · intro x
        simp [hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport,
          hbXiPeierlsCenteredQNMPhysicalClockStep_zero]
    · refine ⟨LinearEquiv.refl ℂ HBXiPeierlsPacket, ?_, ?_⟩
      · intro q
        rfl
      · have hliteral :=
          (hbXiPeierlsUnitSourceFEPhysicalClockStepCovariant_iff n t).mpr (Or.inr hRH)
        intro x
        simpa [hbXiPeierlsLinearGaugeConjugatedUnitSourceFETransport] using hliteral x

/-- Unit-clock specialization: arbitrary source-fixed linear mixing produces covariance exactly
under RH. -/
theorem hbXiPeierlsExistsUnitSourceFixedLinearGaugeUnitPhysicalClockStepCovariant_iff_rh :
    HBXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant 0 1 ↔
      RiemannHypothesis := by
  rw [hbXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant_iff]
  norm_num

/-- Closed route-kill package: arbitrary static complex-linear mixing cannot manufacture the HB
clock law while retaining literal sources; any successful tilted-orbit mixing must displace one
of its two source packets. -/
def D4HBSourceFixedLinearMixingClockCovarianceRouteKilled : Prop :=
  (∀ (n : ℕ) (t : ℝ),
    HBXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant n t ↔
      t = 0 ∨ RiemannHypothesis) ∧
  ∀ (g : HBXiPeierlsPacket ≃ₗ[ℂ] HBXiPeierlsPacket)
      (n : ℕ) (t : ℝ), t ≠ 0 →
    HBXiPeierlsLinearGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant g n t →
    ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
      ¬(HBXiPeierlsUnitSourceLinearGaugeFixedAt g q ∧
        HBXiPeierlsUnitSourceLinearGaugeFixedAt g (xiZeroCopyReflectEquiv q))

theorem d4HBSourceFixedLinearMixingClockCovarianceRouteKilled :
    D4HBSourceFixedLinearMixingClockCovarianceRouteKilled := by
  refine ⟨hbXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant_iff, ?_⟩
  intro g n t ht hcov q hoff
  exact hbXiPeierlsLinearGaugeClockCovariant_sourceDisplacement_of_offLine
    ht hcov q hoff

end

end RHTower
