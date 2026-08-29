import GaloisForLFunctions.RHTower.JointAncestryGammaThetaBooleanClosedCreation

/-!
# JAS Gamma--theta divisor-gauge trivialization

The state-dependent Gamma insertion coefficient is the exact ratio of synchronized-lcm support
weights.  This module turns that corpus identity into an operator-level no-go on the actual
completed-theta packet core.

There is one aperture-independent closed creator: maximal multiplication by
`1_{p notin P} exp(y)` followed by the Boolean support toggle.  For every positive aperture `x`,
the positive closed diagonal multiplier by `gammaSewnSynchronizedLcmWeight x P` intertwines this
flat creator with the literal Gamma--theta creator on every support/grade packet.  Creators at any
two positive apertures are therefore related by explicit nonzero diagonal gauge factors.

Consequently closedness, Boolean flatness, and divisor-parameter independence of these creators
cannot by themselves force the critical line: the same gauge relation holds off wall.  The
surviving RH-bearing burden is a gauge-invariant, coefficient-faithful identification with the
literal prime-Poisson multiplication representation.
-/

open Complex Real MeasureTheory Set
open scoped ENNReal LinearPMap

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Aperture-independent creation energy: advance theta grade only on an unoccupied support. -/
def jasGammaThetaFlatCreationEnergy
    (p : Nat.Primes) (z : JASGammaThetaSupport × ℝ) : ℝ :=
  if p ∈ z.1 then 0 else Real.exp z.2

theorem measurable_jasGammaThetaFlatCreationEnergy (p : Nat.Primes) :
    Measurable (jasGammaThetaFlatCreationEnergy p) := by
  unfold jasGammaThetaFlatCreationEnergy
  apply Measurable.ite
  · have hm : Measurable (fun P : JASGammaThetaSupport => p ∈ P) :=
      measurable_of_countable _
    simpa using (hm.comp measurable_fst) (measurableSet_singleton True)
  · exact measurable_const
  · exact Real.measurable_exp.comp measurable_snd

private def jasGaugePostUnitaryLinearPMap {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H where
  domain := T.domain
  toFun := U.toLinearEquiv.toLinearMap.comp T.toFun

@[simp] private theorem jasGaugePostUnitaryLinearPMap_apply {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H)
    (f : (jasGaugePostUnitaryLinearPMap U T).domain) :
    jasGaugePostUnitaryLinearPMap U T f = U (T f) := rfl

private theorem LinearPMap.IsClosed.jasGaugePostUnitary {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
    (jasGaugePostUnitaryLinearPMap U T).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph : ((jasGaugePostUnitaryLinearPMap U T).graph : Set (H × H)) =
      (fun z : H × H => (z.1, U.symm z.2)) ⁻¹' (T.graph : Set (H × H)) := by
    ext z
    change z ∈ (jasGaugePostUnitaryLinearPMap U T).graph ↔
      (z.1, U.symm z.2) ∈ T.graph
    rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨f, hf, hval⟩
      refine ⟨f, hf, ?_⟩
      change T f = U.symm z.2
      rw [← hval]
      simp
    · rintro ⟨f, hf, hval⟩
      refine ⟨f, hf, ?_⟩
      change U (T f) = z.2
      rw [hval]
      simp
  rw [hgraph]
  exact hT.preimage
    (continuous_fst.prodMk (U.symm.continuous.comp continuous_snd))

/-- Universal support-cutting creator, independent of the divisor/aperture parameter. -/
def jasGammaThetaFlatCreation (p : Nat.Primes) :
    JASGammaThetaL2 →ₗ.[ℂ] JASGammaThetaL2 :=
  jasGaugePostUnitaryLinearPMap (jasGammaThetaToggleUnitary p)
    (maximalRealL2Mul _ (jasGammaThetaFlatCreationEnergy p))

theorem dense_jasGammaThetaFlatCreation_domain (p : Nat.Primes) :
    Dense ((jasGammaThetaFlatCreation p).domain : Set JASGammaThetaL2) :=
  maximalRealL2Mul_dense _ (measurable_jasGammaThetaFlatCreationEnergy p)

theorem jasGammaThetaFlatCreation_closed (p : Nat.Primes) :
    (jasGammaThetaFlatCreation p).IsClosed := by
  apply LinearPMap.IsClosed.jasGaugePostUnitary
  exact (maximalRealL2Mul_isSelfAdjoint _
    (measurable_jasGammaThetaFlatCreationEnergy p)).isClosed

def jasGammaThetaFlatEffectiveGain
    (p : Nat.Primes) (P : JASGammaThetaSupport) : ℝ :=
  if p ∈ P then 0 else 1

private theorem jasGammaThetaFlatEnergy_mul_packetFun
    (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ)
    (z : JASGammaThetaSupport × ℝ) :
    (jasGammaThetaFlatCreationEnergy p z : ℂ) * jasGammaThetaPacketFun P r z =
      (jasGammaThetaFlatEffectiveGain p P : ℂ) *
        jasGammaThetaPacketFun P (r + 1) z := by
  by_cases hz : z.1 = P
  · rcases z with ⟨Q, y⟩
    change Q = P at hz
    subst Q
    by_cases hp : p ∈ P
    · simp [jasGammaThetaFlatCreationEnergy, jasGammaThetaPacketFun,
        jasGammaThetaFlatEffectiveGain, hp]
    · simp only [jasGammaThetaFlatCreationEnergy, jasGammaThetaPacketFun,
        jasGammaThetaFlatEffectiveGain, hp, if_false, if_pos]
      norm_cast
      have hexp : Real.exp y * Real.exp ((r : ℝ) * y) =
          Real.exp (((r + 1 : ℕ) : ℝ) * y) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      calc
        Real.exp y * (Real.exp ((r : ℝ) * y) * thetaCuspFullSource y) =
            (Real.exp y * Real.exp ((r : ℝ) * y)) * thetaCuspFullSource y := by ring
        _ = 1 * (Real.exp (((r + 1 : ℕ) : ℝ) * y) * thetaCuspFullSource y) := by
          rw [hexp]
          ring
  · simp [jasGammaThetaPacketFun, hz]

theorem jasGammaThetaPacket_mem_flatCreationDomain
    (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaPacket P r ∈ (jasGammaThetaFlatCreation p).domain := by
  change MemLp (fun z => (jasGammaThetaFlatCreationEnergy p z : ℂ) *
    (jasGammaThetaPacket P r : JASGammaThetaSupport × ℝ → ℂ) z) 2
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
  refine (memLp_congr_ae ?_).mpr
    (Lp.memLp ((jasGammaThetaFlatEffectiveGain p P : ℂ) •
      jasGammaThetaPacket P (r + 1)))
  filter_upwards [jasGammaThetaPacket_ae P r,
    jasGammaThetaPacket_ae P (r + 1),
    Lp.coeFn_smul (jasGammaThetaFlatEffectiveGain p P : ℂ)
      (jasGammaThetaPacket P (r + 1))] with z hr hnext hsmul
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hr, hsmul, hnext]
  exact jasGammaThetaFlatEnergy_mul_packetFun p P r z

def jasGammaThetaFlatPacketDomain
    (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    (jasGammaThetaFlatCreation p).domain :=
  ⟨jasGammaThetaPacket P r, jasGammaThetaPacket_mem_flatCreationDomain p P r⟩

theorem jasGammaThetaFlatCreation_packet
    (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaFlatCreation p (jasGammaThetaFlatPacketDomain p P r) =
      (jasGammaThetaFlatEffectiveGain p P : ℂ) •
        jasGammaThetaPacket (jasGammaSupportToggle p P) (r + 1) := by
  change jasGammaThetaToggleUnitary p
      (maximalRealL2Mul
        ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
        (jasGammaThetaFlatCreationEnergy p)
        ⟨jasGammaThetaPacket P r,
          jasGammaThetaPacket_mem_flatCreationDomain p P r⟩) = _
  have hmul : maximalRealL2Mul
        ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
        (jasGammaThetaFlatCreationEnergy p)
        ⟨jasGammaThetaPacket P r,
          jasGammaThetaPacket_mem_flatCreationDomain p P r⟩ =
      (jasGammaThetaFlatEffectiveGain p P : ℂ) •
        jasGammaThetaPacket P (r + 1) := by
    apply Lp.ext
    filter_upwards [
      maximalRealL2Mul_apply_ae
        ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
        (jasGammaThetaFlatCreationEnergy p)
        ⟨jasGammaThetaPacket P r,
          jasGammaThetaPacket_mem_flatCreationDomain p P r⟩,
      jasGammaThetaPacket_ae P r,
      jasGammaThetaPacket_ae P (r + 1),
      Lp.coeFn_smul (jasGammaThetaFlatEffectiveGain p P : ℂ)
        (jasGammaThetaPacket P (r + 1))] with z hmul hr hnext hsmul
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul
    rw [hmul, hsmul]
    change (jasGammaThetaFlatCreationEnergy p z : ℂ) *
        (jasGammaThetaPacket P r : JASGammaThetaSupport × ℝ → ℂ) z =
      (jasGammaThetaFlatEffectiveGain p P : ℂ) *
        (jasGammaThetaPacket P (r + 1) : JASGammaThetaSupport × ℝ → ℂ) z
    rw [hr, hnext]
    exact jasGammaThetaFlatEnergy_mul_packetFun p P r z
  rw [hmul, map_smul, jasGammaThetaToggleUnitary_packet]

theorem jasGammaThetaFlatCreation_packet_of_not_mem
    (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) (hp : p ∉ P) :
    jasGammaThetaFlatCreation p (jasGammaThetaFlatPacketDomain p P r) =
      jasGammaThetaPacket (insert p P) (r + 1) := by
  rw [jasGammaThetaFlatCreation_packet]
  simp [jasGammaThetaFlatEffectiveGain, jasGammaSupportToggle_apply, hp]

theorem jasGammaThetaFlatCreation_packet_of_mem
    (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) (hp : p ∈ P) :
    jasGammaThetaFlatCreation p (jasGammaThetaFlatPacketDomain p P r) = 0 := by
  rw [jasGammaThetaFlatCreation_packet]
  simp [jasGammaThetaFlatEffectiveGain, hp]

/-- Positive support-diagonal gauge whose edge ratios are the Gamma insertion gains. -/
def jasGammaThetaSupportGaugeEnergy
    (x : ℝ) (z : JASGammaThetaSupport × ℝ) : ℝ :=
  gammaSewnSynchronizedLcmWeight x z.1

theorem measurable_jasGammaThetaSupportGaugeEnergy (x : ℝ) :
    Measurable (jasGammaThetaSupportGaugeEnergy x) := by
  exact (measurable_of_countable
    (gammaSewnSynchronizedLcmWeight x)).comp measurable_fst

theorem jasGammaThetaSupportGaugeEnergy_pos
    {x : ℝ} (hx : 0 < x) (z : JASGammaThetaSupport × ℝ) :
    0 < jasGammaThetaSupportGaugeEnergy x z :=
  jasGammaSynchronizedLcmWeight_pos hx z.1

/-- Maximal positive diagonal support gauge.  It is generally unbounded. -/
abbrev jasGammaThetaSupportGauge (x : ℝ) :
    JASGammaThetaL2 →ₗ.[ℂ] JASGammaThetaL2 :=
  maximalRealL2Mul _ (jasGammaThetaSupportGaugeEnergy x)

theorem dense_jasGammaThetaSupportGauge_domain (x : ℝ) :
    Dense ((jasGammaThetaSupportGauge x).domain : Set JASGammaThetaL2) :=
  maximalRealL2Mul_dense _ (measurable_jasGammaThetaSupportGaugeEnergy x)

theorem jasGammaThetaSupportGauge_closed (x : ℝ) :
    (jasGammaThetaSupportGauge x).IsClosed :=
  (maximalRealL2Mul_isSelfAdjoint _
    (measurable_jasGammaThetaSupportGaugeEnergy x)).isClosed

theorem jasGammaThetaPacket_mem_supportGaugeDomain
    (x : ℝ) (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaPacket P r ∈ (jasGammaThetaSupportGauge x).domain := by
  change MemLp (fun z => (jasGammaThetaSupportGaugeEnergy x z : ℂ) *
    (jasGammaThetaPacket P r : JASGammaThetaSupport × ℝ → ℂ) z) 2
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
  refine (memLp_congr_ae ?_).mpr
    (Lp.memLp ((gammaSewnSynchronizedLcmWeight x P : ℂ) •
      jasGammaThetaPacket P r))
  filter_upwards [jasGammaThetaPacket_ae P r,
    Lp.coeFn_smul (gammaSewnSynchronizedLcmWeight x P : ℂ)
      (jasGammaThetaPacket P r)] with z hpacket hsmul
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hpacket, hsmul, hpacket]
  unfold jasGammaThetaSupportGaugeEnergy
  by_cases hz : z.1 = P
  · subst P
    rfl
  · simp [jasGammaThetaPacketFun, hz]

def jasGammaThetaSupportGaugePacketDomain
    (x : ℝ) (P : JASGammaThetaSupport) (r : ℕ) :
    (jasGammaThetaSupportGauge x).domain :=
  ⟨jasGammaThetaPacket P r,
    jasGammaThetaPacket_mem_supportGaugeDomain x P r⟩

theorem jasGammaThetaSupportGauge_packet
    (x : ℝ) (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaSupportGauge x
        (jasGammaThetaSupportGaugePacketDomain x P r) =
      (gammaSewnSynchronizedLcmWeight x P : ℂ) •
        jasGammaThetaPacket P r := by
  apply Lp.ext
  filter_upwards [maximalRealL2Mul_apply_ae
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
      (jasGammaThetaSupportGaugeEnergy x)
      (jasGammaThetaSupportGaugePacketDomain x P r),
    jasGammaThetaPacket_ae P r,
    Lp.coeFn_smul (gammaSewnSynchronizedLcmWeight x P : ℂ)
      (jasGammaThetaPacket P r)] with z hmul hpacket hsmul
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hmul]
  change (jasGammaThetaSupportGaugeEnergy x z : ℂ) *
      (jasGammaThetaPacket P r : JASGammaThetaSupport × ℝ → ℂ) z = _
  rw [hpacket, hsmul, hpacket]
  unfold jasGammaThetaSupportGaugeEnergy
  by_cases hz : z.1 = P
  · subst P
    rfl
  · simp [jasGammaThetaPacketFun, hz]

def jasGammaThetaGaugedInputCreationDomain
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    (jasGammaThetaCreation x p).domain :=
  (gammaSewnSynchronizedLcmWeight x P : ℂ) •
    jasGammaThetaPacketDomain x p P r

def jasGammaThetaFlatOutputGaugeDomain
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    (jasGammaThetaSupportGauge x).domain :=
  (jasGammaThetaFlatEffectiveGain p P : ℂ) •
    jasGammaThetaSupportGaugePacketDomain x
      (jasGammaSupportToggle p P) (r + 1)

/-- Exact closed-gauge intertwining on every actual completed-theta packet. -/
theorem jasGammaThetaCreation_supportGauge_intertwines_flat_packet
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes)
    (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaCreation x p
        (jasGammaThetaGaugedInputCreationDomain x p P r) =
      jasGammaThetaSupportGauge x
        (jasGammaThetaFlatOutputGaugeDomain x p P r) := by
  change (jasGammaThetaCreation x p).toFun
      ((gammaSewnSynchronizedLcmWeight x P : ℂ) •
        jasGammaThetaPacketDomain x p P r) =
    (jasGammaThetaSupportGauge x).toFun
      ((jasGammaThetaFlatEffectiveGain p P : ℂ) •
        jasGammaThetaSupportGaugePacketDomain x
          (jasGammaSupportToggle p P) (r + 1))
  rw [(jasGammaThetaCreation x p).toFun.map_smul,
    (jasGammaThetaSupportGauge x).toFun.map_smul]
  have hGauge := jasGammaThetaSupportGauge_packet x
    (jasGammaSupportToggle p P) (r + 1)
  change (jasGammaThetaSupportGauge x).toFun
      (jasGammaThetaSupportGaugePacketDomain x
        (jasGammaSupportToggle p P) (r + 1)) = _ at hGauge
  rw [hGauge]
  by_cases hp : p ∈ P
  · have hCreation := jasGammaThetaCreation_packet_of_mem x p P r hp
    change (jasGammaThetaCreation x p).toFun
        (jasGammaThetaPacketDomain x p P r) = 0 at hCreation
    rw [hCreation]
    simp [jasGammaThetaFlatEffectiveGain, hp]
  · have hCreation := jasGammaThetaCreation_packet_of_not_mem x p P r hp
    change (jasGammaThetaCreation x p).toFun
        (jasGammaThetaPacketDomain x p P r) = _ at hCreation
    rw [hCreation, jasGammaSupportToggle_apply, if_neg hp,
      jasGammaSynchronizedLcmWeight_insert_boolean hx]
    simp only [jasGammaThetaFlatEffectiveGain, hp, if_false, smul_smul]
    congr 1
    norm_cast
    ring

/-- Scalar form of the same gauge trivialization, directly comparing creator outputs. -/
theorem jasGammaThetaCreation_gauge_flattened_packet
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes)
    (P : JASGammaThetaSupport) (r : ℕ) :
    (gammaSewnSynchronizedLcmWeight x P : ℂ) •
        jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) =
      (gammaSewnSynchronizedLcmWeight x (jasGammaSupportToggle p P) : ℂ) •
        jasGammaThetaFlatCreation p (jasGammaThetaFlatPacketDomain p P r) := by
  by_cases hp : p ∈ P
  · rw [jasGammaThetaCreation_packet_of_mem x p P r hp,
      jasGammaThetaFlatCreation_packet_of_mem p P r hp]
    simp
  · rw [jasGammaThetaCreation_packet_of_not_mem x p P r hp,
      jasGammaThetaFlatCreation_packet_of_not_mem p P r hp,
      jasGammaSupportToggle_apply, if_neg hp]
    rw [jasGammaSynchronizedLcmWeight_insert_boolean hx]
    push_cast
    simp only [smul_smul]
    congr 1
    ring

/-- Any two positive-aperture creators have the same packet-core connection after explicit
cross-multiplication by their diagonal support gauges. -/
theorem jasGammaThetaCreation_crossAperture_packet_gauge
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (p : Nat.Primes)
    (P : JASGammaThetaSupport) (r : ℕ) :
    ((gammaSewnSynchronizedLcmWeight x P *
        gammaSewnSynchronizedLcmWeight y (jasGammaSupportToggle p P) : ℝ) : ℂ) •
        jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) =
      ((gammaSewnSynchronizedLcmWeight y P *
        gammaSewnSynchronizedLcmWeight x (jasGammaSupportToggle p P) : ℝ) : ℂ) •
        jasGammaThetaCreation y p (jasGammaThetaPacketDomain y p P r) := by
  by_cases hp : p ∈ P
  · rw [jasGammaThetaCreation_packet_of_mem x p P r hp,
      jasGammaThetaCreation_packet_of_mem y p P r hp]
    simp
  · rw [jasGammaThetaCreation_packet_of_not_mem x p P r hp,
      jasGammaThetaCreation_packet_of_not_mem y p P r hp,
      jasGammaSupportToggle_apply, if_neg hp,
      jasGammaSynchronizedLcmWeight_insert_boolean hx,
      jasGammaSynchronizedLcmWeight_insert_boolean hy]
    push_cast
    simp only [smul_smul]
    congr 1
    ring

/-- Gauge factors in the cross-aperture identity are nonzero, so the comparison is not vacuous. -/
theorem jasGammaThetaCreation_crossAperture_packet_gauge_nonzero
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (p : Nat.Primes)
    (P : JASGammaThetaSupport) (r : ℕ) :
    (gammaSewnSynchronizedLcmWeight x P *
        gammaSewnSynchronizedLcmWeight y (jasGammaSupportToggle p P) ≠ 0) ∧
      (gammaSewnSynchronizedLcmWeight y P *
        gammaSewnSynchronizedLcmWeight x (jasGammaSupportToggle p P) ≠ 0) ∧
      ((gammaSewnSynchronizedLcmWeight x P *
          gammaSewnSynchronizedLcmWeight y (jasGammaSupportToggle p P) : ℝ) : ℂ) •
          jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) =
        ((gammaSewnSynchronizedLcmWeight y P *
          gammaSewnSynchronizedLcmWeight x (jasGammaSupportToggle p P) : ℝ) : ℂ) •
          jasGammaThetaCreation y p (jasGammaThetaPacketDomain y p P r) := by
  refine ⟨mul_ne_zero
      (jasGammaSynchronizedLcmWeight_pos hx P).ne'
      (jasGammaSynchronizedLcmWeight_pos hy (jasGammaSupportToggle p P)).ne',
    mul_ne_zero
      (jasGammaSynchronizedLcmWeight_pos hy P).ne'
      (jasGammaSynchronizedLcmWeight_pos hx (jasGammaSupportToggle p P)).ne',
    jasGammaThetaCreation_crossAperture_packet_gauge hx hy p P r⟩

end

end RHTower
