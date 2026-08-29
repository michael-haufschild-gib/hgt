import GaloisForLFunctions.RHTower.JointAncestryGammaBooleanClosedCreation
import GaloisForLFunctions.RHTower.L2SeparatedProductDensity
import GaloisForLFunctions.RHTower.L2MellinUnitary

/-!
# JAS Gamma--theta Boolean closed creation

This module couples the state-dependent Gamma Boolean support connection to the literal completed-
theta Mellin ladder on one product Hilbert space.  For every prime, maximal multiplication by

`1_{p ∉ P} · jasGammaBooleanInsertionGain x p P · exp(y)`

is followed by the measure-preserving unitary toggling `p` in the finite support.  The resulting
partial operator is closed and densely defined.  On every separated support/theta packet it kills
occupied supports and otherwise inserts the prime with the exact Gamma coefficient while advancing
the actual completed-theta grade by one.

At positive sewing points the Boolean ratio cocycle proves equality of the two literal partial-
operator paths for every pair of primes, including occupied and repeated-prime degeneracies.  At
grade `|P|`, insertion advances support cardinality and theta grade synchronously.  This closes the
cross-coordinate closed-graph burden exposed by the bounded grade-successor and prime-torus-unit
obstructions.  Source-linearity, divisor independence, and landing in an Xi reflection sewing
remain separate producer problems.
-/

open Complex Real MeasureTheory Set
open scoped ENNReal LinearPMap

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

abbrev JASGammaThetaSupport := Finset Nat.Primes

def jasGammaSupportToggleMeasurableEquiv (p : Nat.Primes) :
    JASGammaThetaSupport ≃ᵐ JASGammaThetaSupport :=
  MeasurableEquiv.mk (jasGammaSupportToggle p)
    (measurable_of_countable _) (measurable_of_countable _)

theorem jasGammaSupportToggle_measurePreserving (p : Nat.Primes) :
    MeasurePreserving (jasGammaSupportToggleMeasurableEquiv p)
      (Measure.count : Measure JASGammaThetaSupport) Measure.count := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply_of_aemeasurable
    (measurable_of_countable _).aemeasurable hs,
    Measure.count_apply hs,
    Measure.count_apply (hs.preimage (measurable_of_countable _))]
  congr 1
  let e := jasGammaSupportToggle p
  let es : (e ⁻¹' s) ≃ s := {
    toFun := fun z => ⟨e z.1, z.2⟩
    invFun := fun z => ⟨e.symm z.1, by
      change e (e.symm z.1) ∈ s
      simpa only [Equiv.apply_symm_apply] using z.2⟩
    left_inv := fun z => by ext; simp
    right_inv := fun z => by ext; simp
  }
  exact Set.encard_congr es

def jasGammaThetaToggleMeasurableEquiv (p : Nat.Primes) :
    (JASGammaThetaSupport × ℝ) ≃ᵐ (JASGammaThetaSupport × ℝ) :=
  (jasGammaSupportToggleMeasurableEquiv p).prodCongr (MeasurableEquiv.refl ℝ)

theorem jasGammaThetaToggle_measurePreserving (p : Nat.Primes) :
    MeasurePreserving (jasGammaThetaToggleMeasurableEquiv p)
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)) := by
  exact (jasGammaSupportToggle_measurePreserving p).prod
    (MeasurePreserving.id volume)

abbrev JASGammaThetaL2 :=
  Lp ℂ 2 ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))

def jasGammaThetaToggleUnitary (p : Nat.Primes) :
    JASGammaThetaL2 ≃ₗᵢ[ℂ] JASGammaThetaL2 :=
  MellinL2.lpCompMeasurePreservingEquiv
    (jasGammaThetaToggleMeasurableEquiv p)
    (jasGammaThetaToggle_measurePreserving p)

def jasGammaThetaCreationEnergy
    (x : ℝ) (p : Nat.Primes) (z : JASGammaThetaSupport × ℝ) : ℝ :=
  if p ∈ z.1 then 0
  else jasGammaBooleanInsertionGain x p z.1 * Real.exp z.2

theorem measurable_jasGammaThetaCreationEnergy (x : ℝ) (p : Nat.Primes) :
    Measurable (jasGammaThetaCreationEnergy x p) := by
  unfold jasGammaThetaCreationEnergy
  apply Measurable.ite
  · have hm : Measurable (fun P : JASGammaThetaSupport => p ∈ P) :=
      measurable_of_countable _
    simpa using (hm.comp measurable_fst) (measurableSet_singleton True)
  · exact measurable_const
  · exact ((measurable_of_countable
      (jasGammaBooleanInsertionGain x p)).comp measurable_fst).mul
        (Real.measurable_exp.comp measurable_snd)

private def postUnitaryLinearPMap {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H where
  domain := T.domain
  toFun := U.toLinearEquiv.toLinearMap.comp T.toFun

@[simp] private theorem postUnitaryLinearPMap_apply {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H)
    (f : (postUnitaryLinearPMap U T).domain) :
    postUnitaryLinearPMap U T f = U (T f) := rfl

private theorem LinearPMap.IsClosed.postUnitary {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
    (postUnitaryLinearPMap U T).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph : ((postUnitaryLinearPMap U T).graph : Set (H × H)) =
      (fun z : H × H => (z.1, U.symm z.2)) ⁻¹' (T.graph : Set (H × H)) := by
    ext z
    change z ∈ (postUnitaryLinearPMap U T).graph ↔
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

def jasGammaThetaCreation (x : ℝ) (p : Nat.Primes) :
    JASGammaThetaL2 →ₗ.[ℂ] JASGammaThetaL2 :=
  postUnitaryLinearPMap (jasGammaThetaToggleUnitary p)
    (maximalRealL2Mul _ (jasGammaThetaCreationEnergy x p))

theorem dense_jasGammaThetaCreation_domain (x : ℝ) (p : Nat.Primes) :
    Dense ((jasGammaThetaCreation x p).domain : Set JASGammaThetaL2) :=
  maximalRealL2Mul_dense _ (measurable_jasGammaThetaCreationEnergy x p)

theorem jasGammaThetaCreation_closed (x : ℝ) (p : Nat.Primes) :
    (jasGammaThetaCreation x p).IsClosed := by
  apply LinearPMap.IsClosed.postUnitary
  exact (maximalRealL2Mul_isSelfAdjoint _
    (measurable_jasGammaThetaCreationEnergy x p)).isClosed

def jasGammaSupportBasis (P : JASGammaThetaSupport) :
    Lp ℂ 2 (Measure.count : Measure JASGammaThetaSupport) :=
  indicatorConstLp 2 (measurableSet_singleton P) (by simp) 1

def jasGammaThetaPacket (P : JASGammaThetaSupport) (r : ℕ) : JASGammaThetaL2 :=
  l2SeparatedProduct (jasGammaSupportBasis P)
    (jointAncestryCompletedThetaGradeL2 r)

theorem jasGammaSupportBasis_ae (P : JASGammaThetaSupport) :
    (jasGammaSupportBasis P : JASGammaThetaSupport → ℂ) =ᵐ[Measure.count]
      Set.indicator ({P} : Set JASGammaThetaSupport) (fun _ => (1 : ℂ)) := by
  simpa [jasGammaSupportBasis] using
    (indicatorConstLp_coeFn (p := 2)
      (μ := (Measure.count : Measure JASGammaThetaSupport))
      (hs := measurableSet_singleton P) (hμs := by simp))

def jasGammaThetaPacketFun
    (P : JASGammaThetaSupport) (r : ℕ)
    (z : JASGammaThetaSupport × ℝ) : ℂ :=
  if z.1 = P then
    ((Real.exp ((r : ℝ) * z.2) * thetaCuspFullSource z.2 : ℝ) : ℂ)
  else 0

theorem jasGammaThetaPacket_ae (P : JASGammaThetaSupport) (r : ℕ) :
    (jasGammaThetaPacket P r : JASGammaThetaSupport × ℝ → ℂ) =ᵐ[
      (Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)]
      jasGammaThetaPacketFun P r := by
  filter_upwards [
    l2SeparatedProduct_ae (jasGammaSupportBasis P)
      (jointAncestryCompletedThetaGradeL2 r),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (jasGammaSupportBasis_ae P),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (jointAncestryCompletedThetaGradeL2_coeFn r)]
      with z hsep hbasis htheta
  change (l2SeparatedProduct (jasGammaSupportBasis P)
    (jointAncestryCompletedThetaGradeL2 r) :
      JASGammaThetaSupport × ℝ → ℂ) z = jasGammaThetaPacketFun P r z
  rw [hsep]
  simp only [l2SeparatedFun, Function.comp_apply] at hbasis htheta ⊢
  rw [hbasis, htheta]
  by_cases hz : z.1 = P
  · rcases z with ⟨Q, y⟩
    change Q = P at hz
    subst Q
    simp [jasGammaThetaPacketFun]
  · simp [jasGammaThetaPacketFun, Set.indicator, hz]

def jasGammaThetaEffectiveGain
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) : ℝ :=
  if p ∈ P then 0 else jasGammaBooleanInsertionGain x p P

private theorem jasGammaThetaEnergy_mul_packetFun
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ)
    (z : JASGammaThetaSupport × ℝ) :
    (jasGammaThetaCreationEnergy x p z : ℂ) * jasGammaThetaPacketFun P r z =
      (jasGammaThetaEffectiveGain x p P : ℂ) *
        jasGammaThetaPacketFun P (r + 1) z := by
  by_cases hz : z.1 = P
  · rcases z with ⟨Q, y⟩
    change Q = P at hz
    subst Q
    by_cases hp : p ∈ P
    · simp [jasGammaThetaCreationEnergy, jasGammaThetaPacketFun,
        jasGammaThetaEffectiveGain, hp]
    · simp only [jasGammaThetaCreationEnergy, jasGammaThetaPacketFun,
        jasGammaThetaEffectiveGain, hp, if_false, if_pos]
      norm_cast
      have hexp : Real.exp y * Real.exp ((r : ℝ) * y) =
          Real.exp (((r + 1 : ℕ) : ℝ) * y) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      calc
        jasGammaBooleanInsertionGain x p P * Real.exp y *
              (Real.exp ((r : ℝ) * y) * thetaCuspFullSource y) =
            jasGammaBooleanInsertionGain x p P *
              (Real.exp y * Real.exp ((r : ℝ) * y)) *
                thetaCuspFullSource y := by ring
        _ = jasGammaBooleanInsertionGain x p P *
              (Real.exp (((r + 1 : ℕ) : ℝ) * y) *
                thetaCuspFullSource y) := by rw [hexp]; ring
  · simp [jasGammaThetaPacketFun, hz]

theorem jasGammaThetaPacket_mem_creationDomain
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaPacket P r ∈ (jasGammaThetaCreation x p).domain := by
  change MemLp (fun z => (jasGammaThetaCreationEnergy x p z : ℂ) *
    (jasGammaThetaPacket P r : JASGammaThetaSupport × ℝ → ℂ) z) 2
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
  refine (memLp_congr_ae ?_).mpr
    (Lp.memLp ((jasGammaThetaEffectiveGain x p P : ℂ) •
      jasGammaThetaPacket P (r + 1)))
  filter_upwards [jasGammaThetaPacket_ae P r,
    jasGammaThetaPacket_ae P (r + 1),
    Lp.coeFn_smul (jasGammaThetaEffectiveGain x p P : ℂ)
      (jasGammaThetaPacket P (r + 1))] with z hr hnext hsmul
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hr, hsmul, hnext]
  exact jasGammaThetaEnergy_mul_packetFun x p P r z

def jasGammaThetaPacketMulDomain
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    (maximalRealL2Mul
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
      (jasGammaThetaCreationEnergy x p)).domain :=
  ⟨jasGammaThetaPacket P r, by
    exact jasGammaThetaPacket_mem_creationDomain x p P r⟩

def jasGammaThetaPacketDomain
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    (jasGammaThetaCreation x p).domain :=
  jasGammaThetaPacketMulDomain x p P r

theorem maximalRealL2Mul_jasGammaThetaPacket
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    maximalRealL2Mul
        ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
        (jasGammaThetaCreationEnergy x p)
        (jasGammaThetaPacketMulDomain x p P r) =
      (jasGammaThetaEffectiveGain x p P : ℂ) •
        jasGammaThetaPacket P (r + 1) := by
  apply Lp.ext
  filter_upwards [
    maximalRealL2Mul_apply_ae
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
      (jasGammaThetaCreationEnergy x p)
      (jasGammaThetaPacketMulDomain x p P r),
    jasGammaThetaPacket_ae P r,
    jasGammaThetaPacket_ae P (r + 1),
    Lp.coeFn_smul (jasGammaThetaEffectiveGain x p P : ℂ)
      (jasGammaThetaPacket P (r + 1))] with z hmul hr hnext hsmul
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hmul, hsmul]
  change (jasGammaThetaCreationEnergy x p z : ℂ) *
      (jasGammaThetaPacket P r : JASGammaThetaSupport × ℝ → ℂ) z =
    (jasGammaThetaEffectiveGain x p P : ℂ) *
      (jasGammaThetaPacket P (r + 1) : JASGammaThetaSupport × ℝ → ℂ) z
  rw [hr, hnext]
  exact jasGammaThetaEnergy_mul_packetFun x p P r z

theorem jasGammaThetaToggleUnitary_packet
    (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaToggleUnitary p (jasGammaThetaPacket P r) =
      jasGammaThetaPacket (jasGammaSupportToggle p P) r := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (jasGammaThetaPacket P r)
      (jasGammaThetaToggle_measurePreserving p),
    (jasGammaThetaPacket_ae P r).comp_tendsto
      (jasGammaThetaToggle_measurePreserving p).quasiMeasurePreserving.tendsto_ae,
    jasGammaThetaPacket_ae (jasGammaSupportToggle p P) r]
      with z hcomp hsource htarget
  change (Lp.compMeasurePreserving (jasGammaThetaToggleMeasurableEquiv p)
      (jasGammaThetaToggle_measurePreserving p) (jasGammaThetaPacket P r) :
        JASGammaThetaSupport × ℝ → ℂ) z =
    (jasGammaThetaPacket (jasGammaSupportToggle p P) r :
      JASGammaThetaSupport × ℝ → ℂ) z
  rw [hcomp, hsource, htarget]
  have heq : jasGammaSupportToggle p z.1 = P ↔
      z.1 = jasGammaSupportToggle p P := by
    simpa using
      ((jasGammaSupportToggle p).apply_eq_iff_eq_symm_apply)
  change jasGammaThetaPacketFun P r
      (jasGammaSupportToggle p z.1, z.2) =
    jasGammaThetaPacketFun (jasGammaSupportToggle p P) r z
  simp only [jasGammaThetaPacketFun, heq]

theorem jasGammaThetaCreation_packet
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) =
      (jasGammaThetaEffectiveGain x p P : ℂ) •
        jasGammaThetaPacket (jasGammaSupportToggle p P) (r + 1) := by
  change jasGammaThetaToggleUnitary p
      (maximalRealL2Mul
        ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
        (jasGammaThetaCreationEnergy x p)
        (jasGammaThetaPacketMulDomain x p P r)) = _
  rw [maximalRealL2Mul_jasGammaThetaPacket, map_smul,
    jasGammaThetaToggleUnitary_packet]

theorem jasGammaThetaCreation_packet_of_mem
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ)
    (hp : p ∈ P) :
    jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) = 0 := by
  rw [jasGammaThetaCreation_packet]
  simp [jasGammaThetaEffectiveGain, hp]

theorem jasGammaThetaCreation_packet_of_not_mem
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ)
    (hp : p ∉ P) :
    jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) =
      (jasGammaBooleanInsertionGain x p P : ℂ) •
        jasGammaThetaPacket (insert p P) (r + 1) := by
  rw [jasGammaThetaCreation_packet]
  simp [jasGammaThetaEffectiveGain, jasGammaSupportToggle_apply, hp]

theorem jasGammaThetaCreation_packet_eq_gamma
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ)
    (hx : 0 < x) (hP : P.Nonempty) (hp : p ∉ P) :
    jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) =
      (gammaSewnSynchronizedLcmInsertionGain x p P : ℂ) •
        jasGammaThetaPacket (insert p P) (r + 1) := by
  rw [jasGammaThetaCreation_packet_of_not_mem x p P r hp,
    jasGammaBooleanInsertionGain_eq_gamma hx hP hp]

theorem jasGammaThetaCreation_supportCard_grade
    (x : ℝ) (p : Nat.Primes) (P : JASGammaThetaSupport) (hp : p ∉ P) :
    jasGammaThetaCreation x p
        (jasGammaThetaPacketDomain x p P P.card) =
      (jasGammaBooleanInsertionGain x p P : ℂ) •
        jasGammaThetaPacket (insert p P) (insert p P).card := by
  rw [jasGammaThetaCreation_packet_of_not_mem x p P P.card hp]
  congr 2
  simp [hp]

theorem jasGammaSupportToggle_comm
    (p q : Nat.Primes) (P : JASGammaThetaSupport) :
    jasGammaSupportToggle q (jasGammaSupportToggle p P) =
      jasGammaSupportToggle p (jasGammaSupportToggle q P) := by
  by_cases hpq : p = q
  · subst q
    rfl
  · ext a
    by_cases hp : p ∈ P <;> by_cases hq : q ∈ P <;>
      simp [jasGammaSupportToggle_apply, hp, hq, hpq,
        Ne.symm hpq] <;> aesop

theorem jasGammaThetaEffectiveGain_cocycle
    {x : ℝ} (hx : 0 < x) (p q : Nat.Primes) (P : JASGammaThetaSupport) :
    jasGammaThetaEffectiveGain x p P *
        jasGammaThetaEffectiveGain x q (jasGammaSupportToggle p P) =
      jasGammaThetaEffectiveGain x q P *
        jasGammaThetaEffectiveGain x p (jasGammaSupportToggle q P) := by
  by_cases hpq : p = q
  · subst q
    rfl
  · by_cases hp : p ∈ P <;> by_cases hq : q ∈ P
    · simp [jasGammaThetaEffectiveGain, jasGammaSupportToggle_apply,
        hp, hq, hpq, Ne.symm hpq]
    · simp [jasGammaThetaEffectiveGain, jasGammaSupportToggle_apply,
        hp, hq, hpq, Ne.symm hpq]
    · simp [jasGammaThetaEffectiveGain, jasGammaSupportToggle_apply,
        hp, hq, hpq, Ne.symm hpq]
    · simpa [jasGammaThetaEffectiveGain, jasGammaSupportToggle_apply,
        hp, hq, hpq, Ne.symm hpq] using
          jasGammaBooleanInsertionGain_cocycle hx p q P

def jasGammaThetaSecondPathDomain
    (x : ℝ) (p q : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    (jasGammaThetaCreation x q).domain :=
  (jasGammaThetaEffectiveGain x p P : ℂ) •
    jasGammaThetaPacketDomain x q (jasGammaSupportToggle p P) (r + 1)

theorem jasGammaThetaSecondPathDomain_value
    (x : ℝ) (p q : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    (jasGammaThetaSecondPathDomain x p q P r : JASGammaThetaL2) =
      jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) := by
  rw [jasGammaThetaCreation_packet]
  rfl

theorem jasGammaThetaCreation_twoStepPath
    (x : ℝ) (p q : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaCreation x q
        (jasGammaThetaSecondPathDomain x p q P r) =
      ((jasGammaThetaEffectiveGain x p P *
          jasGammaThetaEffectiveGain x q (jasGammaSupportToggle p P) : ℝ) : ℂ) •
        jasGammaThetaPacket
          (jasGammaSupportToggle q (jasGammaSupportToggle p P)) (r + 2) := by
  change jasGammaThetaCreation x q
      ((jasGammaThetaEffectiveGain x p P : ℂ) •
        jasGammaThetaPacketDomain x q (jasGammaSupportToggle p P) (r + 1)) = _
  change (jasGammaThetaCreation x q).toFun
      ((jasGammaThetaEffectiveGain x p P : ℂ) •
        jasGammaThetaPacketDomain x q (jasGammaSupportToggle p P) (r + 1)) = _
  have hstep := jasGammaThetaCreation_packet x q
    (jasGammaSupportToggle p P) (r + 1)
  change (jasGammaThetaCreation x q).toFun
      (jasGammaThetaPacketDomain x q (jasGammaSupportToggle p P) (r + 1)) = _
    at hstep
  rw [(jasGammaThetaCreation x q).toFun.map_smul, hstep]
  push_cast
  rw [smul_smul]

/-- Closed-operator flatness: the two actual Gamma--theta creation paths agree on every packet. -/
theorem jasGammaThetaCreation_twoPrime_operator_paths
    {x : ℝ} (hx : 0 < x) (p q : Nat.Primes)
    (P : JASGammaThetaSupport) (r : ℕ) :
    jasGammaThetaCreation x q
        (jasGammaThetaSecondPathDomain x p q P r) =
      jasGammaThetaCreation x p
        (jasGammaThetaSecondPathDomain x q p P r) := by
  rw [jasGammaThetaCreation_twoStepPath,
    jasGammaThetaCreation_twoStepPath,
    jasGammaThetaEffectiveGain_cocycle hx]
  rw [jasGammaSupportToggle_comm]

/-- Closed theorem package, with no external premise: every Gamma--theta creator is densely
defined and closed, has exact packet action, and all two-prime packet paths commute. -/
theorem jasGammaThetaClosedCreation_package :
    ∀ (x : ℝ) (p q : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ),
      Dense ((jasGammaThetaCreation x p).domain : Set JASGammaThetaL2) ∧
      (jasGammaThetaCreation x p).IsClosed ∧
      jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) =
        (jasGammaThetaEffectiveGain x p P : ℂ) •
          jasGammaThetaPacket (jasGammaSupportToggle p P) (r + 1) ∧
      (0 < x →
        jasGammaThetaCreation x q
            (jasGammaThetaSecondPathDomain x p q P r) =
          jasGammaThetaCreation x p
            (jasGammaThetaSecondPathDomain x q p P r)) := by
  intro x p q P r
  exact ⟨dense_jasGammaThetaCreation_domain x p,
    jasGammaThetaCreation_closed x p,
    jasGammaThetaCreation_packet x p P r,
    fun hx => jasGammaThetaCreation_twoPrime_operator_paths hx p q P r⟩

end

end RHTower
