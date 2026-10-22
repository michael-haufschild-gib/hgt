import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittCoherentCyclotomicDescent
import Mathlib.Data.ZMod.Aut

/-!
# Rational-Witt packet gauge descent

Independently chosen primitive roots force a unit gauge between the coherent
rational-Witt source transition and standard finite packet reduction.  This
file constructs that gauge, proves the exact evaluation duality, and replaces
the incompatible untwisted packet pullbacks by a strictly composable affine
packet functor.  Every finite packet function then has one
arithmetic-Frobenius-fixed rational-Witt witness whose images at all larger
stages realize the corrected pullbacks.

The exact obstruction theorem characterizes when the old untwisted pullback
remains valid: precisely when the packet function is invariant under the
forced gauge translation.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

theorem deningerPrimeFiniteWittStandardEmbeddedRoot_isPrimitive
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    IsPrimitiveRoot
      (deningerPrimeFiniteWittPrimitiveRootUnit p t ^
        (t.modulus / s.modulus))
      s.modulus := by
  apply IsPrimitiveRoot.pow (NeZero.pos t.modulus)
    (deningerPrimeFiniteWittPrimitiveRootUnit_spec p t)
  rw [mul_comm, Nat.mul_div_cancel' hst]

theorem deningerPrimeFiniteWitt_exists_cyclotomicGaugeExponent
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    ∃ i < s.modulus,
      i.Coprime s.modulus ∧
        (deningerPrimeFiniteWittPrimitiveRootUnit p t ^
          (t.modulus / s.modulus)) ^ i =
        deningerPrimeFiniteWittPrimitiveRootUnit p s := by
  exact
    (deningerPrimeFiniteWittStandardEmbeddedRoot_isPrimitive p hst).isPrimitiveRoot_iff'.mp
      (deningerPrimeFiniteWittPrimitiveRootUnit_spec p s)

noncomputable def deningerPrimeFiniteWittCyclotomicGaugeExponent
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) : ℕ :=
  Classical.choose (deningerPrimeFiniteWitt_exists_cyclotomicGaugeExponent p hst)

theorem deningerPrimeFiniteWittCyclotomicGaugeExponent_lt
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    deningerPrimeFiniteWittCyclotomicGaugeExponent p hst < s.modulus :=
  (Classical.choose_spec
    (deningerPrimeFiniteWitt_exists_cyclotomicGaugeExponent p hst)).1

theorem deningerPrimeFiniteWittCyclotomicGaugeExponent_coprime
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    (deningerPrimeFiniteWittCyclotomicGaugeExponent p hst).Coprime s.modulus :=
  (Classical.choose_spec
    (deningerPrimeFiniteWitt_exists_cyclotomicGaugeExponent p hst)).2.1

theorem deningerPrimeFiniteWittCyclotomicGaugeExponent_root
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    (deningerPrimeFiniteWittPrimitiveRootUnit p t ^
      (t.modulus / s.modulus)) ^
        deningerPrimeFiniteWittCyclotomicGaugeExponent p hst =
      deningerPrimeFiniteWittPrimitiveRootUnit p s :=
  (Classical.choose_spec
    (deningerPrimeFiniteWitt_exists_cyclotomicGaugeExponent p hst)).2.2

noncomputable def deningerPrimeFiniteWittCyclotomicGaugeUnit
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    (ZMod s.modulus)ˣ :=
  ZMod.unitOfCoprime
    (deningerPrimeFiniteWittCyclotomicGaugeExponent p hst)
    (deningerPrimeFiniteWittCyclotomicGaugeExponent_coprime p hst)

@[simp]
theorem deningerPrimeFiniteWittCyclotomicGaugeUnit_val
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    ((deningerPrimeFiniteWittCyclotomicGaugeUnit p hst : (ZMod s.modulus)ˣ) :
      ZMod s.modulus) =
      deningerPrimeFiniteWittCyclotomicGaugeExponent p hst := by
  simp [deningerPrimeFiniteWittCyclotomicGaugeUnit, ZMod.unitOfCoprime]

theorem deningerPrimeFiniteWittIndexTransition_one_eq_inflatedGauge
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    deningerPrimeFiniteWittIndexTransition p hst 1 =
      deningerFiniteFrobeniusStageIndexInflation hst
        (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst : ZMod s.modulus) := by
  have hmul :
      deningerPrimeFiniteWittRootEmbedding p t
          (Multiplicative.ofAdd
            (deningerPrimeFiniteWittIndexTransition p hst 1)) =
        deningerPrimeFiniteWittRootEmbedding p t
          (Multiplicative.ofAdd
            (deningerFiniteFrobeniusStageIndexInflation hst
              (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst :
                ZMod s.modulus))) := by
    calc
      deningerPrimeFiniteWittRootEmbedding p t
          (Multiplicative.ofAdd
            (deningerPrimeFiniteWittIndexTransition p hst 1)) =
          deningerPrimeFiniteWittRootEmbedding p s
            (Multiplicative.ofAdd 1) := by
        rw [deningerPrimeFiniteWittIndexTransition_apply,
          deningerPrimeFiniteWittRootTransition_spec]
      _ = deningerPrimeFiniteWittPrimitiveRootUnit p s := by
        simpa using deningerPrimeFiniteWittRootEmbedding_nat p s 1
      _ = (deningerPrimeFiniteWittPrimitiveRootUnit p t ^
          (t.modulus / s.modulus)) ^
          deningerPrimeFiniteWittCyclotomicGaugeExponent p hst :=
        (deningerPrimeFiniteWittCyclotomicGaugeExponent_root p hst).symm
      _ = deningerPrimeFiniteWittPrimitiveRootUnit p t ^
          ((t.modulus / s.modulus) *
            deningerPrimeFiniteWittCyclotomicGaugeExponent p hst) := by
        rw [pow_mul]
      _ = deningerPrimeFiniteWittRootEmbedding p t
          (Multiplicative.ofAdd
            (deningerFiniteFrobeniusStageIndexInflation hst
              (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst :
                ZMod s.modulus))) := by
        symm
        change deningerPrimeFiniteWittRootEmbedding p t
          (Multiplicative.ofAdd
            (((t.modulus / s.modulus) *
              (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst :
                ZMod s.modulus).val : ℕ) : ZMod t.modulus)) = _
        rw [deningerPrimeFiniteWittRootEmbedding_nat,
          deningerPrimeFiniteWittCyclotomicGaugeUnit_val, ZMod.val_natCast,
          Nat.mod_eq_of_lt (deningerPrimeFiniteWittCyclotomicGaugeExponent_lt p hst)]
  have hpre :=
    deningerPrimeFiniteWittRootEmbedding_injective p t hmul
  simpa [deningerPrimeFiniteWittIndexTransition] using
    congrArg Multiplicative.toAdd hpre

/-- Standard additive index inflation, now as a homomorphism rather than only
a pointwise formula. -/
noncomputable def deningerFiniteFrobeniusStageIndexInflationHom
    {p : ℕ}
    {s t : DeningerFiniteFrobeniusStage p}
    (hst : s ≤ t) :
    ZMod s.modulus →+ ZMod t.modulus where
  toFun := deningerFiniteFrobeniusStageIndexInflation hst
  map_zero' := by
    simp [deningerFiniteFrobeniusStageIndexInflation]
  map_add' a b := by
    apply ZMod.injective_stdAddChar
    have hab :=
      deningerFiniteUnitEvaluation_stageReduction hst (a + b)
        (1 : (ZMod t.modulus)ˣ)
    have ha :=
      deningerFiniteUnitEvaluation_stageReduction hst a
        (1 : (ZMod t.modulus)ˣ)
    have hb :=
      deningerFiniteUnitEvaluation_stageReduction hst b
        (1 : (ZMod t.modulus)ˣ)
    simp only [deningerFiniteUnitEvaluation, map_one, Units.val_one, mul_one]
      at hab ha hb
    calc
      ZMod.stdAddChar
          (deningerFiniteFrobeniusStageIndexInflation hst (a + b)) =
          ZMod.stdAddChar (a + b) := hab.symm
      _ = ZMod.stdAddChar a * ZMod.stdAddChar b :=
        (ZMod.stdAddChar (N := s.modulus)).map_add_eq_mul _ _
      _ = ZMod.stdAddChar
            (deningerFiniteFrobeniusStageIndexInflation hst a) *
          ZMod.stdAddChar
            (deningerFiniteFrobeniusStageIndexInflation hst b) := by
        rw [ha, hb]
      _ = ZMod.stdAddChar
          (deningerFiniteFrobeniusStageIndexInflation hst a +
            deningerFiniteFrobeniusStageIndexInflation hst b) := by
        exact
          ((ZMod.stdAddChar (N := t.modulus)).map_add_eq_mul _ _).symm

theorem deningerFiniteFrobeniusStageIndexInflationHom_injective
    {p : ℕ}
    {s t : DeningerFiniteFrobeniusStage p}
    (hst : s ≤ t) :
    Function.Injective (deningerFiniteFrobeniusStageIndexInflationHom hst) := by
  intro a b hab
  apply ZMod.injective_stdAddChar
  have ha :=
    deningerFiniteUnitEvaluation_stageReduction hst a
      (1 : (ZMod t.modulus)ˣ)
  have hb :=
    deningerFiniteUnitEvaluation_stageReduction hst b
      (1 : (ZMod t.modulus)ˣ)
  simp only [deningerFiniteUnitEvaluation, map_one, Units.val_one, mul_one] at ha hb
  change deningerFiniteFrobeniusStageIndexInflation hst a =
    deningerFiniteFrobeniusStageIndexInflation hst b at hab
  rw [ha, hb, hab]

noncomputable def deningerPrimeFiniteWittCyclotomicGaugeAddAut
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    AddAut (ZMod s.modulus) :=
  AddAut.mulLeft (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst)

@[simp]
theorem deningerPrimeFiniteWittCyclotomicGaugeAddAut_apply
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (j : ZMod s.modulus) :
    deningerPrimeFiniteWittCyclotomicGaugeAddAut p hst j =
      (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst : ZMod s.modulus) * j := by
  rfl

theorem deningerPrimeFiniteWittIndexTransition_eq_inflation_comp_gauge
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    deningerPrimeFiniteWittIndexTransition p hst =
      (deningerFiniteFrobeniusStageIndexInflationHom hst).comp
        (deningerPrimeFiniteWittCyclotomicGaugeAddAut p hst).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro j
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective j
  change deningerPrimeFiniteWittIndexTransition p hst
      ((z : ℤ) : ZMod s.modulus) =
    deningerFiniteFrobeniusStageIndexInflationHom hst
      (deningerPrimeFiniteWittCyclotomicGaugeAddAut p hst
        ((z : ℤ) : ZMod s.modulus))
  rw [← zsmul_one, map_zsmul, map_zsmul, map_zsmul]
  have hone :
      deningerPrimeFiniteWittIndexTransition p hst 1 =
        deningerFiniteFrobeniusStageIndexInflationHom hst
          (deningerPrimeFiniteWittCyclotomicGaugeAddAut p hst 1) := by
    simpa [deningerFiniteFrobeniusStageIndexInflationHom] using
      deningerPrimeFiniteWittIndexTransition_one_eq_inflatedGauge p hst
  exact congrArg (z • ·) hone

theorem deningerPrimeFiniteWittIndexTransition_apply_eq_inflatedGauge
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (j : ZMod s.modulus) :
    deningerPrimeFiniteWittIndexTransition p hst j =
      deningerFiniteFrobeniusStageIndexInflation hst
        ((deningerPrimeFiniteWittCyclotomicGaugeUnit p hst : ZMod s.modulus) * j) := by
  have h := DFunLike.congr_fun
    (deningerPrimeFiniteWittIndexTransition_eq_inflation_comp_gauge p hst) j
  simpa [deningerFiniteFrobeniusStageIndexInflationHom] using h

/-- Duality law: the rational-Witt transition evaluates against standard
packet reduction followed by the forced cyclotomic unit translation. -/
theorem deningerFiniteUnitEvaluation_wittIndexTransition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (j : ZMod s.modulus)
    (u : (ZMod t.modulus)ˣ) :
    deningerFiniteUnitEvaluation t.modulus
        (deningerPrimeFiniteWittIndexTransition p hst j) u =
      deningerFiniteUnitEvaluation s.modulus j
        (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst *
          deningerFiniteFrobeniusStageReduction hst u) := by
  rw [deningerPrimeFiniteWittIndexTransition_apply_eq_inflatedGauge]
  rw [← deningerFiniteUnitEvaluation_stageReduction hst
    ((deningerPrimeFiniteWittCyclotomicGaugeUnit p hst : ZMod s.modulus) * j) u]
  simp only [deningerFiniteUnitEvaluation, Units.val_mul]
  congr 1
  ac_rfl

/-- Evaluation naturality for every finite cyclotomic rational-Witt
element, with the forced packet gauge exposed. -/
theorem deningerFiniteCyclotomicWittEvaluation_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (u : (ZMod t.modulus)ˣ)
    (w : DeningerFiniteCyclotomicWittAlgebra s.modulus) :
    deningerFiniteCyclotomicWittEvaluation t.modulus u
        (deningerPrimeFiniteCyclotomicWittTransition p hst w) =
      deningerFiniteCyclotomicWittEvaluation s.modulus
        (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst *
          deningerFiniteFrobeniusStageReduction hst u) w := by
  induction w using AddMonoidAlgebra.induction with
  | zero =>
      simp
  | single_add j c w _hj _hc ih =>
      simp only [map_add, ih,
        deningerPrimeFiniteCyclotomicWittTransition_single,
        deningerFiniteCyclotomicWittEvaluation_single]
      rw [deningerFiniteUnitEvaluation_wittIndexTransition]

/-- Gauge-corrected contravariant transition on finite Frobenius packets. -/
noncomputable def deningerFiniteFrobeniusPacketGaugeTransition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    DeningerFiniteFrobeniusStageQuotient (p : ℕ) t →
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s :=
  fun q =>
    (QuotientGroup.mk (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst) :
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) *
      deningerFiniteFrobeniusStageQuotientMap hst q

@[simp]
theorem deningerFiniteFrobeniusPacketGaugeTransition_mk
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (u : (ZMod t.modulus)ˣ) :
    deningerFiniteFrobeniusPacketGaugeTransition p hst (QuotientGroup.mk u) =
      (QuotientGroup.mk
        (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst *
          deningerFiniteFrobeniusStageReduction hst u) :
        DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) := by
  simp [deningerFiniteFrobeniusPacketGaugeTransition,
    deningerFiniteFrobeniusStageQuotientMap]

theorem deningerFiniteFrobeniusPacketGaugeTransition_surjective
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    Function.Surjective (deningerFiniteFrobeniusPacketGaugeTransition p hst) := by
  intro q
  obtain ⟨r, hr⟩ :=
    deningerFiniteFrobeniusStageQuotientMap_surjective hst
      ((QuotientGroup.mk (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst) :
        DeningerFiniteFrobeniusStageQuotient (p : ℕ) s)⁻¹ * q)
  refine ⟨r, ?_⟩
  simp [deningerFiniteFrobeniusPacketGaugeTransition, hr]

noncomputable def deningerFiniteFrobeniusPacketGaugeFunctionPullback
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    (DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) →ₗ[ℂ]
      (DeningerFiniteFrobeniusStageQuotient (p : ℕ) t → ℂ) where
  toFun F := F ∘ deningerFiniteFrobeniusPacketGaugeTransition p hst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem deningerFiniteFrobeniusPacketGaugeFunctionPullback_injective
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    Function.Injective (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst) := by
  intro F G hFG
  funext q
  obtain ⟨r, rfl⟩ :=
    deningerFiniteFrobeniusPacketGaugeTransition_surjective p hst q
  exact congrFun hFG r

/-- A finite rational-Witt witness at one stage becomes exactly the
gauge-corrected packet pullback at every larger stage. -/
theorem deningerPrimeFiniteCyclotomicWittTransition_realizes_packetGaugePullback
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ)
    (w : DeningerFiniteCyclotomicWittAlgebra s.modulus)
    (hw : ∀ u : (ZMod s.modulus)ˣ,
      deningerFiniteCyclotomicWittEvaluation s.modulus u w =
        F (QuotientGroup.mk u))
    (u : (ZMod t.modulus)ˣ) :
    deningerFiniteCyclotomicWittEvaluation t.modulus u
        (deningerPrimeFiniteCyclotomicWittTransition p hst w) =
      deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F
        (QuotientGroup.mk u) := by
  rw [deningerFiniteCyclotomicWittEvaluation_transition, hw]
  rfl

/-- The gauge-corrected packet transitions compose strictly.  The proof is
forced by faithful evaluation of the strictly composable rational-Witt
source transitions, rather than by choosing a second gauge normalization. -/
theorem deningerFiniteFrobeniusPacketGaugeTransition_comp
    (p : Nat.Primes)
    {r s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hrs : r ≤ s)
    (hst : s ≤ t)
    (q : DeningerFiniteFrobeniusStageQuotient (p : ℕ) t) :
    deningerFiniteFrobeniusPacketGaugeTransition p hrs
        (deningerFiniteFrobeniusPacketGaugeTransition p hst q) =
      deningerFiniteFrobeniusPacketGaugeTransition p (hrs.trans hst) q := by
  classical
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  by_contra hne
  let F :
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) r → ℂ :=
    fun x =>
      if x =
        deningerFiniteFrobeniusPacketGaugeTransition p (hrs.trans hst)
          (QuotientGroup.mk u) then 1 else 0
  obtain ⟨w, _hwfixed, hw⟩ :=
    deningerFiniteCyclotomicWittEvaluation_surjective_fixed
      (p : ℕ) r.modulus r.coprime F
  have hw_s :
      ∀ v : (ZMod s.modulus)ˣ,
        deningerFiniteCyclotomicWittEvaluation s.modulus v
            (deningerPrimeFiniteCyclotomicWittTransition p hrs w) =
          deningerFiniteFrobeniusPacketGaugeFunctionPullback p hrs F
            (QuotientGroup.mk v) :=
    deningerPrimeFiniteCyclotomicWittTransition_realizes_packetGaugePullback
      p hrs F w hw
  have htwo :=
    deningerPrimeFiniteCyclotomicWittTransition_realizes_packetGaugePullback
      p hst (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hrs F)
      (deningerPrimeFiniteCyclotomicWittTransition p hrs w)
      hw_s u
  have hone :=
    deningerPrimeFiniteCyclotomicWittTransition_realizes_packetGaugePullback
      p (hrs.trans hst) F w hw u
  have hsource :=
    DFunLike.congr_fun
      (deningerPrimeFiniteCyclotomicWittTransition_comp p hrs hst) w
  have hsource' :
      deningerPrimeFiniteCyclotomicWittTransition p hst
          (deningerPrimeFiniteCyclotomicWittTransition p hrs w) =
        deningerPrimeFiniteCyclotomicWittTransition p
          (hrs.trans hst) w := by
    simpa only [AlgHom.comp_apply] using hsource
  have hvalues :
      deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst
          (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hrs F)
          (QuotientGroup.mk u) =
        deningerFiniteFrobeniusPacketGaugeFunctionPullback p (hrs.trans hst) F
          (QuotientGroup.mk u) := by
    calc
      deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst
          (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hrs F)
          (QuotientGroup.mk u) =
          deningerFiniteCyclotomicWittEvaluation t.modulus u
            (deningerPrimeFiniteCyclotomicWittTransition p hst
              (deningerPrimeFiniteCyclotomicWittTransition p hrs w)) :=
        htwo.symm
      _ = deningerFiniteCyclotomicWittEvaluation t.modulus u
            (deningerPrimeFiniteCyclotomicWittTransition p
              (hrs.trans hst) w) := by rw [hsource']
      _ = deningerFiniteFrobeniusPacketGaugeFunctionPullback p (hrs.trans hst) F
            (QuotientGroup.mk u) := hone
  change
    F (deningerFiniteFrobeniusPacketGaugeTransition p hrs
      (deningerFiniteFrobeniusPacketGaugeTransition p hst (QuotientGroup.mk u))) =
    F (deningerFiniteFrobeniusPacketGaugeTransition p (hrs.trans hst)
      (QuotientGroup.mk u)) at hvalues
  simp [F] at hvalues
  apply hne
  simpa only [deningerFiniteFrobeniusPacketGaugeTransition_mk, QuotientGroup.mk_mul] using
    hvalues

theorem deningerFiniteFrobeniusPacketGaugeFunctionPullback_comp
    (p : Nat.Primes)
    {r s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hrs : r ≤ s)
    (hst : s ≤ t) :
    (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst).comp
        (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hrs) =
      deningerFiniteFrobeniusPacketGaugeFunctionPullback p (hrs.trans hst) := by
  ext F q
  exact congrArg F (deningerFiniteFrobeniusPacketGaugeTransition_comp p hrs hst q)

theorem deningerFiniteFrobeniusPacketGaugeTransition_refl
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) :
    deningerFiniteFrobeniusPacketGaugeTransition p (le_refl s) q = q := by
  obtain ⟨r, rfl⟩ :=
    deningerFiniteFrobeniusPacketGaugeTransition_surjective p (le_refl s) q
  simpa using
    deningerFiniteFrobeniusPacketGaugeTransition_comp p (le_refl s) (le_refl s) r

theorem deningerFiniteFrobeniusPacketGaugeFunctionPullback_refl
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    deningerFiniteFrobeniusPacketGaugeFunctionPullback p (le_refl s) =
      LinearMap.id := by
  ext F q
  exact congrArg F (deningerFiniteFrobeniusPacketGaugeTransition_refl p s q)

/-- Exact boundary between the corrected source-compatible pullback and
the old untwisted packet pullback: they agree on precisely the functions
invariant under the forced finite gauge translation. -/
theorem deningerFiniteFrobeniusPacketGaugeFunctionPullback_eq_standard_iff
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F =
        deningerFiniteFrobeniusStageFunctionPullback hst F ↔
      ∀ q : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s,
        F ((QuotientGroup.mk (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst) :
            DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) * q) =
          F q := by
  constructor
  · intro heq q
    obtain ⟨r, hr⟩ :=
      deningerFiniteFrobeniusStageQuotientMap_surjective hst q
    have hpoint := congrFun heq r
    change
      F ((QuotientGroup.mk (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst) :
          DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) *
          deningerFiniteFrobeniusStageQuotientMap hst r) =
        F (deningerFiniteFrobeniusStageQuotientMap hst r) at hpoint
    simpa [hr] using hpoint
  · intro hinv
    funext q
    exact hinv (deningerFiniteFrobeniusStageQuotientMap hst q)

/-- Source-to-packet producer theorem: every finite packet function has one
arithmetic-Frobenius-fixed rational-Witt witness whose images at all larger
stages realize the strictly coherent gauge-corrected pullbacks. -/
theorem deningerPrimeComplexifiedRationalWitt_exists_coherentPacketGaugeDescent
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra s.modulus,
      deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w ∧
      (∀ u : (ZMod s.modulus)ˣ,
        deningerFiniteCyclotomicWittEvaluation s.modulus u w =
          F (QuotientGroup.mk u)) ∧
      ∀ (t : DeningerFiniteFrobeniusStage (p : ℕ))
        (hst : s ≤ t) (u : (ZMod t.modulus)ˣ),
        deningerFiniteCyclotomicWittEvaluation t.modulus u
            (deningerPrimeFiniteCyclotomicWittTransition p hst w) =
          deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F
            (QuotientGroup.mk u) := by
  obtain ⟨w, hwfixed, heval⟩ :=
    deningerPrimeComplexifiedRationalWitt_finiteRestriction_surjective
      p s F
  exact
    ⟨w, hwfixed, heval,
      fun _t hst u =>
        deningerPrimeFiniteCyclotomicWittTransition_realizes_packetGaugePullback
          p hst F w heval u⟩

end
end RHTower
