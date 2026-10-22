import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittGaugeFirstSuspensionDescent
import Mathlib.Algebra.DirectSum.Module

/-!
# Calderón--Witt derived cup source

The source-varying Calderón/rational-Witt first-suspension value is bilinear.
It therefore cannot be a differential on the square-zero direct sum.  This
module installs it in the source object where a bilinear operation belongs:
as the degree-one product of a two-step graded coefficient.

At a prime `p`, degree one is the direct sum of the Meyer--Poisson Calderón
defect line and the affine-gauge rational-Witt packet.  Degree two is the
first-suspension packet.  The cup is

`(q,a) ∪ (q',a') = χ(q,a') - χ(q',a)`.

The construction is alternating and has zero vector-valued radical.  It is
also strictly invariant under every gauge-corrected finite rational-Witt
refinement.  Thus the nonzero cross-effect is source multiplication before
completion or cohomology, not a packet selected after the fact.
-/

namespace RHTower

open scoped DirectSum TensorProduct

noncomputable section

/-- Abstract two-step graded source with only its load-bearing degree-one
cup retained. -/
structure DeningerTwoStepCupSource
    (R A1 A2 : Type*)
    [CommRing R]
    [AddCommGroup A1] [Module R A1]
    [AddCommGroup A2] [Module R A2] where
  cup11 : A1 →ₗ[R] A1 →ₗ[R] A2
  cup11_skew : ∀ x y, cup11 x y = -cup11 y x

namespace DeningerTwoStepCupSource

variable {R A1 A2 : Type*}
variable [CommRing R]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]

variable (A : DeningerTwoStepCupSource R A1 A2)

/-- Left vector-valued cup radical. -/
def leftRadical : Submodule R A1 :=
  LinearMap.ker A.cup11

end DeningerTwoStepCupSource

/-- Degree one of the local derived Calderón--Witt source. -/
abbrev DeningerCalderonWittDegreeOne (p : Nat.Primes) : Type :=
  DeningerMeyerPrimeCalderonQuotient p ×
    DeningerPrimeFinitePacketGaugeComplexHaarL2 p

/-- Degree two of the local derived Calderón--Witt source. -/
abbrev DeningerCalderonWittDegreeTwo (p : Nat.Primes) : Type :=
  DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p

/-- Alternating polarization of a bilinear source cross-effect. -/
def deningerAlternatingCrossEffect
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S) :
    (Q × P) →ₗ[R] (Q × P) →ₗ[R] S where
  toFun x :=
    { toFun := fun y => B x.1 y.2 - B y.1 x.2
      map_add' := by
        intro y z
        simp only [Prod.fst_add, Prod.snd_add, map_add,
          LinearMap.add_apply]
        abel
      map_smul' := by
        intro c y
        change
          B x.1 (c • y.2) - B (c • y.1) x.2 =
            c • (B x.1 y.2 - B y.1 x.2)
        simp only [map_smul, LinearMap.smul_apply, smul_sub] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change
      B (x.1 + y.1) z.2 - B z.1 (x.2 + y.2) =
        (B x.1 z.2 - B z.1 x.2) +
          (B y.1 z.2 - B z.1 y.2)
    rw [map_add, map_add, LinearMap.add_apply]
    abel
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change
      B (c • x.1) y.2 - B y.1 (c • x.2) =
        c • (B x.1 y.2 - B y.1 x.2)
    rw [map_smul, map_smul, LinearMap.smul_apply]
    module

@[simp]
theorem deningerAlternatingCrossEffect_apply
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S)
    (x y : Q × P) :
    deningerAlternatingCrossEffect B x y =
      B x.1 y.2 - B y.1 x.2 :=
  rfl

/-- Forced local degree-one cup: alternating polarization of the actual
Calderón/packet cross-effect. -/
def deningerCalderonWittCup (p : Nat.Primes) :
    DeningerCalderonWittDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittDegreeOne p →ₗ[ℂ]
        DeningerCalderonWittDegreeTwo p :=
  deningerAlternatingCrossEffect
    (deningerMeyerCalderonGaugePacketCrossEffect p)

@[simp]
theorem deningerCalderonWittCup_apply
    (p : Nat.Primes)
    (x y : DeningerCalderonWittDegreeOne p) :
    deningerCalderonWittCup p x y =
      deningerMeyerCalderonGaugePacketCrossEffect p x.1 y.2 -
        deningerMeyerCalderonGaugePacketCrossEffect p y.1 x.2 :=
  rfl

/-- The forced local cup is graded-skew. -/
theorem deningerCalderonWittCup_skew
    (p : Nat.Primes)
    (x y : DeningerCalderonWittDegreeOne p) :
    deningerCalderonWittCup p x y =
      -deningerCalderonWittCup p y x := by
  rw [deningerCalderonWittCup_apply,
    deningerCalderonWittCup_apply]
  module

/-- The local cup is alternating. -/
@[simp]
theorem deningerCalderonWittCup_self
    (p : Nat.Primes)
    (x : DeningerCalderonWittDegreeOne p) :
    deningerCalderonWittCup p x x = 0 := by
  rw [deningerCalderonWittCup_apply, sub_self]

/-- The local two-step graded coefficient object. -/
def deningerCalderonWittLocalCupSource (p : Nat.Primes) :
    DeningerTwoStepCupSource ℂ
      (DeningerCalderonWittDegreeOne p)
      (DeningerCalderonWittDegreeTwo p) where
  cup11 := deningerCalderonWittCup p
  cup11_skew := deningerCalderonWittCup_skew p

/-- Canonical nonzero Calderón defect coordinate. -/
def deningerCalderonWittUnitDefect (p : Nat.Primes) :
    DeningerMeyerPrimeCalderonQuotient p :=
  Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ))

@[simp]
theorem deningerMeyerPoissonCalderonQuotientEquiv_unitDefect
    (p : Nat.Primes) :
    deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ)
        (deningerCalderonWittUnitDefect p) =
      1 := by
  simp [deningerCalderonWittUnitDefect,
    deningerMeyerReflectedCollarDefect_apply]

/-- Smallest finite rational-Witt stage, used only as a source-defined
nonzero packet witness. -/
def deningerCalderonWittUnitStage (p : Nat.Primes) :
    DeningerFiniteFrobeniusStage (p : ℕ) :=
  ⟨1, one_ne_zero, Nat.coprime_one_right (p : ℕ)⟩

/-- Constant finite-stage packet on the affine gauge limit. -/
def deningerCalderonWittUnitPacket (p : Nat.Primes) :
    DeningerPrimeFinitePacketGaugeComplexHaarL2 p :=
  deningerPrimeFinitePacketGaugeStageComplexHaarL2 p
    (deningerCalderonWittUnitStage p) (fun _ => 1)

/-- The constant affine packet is nonzero. -/
theorem deningerCalderonWittUnitPacket_ne_zero
    (p : Nat.Primes) :
    deningerCalderonWittUnitPacket p ≠ 0 := by
  let s := deningerCalderonWittUnitStage p
  let F :
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ :=
    fun _ => 1
  have hF : F ≠ 0 := by
    intro hzero
    let q : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s :=
      Classical.choice inferInstance
    have hq := congrFun hzero q
    simp [F] at hq
  intro hpacket
  have hreg :=
    deningerMeyerCalderonGaugePacketTensorRegulator_unit_ne_zero
      p s hF
  apply hreg
  change
    deningerMeyerCalderonGaugePacketTensorRegulator p
      (deningerCalderonWittUnitDefect p ⊗ₜ[ℂ]
        deningerCalderonWittUnitPacket p) =
      0
  rw [hpacket]
  simp

/-- A nonzero affine packet makes the Calderón-defect leg injective. -/
theorem deningerMeyerCalderonGaugePacketCrossEffect_left_injective
    (p : Nat.Primes)
    {packet : DeningerPrimeFinitePacketGaugeComplexHaarL2 p}
    (hpacket : packet ≠ 0) :
    Function.Injective
      (fun q =>
        deningerMeyerCalderonGaugePacketCrossEffect p q packet) := by
  intro q r hqr
  apply (deningerMeyerPoissonCalderonQuotientEquiv
    (p : ℝ)).injective
  apply sub_eq_zero.mp
  have hzero :
      deningerMeyerCalderonGaugePacketCrossEffect p (q - r) packet =
        0 := by
    calc
      deningerMeyerCalderonGaugePacketCrossEffect p (q - r) packet =
          (deningerMeyerCalderonGaugePacketCrossEffect p q -
            deningerMeyerCalderonGaugePacketCrossEffect p r) packet := by
              rw [map_sub]
      _ = deningerMeyerCalderonGaugePacketCrossEffect p q packet -
          deningerMeyerCalderonGaugePacketCrossEffect p r packet := rfl
      _ = 0 := sub_eq_zero.mpr hqr
  change
    (deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ) (q - r)) •
      (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
        deningerPrimeFinitePacketGaugeSuspensionFirstMode p packet) =
      0 at hzero
  have hmode :
      (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
        deningerPrimeFinitePacketGaugeSuspensionFirstMode p packet) ≠
      0 := by
    apply smul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr
        (deningerPrimePolarizedHalfDensity_pos p).ne'
    · intro hfirst
      apply hpacket
      apply deningerPrimeFinitePacketGaugeSuspensionFirstMode_injective p
      calc
        deningerPrimeFinitePacketGaugeSuspensionFirstMode p packet = 0 :=
          hfirst
        _ = deningerPrimeFinitePacketGaugeSuspensionFirstMode p 0 := by
          rw [map_zero]
  simpa using (smul_eq_zero.mp hzero).resolve_right hmode

/-- The canonical unit defect makes the packet leg injective. -/
theorem deningerMeyerCalderonGaugePacketCrossEffect_unit_injective
    (p : Nat.Primes) :
    Function.Injective
      (deningerMeyerCalderonGaugePacketCrossEffect p
        (deningerCalderonWittUnitDefect p)) := by
  intro a b hab
  apply deningerPrimeFinitePacketGaugeSuspensionFirstMode_injective p
  apply sub_eq_zero.mp
  have hzero :
      deningerMeyerCalderonGaugePacketCrossEffect p
          (deningerCalderonWittUnitDefect p) (a - b) =
        0 := by
    rw [map_sub, hab, sub_self]
  change
    deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ)
        (deningerCalderonWittUnitDefect p) •
      (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
        deningerPrimeFinitePacketGaugeSuspensionFirstMode p (a - b)) =
      0 at hzero
  rw [deningerMeyerPoissonCalderonQuotientEquiv_unitDefect,
    one_smul] at hzero
  simpa [map_sub] using
    (smul_eq_zero.mp hzero).resolve_left
      (Complex.ofReal_ne_zero.mpr
        (deningerPrimePolarizedHalfDensity_pos p).ne')

/-- **Local source nondegeneracy.**  The vector-valued cup retains both
Calderón and rational-Witt directions before scalar trace. -/
theorem deningerCalderonWittCup_leftRadical_eq_zero
    (p : Nat.Primes)
    (x : DeningerCalderonWittDegreeOne p)
    (hx : ∀ y, deningerCalderonWittCup p x y = 0) :
    x = 0 := by
  apply Prod.ext
  · have hq := hx
      ((0 : DeningerMeyerPrimeCalderonQuotient p),
        deningerCalderonWittUnitPacket p)
    rw [deningerCalderonWittCup_apply] at hq
    simp only [map_zero, zero_apply, sub_zero] at hq
    exact
      (deningerMeyerCalderonGaugePacketCrossEffect_left_injective
        p (deningerCalderonWittUnitPacket_ne_zero p))
        (by simpa using hq)
  · have ha := hx
      (deningerCalderonWittUnitDefect p,
        (0 : DeningerPrimeFinitePacketGaugeComplexHaarL2 p))
    rw [deningerCalderonWittCup_apply] at ha
    simp only [map_zero, sub_zero, zero_sub] at ha
    have ha' :
        deningerMeyerCalderonGaugePacketCrossEffect p
            (deningerCalderonWittUnitDefect p) x.2 =
          0 := by
      exact neg_eq_zero.mp ha
    exact
      (deningerMeyerCalderonGaugePacketCrossEffect_unit_injective p)
        (by simpa using ha')

/-! ## Finite rational-Witt stages -/

/-- Degree one at a finite affine rational-Witt stage. -/
abbrev DeningerCalderonWittFiniteStageDegreeOne
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) : Type :=
  DeningerMeyerPrimeCalderonQuotient p ×
    (DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ)

/-- Linear inclusion of a finite rational-Witt packet stage into affine-limit
Haar `L²`. -/
def deningerPrimeFinitePacketGaugeStageComplexHaarL2LM
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    (DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) →ₗ[ℂ]
      DeningerPrimeFinitePacketGaugeComplexHaarL2 p where
  toFun := deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s
  map_add' F G := by
    change
      (ContinuousMap.toLp 2
        (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ)
          (deningerPrimeFinitePacketGaugeStageComplexPullback p s (F + G)) =
        (ContinuousMap.toLp 2
          (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ)
            (deningerPrimeFinitePacketGaugeStageComplexPullback p s F) +
          (ContinuousMap.toLp 2
            (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ)
              (deningerPrimeFinitePacketGaugeStageComplexPullback p s G)
    rw [show
      deningerPrimeFinitePacketGaugeStageComplexPullback p s (F + G) =
        deningerPrimeFinitePacketGaugeStageComplexPullback p s F +
          deningerPrimeFinitePacketGaugeStageComplexPullback p s G by
        ext a
        rfl,
      map_add]
  map_smul' c F := by
    change
      (ContinuousMap.toLp 2
        (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ)
          (deningerPrimeFinitePacketGaugeStageComplexPullback p s (c • F)) =
        c •
          (ContinuousMap.toLp 2
            (deningerPrimeFinitePacketGaugeHaarMeasure p) ℂ)
              (deningerPrimeFinitePacketGaugeStageComplexPullback p s F)
    rw [show
      deningerPrimeFinitePacketGaugeStageComplexPullback p s (c • F) =
        c • deningerPrimeFinitePacketGaugeStageComplexPullback p s F by
        ext a
        rfl,
      map_smul]

/-- Finite-stage restriction of the source cross-effect. -/
def deningerMeyerCalderonWittFiniteStageCrossEffect
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerMeyerPrimeCalderonQuotient p →ₗ[ℂ]
      (DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) →ₗ[ℂ]
        DeningerCalderonWittDegreeTwo p where
  toFun q :=
    (deningerMeyerCalderonGaugePacketCrossEffect p q).comp
      (deningerPrimeFinitePacketGaugeStageComplexHaarL2LM p s)
  map_add' q r := by
    ext F
    simp
  map_smul' c q := by
    ext F
    simp

/-- Finite-stage source cup, formed before the cofinal packet limit. -/
def deningerCalderonWittFiniteStageCup
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerCalderonWittFiniteStageDegreeOne p s →ₗ[ℂ]
      DeningerCalderonWittFiniteStageDegreeOne p s →ₗ[ℂ]
        DeningerCalderonWittDegreeTwo p :=
  deningerAlternatingCrossEffect
    (deningerMeyerCalderonWittFiniteStageCrossEffect p s)

@[simp]
theorem deningerCalderonWittFiniteStageCup_apply
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (x y : DeningerCalderonWittFiniteStageDegreeOne p s) :
    deningerCalderonWittFiniteStageCup p s x y =
      deningerMeyerCalderonGaugePacketCrossEffect p x.1
          (deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s y.2) -
      deningerMeyerCalderonGaugePacketCrossEffect p y.1
          (deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s x.2) :=
  rfl

/-- Every finite-stage source cup is graded-skew. -/
theorem deningerCalderonWittFiniteStageCup_skew
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (x y : DeningerCalderonWittFiniteStageDegreeOne p s) :
    deningerCalderonWittFiniteStageCup p s x y =
      -deningerCalderonWittFiniteStageCup p s y x := by
  rw [deningerCalderonWittFiniteStageCup_apply,
    deningerCalderonWittFiniteStageCup_apply]
  module

/-- Finite-stage two-step source coefficient. -/
def deningerCalderonWittFiniteStageCupSource
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerTwoStepCupSource ℂ
      (DeningerCalderonWittFiniteStageDegreeOne p s)
      (DeningerCalderonWittDegreeTwo p) where
  cup11 := deningerCalderonWittFiniteStageCup p s
  cup11_skew := deningerCalderonWittFiniteStageCup_skew p s

/-- Gauge refinement on the finite-stage degree-one source. -/
def deningerCalderonWittFiniteStageRefinement
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    DeningerCalderonWittFiniteStageDegreeOne p s →ₗ[ℂ]
      DeningerCalderonWittFiniteStageDegreeOne p t where
  toFun x :=
    (x.1, deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Gauge-corrected source refinement is faithful. -/
theorem deningerCalderonWittFiniteStageRefinement_injective
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    Function.Injective
      (deningerCalderonWittFiniteStageRefinement p hst) := by
  intro x y hxy
  apply Prod.ext
  · have hfst := congrArg Prod.fst hxy
    change x.1 = y.1 at hfst
    exact hfst
  · apply deningerFiniteFrobeniusPacketGaugeFunctionPullback_injective p hst
    have hsnd := congrArg Prod.snd hxy
    change
      deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst x.2 =
        deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst y.2 at hsnd
    exact hsnd

/-- Identity refinement is literally the identity source map. -/
theorem deningerCalderonWittFiniteStageRefinement_refl
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    deningerCalderonWittFiniteStageRefinement p (le_refl s) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · change
      deningerFiniteFrobeniusPacketGaugeFunctionPullback p (le_refl s) x.2 =
        x.2
    rw [deningerFiniteFrobeniusPacketGaugeFunctionPullback_refl]
    rfl

/-- Gauge-corrected source refinements compose strictly. -/
theorem deningerCalderonWittFiniteStageRefinement_comp
    (p : Nat.Primes)
    {r s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hrs : r ≤ s)
    (hst : s ≤ t) :
    (deningerCalderonWittFiniteStageRefinement p hst).comp
        (deningerCalderonWittFiniteStageRefinement p hrs) =
      deningerCalderonWittFiniteStageRefinement p (hrs.trans hst) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · exact DFunLike.congr_fun
      (deningerFiniteFrobeniusPacketGaugeFunctionPullback_comp p hrs hst)
      x.2

/-- **Cofinal source law.**  Gauge-corrected rational-Witt refinement
preserves the derived cup literally. -/
theorem deningerCalderonWittFiniteStageCup_refinement
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (x y : DeningerCalderonWittFiniteStageDegreeOne p s) :
    deningerCalderonWittFiniteStageCup p t
        (deningerCalderonWittFiniteStageRefinement p hst x)
        (deningerCalderonWittFiniteStageRefinement p hst y) =
      deningerCalderonWittFiniteStageCup p s x y := by
  rw [deningerCalderonWittFiniteStageCup_apply,
    deningerCalderonWittFiniteStageCup_apply]
  change
    deningerMeyerCalderonGaugePacketCrossEffect p x.1
        (deningerPrimeFinitePacketGaugeStageComplexHaarL2 p t
          (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst y.2)) -
      deningerMeyerCalderonGaugePacketCrossEffect p y.1
        (deningerPrimeFinitePacketGaugeStageComplexHaarL2 p t
          (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst x.2)) =
    _
  rw [deningerPrimeFinitePacketGaugeStageComplexHaarL2_transition p hst y.2,
    deningerPrimeFinitePacketGaugeStageComplexHaarL2_transition p hst x.2]

/-! ## All-prime algebraic source before completion -/

/-- Degree one of the all-prime source: algebraic finite-support sum, before
any Hilbert completion. -/
abbrev DeningerCalderonWittGlobalDegreeOne : Type :=
  ⨁ p : Nat.Primes, DeningerCalderonWittDegreeOne p

/-- Degree two of the all-prime source: algebraic finite-support sum of
first-suspension packets. -/
abbrev DeningerCalderonWittGlobalDegreeTwo : Type :=
  ⨁ p : Nat.Primes, DeningerCalderonWittDegreeTwo p

/-- Contribution of one prime to all-prime source multiplication. -/
def deningerCalderonWittGlobalPrimeCup
    (p : Nat.Primes) :
    DeningerCalderonWittDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittGlobalDegreeOne →ₗ[ℂ]
        DeningerCalderonWittGlobalDegreeTwo where
  toFun x :=
    (DirectSum.lof ℂ Nat.Primes DeningerCalderonWittDegreeTwo p).comp
      ((deningerCalderonWittCup p x).comp
        (DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittDegreeOne p))
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    simp

/-- Componentwise all-prime cup. Cross-prime products vanish, while every
local source product is retained in its prime summand. -/
def deningerCalderonWittGlobalCup :
    DeningerCalderonWittGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittGlobalDegreeOne →ₗ[ℂ]
        DeningerCalderonWittGlobalDegreeTwo :=
  DirectSum.toModule ℂ Nat.Primes
    (DeningerCalderonWittGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittGlobalDegreeTwo)
    deningerCalderonWittGlobalPrimeCup

/-- A prime generator multiplies only the matching component. -/
@[simp]
theorem deningerCalderonWittGlobalCup_lof_left
    (p : Nat.Primes)
    (x : DeningerCalderonWittDegreeOne p)
    (y : DeningerCalderonWittGlobalDegreeOne) :
    deningerCalderonWittGlobalCup
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittDegreeOne p x) y =
      DirectSum.lof ℂ Nat.Primes DeningerCalderonWittDegreeTwo p
        (deningerCalderonWittCup p x
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittDegreeOne p y)) := by
  rw [deningerCalderonWittGlobalCup, DirectSum.toModule_lof]
  rfl

/-- Same-prime generator products recover the local source cup exactly. -/
@[simp]
theorem deningerCalderonWittGlobalCup_lof_same
    (p : Nat.Primes)
    (x y : DeningerCalderonWittDegreeOne p) :
    deningerCalderonWittGlobalCup
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittDegreeOne p x)
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittDegreeOne p y) =
      DirectSum.lof ℂ Nat.Primes DeningerCalderonWittDegreeTwo p
        (deningerCalderonWittCup p x y) := by
  rw [deningerCalderonWittGlobalCup_lof_left,
    DirectSum.component.lof_self]

/-- Distinct-prime generator products vanish before completion. -/
@[simp]
theorem deningerCalderonWittGlobalCup_lof_ne
    {p q : Nat.Primes}
    (hpq : p ≠ q)
    (x : DeningerCalderonWittDegreeOne p)
    (y : DeningerCalderonWittDegreeOne q) :
    deningerCalderonWittGlobalCup
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittDegreeOne p x)
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittDegreeOne q y) =
      0 := by
  rw [deningerCalderonWittGlobalCup_lof_left,
    DirectSum.component.of]
  simp [hpq.symm]

/-- Every output component is exactly the cup of the corresponding input
components. -/
theorem deningerCalderonWittGlobalCup_component
    (p : Nat.Primes)
    (x y : DeningerCalderonWittGlobalDegreeOne) :
    DirectSum.component ℂ Nat.Primes
        DeningerCalderonWittDegreeTwo p
        (deningerCalderonWittGlobalCup x y) =
      deningerCalderonWittCup p
        (DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittDegreeOne p x)
        (DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittDegreeOne p y) := by
  induction x using DirectSum.induction_on with
  | zero =>
      simp
  | of q x =>
      rw [← DirectSum.lof_eq_of
        (R := ℂ) (ι := Nat.Primes)
        (M := DeningerCalderonWittDegreeOne) q x]
      by_cases hqp : q = p
      · subst q
        simp
      · rw [deningerCalderonWittGlobalCup_lof_left,
          DirectSum.component.of, DirectSum.component.of]
        simp [hqp]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hz]

/-- All-prime source multiplication remains graded-skew. -/
theorem deningerCalderonWittGlobalCup_skew
    (x y : DeningerCalderonWittGlobalDegreeOne) :
    deningerCalderonWittGlobalCup x y =
      -deningerCalderonWittGlobalCup y x := by
  apply DirectSum.ext_component ℂ
  intro p
  rw [map_neg, deningerCalderonWittGlobalCup_component,
    deningerCalderonWittGlobalCup_component,
    deningerCalderonWittCup_skew]

/-- The all-prime algebraic two-step source coefficient. -/
def deningerCalderonWittGlobalCupSource :
    DeningerTwoStepCupSource ℂ
      DeningerCalderonWittGlobalDegreeOne
      DeningerCalderonWittGlobalDegreeTwo where
  cup11 := deningerCalderonWittGlobalCup
  cup11_skew := deningerCalderonWittGlobalCup_skew

/-- **Global algebraic source nondegeneracy.** No nonzero finite-support
Calderón--Witt class lies in the vector-valued cup radical. -/
theorem deningerCalderonWittGlobalCup_leftRadical_eq_zero
    (x : DeningerCalderonWittGlobalDegreeOne)
    (hx : ∀ y, deningerCalderonWittGlobalCup x y = 0) :
    x = 0 := by
  apply DirectSum.ext_component ℂ
  intro p
  apply deningerCalderonWittCup_leftRadical_eq_zero p
  intro y
  have hglobal := congrArg
    (DirectSum.component ℂ Nat.Primes
      DeningerCalderonWittDegreeTwo p)
    (hx (DirectSum.lof ℂ Nat.Primes
      DeningerCalderonWittDegreeOne p y))
  rw [deningerCalderonWittGlobalCup_component] at hglobal
  simpa using hglobal

end

end RHTower
