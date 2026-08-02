import GaloisForLFunctions.RHTower.DeningerCalderonWittDerivedCupSource

/-!
# Algebraic Calderón--Witt source before completion

The affine-gauge Haar `L²` packet is an analytic envelope, not the
arithmetic source.  The source packet is the directed union of the
images of all finite rational-Witt stages.  Strict gauge-transition
naturality makes those images a directed family, so every algebraic
packet already occurs at one finite stage.

The first-suspension center is restricted to the image of this
algebraic packet.  The Calderón cross-effect and its alternating
polarization land in that center.  Thus this module constructs the
actual two-step source before Hilbert completion:

`A_p^1 = Q_p ⊕ P_p^alg`, `A_p^2 = T_p(P_p^alg)`.

The local and all-prime vector-valued cup radicals are zero.  No zeta
zero, divisor sector, positivity premise, or completion enters.
-/

namespace RHTower

open scoped DirectSum

noncomputable section

/-! ## Directed algebraic packet -/

/-- Image of one finite gauge-corrected rational-Witt stage in affine
Haar `L²`. -/
def deningerPrimeFinitePacketGaugeStageRange
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Submodule ℂ (DeningerPrimeFinitePacketGaugeComplexHaarL2 p) :=
  LinearMap.range
    (deningerPrimeFinitePacketGaugeStageComplexHaarL2LM p s)

/-- Stage ranges increase under gauge-corrected refinement. -/
theorem deningerPrimeFinitePacketGaugeStageRange_mono
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    deningerPrimeFinitePacketGaugeStageRange p s ≤
      deningerPrimeFinitePacketGaugeStageRange p t := by
  rintro _ ⟨F, rfl⟩
  refine
    ⟨deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F, ?_⟩
  exact
    deningerPrimeFinitePacketGaugeStageComplexHaarL2_transition
      p hst F

/-- Finite rational-Witt stage ranges form a directed family. -/
theorem deningerPrimeFinitePacketGaugeStageRange_directed
    (p : Nat.Primes) :
    Directed (· ≤ ·)
      (deningerPrimeFinitePacketGaugeStageRange p) := by
  intro s t
  obtain ⟨u, hsu, htu⟩ := exists_ge_ge s t
  exact
    ⟨u,
      deningerPrimeFinitePacketGaugeStageRange_mono p hsu,
      deningerPrimeFinitePacketGaugeStageRange_mono p htu⟩

/-- Algebraic affine-gauge packet: directed union of all finite
rational-Witt stage images inside the analytic Haar envelope. -/
def deningerPrimeFinitePacketGaugeAlgebraicSubmodule
    (p : Nat.Primes) :
    Submodule ℂ (DeningerPrimeFinitePacketGaugeComplexHaarL2 p) :=
  ⨆ s : DeningerFiniteFrobeniusStage (p : ℕ),
    deningerPrimeFinitePacketGaugeStageRange p s

/-- The actual local rational-Witt source packet before completion. -/
abbrev DeningerPrimeFinitePacketGaugeAlgebraic
    (p : Nat.Primes) : Type :=
  deningerPrimeFinitePacketGaugeAlgebraicSubmodule p

/-- Every algebraic packet occurs at one finite rational-Witt stage.
This is stronger than being a finite linear combination of stages. -/
theorem deningerPrimeFinitePacketGaugeAlgebraic_exists_stage
    (p : Nat.Primes)
    (a : DeningerPrimeFinitePacketGaugeAlgebraic p) :
    ∃ s : DeningerFiniteFrobeniusStage (p : ℕ),
      ∃ F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ,
        deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F =
          (a :
            DeningerPrimeFinitePacketGaugeComplexHaarL2 p) := by
  have ha :
      (a : DeningerPrimeFinitePacketGaugeComplexHaarL2 p) ∈
        ⨆ s : DeningerFiniteFrobeniusStage (p : ℕ),
          deningerPrimeFinitePacketGaugeStageRange p s :=
    a.property
  rw [Submodule.mem_iSup_of_directed
    (deningerPrimeFinitePacketGaugeStageRange p)
    (deningerPrimeFinitePacketGaugeStageRange_directed p)] at ha
  obtain ⟨s, F, hF⟩ := ha
  exact ⟨s, F, hF⟩

/-- Canonical finite-stage map into the algebraic packet. -/
def deningerPrimeFinitePacketGaugeStageToAlgebraic
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    (DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) →ₗ[ℂ]
      DeningerPrimeFinitePacketGaugeAlgebraic p :=
  (deningerPrimeFinitePacketGaugeStageComplexHaarL2LM p s).codRestrict
    (deningerPrimeFinitePacketGaugeAlgebraicSubmodule p)
    (fun F =>
      Submodule.mem_iSup_of_mem s
        ⟨F, rfl⟩)

@[simp]
theorem deningerPrimeFinitePacketGaugeStageToAlgebraic_coe
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    (deningerPrimeFinitePacketGaugeStageToAlgebraic p s F :
        DeningerPrimeFinitePacketGaugeComplexHaarL2 p) =
      deningerPrimeFinitePacketGaugeStageComplexHaarL2 p s F :=
  rfl

/-- Each finite stage embeds faithfully in the algebraic source. -/
theorem deningerPrimeFinitePacketGaugeStageToAlgebraic_injective
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Injective
      (deningerPrimeFinitePacketGaugeStageToAlgebraic p s) := by
  intro F G hFG
  apply deningerPrimeFinitePacketGaugeStageComplexHaarL2_injective p s
  exact congrArg Subtype.val hFG

/-- Finite-stage maps form a strict cocone over gauge refinement. -/
theorem deningerPrimeFinitePacketGaugeStageToAlgebraic_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    deningerPrimeFinitePacketGaugeStageToAlgebraic p t
        (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst F) =
      deningerPrimeFinitePacketGaugeStageToAlgebraic p s F := by
  apply Subtype.ext
  exact
    deningerPrimeFinitePacketGaugeStageComplexHaarL2_transition
      p hst F

/-! ## Algebraic first-suspension center and cup -/

/-- First suspension as a linear map, forgetting only continuity. -/
def deningerPrimeFinitePacketGaugeSuspensionFirstModeLM
    (p : Nat.Primes) :
    DeningerPrimeFinitePacketGaugeComplexHaarL2 p →ₗ[ℂ]
      DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p :=
  (deningerPrimeFinitePacketGaugeSuspensionFirstMode p).toLinearMap

/-- Algebraic degree-two center: first-suspension image of the
algebraic packet, before taking its closure. -/
def deningerPrimeFinitePacketGaugeAlgebraicSuspensionSubmodule
    (p : Nat.Primes) :
    Submodule ℂ
      (DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p) :=
  (deningerPrimeFinitePacketGaugeAlgebraicSubmodule p).map
    (deningerPrimeFinitePacketGaugeSuspensionFirstModeLM p)

/-- Actual local degree-two center before completion. -/
abbrev DeningerPrimeFinitePacketGaugeAlgebraicSuspension
    (p : Nat.Primes) : Type :=
  deningerPrimeFinitePacketGaugeAlgebraicSuspensionSubmodule p

/-- Local algebraic degree one. -/
abbrev DeningerCalderonWittAlgebraicDegreeOne
    (p : Nat.Primes) : Type :=
  DeningerMeyerPrimeCalderonQuotient p ×
    DeningerPrimeFinitePacketGaugeAlgebraic p

/-- Local algebraic degree two. -/
abbrev DeningerCalderonWittAlgebraicDegreeTwo
    (p : Nat.Primes) : Type :=
  DeningerPrimeFinitePacketGaugeAlgebraicSuspension p

/-- The source cross-effect restricted to the algebraic packet and
its algebraic suspension center. -/
def deningerMeyerCalderonWittAlgebraicCrossEffect
    (p : Nat.Primes) :
    DeningerMeyerPrimeCalderonQuotient p →ₗ[ℂ]
      DeningerPrimeFinitePacketGaugeAlgebraic p →ₗ[ℂ]
        DeningerPrimeFinitePacketGaugeAlgebraicSuspension p where
  toFun q :=
    { toFun := fun a =>
        ⟨deningerMeyerCalderonGaugePacketCrossEffect p q a.1, by
          change
            deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ) q •
                (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
                  deningerPrimeFinitePacketGaugeSuspensionFirstMode p a.1) ∈
              deningerPrimeFinitePacketGaugeAlgebraicSuspensionSubmodule p
          apply Submodule.smul_mem
          apply Submodule.smul_mem
          exact ⟨a.1, a.2, rfl⟩⟩
      map_add' a b := by
        apply Subtype.ext
        exact map_add
          (deningerMeyerCalderonGaugePacketCrossEffect p q) a.1 b.1
      map_smul' c a := by
        apply Subtype.ext
        exact map_smul
          (deningerMeyerCalderonGaugePacketCrossEffect p q) c a.1 }
  map_add' q r := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change
      deningerMeyerCalderonGaugePacketCrossEffect p (q + r) a.1 =
        deningerMeyerCalderonGaugePacketCrossEffect p q a.1 +
          deningerMeyerCalderonGaugePacketCrossEffect p r a.1
    rw [map_add, LinearMap.add_apply]
  map_smul' c q := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change
      deningerMeyerCalderonGaugePacketCrossEffect p (c • q) a.1 =
        c • deningerMeyerCalderonGaugePacketCrossEffect p q a.1
    rw [map_smul, LinearMap.smul_apply]

@[simp]
theorem deningerMeyerCalderonWittAlgebraicCrossEffect_coe
    (p : Nat.Primes)
    (q : DeningerMeyerPrimeCalderonQuotient p)
    (a : DeningerPrimeFinitePacketGaugeAlgebraic p) :
    (deningerMeyerCalderonWittAlgebraicCrossEffect p q a :
        DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p) =
      deningerMeyerCalderonGaugePacketCrossEffect p q a.1 :=
  rfl

/-- Alternating local algebraic source cup. -/
def deningerCalderonWittAlgebraicCup
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
        DeningerCalderonWittAlgebraicDegreeTwo p :=
  deningerAlternatingCrossEffect
    (deningerMeyerCalderonWittAlgebraicCrossEffect p)

@[simp]
theorem deningerCalderonWittAlgebraicCup_coe
    (p : Nat.Primes)
    (x y : DeningerCalderonWittAlgebraicDegreeOne p) :
    (deningerCalderonWittAlgebraicCup p x y :
        DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p) =
      deningerCalderonWittCup p (x.1, x.2.1) (y.1, y.2.1) :=
  rfl

/-- Canonical algebraic unit packet from the smallest finite stage. -/
def deningerCalderonWittAlgebraicUnitPacket
    (p : Nat.Primes) :
    DeningerPrimeFinitePacketGaugeAlgebraic p :=
  deningerPrimeFinitePacketGaugeStageToAlgebraic p
    (deningerCalderonWittUnitStage p) (fun _ => 1)

@[simp]
theorem deningerCalderonWittAlgebraicUnitPacket_coe
    (p : Nat.Primes) :
    (deningerCalderonWittAlgebraicUnitPacket p :
        DeningerPrimeFinitePacketGaugeComplexHaarL2 p) =
      deningerCalderonWittUnitPacket p :=
  rfl

theorem deningerCalderonWittAlgebraicUnitPacket_ne_zero
    (p : Nat.Primes) :
    deningerCalderonWittAlgebraicUnitPacket p ≠ 0 := by
  intro hzero
  apply deningerCalderonWittUnitPacket_ne_zero p
  exact congrArg Subtype.val hzero

/-- The algebraic local cup retains every source direction. -/
theorem deningerCalderonWittAlgebraicCup_leftRadical_eq_zero
    (p : Nat.Primes)
    (x : DeningerCalderonWittAlgebraicDegreeOne p)
    (hx : ∀ y, deningerCalderonWittAlgebraicCup p x y = 0) :
    x = 0 := by
  apply Prod.ext
  · have hq := congrArg Subtype.val
      (hx ((0 : DeningerMeyerPrimeCalderonQuotient p),
        deningerCalderonWittAlgebraicUnitPacket p))
    apply
      (deningerMeyerCalderonGaugePacketCrossEffect_left_injective
        p (deningerCalderonWittUnitPacket_ne_zero p))
    simpa using hq
  · apply Subtype.ext
    have ha := congrArg Subtype.val
      (hx (deningerCalderonWittUnitDefect p,
        (0 : DeningerPrimeFinitePacketGaugeAlgebraic p)))
    have haNeg :
        -deningerMeyerCalderonGaugePacketCrossEffect p
            (deningerCalderonWittUnitDefect p) x.2.1 =
          0 := by
      simpa [deningerCalderonWittAlgebraicCup] using ha
    apply
      (deningerMeyerCalderonGaugePacketCrossEffect_unit_injective p)
    have ha' :
        deningerMeyerCalderonGaugePacketCrossEffect p
            (deningerCalderonWittUnitDefect p) x.2.1 =
          0 := by
      simpa using (neg_eq_zero.mp haNeg)
    simpa using ha'

/-- The local algebraic two-step source coefficient. -/
def deningerCalderonWittAlgebraicLocalCupSource
    (p : Nat.Primes) :
    DeningerTwoStepCupSource ℂ
      (DeningerCalderonWittAlgebraicDegreeOne p)
      (DeningerCalderonWittAlgebraicDegreeTwo p) where
  cup11 := deningerCalderonWittAlgebraicCup p
  cup11_skew := by
    intro x y
    change
      deningerMeyerCalderonWittAlgebraicCrossEffect p x.1 y.2 -
          deningerMeyerCalderonWittAlgebraicCrossEffect p y.1 x.2 =
        -(deningerMeyerCalderonWittAlgebraicCrossEffect p y.1 x.2 -
          deningerMeyerCalderonWittAlgebraicCrossEffect p x.1 y.2)
    module

/-! ## Finite-stage cocone -/

/-- A finite-stage degree-one source maps canonically into the
algebraic local source. -/
def deningerCalderonWittFiniteStageToAlgebraic
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerCalderonWittFiniteStageDegreeOne p s →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeOne p where
  toFun x :=
    (x.1, deningerPrimeFinitePacketGaugeStageToAlgebraic p s x.2)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact map_add
        (deningerPrimeFinitePacketGaugeStageToAlgebraic p s) x.2 y.2
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · exact map_smul
        (deningerPrimeFinitePacketGaugeStageToAlgebraic p s) c x.2

/-- Every finite-stage degree-one source embeds faithfully. -/
theorem deningerCalderonWittFiniteStageToAlgebraic_injective
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Injective
      (deningerCalderonWittFiniteStageToAlgebraic p s) := by
  intro x y hxy
  apply Prod.ext
  · have hfst := congrArg Prod.fst hxy
    change x.1 = y.1 at hfst
    exact hfst
  · apply deningerPrimeFinitePacketGaugeStageToAlgebraic_injective p s
    have hsnd := congrArg Prod.snd hxy
    change
      deningerPrimeFinitePacketGaugeStageToAlgebraic p s x.2 =
        deningerPrimeFinitePacketGaugeStageToAlgebraic p s y.2 at hsnd
    exact hsnd

/-- Finite-stage degree-one maps are a strict cocone over refinement. -/
theorem deningerCalderonWittFiniteStageToAlgebraic_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    (deningerCalderonWittFiniteStageToAlgebraic p t).comp
        (deningerCalderonWittFiniteStageRefinement p hst) =
      deningerCalderonWittFiniteStageToAlgebraic p s := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · exact
      deningerPrimeFinitePacketGaugeStageToAlgebraic_transition
        p hst x.2

/-- Every algebraic local degree-one class already comes from one
finite rational-Witt stage. -/
theorem deningerCalderonWittAlgebraicDegreeOne_exists_stage
    (p : Nat.Primes)
    (x : DeningerCalderonWittAlgebraicDegreeOne p) :
    ∃ s : DeningerFiniteFrobeniusStage (p : ℕ),
      ∃ y : DeningerCalderonWittFiniteStageDegreeOne p s,
        deningerCalderonWittFiniteStageToAlgebraic p s y = x := by
  obtain ⟨s, F, hF⟩ :=
    deningerPrimeFinitePacketGaugeAlgebraic_exists_stage p x.2
  refine ⟨s, (x.1, F), ?_⟩
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact hF

/-- The algebraic cup is literally the finite-stage cup after the
cocone map. -/
theorem deningerCalderonWittAlgebraicCup_finiteStage_coe
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (x y : DeningerCalderonWittFiniteStageDegreeOne p s) :
    (deningerCalderonWittAlgebraicCup p
        (deningerCalderonWittFiniteStageToAlgebraic p s x)
        (deningerCalderonWittFiniteStageToAlgebraic p s y) :
      DeningerPrimeFinitePacketGaugeSuspensionHaarL2 p) =
      deningerCalderonWittFiniteStageCup p s x y :=
  rfl

/-! ## All-prime algebraic source -/

/-- All-prime algebraic degree one, with finite prime support and
finite rational-Witt stage support at each prime. -/
abbrev DeningerCalderonWittAlgebraicGlobalDegreeOne : Type :=
  ⨁ p : Nat.Primes, DeningerCalderonWittAlgebraicDegreeOne p

/-- All-prime algebraic degree-two center. -/
abbrev DeningerCalderonWittAlgebraicGlobalDegreeTwo : Type :=
  ⨁ p : Nat.Primes, DeningerCalderonWittAlgebraicDegreeTwo p

/-- One prime contribution to the all-prime algebraic cup. -/
def deningerCalderonWittAlgebraicGlobalPrimeCup
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
        DeningerCalderonWittAlgebraicGlobalDegreeTwo where
  toFun x :=
    (DirectSum.lof ℂ Nat.Primes
      DeningerCalderonWittAlgebraicDegreeTwo p).comp
      ((deningerCalderonWittAlgebraicCup p x).comp
        (DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p))
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    simp

/-- Componentwise all-prime algebraic cup, constructed before any
topological completion. -/
def deningerCalderonWittAlgebraicGlobalCup :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
        DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
  DirectSum.toModule ℂ Nat.Primes
    (DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeTwo)
    deningerCalderonWittAlgebraicGlobalPrimeCup

@[simp]
theorem deningerCalderonWittAlgebraicGlobalCup_lof_left
    (p : Nat.Primes)
    (x : DeningerCalderonWittAlgebraicDegreeOne p)
    (y : DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    deningerCalderonWittAlgebraicGlobalCup
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p x) y =
      DirectSum.lof ℂ Nat.Primes
        DeningerCalderonWittAlgebraicDegreeTwo p
        (deningerCalderonWittAlgebraicCup p x
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p y)) := by
  rw [deningerCalderonWittAlgebraicGlobalCup,
    DirectSum.toModule_lof]
  rfl

@[simp]
theorem deningerCalderonWittAlgebraicGlobalCup_lof_same
    (p : Nat.Primes)
    (x y : DeningerCalderonWittAlgebraicDegreeOne p) :
    deningerCalderonWittAlgebraicGlobalCup
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p x)
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p y) =
      DirectSum.lof ℂ Nat.Primes
        DeningerCalderonWittAlgebraicDegreeTwo p
        (deningerCalderonWittAlgebraicCup p x y) := by
  rw [deningerCalderonWittAlgebraicGlobalCup_lof_left,
    DirectSum.component.lof_self]

@[simp]
theorem deningerCalderonWittAlgebraicGlobalCup_lof_ne
    {p q : Nat.Primes}
    (hpq : p ≠ q)
    (x : DeningerCalderonWittAlgebraicDegreeOne p)
    (y : DeningerCalderonWittAlgebraicDegreeOne q) :
    deningerCalderonWittAlgebraicGlobalCup
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p x)
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne q y) =
      0 := by
  rw [deningerCalderonWittAlgebraicGlobalCup_lof_left,
    DirectSum.component.of]
  simp [hpq.symm]

/-- All-prime output components are exactly local algebraic cups. -/
theorem deningerCalderonWittAlgebraicGlobalCup_component
    (p : Nat.Primes)
    (x y : DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    DirectSum.component ℂ Nat.Primes
        DeningerCalderonWittAlgebraicDegreeTwo p
        (deningerCalderonWittAlgebraicGlobalCup x y) =
      deningerCalderonWittAlgebraicCup p
        (DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p x)
        (DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p y) := by
  induction x using DirectSum.induction_on with
  | zero =>
      simp
  | of q x =>
      rw [← DirectSum.lof_eq_of
        (R := ℂ) (ι := Nat.Primes)
        (M := DeningerCalderonWittAlgebraicDegreeOne) q x]
      by_cases hqp : q = p
      · subst q
        simp
      · rw [deningerCalderonWittAlgebraicGlobalCup_lof_left,
          DirectSum.component.of, DirectSum.component.of]
        simp [hqp]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hz]

/-- The all-prime algebraic source cup is graded-skew. -/
theorem deningerCalderonWittAlgebraicGlobalCup_skew
    (x y : DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    deningerCalderonWittAlgebraicGlobalCup x y =
      -deningerCalderonWittAlgebraicGlobalCup y x := by
  apply DirectSum.ext_component ℂ
  intro p
  rw [map_neg,
    deningerCalderonWittAlgebraicGlobalCup_component,
    deningerCalderonWittAlgebraicGlobalCup_component]
  change
    deningerMeyerCalderonWittAlgebraicCrossEffect p
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p x).1
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p y).2 -
        deningerMeyerCalderonWittAlgebraicCrossEffect p
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p y).1
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p x).2 =
      -(deningerMeyerCalderonWittAlgebraicCrossEffect p
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p y).1
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p x).2 -
        deningerMeyerCalderonWittAlgebraicCrossEffect p
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p x).1
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeOne p y).2)
  module

/-- The all-prime algebraic two-step source coefficient. -/
def deningerCalderonWittAlgebraicGlobalCupSource :
    DeningerTwoStepCupSource ℂ
      DeningerCalderonWittAlgebraicGlobalDegreeOne
      DeningerCalderonWittAlgebraicGlobalDegreeTwo where
  cup11 := deningerCalderonWittAlgebraicGlobalCup
  cup11_skew := deningerCalderonWittAlgebraicGlobalCup_skew

/-- The all-prime algebraic vector-valued cup radical is zero. -/
theorem deningerCalderonWittAlgebraicGlobalCup_leftRadical_eq_zero
    (x : DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (hx : ∀ y, deningerCalderonWittAlgebraicGlobalCup x y = 0) :
    x = 0 := by
  apply DirectSum.ext_component ℂ
  intro p
  apply deningerCalderonWittAlgebraicCup_leftRadical_eq_zero p
  intro y
  have hglobal := congrArg
    (DirectSum.component ℂ Nat.Primes
      DeningerCalderonWittAlgebraicDegreeTwo p)
    (hx (DirectSum.lof ℂ Nat.Primes
      DeningerCalderonWittAlgebraicDegreeOne p y))
  rw [deningerCalderonWittAlgebraicGlobalCup_component] at hglobal
  simpa using hglobal

end

end RHTower
