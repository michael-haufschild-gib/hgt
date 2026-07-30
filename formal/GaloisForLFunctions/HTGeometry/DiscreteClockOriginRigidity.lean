import GaloisForLFunctions.HTGeometry.RelationalHistoryExternalTimeAmbiguityClassification

/-!
# Cardinality-free discrete clock-origin rigidity

On the full function space over an arbitrary clock group, covariance of every
labelled reading projector and every regular shift forces an arbitrary linear
operator to be one left translation times one global scalar.  No finiteness,
countability, basis expansion, topology, boundedness, or summability assumption
is used.
-/

namespace HTGeometry

noncomputable section

universe u v

variable {𝕜 : Type u} {clock : Type v}
  [Field 𝕜] [Group clock] [DecidableEq clock]

/-- Delta record at one reading of an arbitrary discrete clock. -/
def discreteClockKet (t : clock) : clock → 𝕜 :=
  fun i => if i = t then 1 else 0

/-- Coordinate projector onto one labelled clock reading. -/
def discreteClockBasisProjector (t : clock) :
    Module.End 𝕜 (clock → 𝕜) where
  toFun f i := if i = t then f i else 0
  map_add' f h := by
    ext i
    by_cases hi : i = t <;> simp [hi]
  map_smul' c f := by
    ext i
    by_cases hi : i = t <;> simp [hi]

/-- Left translation on records over an arbitrary clock group. -/
def discreteClockLeftTranslation (g : clock) :
    Module.End 𝕜 (clock → 𝕜) where
  toFun f row := f (g⁻¹ * row)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Group clock] in
/-- Every one-coordinate projection is a scalar multiple of its delta
record, even when the clock is infinite. -/
theorem discreteClockBasisProjector_apply
    (t : clock) (f : clock → 𝕜) :
    discreteClockBasisProjector t f =
      f t • discreteClockKet t := by
  ext i
  by_cases hi : i = t
  · subst i
    simp [discreteClockBasisProjector, discreteClockKet]
  · simp [discreteClockBasisProjector, discreteClockKet, hi]

/-- Translation carries a delta record to its translated reading. -/
theorem discreteClockLeftTranslation_ket
    (g t : clock) :
    discreteClockLeftTranslation (𝕜 := 𝕜) g
        (discreteClockKet t) =
      discreteClockKet (g * t) := by
  ext row
  simp only [discreteClockLeftTranslation, LinearMap.coe_mk,
    AddHom.coe_mk, discreteClockKet]
  by_cases hleft : g⁻¹ * row = t
  · have hright : row = g * t := by
      calc
        row = g * (g⁻¹ * row) := by group
        _ = g * t := by rw [hleft]
    simp [hright]
  · have hright : row ≠ g * t := by
      intro hrow
      apply hleft
      rw [hrow]
      group
    simp [hleft, hright]

/-- Translation transports each labelled reading projector. -/
theorem discreteClockLeftTranslation_projector_intertwines
    (g t : clock) (f : clock → 𝕜) :
    discreteClockLeftTranslation g
        (discreteClockBasisProjector t f) =
      discreteClockBasisProjector (g * t)
        (discreteClockLeftTranslation g f) := by
  ext row
  simp only [discreteClockLeftTranslation, LinearMap.coe_mk,
    AddHom.coe_mk, discreteClockBasisProjector]
  by_cases hleft : g⁻¹ * row = t
  · have hright : row = g * t := by
      calc
        row = g * (g⁻¹ * row) := by group
        _ = g * t := by rw [hleft]
    simp [hright]
  · have hright : row ≠ g * t := by
      intro hrow
      apply hleft
      rw [hrow]
      group
    simp [hleft, hright]

omit [DecidableEq clock] in
/-- Translation conjugates every regular shift by the same origin change. -/
theorem discreteClockLeftTranslation_shift_covariant
    (g h : clock) (f : clock → 𝕜) :
    discreteClockLeftTranslation g
        (discreteClockLeftTranslation h f) =
      discreteClockLeftTranslation (g * h * g⁻¹)
        (discreteClockLeftTranslation g f) := by
  ext row
  simp only [discreteClockLeftTranslation, LinearMap.coe_mk,
    AddHom.coe_mk]
  congr 1
  group

/-- Reading-projector covariance determines each output coordinate from
exactly one input coordinate. -/
theorem discreteClock_projector_intertwining_coordinate
    (g : clock) (T : Module.End 𝕜 (clock → 𝕜))
    (hprojector :
      ∀ t : clock, ∀ f : clock → 𝕜,
        T (discreteClockBasisProjector t f) =
          discreteClockBasisProjector (g * t) (T f))
    (t : clock) (f : clock → 𝕜) :
    T f (g * t) =
      f t * T (discreteClockKet t) (g * t) := by
  have hentry :=
    congr_fun (hprojector t f) (g * t)
  rw [discreteClockBasisProjector_apply,
    LinearMap.map_smul] at hentry
  simpa [discreteClockBasisProjector, mul_comm] using hentry.symm

/-- Shift covariance makes every coordinate weight equal. -/
theorem discreteClock_intertwining_weight_constant
    (g : clock) (T : Module.End 𝕜 (clock → 𝕜))
    (hshift :
      ∀ h : clock, ∀ f : clock → 𝕜,
        T (discreteClockLeftTranslation h f) =
          discreteClockLeftTranslation (g * h * g⁻¹) (T f))
    (t : clock) :
    T (discreteClockKet t) (g * t) =
      T (discreteClockKet 1) g := by
  have hcov :=
    congr_fun (hshift t (discreteClockKet (𝕜 := 𝕜) 1))
      (g * t)
  rw [discreteClockLeftTranslation_ket] at hcov
  have hindex :
      (g * t * g⁻¹)⁻¹ * (g * t) = g := by
    group
  simp only [mul_one] at hcov
  change
    T (discreteClockKet t) (g * t) =
      T (discreteClockKet 1) ((g * t * g⁻¹)⁻¹ * (g * t))
    at hcov
  rw [hindex] at hcov
  exact hcov

/-- **Cardinality-free clock-origin rigidity.**  For every group, finite or
infinite of any cardinality, the two covariance families force one origin
translation times one global scalar. -/
theorem eq_smul_discreteClockLeftTranslation_of_intertwines
    (g : clock) (T : Module.End 𝕜 (clock → 𝕜))
    (hprojector :
      ∀ t : clock, ∀ f : clock → 𝕜,
        T (discreteClockBasisProjector t f) =
          discreteClockBasisProjector (g * t) (T f))
    (hshift :
      ∀ h : clock, ∀ f : clock → 𝕜,
        T (discreteClockLeftTranslation h f) =
          discreteClockLeftTranslation (g * h * g⁻¹) (T f)) :
    ∃ c : 𝕜,
      T = c • discreteClockLeftTranslation g := by
  refine ⟨T (discreteClockKet 1) g, LinearMap.ext fun f => ?_⟩
  ext row
  let t : clock := g⁻¹ * row
  have hrow : g * t = row := by
    dsimp [t]
    group
  have hcoordinate :=
    discreteClock_projector_intertwining_coordinate
      g T hprojector t f
  have hconstant :=
    discreteClock_intertwining_weight_constant
      g T hshift t
  rw [hconstant, hrow] at hcoordinate
  simpa [discreteClockLeftTranslation, t, mul_comm] using hcoordinate

/-- Exact stabilizer iff for an arbitrary discrete clock group. -/
theorem discreteClockOriginStabilizer_iff
    (T : Module.End 𝕜 (clock → 𝕜)) :
    (∃ g : clock,
      (∀ t : clock, ∀ f : clock → 𝕜,
        T (discreteClockBasisProjector t f) =
          discreteClockBasisProjector (g * t) (T f)) ∧
      (∀ h : clock, ∀ f : clock → 𝕜,
        T (discreteClockLeftTranslation h f) =
          discreteClockLeftTranslation (g * h * g⁻¹) (T f))) ↔
    ∃ g : clock, ∃ c : 𝕜,
      T = c • discreteClockLeftTranslation g := by
  constructor
  · rintro ⟨g, hprojector, hshift⟩
    obtain ⟨c, hc⟩ :=
      eq_smul_discreteClockLeftTranslation_of_intertwines
        g T hprojector hshift
    exact ⟨g, c, hc⟩
  · rintro ⟨g, c, rfl⟩
    refine ⟨g, ?_, ?_⟩
    · intro t f
      simp only [LinearMap.smul_apply]
      rw [discreteClockLeftTranslation_projector_intertwines]
      exact
        (map_smul (discreteClockBasisProjector (𝕜 := 𝕜) (g * t))
          c (discreteClockLeftTranslation g f)).symm
    · intro h f
      simp only [LinearMap.smul_apply]
      rw [discreteClockLeftTranslation_shift_covariant]
      exact
        (map_smul
          (discreteClockLeftTranslation (𝕜 := 𝕜)
            (g * h * g⁻¹))
          c (discreteClockLeftTranslation g f)).symm

/-- Injectivity excludes the zero scalar from a classified clock
refactorization. -/
theorem discreteClockOriginStabilizer_scalar_ne_zero
    (T : Module.End 𝕜 (clock → 𝕜))
    (hT : Function.Injective T)
    (g : clock) (c : 𝕜)
    (hclass : T = c • discreteClockLeftTranslation g) :
    c ≠ 0 := by
  intro hc
  have hTzero : T = 0 := by
    rw [hclass, hc]
    simp
  have heq :
      T (discreteClockKet (𝕜 := 𝕜) 1) = T 0 := by
    rw [hTzero]
    rfl
  have hket := hT heq
  have hentry := congr_fun hket 1
  simp [discreteClockKet] at hentry

/-- **Invertible cardinality-free stabilizer.**  For every discrete clock
group of any cardinality, bijective physical refactorizations preserving all
labelled readings and regular shifts are exactly nonzero scalar multiples of
one clock-origin translation. -/
theorem invertibleDiscreteClockOriginStabilizer_iff
    (T : Module.End 𝕜 (clock → 𝕜))
    (hT : Function.Bijective T) :
    (∃ g : clock,
      (∀ t : clock, ∀ f : clock → 𝕜,
        T (discreteClockBasisProjector t f) =
          discreteClockBasisProjector (g * t) (T f)) ∧
      (∀ h : clock, ∀ f : clock → 𝕜,
        T (discreteClockLeftTranslation h f) =
          discreteClockLeftTranslation (g * h * g⁻¹) (T f))) ↔
    ∃ g : clock, ∃ c : 𝕜,
      c ≠ 0 ∧ T = c • discreteClockLeftTranslation g := by
  constructor
  · intro h
    obtain ⟨g, c, hc⟩ := (discreteClockOriginStabilizer_iff T).mp h
    exact
      ⟨g, c,
        discreteClockOriginStabilizer_scalar_ne_zero
          T hT.1 g c hc,
        hc⟩
  · rintro ⟨g, c, _, hc⟩
    exact (discreteClockOriginStabilizer_iff T).mpr
      ⟨g, c, hc⟩

section FiniteWorld

variable {world : Type*}
  [Fintype world] [DecidableEq world]

/-- Restriction of a total record to one physical world label. -/
def discreteWorldFiber (i : world)
    (f : clock × world → 𝕜) : clock → 𝕜 :=
  fun a => f (a, i)

/-- Embedding of one clock record into one physical world sector. -/
def discreteWorldSector (i : world)
    (φ : clock → 𝕜) : clock × world → 𝕜 :=
  fun aj => if aj.2 = i then φ aj.1 else 0

/-- Nondegenerate world coordinate observable on a possibly infinite
discrete clock. -/
def discreteLiftedWorldCoordinateObservable
    (label : world → 𝕜) :
    Module.End 𝕜 (clock × world → 𝕜) where
  toFun f ai := label ai.2 * f ai
  map_add' f h := by
    ext ai
    simp [mul_add]
  map_smul' c f := by
    ext ai
    simp [mul_left_comm]

/-- Fully connected world coupling acting separately at every clock
reading. -/
def discreteLiftedWorldCompleteCouplingObservable :
    Module.End 𝕜 (clock × world → 𝕜) where
  toFun f ai := ∑ j : world, f (ai.1, j)
  map_add' f h := by
    ext ai
    simp [Finset.sum_add_distrib]
  map_smul' c f := by
    ext ai
    simp [Finset.mul_sum]

/-- An arbitrary clock endomorphism acting identically on every world
label. -/
def discreteLiftedClockOperator
    (T : Module.End 𝕜 (clock → 𝕜)) :
    Module.End 𝕜 (clock × world → 𝕜) where
  toFun f ai := T (discreteWorldFiber ai.2 f) ai.1
  map_add' f h := by
    ext ai
    change
      T (discreteWorldFiber ai.2 f +
          discreteWorldFiber ai.2 h) ai.1 =
        T (discreteWorldFiber ai.2 f) ai.1 +
          T (discreteWorldFiber ai.2 h) ai.1
    rw [map_add]
    rfl
  map_smul' c f := by
    ext ai
    change
      T (c • discreteWorldFiber ai.2 f) ai.1 =
        c * T (discreteWorldFiber ai.2 f) ai.1
    rw [map_smul]
    rfl

omit [Group clock] [DecidableEq clock] in
/-- Finite decomposition across world labels; no decomposition of the clock
record is used. -/
theorem sum_discreteWorldSector_fiber
    (f : clock × world → 𝕜) :
    ∑ i : world, discreteWorldSector i
      (discreteWorldFiber i f) = f := by
  ext ai
  simp [discreteWorldSector, discreteWorldFiber]

omit [Group clock] [DecidableEq clock] [Fintype world] in
/-- The coordinate observable acts by its label on a single world sector. -/
theorem discreteCoordinate_on_worldSector
    (label : world → 𝕜) (i : world) (φ : clock → 𝕜) :
    discreteLiftedWorldCoordinateObservable
        (clock := clock) label (discreteWorldSector i φ) =
      label i • discreteWorldSector i φ := by
  ext aj
  by_cases hji : aj.2 = i
  · subst i
    simp [discreteLiftedWorldCoordinateObservable,
      discreteWorldSector]
  · simp [discreteLiftedWorldCoordinateObservable,
      discreteWorldSector, hji]

omit [Group clock] [DecidableEq clock] [Fintype world] in
/-- Coordinate commutation prevents a record supported on one world label
from leaking into any differently labelled sector. -/
theorem discreteWorldSector_offdiag_zero_of_commutes_coordinate
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Module.End 𝕜 (clock × world → 𝕜))
    (hcoordinate :
      ∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCoordinateObservable label f) =
          discreteLiftedWorldCoordinateObservable label (X f))
    (i j : world) (hij : i ≠ j)
    (φ : clock → 𝕜) (a : clock) :
    X (discreteWorldSector i φ) (a, j) = 0 := by
  have hcomm := hcoordinate (discreteWorldSector i φ)
  rw [discreteCoordinate_on_worldSector, LinearMap.map_smul]
    at hcomm
  have hentry := congr_fun hcomm (a, j)
  simp only [Pi.smul_apply,
    discreteLiftedWorldCoordinateObservable,
    LinearMap.coe_mk, AddHom.coe_mk] at hentry
  have hne : label i - label j ≠ 0 :=
    sub_ne_zero.mpr (hlabel.ne hij)
  apply (mul_eq_zero.mp ?_).resolve_left hne
  calc
    (label i - label j) *
        X (discreteWorldSector i φ) (a, j) =
      label i * X (discreteWorldSector i φ) (a, j) -
        label j * X (discreteWorldSector i φ) (a, j) := by ring
    _ = 0 := sub_eq_zero.mpr hentry

omit [Group clock] [DecidableEq clock] in
/-- The output at one world label is determined by the corresponding input
sector alone. -/
theorem discreteWorldSector_reconstructs_output_coordinate
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Module.End 𝕜 (clock × world → 𝕜))
    (hcoordinate :
      ∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCoordinateObservable label f) =
          discreteLiftedWorldCoordinateObservable label (X f))
    (f : clock × world → 𝕜) (a : clock) (i : world) :
    X f (a, i) =
      X (discreteWorldSector i (discreteWorldFiber i f)) (a, i) := by
  calc
    X f (a, i) =
        X (∑ j : world,
          discreteWorldSector j (discreteWorldFiber j f)) (a, i) := by
      rw [sum_discreteWorldSector_fiber]
    _ = ∑ j : world,
        X (discreteWorldSector j (discreteWorldFiber j f)) (a, i) := by
      rw [map_sum]
      simp only [Finset.sum_apply]
    _ = X (discreteWorldSector i (discreteWorldFiber i f)) (a, i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact discreteWorldSector_offdiag_zero_of_commutes_coordinate
          label hlabel X hcoordinate j i hji
            (discreteWorldFiber j f) a
      · intro hi
        exact (hi (Finset.mem_univ i)).elim

/-- Clock operator induced on one labelled world sector. -/
def inducedDiscreteClockOperator
    (X : Module.End 𝕜 (clock × world → 𝕜))
    (i : world) :
    Module.End 𝕜 (clock → 𝕜) where
  toFun φ a := X (discreteWorldSector i φ) (a, i)
  map_add' φ ψ := by
    ext a
    have hsector :
        discreteWorldSector i (φ + ψ) =
          discreteWorldSector i φ + discreteWorldSector i ψ := by
      ext aj
      by_cases hji : aj.2 = i <;>
        simp [discreteWorldSector, hji]
    rw [hsector, map_add]
    rfl
  map_smul' c φ := by
    ext a
    have hsector :
        discreteWorldSector i (c • φ) =
          c • discreteWorldSector i φ := by
      ext aj
      by_cases hji : aj.2 = i <;>
        simp [discreteWorldSector, hji]
    rw [hsector, map_smul]
    rfl

omit [Group clock] [DecidableEq clock] in
/-- Complete coupling sends any one world sector to the same record on every
world label. -/
theorem completeCoupling_on_worldSector
    (i : world) (φ : clock → 𝕜) :
    discreteLiftedWorldCompleteCouplingObservable
        (world := world) (discreteWorldSector i φ) =
      fun ai => φ ai.1 := by
  ext ai
  simp [discreteLiftedWorldCompleteCouplingObservable,
    discreteWorldSector]

omit [Group clock] [DecidableEq clock] in
/-- Commutation with the complete coupling forces the induced clock operator
to be identical on every world label. -/
theorem inducedDiscreteClockOperator_eq_of_commutes_world_pair
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Module.End 𝕜 (clock × world → 𝕜))
    (hcoordinate :
      ∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCoordinateObservable label f) =
          discreteLiftedWorldCoordinateObservable label (X f))
    (hcoupling :
      ∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCompleteCouplingObservable f) =
          discreteLiftedWorldCompleteCouplingObservable (X f))
    (i j : world) :
    inducedDiscreteClockOperator X i =
      inducedDiscreteClockOperator X j := by
  ext φ a
  have hcomm := congr_fun (hcoupling (discreteWorldSector j φ)) (a, i)
  rw [completeCoupling_on_worldSector] at hcomm
  have hleft :=
    discreteWorldSector_reconstructs_output_coordinate
      label hlabel X hcoordinate (fun ai : clock × world => φ ai.1) a i
  have hfiber :
      discreteWorldFiber i (fun ai : clock × world => φ ai.1) = φ := by
    rfl
  rw [hfiber] at hleft
  rw [hleft] at hcomm
  simp only [discreteLiftedWorldCompleteCouplingObservable,
    LinearMap.coe_mk, AddHom.coe_mk] at hcomm
  have hsum :
      ∑ k : world, X (discreteWorldSector j φ) (a, k) =
        X (discreteWorldSector j φ) (a, j) := by
    apply Finset.sum_eq_single j
    · intro k _ hkj
      exact discreteWorldSector_offdiag_zero_of_commutes_coordinate
        label hlabel X hcoordinate j k hkj.symm φ a
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  rw [hsum] at hcomm
  exact hcomm

omit [Group clock] [DecidableEq clock] in
/-- **Arbitrary-discrete-clock no-mixing law.**  Two complete physical world
labels force every linear total refactorization to be one clock operator
acting identically across the world, without any cardinality restriction on
the clock. -/
theorem eq_discreteLiftedClockOperator_of_commutes_world_pair
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Module.End 𝕜 (clock × world → 𝕜))
    (hcoordinate :
      ∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCoordinateObservable label f) =
          discreteLiftedWorldCoordinateObservable label (X f))
    (hcoupling :
      ∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCompleteCouplingObservable f) =
          discreteLiftedWorldCompleteCouplingObservable (X f))
    [Nonempty world] :
    ∃ T : Module.End 𝕜 (clock → 𝕜),
      X = discreteLiftedClockOperator (world := world) T := by
  let anchor : world := Classical.choice inferInstance
  let T := inducedDiscreteClockOperator X anchor
  refine ⟨T, LinearMap.ext fun f => ?_⟩
  ext ai
  rw [discreteWorldSector_reconstructs_output_coordinate
    label hlabel X hcoordinate f ai.1 ai.2]
  have heq :=
    inducedDiscreteClockOperator_eq_of_commutes_world_pair
      label hlabel X hcoordinate hcoupling ai.2 anchor
  have hentry :=
    congr_fun (LinearMap.congr_fun heq
      (discreteWorldFiber ai.2 f)) ai.1
  simp [discreteLiftedClockOperator, inducedDiscreteClockOperator,
    T] at hentry ⊢
  exact hentry

omit [Group clock] [DecidableEq clock]
  [Fintype world] [DecidableEq world] in
/-- Every lifted clock operator commutes with the physical world coordinate. -/
theorem discreteLiftedClockOperator_commutes_worldCoordinate
    (label : world → 𝕜)
    (T : Module.End 𝕜 (clock → 𝕜))
    (f : clock × world → 𝕜) :
    discreteLiftedClockOperator T
        (discreteLiftedWorldCoordinateObservable label f) =
      discreteLiftedWorldCoordinateObservable label
        (discreteLiftedClockOperator T f) := by
  ext ai
  have hfiber :
      discreteWorldFiber ai.2
          (discreteLiftedWorldCoordinateObservable label f) =
        label ai.2 • discreteWorldFiber ai.2 f := by
    ext a
    simp [discreteWorldFiber,
      discreteLiftedWorldCoordinateObservable]
  simp only [discreteLiftedClockOperator, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [hfiber, map_smul]
  rfl

omit [Group clock] [DecidableEq clock] [DecidableEq world] in
/-- Every lifted clock operator commutes with the physical world coupling. -/
theorem discreteLiftedClockOperator_commutes_worldCoupling
    (T : Module.End 𝕜 (clock → 𝕜))
    (f : clock × world → 𝕜) :
    discreteLiftedClockOperator T
        (discreteLiftedWorldCompleteCouplingObservable f) =
      discreteLiftedWorldCompleteCouplingObservable
        (discreteLiftedClockOperator T f) := by
  ext ai
  have hfiber :
      discreteWorldFiber ai.2
          (discreteLiftedWorldCompleteCouplingObservable f) =
        ∑ j : world, discreteWorldFiber j f := by
    ext a
    simp [discreteWorldFiber,
      discreteLiftedWorldCompleteCouplingObservable]
  change
    T (discreteWorldFiber ai.2
      (discreteLiftedWorldCompleteCouplingObservable f)) ai.1 =
      ∑ j : world, T (discreteWorldFiber j f) ai.1
  rw [hfiber, map_sum]
  simp only [Finset.sum_apply]

omit [Group clock] [DecidableEq clock] in
/-- Exact world-label commutant classification for an arbitrary discrete
clock. -/
theorem commutes_discrete_world_pair_iff_exists_liftedClockOperator
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Module.End 𝕜 (clock × world → 𝕜))
    [Nonempty world] :
    ((∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCoordinateObservable label f) =
          discreteLiftedWorldCoordinateObservable label (X f)) ∧
      (∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCompleteCouplingObservable f) =
          discreteLiftedWorldCompleteCouplingObservable (X f))) ↔
    ∃ T : Module.End 𝕜 (clock → 𝕜),
      X = discreteLiftedClockOperator (world := world) T := by
  constructor
  · rintro ⟨hcoordinate, hcoupling⟩
    exact eq_discreteLiftedClockOperator_of_commutes_world_pair
      label hlabel X hcoordinate hcoupling
  · rintro ⟨T, rfl⟩
    exact
      ⟨discreteLiftedClockOperator_commutes_worldCoordinate label T,
        discreteLiftedClockOperator_commutes_worldCoupling T⟩

omit [Group clock] [DecidableEq clock]
  [Fintype world] [DecidableEq world] in
/-- Lifting arbitrary discrete-clock operators respects composition. -/
theorem discreteLiftedClockOperator_comp
    (T U : Module.End 𝕜 (clock → 𝕜)) :
    discreteLiftedClockOperator (world := world) (T.comp U) =
      (discreteLiftedClockOperator (world := world) T).comp
        (discreteLiftedClockOperator (world := world) U) := by
  ext f ai
  rfl

omit [Group clock] [DecidableEq clock]
  [Fintype world] [DecidableEq world] in
/-- A nonempty world makes the arbitrary-clock lift injective. -/
theorem discreteLiftedClockOperator_injective [Nonempty world] :
    Function.Injective
      (discreteLiftedClockOperator (𝕜 := 𝕜)
        (clock := clock) (world := world)) := by
  intro T U h
  let anchor : world := Classical.choice inferInstance
  ext φ a
  let f : clock × world → 𝕜 := fun ai => φ ai.1
  have hentry :=
    congr_fun (LinearMap.congr_fun h f) (a, anchor)
  simpa [discreteLiftedClockOperator, discreteWorldFiber, f]
    using! hentry

/-- **Cardinality-free physical clock--world stabilizer.**  For every
discrete clock group of any cardinality and every nonempty finite world, two
complete physical world labels together with all clock-reading and
regular-shift covariance laws classify every linear total refactorization as
one clock-origin translation times one global scalar. -/
theorem discretePhysicalClockWorldStabilizer_iff
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Module.End 𝕜 (clock × world → 𝕜))
    [Nonempty world] :
    ((∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCoordinateObservable label f) =
          discreteLiftedWorldCoordinateObservable label (X f)) ∧
      (∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCompleteCouplingObservable f) =
          discreteLiftedWorldCompleteCouplingObservable (X f)) ∧
      ∃ g : clock,
        (∀ t : clock, ∀ f : clock × world → 𝕜,
          X (discreteLiftedClockOperator
                (world := world) (discreteClockBasisProjector t) f) =
            discreteLiftedClockOperator (world := world)
                (discreteClockBasisProjector (g * t)) (X f)) ∧
        (∀ h : clock, ∀ f : clock × world → 𝕜,
          X (discreteLiftedClockOperator
                (world := world) (discreteClockLeftTranslation h) f) =
            discreteLiftedClockOperator (world := world)
                (discreteClockLeftTranslation (g * h * g⁻¹)) (X f))) ↔
    ∃ g : clock, ∃ c : 𝕜,
      X = discreteLiftedClockOperator (world := world)
        (c • discreteClockLeftTranslation g) := by
  constructor
  · rintro ⟨hcoordinate, hcoupling, g, hprojector, hshift⟩
    obtain ⟨T, hX⟩ :=
      (commutes_discrete_world_pair_iff_exists_liftedClockOperator
        label hlabel X).mp ⟨hcoordinate, hcoupling⟩
    have hprojectorT :
        ∀ t : clock, ∀ f : clock → 𝕜,
          T (discreteClockBasisProjector t f) =
            discreteClockBasisProjector (g * t) (T f) := by
      intro t f
      have htotal :
          (discreteLiftedClockOperator (world := world) T).comp
              (discreteLiftedClockOperator (world := world)
                (discreteClockBasisProjector t)) =
            (discreteLiftedClockOperator (world := world)
              (discreteClockBasisProjector (g * t))).comp
              (discreteLiftedClockOperator (world := world) T) := by
        apply LinearMap.ext
        intro F
        rw [← hX]
        exact hprojector t F
      have hlift :
          discreteLiftedClockOperator (world := world)
              (T.comp (discreteClockBasisProjector t)) =
            discreteLiftedClockOperator (world := world)
              ((discreteClockBasisProjector (g * t)).comp T) := by
        simpa only [discreteLiftedClockOperator_comp] using htotal
      have hbase :=
        discreteLiftedClockOperator_injective (world := world) hlift
      exact LinearMap.congr_fun hbase f
    have hshiftT :
        ∀ h : clock, ∀ f : clock → 𝕜,
          T (discreteClockLeftTranslation h f) =
            discreteClockLeftTranslation (g * h * g⁻¹) (T f) := by
      intro h f
      have htotal :
          (discreteLiftedClockOperator (world := world) T).comp
              (discreteLiftedClockOperator (world := world)
                (discreteClockLeftTranslation h)) =
            (discreteLiftedClockOperator (world := world)
              (discreteClockLeftTranslation (g * h * g⁻¹))).comp
              (discreteLiftedClockOperator (world := world) T) := by
        apply LinearMap.ext
        intro F
        rw [← hX]
        exact hshift h F
      have hlift :
          discreteLiftedClockOperator (world := world)
              (T.comp (discreteClockLeftTranslation h)) =
            discreteLiftedClockOperator (world := world)
              ((discreteClockLeftTranslation
                (g * h * g⁻¹)).comp T) := by
        simpa only [discreteLiftedClockOperator_comp] using htotal
      have hbase :=
        discreteLiftedClockOperator_injective (world := world) hlift
      exact LinearMap.congr_fun hbase f
    obtain ⟨c, hT⟩ :=
      eq_smul_discreteClockLeftTranslation_of_intertwines
        g T hprojectorT hshiftT
    exact
      ⟨g, c, hX.trans
        (congrArg
          (discreteLiftedClockOperator (world := world)) hT)⟩
  · rintro ⟨g, c, hX⟩
    let T : Module.End 𝕜 (clock → 𝕜) :=
      c • discreteClockLeftTranslation g
    have horigin :
        (∀ t : clock, ∀ f : clock → 𝕜,
          T (discreteClockBasisProjector t f) =
            discreteClockBasisProjector (g * t) (T f)) ∧
        (∀ h : clock, ∀ f : clock → 𝕜,
          T (discreteClockLeftTranslation h f) =
            discreteClockLeftTranslation (g * h * g⁻¹) (T f)) :=
      by
        constructor
        · intro t f
          dsimp [T]
          rw [discreteClockLeftTranslation_projector_intertwines]
          exact
            (map_smul
              (discreteClockBasisProjector (𝕜 := 𝕜) (g * t))
              c (discreteClockLeftTranslation g f)).symm
        · intro h f
          dsimp [T]
          rw [discreteClockLeftTranslation_shift_covariant]
          exact
            (map_smul
              (discreteClockLeftTranslation (𝕜 := 𝕜)
                (g * h * g⁻¹))
              c (discreteClockLeftTranslation g f)).symm
    have hworld :
        (∀ f : clock × world → 𝕜,
          X (discreteLiftedWorldCoordinateObservable label f) =
            discreteLiftedWorldCoordinateObservable label (X f)) ∧
        (∀ f : clock × world → 𝕜,
          X (discreteLiftedWorldCompleteCouplingObservable f) =
            discreteLiftedWorldCompleteCouplingObservable (X f)) := by
      apply
        (commutes_discrete_world_pair_iff_exists_liftedClockOperator
          label hlabel X).mpr
      exact ⟨T, hX⟩
    refine ⟨hworld.1, hworld.2, g, ?_, ?_⟩
    · intro t f
      have hbase :
          T.comp (discreteClockBasisProjector t) =
            (discreteClockBasisProjector (g * t)).comp T := by
        apply LinearMap.ext
        intro φ
        exact horigin.1 t φ
      have hlift := congrArg
        (discreteLiftedClockOperator (world := world)) hbase
      rw [discreteLiftedClockOperator_comp,
        discreteLiftedClockOperator_comp] at hlift
      rw [hX]
      exact LinearMap.congr_fun hlift f
    · intro h f
      have hbase :
          T.comp (discreteClockLeftTranslation h) =
            (discreteClockLeftTranslation (g * h * g⁻¹)).comp T := by
        apply LinearMap.ext
        intro φ
        exact horigin.2 h φ
      have hlift := congrArg
        (discreteLiftedClockOperator (world := world)) hbase
      rw [discreteLiftedClockOperator_comp,
        discreteLiftedClockOperator_comp] at hlift
      rw [hX]
      exact LinearMap.congr_fun hlift f

omit [Fintype world] [DecidableEq world] in
/-- Bijectivity excludes the zero scalar in the cardinality-free physical
clock--world stabilizer. -/
theorem discretePhysicalClockWorldStabilizer_scalar_ne_zero
    (X : Module.End 𝕜 (clock × world → 𝕜))
    (hX : Function.Injective X)
    (g : clock) (c : 𝕜)
    (hclass :
      X = discreteLiftedClockOperator (world := world)
        (c • discreteClockLeftTranslation g))
    [Nonempty world] :
    c ≠ 0 := by
  intro hc
  have hXzero : X = 0 := by
    rw [hclass, hc]
    ext f ai
    simp [discreteLiftedClockOperator]
  let anchor : world := Classical.choice inferInstance
  let record : clock × world → 𝕜 :=
    fun ai => discreteClockKet (𝕜 := 𝕜) 1 ai.1
  have heq : X record = X 0 := by
    rw [hXzero]
    rfl
  have hrecord := hX heq
  have hentry := congr_fun hrecord (1, anchor)
  simp [record, discreteClockKet] at hentry

/-- **Invertible cardinality-free physical stabilizer.**  For every
discrete clock group of any cardinality, bijective total refactorizations
preserving the two world labels and all clock readings and shifts are exactly
one origin translation times one nonzero global scalar. -/
theorem invertibleDiscretePhysicalClockWorldStabilizer_iff
    (label : world → 𝕜) (hlabel : Function.Injective label)
    (X : Module.End 𝕜 (clock × world → 𝕜))
    (hX : Function.Bijective X)
    [Nonempty world] :
    ((∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCoordinateObservable label f) =
          discreteLiftedWorldCoordinateObservable label (X f)) ∧
      (∀ f : clock × world → 𝕜,
        X (discreteLiftedWorldCompleteCouplingObservable f) =
          discreteLiftedWorldCompleteCouplingObservable (X f)) ∧
      ∃ g : clock,
        (∀ t : clock, ∀ f : clock × world → 𝕜,
          X (discreteLiftedClockOperator
                (world := world) (discreteClockBasisProjector t) f) =
            discreteLiftedClockOperator (world := world)
                (discreteClockBasisProjector (g * t)) (X f)) ∧
        (∀ h : clock, ∀ f : clock × world → 𝕜,
          X (discreteLiftedClockOperator
                (world := world) (discreteClockLeftTranslation h) f) =
            discreteLiftedClockOperator (world := world)
                (discreteClockLeftTranslation (g * h * g⁻¹)) (X f))) ↔
    ∃ g : clock, ∃ c : 𝕜,
      c ≠ 0 ∧
        X = discreteLiftedClockOperator (world := world)
          (c • discreteClockLeftTranslation g) := by
  constructor
  · intro h
    obtain ⟨g, c, hc⟩ :=
      (discretePhysicalClockWorldStabilizer_iff
        label hlabel X).mp h
    exact
      ⟨g, c,
        discretePhysicalClockWorldStabilizer_scalar_ne_zero
          X hX.1 g c hc,
        hc⟩
  · rintro ⟨g, c, _, hc⟩
    exact
      (discretePhysicalClockWorldStabilizer_iff
        label hlabel X).mpr ⟨g, c, hc⟩

end FiniteWorld

end

end HTGeometry
