import GaloisForLFunctions.HTGeometry.DifferentialPairwiseCommonMode
import GaloisForLFunctions.HTGeometry.FiniteAlgebraicStateBoundary

/-!
# Relational histories and the exact external-time ambiguity

An arbitrary family of clocks valued in a group decomposes into one common origin and a complete
anchored relational configuration.  This remains exact for infinite index types and nonabelian
clock groups.  A reporter invariant under common changes of origin cannot itself transform as an
absolute clock unless the clock group is trivial.

For an arbitrary group action on a state space, covariant conditional histories are exactly the
globally stationary histories under the associated diagonal action.  They are reconstructed from
their conditional value at the identity.

Finally, once observables retain physical labels, two inner evolution laws agree on all labelled
observables exactly when the difference of their generators belongs to the labelled observable
commutant.  Thus common clock origin and observable commutant are distinct residual ambiguities.

These are structural classification theorems.  No group element is interpreted as a chronology
before a cosmological beginning, and no particular Hamiltonian, QFT, or gravitational model is
assumed.
-/

namespace HTGeometry

universe u v w

section ClockConfigurations

variable {G : Type u} {I : Type v} {Y : Type w} [Group G]

/-- Simultaneous left translation of every internal clock by one common origin change. -/
def diagonalClockShift (g : G) (x : I → G) : I → G :=
  fun i => g * x i

/-- Complete relational clock readings with respect to one internal anchor. -/
def anchoredClockRatios (a : I) (x : I → G) : I → G :=
  fun i => (x a)⁻¹ * x i

/-- Anchored clock ratios erase every common origin change, for arbitrary clock families and
possibly nonabelian clock groups. -/
@[simp] theorem anchoredClockRatios_diagonalClockShift
    (a : I) (g : G) (x : I → G) :
    anchoredClockRatios a (diagonalClockShift g x) =
      anchoredClockRatios a x := by
  funext i
  simp [anchoredClockRatios, diagonalClockShift]

/-- **Exact arbitrary-family relational quotient.** Two complete clock configurations have the
same anchored relational readings exactly when a unique common origin change relates them. -/
theorem anchoredClockRatios_eq_iff_existsUnique_diagonalClockShift
    (a : I) (x y : I → G) :
    anchoredClockRatios a x = anchoredClockRatios a y ↔
      ∃! g : G, y = diagonalClockShift g x := by
  constructor
  · intro h
    let g : G := y a * (x a)⁻¹
    refine ⟨g, ?_, ?_⟩
    · funext i
      have hi := congrFun h i
      change (x a)⁻¹ * x i = (y a)⁻¹ * y i at hi
      change y i = g * x i
      calc
        y i = y a * ((y a)⁻¹ * y i) := by group
        _ = y a * ((x a)⁻¹ * x i) := by rw [← hi]
        _ = g * x i := by simp only [g]; group
    · intro z hz
      have ha := congrFun hz a
      change y a = z * x a at ha
      calc
        z = (z * x a) * (x a)⁻¹ := by group
        _ = y a * (x a)⁻¹ := by rw [← ha]
        _ = g := rfl
  · rintro ⟨g, hg, _⟩
    rw [hg, anchoredClockRatios_diagonalClockShift]

/-- Normalizing the anchor to the unit is literally the anchored relational configuration. -/
@[simp] theorem diagonalClockShift_anchorInv_eq_anchoredClockRatios
    (a : I) (x : I → G) :
    diagonalClockShift (x a)⁻¹ x = anchoredClockRatios a x := by
  rfl

/-- One anchor value and all anchored ratios reconstruct every internal clock value. -/
theorem clockConfiguration_reconstruct
    (a i : I) (x : I → G) :
    x i = x a * anchoredClockRatios a x i := by
  simp [anchoredClockRatios]

/-- A reporter depending only on relational clock data. -/
def DiagonalClockInvariant (f : (I → G) → Y) : Prop :=
  ∀ g x, f (diagonalClockShift g x) = f x

/-- A purported absolute-clock reporter transforming with the common clock origin. -/
def DiagonalClockCovariant (f : (I → G) → G) : Prop :=
  ∀ g x, f (diagonalClockShift g x) = g * f x

/-- Every common-origin invariant reporter factors valuewise through the complete anchored
relational configuration. -/
theorem DiagonalClockInvariant.eq_anchoredClockRatios
    {f : (I → G) → Y} (hf : DiagonalClockInvariant f)
    (a : I) (x : I → G) :
    f x = f (anchoredClockRatios a x) := by
  calc
    f x = f (diagonalClockShift (x a)⁻¹ x) := (hf (x a)⁻¹ x).symm
    _ = f (anchoredClockRatios a x) := rfl

/-- **External-clock no-go.** If one reporter is both insensitive to a common origin and transforms
as that common origin, then the entire clock group is trivial.  The statement has no finiteness
hypothesis on the clock family. -/
theorem subsingleton_group_of_diagonalClockInvariant_and_covariant
    (f : (I → G) → G)
    (hinvariant : DiagonalClockInvariant f)
    (hcovariant : DiagonalClockCovariant f) :
    Subsingleton G := by
  refine ⟨?_⟩
  intro g h
  let x : I → G := fun _ => 1
  have hg : g * f x = 1 * f x := by
    calc
      g * f x = f (diagonalClockShift g x) := (hcovariant g x).symm
      _ = f x := hinvariant g x
      _ = 1 * f x := (one_mul _).symm
  have hh : h * f x = 1 * f x := by
    calc
      h * f x = f (diagonalClockShift h x) := (hcovariant h x).symm
      _ = f x := hinvariant h x
      _ = 1 * f x := (one_mul _).symm
  exact (mul_right_cancel hg).trans (mul_right_cancel hh).symm

/-- **Complete external-clock classification.** A common external clock can be recovered by a
reporter that is simultaneously relationally invariant and origin-covariant if and only if the
clock group has no nontrivial time translation at all. -/
theorem exists_diagonalClockInvariant_and_covariant_iff_subsingleton :
    (∃ f : (I → G) → G,
        DiagonalClockInvariant f ∧ DiagonalClockCovariant f) ↔
      Subsingleton G := by
  constructor
  · rintro ⟨f, hinvariant, hcovariant⟩
    exact subsingleton_group_of_diagonalClockInvariant_and_covariant
      f hinvariant hcovariant
  · intro hG
    let f : (I → G) → G := fun _ => 1
    refine ⟨f, ?_, ?_⟩
    · intro g x
      rfl
    · intro g x
      change 1 = g * 1
      rw [hG.elim g 1, one_mul]

end ClockConfigurations

section RelationalHistories

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

/-- The relational history generated from one conditional state. -/
def seededRelationalHistory (x : X) : G → X :=
  fun t => t • x

/-- Covariance of conditional states under the internal clock group. -/
def IsRelationalHistory (h : G → X) : Prop :=
  ∀ g t, h (g * t) = g • h t

/-- The diagonal action combining a clock-origin shift with the corresponding state action. -/
def historyDiagonalShift (g : G) (h : G → X) : G → X :=
  fun t => g • h (g⁻¹ * t)

/-- Every relational history, over every clock group and state action, is reconstructed from its
conditional value at the identity. -/
theorem isRelationalHistory_iff_eq_seeded (h : G → X) :
    IsRelationalHistory h ↔ h = seededRelationalHistory (h 1) := by
  constructor
  · intro hh
    funext t
    simpa [seededRelationalHistory] using hh t 1
  · intro hh g t
    rw [hh]
    simp [seededRelationalHistory, mul_smul]

/-- A history generated by conditional state evolution is globally stationary under the diagonal
clock--state action. -/
theorem historyDiagonalShift_seeded
    (g : G) (x : X) :
    historyDiagonalShift g (seededRelationalHistory x) =
      seededRelationalHistory x := by
  funext t
  simp [historyDiagonalShift, seededRelationalHistory, mul_smul]

/-- **Evolution-without-evolution equivalence.** Covariance of every conditional history value is
equivalent to stationarity of the complete history under every diagonal clock--state shift. -/
theorem isRelationalHistory_iff_stationary (h : G → X) :
    IsRelationalHistory h ↔ ∀ g, historyDiagonalShift g h = h := by
  constructor
  · intro hh g
    funext t
    have hcov := hh g (g⁻¹ * t)
    simpa [historyDiagonalShift] using hcov.symm
  · intro hs g t
    have hstat := congrFun (hs g) (g * t)
    simpa [historyDiagonalShift] using hstat.symm

end RelationalHistories

section IsometricQuantumHistories

variable {G : Type u} {X : Type v} [Group G]
  [NormedAddCommGroup X] [DistribMulAction G X] [IsIsometricSMul G X]

/-- Every conditional component of an isometric, hence in particular unitary, relational history
has exactly the norm of its seed state. -/
theorem norm_seededRelationalHistory
    (t : G) (x : X) :
    ‖seededRelationalHistory x t‖ = ‖x‖ := by
  change ‖t • x‖ = ‖x‖
  simpa only [dist_zero_right, smul_zero] using dist_smul t x 0

end IsometricQuantumHistories

section InfiniteStateExternalClockBoundary

open GaloisForLFunctions
open scoped Differential

universe uField uI

variable {F K : Type uField} {I : Type uI}
  [Field F] [Field K] [Algebra F K]
  [Differential F] [Differential K] [DifferentialAlgebra F K] [CharZero K]

/-- The complete differential field generated by every ordered pairwise clock difference. -/
abbrev completePairwiseClockField (x : I → K) : IntermediateField F K :=
  differentialAdjoin F (Set.range fun p : I × I ↦ x p.1 - x p.2)

/-- **No finite-state external clock.** For an arbitrarily indexed differentially independent
clock family, the missing common mode cannot belong to any derivation-closed state model of finite
transcendence degree over all complete relational clock data. -/
theorem not_finiteAlgebraicStateObservable_anchor_over_completePairwiseClockField
    (anchor : I) (x : I → K) (hx : DifferentialIndependent F x) :
    ¬ GaloisForLFunctions.HTGeometry.FiniteAlgebraicStateObservable
        (differentialAdjoin F
          (Set.range fun p : I × I ↦ x p.1 - x p.2))
        (x anchor) := by
  letI : Differential ↥(differentialAdjoin F
      (Set.range fun p : I × I ↦ x p.1 - x p.2)) :=
    derivationClosedDifferential _
      (derivationClosed_differentialAdjoin F _)
  letI : DifferentialAlgebra
      ↥(differentialAdjoin F
        (Set.range fun p : I × I ↦ x p.1 - x p.2)) K :=
    ⟨fun c => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F _) c⟩
  have hht :
      HypertranscendentalOver
        (differentialAdjoin F
          (Set.range fun p : I × I ↦ x p.1 - x p.2))
        (x anchor) :=
    GaloisForLFunctions.HTGeometry.hypertranscendentalOver_anchor_pairwiseDifferences
      (F := F) (K := K) (V := I) anchor x hx
  exact
    GaloisForLFunctions.HTGeometry.not_finiteAlgebraicStateObservable_of_hypertranscendentalOver
      (F := differentialAdjoin F
        (Set.range fun p : I × I ↦ x p.1 - x p.2))
      (E := K) hht

/-- **Infinite-state lower bound.** Every derivation-closed state field that contains the missing
common clock mode has at least countable transcendence degree over the complete relational clock
field. This holds for finite or infinite clock families and uses no commutativity of the clock
index set. -/
theorem aleph0_le_trdeg_of_mem_stateField_anchor_over_completePairwiseClockField
    (anchor : I) (x : I → K) (hx : DifferentialIndependent F x)
    (S : IntermediateField
      (differentialAdjoin F
        (Set.range fun p : I × I ↦ x p.1 - x p.2))
      K)
    (hSclosed : GaloisForLFunctions.DerivationClosed S)
    (hanchor : x anchor ∈ S) :
    Cardinal.aleph0 ≤
      Algebra.trdeg
        (differentialAdjoin F
          (Set.range fun p : I × I ↦ x p.1 - x p.2))
        S := by
  letI : Differential ↥(differentialAdjoin F
      (Set.range fun p : I × I ↦ x p.1 - x p.2)) :=
    derivationClosedDifferential _
      (derivationClosed_differentialAdjoin F _)
  letI : DifferentialAlgebra
      ↥(differentialAdjoin F
        (Set.range fun p : I × I ↦ x p.1 - x p.2)) K :=
    ⟨fun c => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F _) c⟩
  have hht :
      HypertranscendentalOver
        (differentialAdjoin F
          (Set.range fun p : I × I ↦ x p.1 - x p.2))
        (x anchor) :=
    GaloisForLFunctions.HTGeometry.hypertranscendentalOver_anchor_pairwiseDifferences
      (F := F) (K := K) (V := I) anchor x hx
  exact
    GaloisForLFunctions.HTGeometry.aleph0_le_trdeg_of_mem_derivationClosed_of_hypertranscendentalOver
      (F := differentialAdjoin F
        (Set.range fun p : I × I ↦ x p.1 - x p.2))
      (E := K)
      S hSclosed hht hanchor

end InfiniteStateExternalClockBoundary

section LabelledObservableDynamics

variable {A : Type u} [Ring A]

/-- Infinitesimal Heisenberg law induced by a generator on one labelled observable. -/
def heisenbergObservableDerivative (H X : A) : A :=
  H * X - X * H

/-- Two generators induce the same law on every physically retained observable label. -/
def SameLabelledObservableLaw (S : Set A) (H K : A) : Prop :=
  ∀ X ∈ S, heisenbergObservableDerivative H X =
    heisenbergObservableDerivative K X

/-- The commutant of the physically labelled observable family, written as a Prop interface. -/
def CommutesWithLabelledObservables (S : Set A) (D : A) : Prop :=
  ∀ X ∈ S, D * X = X * D

/-- **Exact physical-law ambiguity.** Once observable meanings are retained as labels, two inner
evolution laws agree exactly when the generator difference lies in the labelled observable
commutant.  No arbitrary-law freedom remains beyond that commutant. -/
theorem sameLabelledObservableLaw_iff_difference_commutes
    (S : Set A) (H K : A) :
    SameLabelledObservableLaw S H K ↔
      CommutesWithLabelledObservables S (H - K) := by
  constructor
  · intro h X hX
    have hderiv := h X hX
    unfold heisenbergObservableDerivative at hderiv
    simp only [sub_mul, mul_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp hderiv
  · intro h X hX
    have hcomm := h X hX
    unfold heisenbergObservableDerivative
    simp only [sub_mul, mul_sub] at hcomm
    exact sub_eq_sub_iff_sub_eq_sub.mpr hcomm

end LabelledObservableDynamics

section FiniteQuantumObservableDynamics

variable {𝕜 : Type u} {n : Type v}
  [CommRing 𝕜] [Fintype n] [DecidableEq n]

/-- **Complete finite quantum-law uniqueness.** Two finite matrix Hamiltonians have identical
Heisenberg derivatives on every observable exactly when they differ by one scalar matrix.  Thus
fixing the complete labelled observable algebra reduces arbitrary generator ambiguity to the
physically silent energy-origin/global-phase term, in every finite dimension. -/
theorem matrix_sameLabelledObservableLaw_univ_iff_exists_scalar
    (H K : Matrix n n 𝕜) :
    SameLabelledObservableLaw Set.univ H K ↔
      ∃ c : 𝕜, H - K = Matrix.scalar n c := by
  rw [sameLabelledObservableLaw_iff_difference_commutes]
  constructor
  · intro h
    have hscalar : H - K ∈ Set.range (Matrix.scalar n) := by
      rw [Matrix.mem_range_scalar_iff_commute_single']
      intro i j
      exact (h (Matrix.single i j 1) (Set.mem_univ _)).symm
    obtain ⟨c, hc⟩ := hscalar
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    intro X _
    rw [hc]
    exact Matrix.scalar_commute c (fun r => Commute.all c r) X

end FiniteQuantumObservableDynamics

end HTGeometry
