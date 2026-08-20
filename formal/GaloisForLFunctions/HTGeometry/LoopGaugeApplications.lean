import GaloisForLFunctions.HTGeometry.ConstitutiveNonabelianRecoveryHolonomy
import GaloisForLFunctions.HTGeometry.ClockReadoutWitnesses
import GaloisForLFunctions.HTGeometry.FramedTwoBoundaryPhaseFibreHistorySeparation
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.AbelianDifferentialCharacter
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicGaugeHolonomyMasterAction
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection
import GaloisForLFunctions.HTGeometry.ParametricHolonomyTransgressionLaw
import GaloisForLFunctions.HTGeometry.PerfectUnitaryLinkFlatness
import GaloisForLFunctions.HTGeometry.RationalNonabelianContextAnomaly
import GaloisForLFunctions.HTGeometry.SymmetricChiralShapeLogDeriv
import GaloisForLFunctions.HTGeometry.WilsonSupportCumulant

/-!
# Loop-gauge applications across the reusable corpus

Premise-free mechanical applications of Wilson and Polyakov holonomy, a finite
Makeenko--Migdal-type plaquette relation, and homotopy Chern--Simons action laws.

The plaquette theorem below is an exact algebraic loop equation for the exponential carrier.  It
is called Makeenko--Migdal-*type* because no Yang--Mills measure or large-rank expectation is
present.  The name records the finite split/reconnection mechanism, not an analytic claim about
the continuum Makeenko--Migdal equation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LoopGaugeApplications

open Matrix
open _root_.HTGeometry.NomologicalHomotopyGeometry

/-! ## Wilson loops -/

/-- Gauge-invariant trace observable of the first rational Wilson triangle. -/
def rationalWilsonTraceX (r : ℕ) : ℂ :=
  Matrix.trace (rationalWilsonLoopX r)

/-- Gauge-invariant trace observable of the second rational Wilson triangle. -/
def rationalWilsonTraceY (r : ℕ) : ℂ :=
  Matrix.trace (rationalWilsonLoopY r)

/-- Every matrix commutator is invisible to the Wilson trace. -/
theorem rationalWilson_commutator_trace_eq_zero (r : ℕ) :
    Matrix.trace
        (rationalWilsonLoopX r * rationalWilsonLoopY r -
          rationalWilsonLoopY r * rationalWilsonLoopX r) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm]
  exact sub_self _

/-- The corpus's explicit loops retain nonabelian ordering data that their traces erase. -/
theorem rationalWilson_untraced_order_survives_trace_loss (r : ℕ) :
    rationalWilsonLoopX r * rationalWilsonLoopY r -
          rationalWilsonLoopY r * rationalWilsonLoopX r ≠ 0 ∧
      Matrix.trace
        (rationalWilsonLoopX r * rationalWilsonLoopY r -
          rationalWilsonLoopY r * rationalWilsonLoopX r) = 0 :=
  ⟨rationalWilsonLoops_commutator_ne_zero r,
    rationalWilson_commutator_trace_eq_zero r⟩

/-- The canonical conjugacy-class Wilson observable is literally gauge invariant. -/
theorem wilsonTrace_conjugacyClass_gauge_invariant
    {V A : Type*} [Group A] {G : SimpleGraph V}
    (g : V → A) (c : V → V → A) (u : V) (p : G.Walk u u) :
    ConjClasses.mk (clockWalkTransport (clockCalibrationGauge g c) p) =
      ConjClasses.mk (clockWalkTransport c p) :=
  clockClosedConjClass_gauge_invariant g c u p

/-- Every length-three Wilson-walk cumulant supported on all four vertices vanishes. -/
theorem wilson_lengthThree_fullSupport_cumulant_zero
    (weight : (Fin 3 → Fin 4) → ℤ) :
    supportMobiusCumulant walkSupport weight (Finset.univ : Finset (Fin 4)) = 0 := by
  exact wilsonWalkSupportCumulant_eq_zero 3 weight
    ⟨Finset.univ, by simp⟩

/-- A flat local connection can retain a nontrivial global Wilson loop. -/
theorem flatWilsonLoop_can_survive_zero_curvature :
    (0 : Module.End ℝ ℝ) = 0 ∧
      FlatSuperconnection.circleSignHolonomy (Multiplicative.ofAdd 1) ≠ 1 :=
  FlatSuperconnection.zeroCurvature_not_imply_trivialHolonomy

/-- Equal Wilson/Berry phase can conceal distinct winding action. -/
theorem wilsonPhase_does_not_determine_windingAction :
    framedBerryHolonomy zeroWindingTwo = framedBerryHolonomy oppositeWindingTwo ∧
      framedWindingProjectedNormSq zeroWindingTwo = 0 ∧
      framedWindingProjectedNormSq oppositeWindingTwo = 2 :=
  berryHolonomy_does_not_determine_windingAction

/-- A flat perfect-link Wilson triangle has trace equal to the fiber dimension. -/
theorem flatWilsonTriangle_trace
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]
    (K : PerfectUnitaryLinkKernel I A) (i j k : I) :
    Matrix.trace
        (K.toNormalizedBlockKernel.link i j *
          K.toNormalizedBlockKernel.link j k *
          K.toNormalizedBlockKernel.link k i) = (Fintype.card A : ℂ) := by
  rw [K.triangle_holonomy]
  simp

/-- Relative Wilson loop comparing two connection slices. -/
abbrev relativeWilsonLoop
    {V A : Type*} {G : SimpleGraph V} [Group A]
    (c d : V → V → A) (x : V) (p : G.Walk x x) : A :=
  clockClosedHolonomyTransgression c d x p

/-- A connection slice has trivial relative Wilson loop against itself. -/
theorem relativeWilsonLoop_self
    {V A : Type*} {G : SimpleGraph V} [Group A]
    (c : V → V → A) (x : V) (p : G.Walk x x) :
    relativeWilsonLoop c c x p = 1 :=
  clockClosedHolonomyTransgression_self c x p

/-- Relative Wilson loops compose as a one-cocycle across connection slices. -/
theorem relativeWilsonLoop_cocycle
    {V A : Type*} {G : SimpleGraph V} [CommGroup A]
    (c d e : V → V → A) (x : V) (p : G.Walk x x) :
    relativeWilsonLoop c e x p =
      relativeWilsonLoop c d x p * relativeWilsonLoop d e x p :=
  clockClosedHolonomyTransgression_cocycle c d e x p

/-- Independent endpoint gauges at both slices leave relative Wilson holonomy unchanged. -/
theorem relativeWilsonLoop_gauge_invariant
    {V A : Type*} {G : SimpleGraph V} [CommGroup A]
    (gc gd : V → A) (c d : V → V → A) (x : V) (p : G.Walk x x) :
    relativeWilsonLoop
        (clockCalibrationGauge gc c) (clockCalibrationGauge gd d) x p =
      relativeWilsonLoop c d x p :=
  clockClosedHolonomyTransgression_gauge_invariant gc gd c d x p

/-! ## Polyakov loops -/

/-- Polyakov loop of a finite clock orbit: ordered link product through one full cycle. -/
abbrev polyakovLoop
    {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
    (T : Equiv.Perm S) (c : S → G) (s : S) : G :=
  groupCycleHolonomy T c s

/-- Local gauge change conjugates the Polyakov loop at its basepoint. -/
theorem polyakovLoop_gauge_covariant
    {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
    (T : Equiv.Perm S) (c h : S → G) (s : S) :
    polyakovLoop T (groupLedgerGauge T c h) s =
      h s * polyakovLoop T c s * (h s)⁻¹ :=
  groupCycleHolonomy_gauge T c h s

/-- Moving the temporal basepoint also changes the Polyakov loop only by conjugation. -/
theorem polyakovLoop_basepoint_covariant
    {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
    (T : Equiv.Perm S) (c : S → G) (j : ℕ) (s : S) :
    polyakovLoop T c ((T ^ j) s) =
      groupLedgerProduct T c j s * polyakovLoop T c s *
        (groupLedgerProduct T c j s)⁻¹ :=
  groupCycleHolonomy_pow_apply T c j s

/-- Every finite observer sees a periodic sequence of Polyakov-loop powers. -/
theorem polyakovLoop_finite_observer_periodic
    {G Q : Type*} [Group G] [Group Q] [Finite Q]
    (π : G →* Q) (H : G) :
    Function.Periodic (fun k : ℕ ↦ π (H ^ k)) (orderOf (π H)) :=
  finite_observer_holonomy_powers_periodic π H

/-- The finite-observer Polyakov period is genuinely positive. -/
theorem polyakovLoop_finite_observer_period_pos
    {G Q : Type*} [Group G] [Group Q] [Finite Q]
    (π : G →* Q) (H : G) :
    0 < orderOf (π H) :=
  finite_observer_holonomy_period_pos π H

/-! ## Finite Makeenko--Migdal-type plaquette equation -/

/-- Exponential parallel transport obeys the corpus's exact finite plaquette cross-ratio law. -/
theorem makeenkoMigdal_exp_plaquette
    (lam a s h : ℂ) :
    symmetricShapeCarrier Complex.exp lam a (s - h) /
        symmetricShapeCarrier Complex.exp lam a (s + h) =
      chiralShapeCarrier Complex.exp lam (a - lam * h) s /
        chiralShapeCarrier Complex.exp lam (a + lam * h) s :=
  symmetricSpectralShift_ratio_eq_chiralShapeShift_ratio
    Complex.exp lam a s h (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

/-! ## Homotopy Chern--Simons action -/

open AbelianDifferentialCharacter

/-- Abelian Chern--Simons transgression turns bulk curvature into boundary-loop holonomy. -/
theorem abelianChernSimons_boundary_loop_holonomy
    {SCnext SCn SCprev SCbelow TCnext TCn TCprev TCbelow V Q : Type*}
    [AddCommGroup SCnext] [AddCommGroup SCn]
    [AddCommGroup SCprev] [AddCommGroup SCbelow]
    [AddCommGroup TCnext] [AddCommGroup TCn]
    [AddCommGroup TCprev] [AddCommGroup TCbelow]
    [AddCommGroup V] [AddCommGroup Q]
    (S : ChainComplex SCnext SCn SCprev SCbelow)
    (T : ChainComplex TCnext TCn TCprev TCbelow)
    (X : TransgressionData S T)
    (h : DifferentialCharacter SCnext SCn SCprev SCbelow V Q S)
    (c : TCn) :
    X.character h (T.boundaryCycle c) =
      h.modLattice (X.curvatureIntegral h c) :=
  X.boundary_formula h c

/-- A transgressed Chern--Simons loop is the signed higher character of its swept cycle. -/
theorem abelianChernSimons_loop_swept_cycle
    {SCnext SCn SCprev SCbelow TCnext TCn TCprev TCbelow V Q : Type*}
    [AddCommGroup SCnext] [AddCommGroup SCn]
    [AddCommGroup SCprev] [AddCommGroup SCbelow]
    [AddCommGroup TCnext] [AddCommGroup TCn]
    [AddCommGroup TCprev] [AddCommGroup TCbelow]
    [AddCommGroup V] [AddCommGroup Q]
    (S : ChainComplex SCnext SCn SCprev SCbelow)
    (T : ChainComplex TCnext TCn TCprev TCbelow)
    (X : TransgressionData S T)
    (h : DifferentialCharacter SCnext SCn SCprev SCbelow V Q S)
    (z : T.cycles) :
    X.character h z = X.sign • h.character (X.sweepCycles z) :=
  X.loop_swept_cycle h z

@[simp] private theorem cyclicEll_zero
    {k L : Type*} [Field k] [CharZero k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicOperations (k := k) (L := L))
    (n : CyclicActionNoether.PositiveNat) :
    A.ell n (fun _ => 0) = 0 := by
  letI : Nonempty (Fin n.1) := ⟨⟨0, n.2⟩⟩
  change (A.ell n) (0 : ∀ _ : Fin n.1, L) = 0
  exact (A.ell n).map_zero

/-- Zero field has zero homotopy Chern--Simons action at every finite arity cutoff. -/
theorem chernSimons_zero_action
    {k L : Type*} [Field k] [CharZero k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicOperations (k := k) (L := L)) (N : ℕ) :
    CyclicActionNoether.actionPartial A N 0 = 0 := by
  simp [CyclicActionNoether.actionPartial, CyclicActionNoether.actionTerm]

/-- Zero field solves every finite Maurer--Cartan truncation. -/
theorem chernSimons_zero_maurerCartan
    {k L : Type*} [Field k] [CharZero k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicOperations (k := k) (L := L)) (N : ℕ) :
    CyclicActionNoether.mcPartial A N 0 = 0 := by
  rw [CyclicActionNoether.mcPartial]
  apply Finset.sum_eq_zero
  intro i _
  rw [CyclicActionNoether.mcTerm, cyclicEll_zero]
  exact smul_zero _

/-- Consequently zero field is a critical point of every finite Chern--Simons action. -/
theorem chernSimons_zero_critical
    {k L : Type*} [Field k] [CharZero k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicOperations (k := k) (L := L)) (N : ℕ) :
    CyclicActionNoether.IsCriticalPartial A N 0 :=
  (CyclicActionNoether.criticalPartial_iff_mcPartial_eq_zero A N 0).2
    (chernSimons_zero_maurerCartan A N)

/-- In every faithful Hamiltonian realization, zero field satisfies the classical master equation. -/
theorem chernSimons_zero_masterEquation
    {C H : Type*} [AddCommGroup C] [Module ℝ C]
    [AddCommGroup H] [Module ℝ H]
    (A : CyclicGaugeHolonomyMasterAction.HamiltonianCorrespondence (C := C) H) :
    A.poisson (A.hamiltonian 0) (A.hamiltonian 0) = 0 := by
  apply (A.masterEquation_iff_square_zero 0).2
  simp [CyclicAInfinityLaw.QGeometry.square]

end GaloisForLFunctions.HTGeometry.LoopGaugeApplications
