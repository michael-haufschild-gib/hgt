import GaloisForLFunctions.HTGeometry.ConstitutiveNonabelianRecoveryHolonomy
import GaloisForLFunctions.HTGeometry.ConstitutiveRecoveryCocycleHolonomy
import GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion
import GaloisForLFunctions.HTGeometry.ConstitutiveMarkedSymmetryQuotient
import GaloisForLFunctions.HTGeometry.ClockReadoutWitnesses
import GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy
import GaloisForLFunctions.HTGeometry.ActualityWallFlatness
import GaloisForLFunctions.HTGeometry.BooleanClockHolonomyUniversalityLaw
import GaloisForLFunctions.HTGeometry.ExponentialShiftHolonomyWitness
import GaloisForLFunctions.HTGeometry.FlatConnection
import GaloisForLFunctions.HTGeometry.FramedTwoBoundaryPhaseFibreHistorySeparation
import GaloisForLFunctions.HTGeometry.HorizonBogoliubovModeGaugeHolonomy
import GaloisForLFunctions.HTGeometry.HolonomyAbelian
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.AbelianDifferentialCharacter
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicGaugeHolonomyMasterAction
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection
import GaloisForLFunctions.HTGeometry.ParametricHolonomyTransgressionLaw
import GaloisForLFunctions.HTGeometry.PerfectUnitaryLinkFlatness
import GaloisForLFunctions.HTGeometry.RationalNonabelianContextAnomaly
import GaloisForLFunctions.HTGeometry.SymmetricChiralShapeLogDeriv
import GaloisForLFunctions.HTGeometry.TriangleHolonomySectorLaw
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.TriangleHolonomy
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
open Topology unitInterval
open scoped ComplexOrder Matrix
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
    {Idx A : Type*} [Fintype Idx] [Fintype A] [DecidableEq A]
    (K : PerfectUnitaryLinkKernel Idx A) (i j k : Idx) :
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

/-! ## Additive finite-orbit Polyakov holonomy -/

/-- Additive Polyakov loop over the global order of a finite permutation. -/
abbrev additivePolyakovLoop
    {S L : Type*} [Fintype S]
    [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    (T : Equiv.Perm S) (c : S → L) : S → L :=
  orderHolonomy T c

/-- Finite additive Polyakov holonomy is a complete invariant of ledger gauge equivalence. -/
theorem additivePolyakovLoop_gauge_complete
    {S L : Type*} [Fintype S]
    [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    (T : Equiv.Perm S) (c d : S → L) :
    (∃ h : S → L, d = ledgerGauge T c h) ↔
      additivePolyakovLoop T d = additivePolyakovLoop T c :=
  finite_livsic_orderHolonomy_iff T c d

/-- Vanishing additive Polyakov holonomy is exactly global gauge exactness. -/
theorem additivePolyakovLoop_zero_iff_coboundary
    {S L : Type*} [Fintype S]
    [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    (T : Equiv.Perm S) (c : S → L) :
    additivePolyakovLoop T c = 0 ↔
      ∃ h : S → L, c = fun s => h (T s) - h s :=
  (finite_livsic_coboundary_iff T c).symm

/-- Vanishing additive Polyakov holonomy is also exactly boundedness of every lifted history. -/
theorem additivePolyakovLoop_zero_iff_bounded
    {S L : Type*} [Fintype S]
    [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    (T : Equiv.Perm S) (c : S → L) :
    additivePolyakovLoop T c = 0 ↔ LedgerHistoriesBounded T c :=
  (ledgerHistoriesBounded_iff_zeroHolonomy T c).symm

/-! ## Order-two and rectangular Wilson transport -/

/-- Boolean graph transport is exactly the order-two XOR Wilson observable on every walk. -/
theorem orderTwoWilsonTransport
    {V : Type*} {G : SimpleGraph V} (c : V → V → Bool)
    {u v : V} (p : G.Walk u v) :
    clockWalkTransport (booleanClockCalibration c) p =
      booleanClockValue (walkXor c p) :=
  clockWalkTransport_booleanClockCalibration c p

/-- Boolean loop flatness and order-two clock-holonomy flatness are identical. -/
theorem orderTwoWilsonFlat_iff
    {V : Type*} {G : SimpleGraph V} (c : V → V → Bool) :
    BooleanEdgeFieldFlat G c ↔
      ClockCalibrationFlat G (booleanClockCalibration c) :=
  booleanEdgeFieldFlat_iff_clockCalibrationFlat c

/-- Exact wall coordinates force zero Wilson holonomy on every triangle. -/
theorem booleanWallWilsonTriangle_zero
    {X W : Type*} (side : W → X → Bool) (a b c : X) :
    (fun w => Bool.xor
      (Bool.xor
        (actualityWallProfile side a b w)
        (actualityWallProfile side b c w))
      (actualityWallProfile side c a w)) =
      fun _ => false :=
  actualityWallProfile_triangleHolonomy side a b c

/-- Single-site exponential shift gives an explicit nontrivial Polyakov matrix. -/
def expPolyakovLoop : Matrix Unit Unit ℂ := expLocalSystem ()

theorem expPolyakovLoop_ne_identity : expPolyakovLoop ≠ 1 := by
  intro h
  have hentry := congrFun (congrFun h ()) ()
  exact exp_one_ne_one (by simpa [expPolyakovLoop, expLocalSystem] using hentry)

/-- Multiplicative Wilson plaquette around an input-output rectangle. -/
abbrev rectangleWilsonLoop
    {X Y : Type*} (kernel : X → Y → ℂ)
    (x₁ x₂ : X) (y₁ y₂ : Y) : ℂ :=
  rectangleKernelHolonomy kernel x₁ x₂ y₁ y₂

/-- Arbitrary row and column exponential gauges cancel from rectangular Wilson holonomy. -/
theorem rectangleWilsonLoop_separableGauge
    {X Y : Type*} (phase : X → Y → ℂ)
    (row : X → ℂ) (column : Y → ℂ)
    (x₁ x₂ : X) (y₁ y₂ : Y) :
    rectangleWilsonLoop
        (exponentialKernel (fun x y => row x + phase x y + column y))
        x₁ x₂ y₁ y₂ =
      rectangleWilsonLoop (exponentialKernel phase) x₁ x₂ y₁ y₂ :=
  rectangleKernelHolonomy_exponential_separableGauge
    phase row column x₁ x₂ y₁ y₂

/-- Thermal rectangular Wilson holonomy exactly isolates the coupled surface-gravity phase. -/
theorem rectangleWilsonLoop_thermal_exact
    (inverseSurfaceGravity x₁ x₂ ℓ₁ ℓ₂ : ℂ) :
    rectangleWilsonLoop
        (exponentialKernel
          (thermalHorizonPhaseExponent inverseSurfaceGravity))
        x₁ x₂ ℓ₁ ℓ₂ =
      Complex.exp
        (-Complex.I * inverseSurfaceGravity *
          (x₁ - x₂) * (ℓ₁ - ℓ₂)) :=
  rectangleKernelHolonomy_thermalHorizon
    inverseSurfaceGravity x₁ x₂ ℓ₁ ℓ₂

/-! ## Noncommutative lattice plaquette curvature -/

/-- Correctly ordered noncommutative lattice plaquette curvature. -/
abbrev latticePlaquetteCurvature
    {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (p q : ι) : G :=
  GaloisForLFunctions.discreteCurvature act A p q

/-- A noncommutative lattice plaquette is trivial exactly when its connection coefficients obey
the ordered cocycle condition. -/
theorem latticePlaquette_flat_iff_cocycle
    {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (p q : ι) :
    latticePlaquetteCurvature act A p q = 1 ↔
      GaloisForLFunctions.cocycleCondition act A p q :=
  GaloisForLFunctions.discreteCurvature_eq_one_iff_cocycleCondition act A p q

/-- Reversing the middle noncommutative factor order changes the flatness law: the draft plaquette
tests a distinct twisted cocycle condition. -/
theorem latticePlaquette_draft_order_iff_twisted_cocycle
    {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (p q : ι) :
    GaloisForLFunctions.draftOrderCurvature act A p q = 1 ↔
      A p * act p (A q) = act q (A p) * A q :=
  GaloisForLFunctions.draftOrderCurvature_eq_one_iff_twisted_cocycle act A p q

/-! ## Further Wilson-loop realizations -/

/-- Closed graph Wilson transport is gauge-covariant by basepoint conjugation. -/
theorem graphWilsonLoop_gauge_conjugate
    {V A : Type*} {G : SimpleGraph V} [Group A]
    (g : V → A) (c : V → V → A) (u : V) (p : G.Walk u u) :
    clockWalkTransport (clockCalibrationGauge g c) p =
      (g u)⁻¹ * clockWalkTransport c p * g u :=
  clockClosedHolonomy_gauge_conjugate g c u p

/-- For an abelian gauge group, closed graph Wilson transport is literally gauge invariant. -/
theorem graphWilsonLoop_gauge_invariant
    {V A : Type*} {G : SimpleGraph V} [CommGroup A]
    (g : V → A) (c : V → V → A) (u : V) (p : G.Walk u u) :
    clockWalkTransport (clockCalibrationGauge g c) p =
      clockWalkTransport c p :=
  clockClosedHolonomy_gauge_invariant g c u p

/-- Every holonomy representation of an abelian source lattice has commuting Wilson image. -/
theorem abelianLatticeWilsonImage_commutes
    {Γ G : Type*} [CommGroup Γ] [Group G] (ρ : Γ →* G) :
    ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, Commute x y :=
  GaloisForLFunctions.monoidHom_range_commutative ρ

/-- Positive semidefiniteness of a scalar three-context kernel is exactly one cubic inequality in
the Wilson-triangle phase. -/
theorem wilsonTriangle_sector_posSemidef_iff (p : TriangleSectorDatum) :
    Matrix.PosSemidef p.matrix ↔
      (p.edge01 : ℝ) ^ 2 + (p.edge12 : ℝ) ^ 2 + (p.edge20 : ℝ) ^ 2 -
          2 * p.edge01 * p.edge12 * p.edge20 * p.phase.val.re ≤ 1 :=
  p.posSemidef_iff

/-- Heterogeneous triangle Wilson defect decomposes exactly into three transported edge defects. -/
theorem transportTriangleWilsonDefect_decomposition
    {R E₀ E₁ E₂ : Type*} [Ring R]
    [AddCommGroup E₀] [Module R E₀]
    [AddCommGroup E₁] [Module R E₁]
    [AddCommGroup E₂] [Module R E₂]
    (T₀₁ : E₀ →ₗ[R] E₁) (T₁₂ : E₁ →ₗ[R] E₂) (T₂₀ : E₂ →ₗ[R] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) :
    T₂₀ (T₁₂ (T₀₁ x₀)) - x₀ =
      T₂₀ (T₁₂ (T₀₁ x₀ - x₁)) + T₂₀ (T₁₂ x₁ - x₂) + (T₂₀ x₂ - x₀) :=
  _root_.HTGeometry.ConstraintRelativity.cyclicDefect_eq T₀₁ T₁₂ T₂₀ x₀ x₁ x₂

/-- The once-wound quotient response is an explicit closed non-null-homotopic Wilson loop. -/
theorem responseWilsonLoop_once_nontrivial :
    ¬ (responseLoop 1).HomotopicRel
      (ContinuousMap.const I (Circle.exp 0)) {0, 1} :=
  responseLoop_not_nullhomotopicRel one_ne_zero

/-- Logarithmic derivative of the determinant Wilson history recovers its exact integer winding. -/
theorem determinantWilson_winding_exact (N : ℤ) :
    (2 * Real.pi * Complex.I)⁻¹ *
        ∫ t in (0 : ℝ)..1,
          (loopHistory N t)⁻¹ * deriv (loopHistory N) t =
      (N : ℂ) :=
  winding_number_eq N

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

/-- Infinitesimal cross equation: chiral spectral response equals scaled symmetric shape response
for exponential transport. -/
theorem makeenkoMigdal_exp_differential_cross
    (lam a s : ℂ) :
    logDeriv (fun z => chiralShapeCarrier Complex.exp lam a z) s =
      lam * logDeriv (fun b => symmetricShapeCarrier Complex.exp lam b s) a :=
  chiralSpectral_logDeriv_eq_scale_mul_symmetricShape_logDeriv
    Complex.exp lam a s Complex.differentiableAt_exp Complex.differentiableAt_exp
      (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

/-- Reciprocal infinitesimal cross equation for the same finite exponential plaquette. -/
theorem makeenkoMigdal_exp_reciprocal_differential_cross
    (lam a s : ℂ) :
    logDeriv (fun z => symmetricShapeCarrier Complex.exp lam a z) s =
      lam * logDeriv (fun b => chiralShapeCarrier Complex.exp lam b s) a :=
  symmetricSpectral_logDeriv_eq_scale_mul_chiralShape_logDeriv
    Complex.exp lam a s Complex.differentiableAt_exp Complex.differentiableAt_exp
      (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

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

/-- Flat ambiguity of an Abelian Chern--Simons character transgresses exactly to flat ambiguity of
its loop holonomy. -/
theorem abelianChernSimons_flat_difference_transgresses
    {SCnext SCn SCprev SCbelow TCnext TCn TCprev TCbelow V Q : Type*}
    [AddCommGroup SCnext] [AddCommGroup SCn]
    [AddCommGroup SCprev] [AddCommGroup SCbelow]
    [AddCommGroup TCnext] [AddCommGroup TCn]
    [AddCommGroup TCprev] [AddCommGroup TCbelow]
    [AddCommGroup V] [AddCommGroup Q]
    (S : ChainComplex SCnext SCn SCprev SCbelow)
    (T : ChainComplex TCnext TCn TCprev TCbelow)
    (X : TransgressionData S T)
    (h h' : DifferentialCharacter SCnext SCn SCprev SCbelow V Q S)
    (z : T.cycles) :
    X.character h z - X.character h' z =
      X.sign • (h.character (X.sweepCycles z) - h'.character (X.sweepCycles z)) :=
  X.flat_difference_transgresses h h' z

/-- First variation of every finite homotopy Chern--Simons action is its Maurer--Cartan equation
paired with the variation. -/
theorem chernSimons_firstVariation_eq_maurerCartan
    {k L : Type*} [Field k] [CharZero k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicOperations (k := k) (L := L))
    (N : ℕ) (α η : L) :
    CyclicActionNoether.firstVariationPartial A N α η =
      A.pairing η (CyclicActionNoether.mcPartial A N α) :=
  CyclicActionNoether.firstVariationPartial_eq_pairing_mcPartial A N α η

/-- Nondegeneracy identifies finite Chern--Simons critical points with Maurer--Cartan solutions. -/
theorem chernSimons_critical_iff_maurerCartan
    {k L : Type*} [Field k] [CharZero k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicOperations (k := k) (L := L))
    (N : ℕ) (α : L) :
    CyclicActionNoether.IsCriticalPartial A N α ↔
      CyclicActionNoether.mcPartial A N α = 0 :=
  CyclicActionNoether.criticalPartial_iff_mcPartial_eq_zero A N α

/-- Every infinitesimal gauge direction annihilates the Chern--Simons variational form off shell. -/
theorem chernSimons_infinitesimal_gauge_invariance
    {k L : Type*} [Field k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicMaurerCartanLaw (k := k) (L := L))
    (α ε : L) :
    CyclicActionNoether.variationalForm A α
      (CyclicActionNoether.gaugeVariation A α ε) = 0 :=
  CyclicActionNoether.infinitesimal_gauge_invariance A α ε

/-- Cyclic coordinate/gauge equivalences preserve every finite Chern--Simons action quotient. -/
theorem chernSimons_action_gauge_natural
    {L M : Type*} [AddCommGroup L] [Module ℝ L]
    [AddCommGroup M] [Module ℝ M]
    {A : CyclicActionNoether.CyclicOperations (k := ℝ) (L := L)}
    {B : CyclicActionNoether.CyclicOperations (k := ℝ) (L := M)}
    (F : CyclicActionNoether.CyclicOperationsEquiv A B) (N : ℕ) (α : L) :
    CyclicActionNoether.actionPartial B N (F.map α) =
      CyclicActionNoether.actionPartial A N α :=
  CyclicGaugeHolonomyMasterAction.actionPartial_natural F N α

/-- BV classical master equation is exactly square-zero of the source coderivation. -/
theorem chernSimons_masterEquation_iff_square_zero
    {C H : Type*} [AddCommGroup C] [Module ℝ C]
    [AddCommGroup H] [Module ℝ H]
    (A : CyclicGaugeHolonomyMasterAction.HamiltonianCorrespondence (C := C) H)
    (Q : CyclicGaugeHolonomyMasterAction.End (C := C)) :
    A.poisson (A.hamiltonian Q) (A.hamiltonian Q) = 0 ↔
      CyclicAInfinityLaw.QGeometry.square Q = 0 :=
  A.masterEquation_iff_square_zero Q

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
