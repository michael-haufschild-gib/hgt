import GaloisForLFunctions.HTGeometry.CaratheodoryFejerLineReality
import GaloisForLFunctions.HTGeometry.HardyClosureZeroFree
import GaloisForLFunctions.RHTower.ConstrainedProlateFullDistanceCCM
import GaloisForLFunctions.RHTower.LiFiniteCriterionFrontier
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import GaloisForLFunctions.RHTower.SalemFermiModeCriterion
import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler
import GaloisForLFunctions.RHTower.SuzukiProjectiveDefectBoundary
import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality
import GaloisForLFunctions.RHTower.SuzukiHerglotzBoundaryStates
import GaloisForLFunctions.RHTower.SuzukiDonoghueSpectralMeasure
import GaloisForLFunctions.RHTower.SuzukiFiniteShiftNonClock
import GaloisForLFunctions.RHTower.SuzukiPrimeTangentTomography
import GaloisForLFunctions.RHTower.SuzukiPrimeClockAtomVelocity
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedLocalThreePoint
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedFourthJetCuspClosure
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedUniformCoalescedSquare
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFullFormula
import GaloisForLFunctions.RHTower.XiHedenmalmBoundaryValueProblem
import GaloisForLFunctions.RHTower.XiHedenmalmSourceCapstone
import GaloisForLFunctions.RHTower.XiLaguerrePolya
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# Riemann-hypothesis research frontier through 2026

This is the typed endpoint ledger for the live RH routes in the primary literature through
2026-07-21.  It records mathematical walls, not evidence and not a claimed proof.

## Spectral routes

* Connes--van Suijlekom (`arXiv:2511.23257`) prove real zeros for the Fourier transform of an
  isolated simple even ground state of a lower-bounded convolution operator.  Connes's 2026
  survey (`arXiv:2602.04022`) and the zeta-spectral-triple construction (`arXiv:2511.22755`) leave
  the actual ground-state convergence to Xi open.  The finite Caratheodory--Fejer/Cayley reality
  connector is `finiteOPUCParaorthogonal_lineCayley_root_im_eq_zero`; the exact infinite wall is
  `ConnesXiGroundStateLimitWall` below.

* Hedenmalm (`arXiv:2606.17494`) gives an explicit theta boundary-value problem whose spectral
  parameters are exactly Xi zeros.  `XiHedenmalmBoundaryValueProblem` formalizes that equivalence.
  It does not make the parameters real.  The exact positive-form wall is
  `HedenmalmXiPositiveFormWall`, proved below equivalent to RH on the complete Xi Weil carrier.

* Gershon's revised 2026 theta-kernel log-concavity preprint and Pierson's computation-dependent
  preprint stop at an order-two condition.  The linked public Lean artifact axiomatizes its
  perturbation step and concludes `True`, so it is not a proof.  The independent source-level
  repair in `ThetaCuspKernelLogConcavity` proves strict global log-concavity, the multiplicative
  midpoint law, and positive semidefiniteness of every two-node center-mixed matrix.  The next
  source-specific layer proves radial monotonicity and an unconditional far-separated three-node
  chamber.  `exists_thetaCuspCenterMixedThreePointMatrix_posSemidef_of_large_gap` now closes the
  entire cofinal order-three region: every packet with at least one sufficiently large adjacent
  gap is positive semidefinite.  The independent fourth-order source theorem
  `thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty` now proves the strict reflected-source
  Hankel law, and its positive quadratic-form transfer proves
  `thetaCuspCenterMixedDensity_fourthHankel_pos`.  Consequently
  `exists_thetaCuspCenterMixed_coalescedCusp_posDef` opens an unconditional positive-definite
  nested cusp at the coalesced corner.  The sixth-jet determinant identity now strengthens this
  to `exists_thetaCuspCenterMixed_raywiseCoalescedCone_posDef`: every fixed positive aspect-ratio
  ray through the corner eventually enters the strict chamber.  The mixed sixth-jet Hessian law
  strengthens this again to `exists_thetaCuspCenterMixed_uniformCoalescedSquare_posDef`: one
  radius works for both positive gaps and hence closes the entire small--small corner, uniformly
  even as the aspect ratio tends to either axis.  The exact remaining order-three wall lies in
  the bounded noncoalesced annulus between that square and the far chamber, inside the compact
  two-gap core from
  `exists_thetaCuspCenterMixedThreePointMatrix_compactCore_iff`, outside the proved far chamber
  and uniform coalesced square.  All-node positive-definiteness remains the RH-equivalent wall.

* Suzuki (`arXiv:2606.09096`) constructs finite-interval self-adjoint extensions and entire
  characteristic functions with only real zeros.  `SuzukiFiniteApertureHermiteBiehler` extracts
  the full-angle consequence: a finite-aperture Hermite--Biehler function, a Schur/Livšic quotient,
  its canonical Herglotz normalization `m(i)=i`, the aperture-independent Schwarz majorant
  `|Theta(z)| <= |(z-i)/(z+i)|`, unconditional local Montel subsequences, and a two-angle quotient
  in which common entire gauges cancel.  The paper's ordinary entire-compact
  target `z^2 xi/xi'` has unconditional real poles,
  so the old zero-transfer predicate below is retained only as a legacy impossible-premise
  connector.  `SuzukiProjectiveDefectBoundary` proves the positive survivor of the failed
  arbitrary-shift route: common source scales cancel, the two-defect Gram state splits exactly
  into even/odd energy weights, parity uniquely selects the odd/even extension phases, and the
  universal free carriers converge locally uniformly to zero at the far-negative projective
  boundary.  `SuzukiGroundEdgeCayleyUniversality` closes the opposite-end no-go: if the shift
  approaches a simple even ground state faster than odd spectral mass leaks through the first
  parity gap, the defect angle tends to one and every locally uniform carrier limit is the
  universal Cayley map `(z-i)/(z+i)`.  The contrapositive theorem
  `suzukiGroundEdge_nonCayley_forces_leakage_not_tendsto_zero` records the positive survivor as an
  exact scale-selection law.  `SuzukiHerglotzBoundaryStates` now identifies the far-negative
  Herglotz state exactly as `coth(a) tan(a z)`, proves its half-integer clock singular set, and
  transports free Schur collapse to locally uniform Herglotz convergence `m_a -> i`.  Together
  with the already formalized opposite identity `CayleyInv((z-i)/(z+i))=z`, this separates two
  exact data-erasure mechanisms: clock-spectrum homogenization to the constant Herglotz state and
  ground-edge escape to the linear point at infinity.  `SuzukiDonoghueSpectralMeasure` identifies
  the exact finite-aperture measure interface: the canonical Herglotz function is
  `-i W_1/W_{-1}`, its Donoghue kernel has zero linear term, and every simple Clark atom has weight
  reciprocal to boundary phase speed.  On paper the full source measure is `(1+t^2)` times the
  spectral probability of the normalized positive deficiency vector for the even extension, with
  atom weight `(1+x^2)|F(-x)|^2/(||v_+||_T^2 ||v_x||_T^2)`.  The live wall is therefore concrete
  and measure-level.  `SuzukiFiniteShiftNonClock` proves that no finite admissible shift is the
  free clock and that the far-negative source path has a nonzero first projective tangent.
  `SuzukiPrimeTangentTomography` strengthens this from nonvanishing to exact arithmetic
  completeness: nonresonant Bohr demodulation of the finite tangent packet recovers each
  von-Mangoldt coefficient, and its normalized limit is exactly `Λ(m)`.  The paper-level source
  theorem derives that packet from Suzuki's distribution formula and supplies cofinal
  nonresonant apertures.  `SuzukiPrimeClockAtomVelocity` now closes the first-order transfer to
  spectral support: the `m`th prime step moves the `k`th free Donoghue pole by
  `Λ(m)/(a*sqrt(m)) * sin(((k+1/2)*pi/a)*log(m))`.  The reflected source geometry and pole
  normalization cancel exactly, leaving the critical explicit-formula weight `Λ(m)/sqrt(m)`, and
  nonresonant demodulation of the atom-velocity packet again recovers `Λ(m)`.  Thus arithmetic
  survival and its infinitesimal transfer into divisor motion are no longer the wall.  The live
  problem is nonlinear integration: choose one intrinsic finite-shift path, retain these critical
  modes while proving tight infinite atomic survival, then identify support and weights with the
  global Xi/de Branges divisor.  The screw-function Hilbert space and its unbounded differential
  operators are not yet present in Lean.

* The constrained-prolate/CCM branch has discharged the abstract secular-vector and Bessel
  algebra.  `ccm_tendsto_min_norm_lp_normalize_sub_twoModeSeed` still takes the two concrete
  prolate-to-Hermite coordinate limits; those limits are the current operator-asymptotic wall.

## Positivity, Li, approximation, and explicit-formula routes

* The complete Weil-form wall is exactly
  `riemannHypothesis_iff_xiWeilPolarization_nonneg`.  The 2026 finite Guinand--Weil work
  (`arXiv:2607.02828`) is covered more strongly at sharp rectangular regularity by
  `xiWeilPolarization_rectangular_eq_prime_add_arch` and its source consequences; finite
  calculations are not imported here.

* Li's finite triangular algebra is closed in `LiFiniteCriterionFrontier`.  The infinite
  canonical zero summation and the Bombieri--Lagarias positivity equivalence remain an analytic
  library wall; no finite packet is identified with the global Li sequence.

* Polson's July 2026 Thorin/GGC preprint reports unconditional infinite divisibility and Thorin
  density positivity for the reciprocal completed-zeta ratio only in `Re s > 1`.  At the critical
  seam its Thorin/complete-monotonicity/Stieltjes--Pick/Li chain is RH-equivalent, not a proof of
  the missing positivity.  The project retains the source-pure construction problem in
  `completed-seam-thorin-subordinator-rh.md`; no critical-seam Thorin measure is asserted here.

* The 2026 Hardy and Colombeau--Beurling criteria (`arXiv:2606.16097`, `arXiv:2606.22562`) are
  closure reformulations.  `HardyClosureZeroFree` proves their common continuous-evaluation
  obstruction.  The concrete half-plane Hardy carrier and the damped Colombeau nets remain to be
  represented.

* The 2026 theta-infinity theorem (`arXiv:2605.24363`) gives zero-free regions, and a family
  quasi-RH, from suitably bounded mollified second moments at every polynomial mollifier length.
  The arbitrary-length estimate is the open premise; the concrete automorphic mollifiers and
  moments are not yet represented.  It is therefore recorded as a live analytic wall, not as an
  established RH conclusion.

* The 2026 Salem specialization (`arXiv:2604.15396`) is formalized in
  `SalemFermiModeCriterion`: the evaluated Fermi--Dirac transform of a pure Mellin mode vanishes
  at every positive scale exactly at a zeta zero, and `SalemFermiModeExclusion` is proved
  equivalent to RH.  The separate improper-integral evaluation remains an analytic-library wall.

* The 2026 discrete Mobius--Laplace route (`arXiv:2607.09797`) is represented by the absolutely
  convergent and positive-axis continuous `mobiusDiscreteLaplaceTransform`, its exponential tail,
  the exact Mellin identity on `Re s > 1`, and the half-power decay premise.  The source's full
  one-way implication is compiled as
  `mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis`: the decay bound makes the Mellin
  transform analytic on `Re s > 1/2`, and the identity theorem propagates the regularized
  `Gamma/zeta` identity.  The decay premise itself remains the research wall.  No simple-zero
  hypothesis or conditional converse is imported.

* The 2026 nonlinear-deficiency identity (`arXiv:2604.16530`) concerns approximation of zeta
  values in the absolutely convergent half-plane.  The random-hyperfunction/CUE comparison
  (`arXiv:2606.07312`) concerns value statistics.  The Guth--Maynard zero-density bound
  (`arXiv:2405.20552`), highlighted in the 2026 exposition `arXiv:2607.04632`, bounds but does not
  eliminate off-line zeros.  These are unconditional frontier results, but none supplies a new
  implication discharging an RH wall.

* The remaining 2026 criterion refinements do not move their inherited walls.  The parabolic
  Mellin transform (`arXiv:2602.17007`) supplies new integral reformulations; the Lagarias paper
  (`arXiv:2602.15905`) reduces a least counterexample to a superabundant integer; the Young-lattice
  construction (`arXiv:2601.22413`) transports a sum-of-divisors equivalence; and the harmonic
  contour formulation (`arXiv:2605.30767`) restates off-line zeros as intersections for a pair of
  harmonic functions.  Each remains an exact equivalent criterion or reduction, not a proof of
  its global open condition.

* Zhao's positive-proportion large/small zero-gap theorem (`arXiv:2603.17334`) is unconditional
  zero statistics; Inoue's sharper small-gap constant (`arXiv:2604.05733`) assumes RH.  The
  probabilistic Mobius partial-sum route (`arXiv:2604.23517`) assumes independence statements.
  None excludes every off-critical zero, so none is promoted to an RH connector.

* Gaussian--Perron, Riccati--Gamma, de Bruijn--Newman, Jensen-polynomial, and Berry--Keating
  papers give conditional localization, finite or computational statements, or reviews.  They do
  not discharge any wall above.  Computational certificates and statements assuming RH or simple
  zeros are deliberately not promoted to unconditional declarations.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- The exact remaining Connes / zeta-spectral-triple limit statement in function-theoretic form:
there is a cofinal sequence of entire real-zero ground-state transforms converging locally
uniformly to centered Xi.  Finite real-zero localization is already supplied by the
Caratheodory--Fejer theorem; construction of this convergent sequence is the wall. -/
def ConnesXiGroundStateLimitWall : Prop :=
  ∃ F : ℕ → ℂ → ℂ,
    TendstoLocallyUniformly F XiC atTop ∧
      (∀ᶠ n in atTop, Differentiable ℂ (F n)) ∧
      (∀ᶠ n in atTop, ∀ z : ℂ, F n z = 0 → z.im = 0)

/-- Closing the Connes ground-state limit wall proves RH.  This theorem is assumption-free as a
Lean declaration: its premise is the explicitly named open mathematical statement above. -/
theorem connesXiGroundStateLimitWall_implies_riemannHypothesis
    (h : ConnesXiGroundStateLimitWall) : RiemannHypothesis := by
  rcases h with ⟨F, hconv, hentire, hreal⟩
  exact riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants
    hconv hentire hreal

/-- The complete positive Xi Weil form singled out by the Hedenmalm/Weil spectral route. -/
def HedenmalmXiPositiveFormWall : Prop :=
  ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
    0 ≤ (xiWeilPolarization F F).re

/-- The positive-form wall is exactly RH, not an already-discharged positivity theorem. -/
theorem hedenmalmXiPositiveFormWall_iff_riemannHypothesis :
    HedenmalmXiPositiveFormWall ↔ RiemannHypothesis := by
  simpa only [HedenmalmXiPositiveFormWall] using
    riemannHypothesis_iff_xiWeilPolarization_nonneg.symm

/-- Suzuki's conjectural centered limit target, up to the harmless nonzero constants introduced
by the change from `xi'(1/2-iz)` to `deriv XiC z`.  Its zeros include every centered Xi zero. -/
def suzukiXiCharacteristicTarget (z : ℂ) : ℂ :=
  z ^ 2 * XiC z / deriv XiC z

/-- Every centered Xi zero is a zero of Suzuki's quotient target in Lean's totalized field. -/
theorem suzukiXiCharacteristicTarget_eq_zero_of_XiC_eq_zero
    {z : ℂ} (hz : XiC z = 0) :
    suzukiXiCharacteristicTarget z = 0 := by
  simp [suzukiXiCharacteristicTarget, hz]

/-- **Legacy impossible-premise connector.**  This is the ordinary entire-compact reading of
Suzuki's displayed Corollary 1.6 limit.  It is retained for API compatibility and to record the
zero-transfer logic, but it is no longer the current research wall: the displayed target has
unconditional real poles and therefore cannot satisfy the `AnalyticOnNhd ... univ` clause.  The
pole-compatible finite-aperture replacement is the Livšic/two-angle carrier formalized in
`SuzukiFiniteApertureHermiteBiehler`. -/
def SuzukiXiCharacteristicLimitWall : Prop :=
  ∃ W : ℕ → ℂ → ℂ,
    TendstoLocallyUniformly W suzukiXiCharacteristicTarget atTop ∧
      (∀ᶠ n in atTop, Differentiable ℂ (W n)) ∧
      (∀ᶠ n in atTop, ∀ z : ℂ, W n z = 0 → z.im = 0) ∧
      AnalyticOnNhd ℂ suzukiXiCharacteristicTarget Set.univ ∧
      ∃ a : ℂ, suzukiXiCharacteristicTarget a ≠ 0

/-- The legacy ordinary entire-compact premise implies RH by the closed zero-locus mechanism.  This
logical implication does not make the premise viable; the current Suzuki wall is meromorphic. -/
theorem suzukiXiCharacteristicLimitWall_implies_riemannHypothesis
    (h : SuzukiXiCharacteristicLimitWall) : RiemannHypothesis := by
  rcases h with ⟨W, hconv, hentire, hreal, htarget, a, ha⟩
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hzero : suzukiXiCharacteristicTarget (xiSpectralPoint q) = 0 :=
    suzukiXiCharacteristicTarget_eq_zero_of_XiC_eq_zero
      (XiC_xiSpectralPoint_eq_zero q)
  have him : (xiSpectralPoint q).im = 0 :=
    zero_mem_closed_of_tendstoLocallyUniformly
      hconv htarget hentire
      (isClosed_eq Complex.continuous_im continuous_const)
      hreal ha hzero
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simp [him]

end

end RHTower
