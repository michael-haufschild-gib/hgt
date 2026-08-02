# Transverse information under singular descent

Status: PAPER THEOREM AND CONSOLIDATED LEAN CAPSTONE PROVED; RH-BEARING ADMISSION OPEN.  
Novelty: `[NOVELTY UNVERIFIED]` (external comparison intentionally deferred).  
Owner manuscript: `docs/drafts/pipeline/4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`.

## Research question

What single law explains the common success and failure of the shell, Möbius--theta,
Hellinger--Gamma, Deninger--Meyer, Hedenmalm, Wold--Poisson, Sonin--Calkin, Ward, Rees,
and Green constructions, and what theorem is still genuinely missing for RH?

## Universal law

Let `q : E -> B` be a descent and let `N = ker q` be its transverse information.
Three operations govern every construction in scope.

1. **Algebraic augmentation.** For a factored covariant transport `X -r-> Y -j-> Z`,
   the composite defect is the codiagonal of the two transported factor defects.  Its
   invisible sector is exactly the antidiagonal.  Once codiagonal is applied, no
   postprocessing recovers a nonzero antidiagonal class.
2. **Cofinal completion.** If resolved source differences converge to zero, every
   uniformly regular single-valued observer erases them.  A closed linear relation that
   nevertheless retains a dense family of output limits acquires full vertical fibre and
   equals its domain times the whole target.  Thus regular deterministic descent erases
   transverse information, while closed relational retention becomes uninformative.
3. **Strict graded escape.** The transverse class can survive only before the limiting
   descent, in a normal/projective or associated-graded object.  For the complete
   prime-normal source this is sharp: a closed gradewise-proper carrier retaining all
   packets exists if and only if every grade has finite exponent fibre.  Infinite fibres
   force saturation; finite fibres are the exact escape boundary.
4. **Positive admission.** If a nonzero functional transforms by the character
   `exp(c z)`, finite invariant domination exists exactly when `Re z = 0`.  No norm,
   seminorm, topology, or common gauge is needed.  Thus positive finite admission is the
   exact neutral-sector selector.

These are not three analogies.  They are three stages of one conservation statement:

> A nonzero transverse class cannot be created downstream.  Before descent it must be
> carried in a strict, locally finite associated grade; under regular descent it is erased;
> under closed ungraded relational descent it reappears only as maximal vertical
> multivaluedness; under positive finite invariant admission it survives exactly at zero
> real modular rate.

## Paper proof

### Algebraic part

Insert and subtract `j B r`:

`A j r - j r C = (A j - j B) r + j (B r - r C)`.

The codiagonal `Σ(u,v)=u+v` has kernel `{(z,-z)}`.  Hence composite covariance sees only
the quotient by the antidiagonal.  Disjoint retained grades make codiagonal conservative.

### Topological part

For a closed linear relation `R subset X x Y`, if `(x_n,y_n) in R`, `x_n -> 0`, and
`y_n -> y`, closedness gives `(0,y) in R`; hence `y in mul R`.  If such limits span a
dense subspace of `Y`, closedness of `mul R` gives `mul R=Y`.  Linearity then gives
`R=dom(R) x Y`.  Thus a closed relation retaining a dense normal family transports no
output information.

For a uniformly Lipschitz family `T_n`, `||T_n x_n-T_n x'_n|| <= L ||x_n-x'_n||`.
If the inputs coalesce, every fixed output separation tends to zero.  Retention of a
nonzero normal limit therefore forces inverse conditioning to diverge.

### Sharp graded part

For prime-normal packets `P_j=(p_i^{-(j+1)})_i in ell^2`, every infinite subsequence
has dense linear span, even after arbitrary affine centering.  Hence any closed relation
retaining an infinite exponent fibre saturates that grade.  If all fibres are infinite,
the entire graded target becomes vertical.  Conversely, finite fibres span finite-
dimensional closed proper grade carriers.  Therefore a closed gradewise-proper carrier
exists exactly when every grade fibre is finite.

### Projective normal survivor

The complete source vectors cofinally collapse in their canonical `ell^1` topology, but
the normalized two-clock projective chart converges to an injective two-prime spectral
coordinate.  Its inverse Lipschitz constants diverge.  This is the canonical survivor
predicted by the law: the spectral coordinate lives in the normal cone, not in the
ordinary completion.

## Arithmetic consequences already proved

1. The positive hypertranscendental shell frame replicates the common completed-zeta
   divisor longitudinally, while horizontal position is carried only by labeled cofinal
   transfer.  One scale is noninjective; two irrational scales are injective.
2. Internal Möbius--theta promotion occurs before spectral selection and lands in every
   Xi derivative.  At a zero of multiplicity `m`, the local `m x m` jet matrix is
   nonsingular.
3. Literal all-weight Meyer cohomology carries every actual Xi divisor with full analytic
   multiplicity.  Every finite family of multiplicity-bounded Xi jets is a surjective
   quotient.
4. The unrestricted product of all Xi jets is not source-admissible.  Along an actual
   escaping divisor sequence, every literal Meyer Mellin transform tends to zero.
5. Finite packet synthesis is possible, but any cofinal unit synthesis is singular at
   every positive differential order.
6. Pointwise nonvanishing at every Xi divisor does not imply source fidelity: a fixed
   regular rank-one comparison can be nonzero at every divisor point while annihilating
   every reflection displacement.
7. Paugam reciprocal descent and the full complementary-jet alternating form exist on
   actual Meyer cohomology and obey exact weight one under dilation.
8. The positive reciprocal Calderón cup--Hodge form lives on the local regulator quotient,
   not on middle cohomology: its pullback to every genuine global middle cycle is zero.
9. The Green composite is covariant unconditionally because its two internal defects are
   exact antidiagonal partners.  The resolved pair vanishes globally exactly when RH holds.
10. The canonical half-density source seminorm `p(g)=∫ exp(t/2)|g(t)|dt` descends to
    literal Meyer cohomology, is exactly invariant under centered dilation, and yields a
    Hausdorff Banach completion with surjective isometric flow.  An actual Xi evaluation is
    bounded for this quotient seminorm exactly when its zero is on the critical line.
11. The target-free logarithmic Gaussian `exp(-πt²)` is an all-weight Meyer source with
    Mellin transform `exp(s²/(4π))`, hence is nonzero under every actual Xi
    zeroth-evaluation.  Boundedness of all its centered evaluation orbits is equivalent to
    RH; no completion, topology, or zero-dependent source selection is required.
12. Burnol right-strip quotient kernels have dense span, making the Berezin diagonal
    faithful on positive quotient-supported operators.  Finite bilateral holonomy reads
    the same rate as `2 sinh(log(r) * kappa)`.

## Corrected frontier

The old “common physical-jet/Hellinger-incidence graph bridge” is not the terminal frontier.
The literal Meyer quotient already supplies a source-native cohomology, reciprocal flow,
full finite Xi jet packets, and weight-one generalized Paugam pairings.

The old completion problem is solved more strongly and more canonically than postulated:
the half-density quotient seminorm and its surjective isometric Banach completion exist
unconditionally.  Faithfulness of the map from algebraic Meyer cohomology is not proved,
but is not needed for the exact continuity selector.

The literal minimal remaining RH theorem is the **Gaussian orbit estimate**

`∀ rho, ∃ C_rho < ∞, ∀ c, |E_{rho,0}(V_c u_*)| ≤ C_rho`,

where `u_*=[e^{-πt²}]` is target-free and already proved nonzero under every actual Xi
evaluation.  A stronger source-geometric target is the **canonical half-density arithmetic
admission estimate**

`∀ rho, ∃ C_rho < ∞, ∀ u, |E_{rho,0}(u)| ≤ C_rho pbar_{1/2}(u)`.

Both exact selectors prove their missing boundedness statements equivalent to RH.  They must
therefore be obtained from a new arithmetic identity or inequality on the co-Poisson/Gamma
source, not from generic functional analysis or a topology chosen after inspecting the zeros.

Global spectral synthesis remains a stronger problem: vanishing of every
multiplicity-bounded Xi jet would have to force a class into the literal Poisson boundary.
It is not logically required for zero exclusion.

## Antagonist audit

- The algebraic identity alone is elementary and not paper-level significance.
- The significant result is the sharp arithmetic realization: ordinary complete source
  topology collapses, projective normal tomography remains injective, regular comparisons
  erase reflection, closed infinite-fibre relations become maximally vertical, and finite
  grade fibres are exactly the proper-carrier boundary.
- No RH proof is claimed.  Positive isometric source geometry is proved; universal
  half-density admission and global spectral synthesis remain unproved.
- No local positivity result may be presented as progress on zero exclusion unless it lands
  on genuine middle cycles; the present local Calderón positivity provably does not.
- No pointwise-nonzero comparison may be called faithful; an explicit counterexample exists.
- External novelty and literature priority remain unverified by instruction.

## Formal evidence map

- `HTGeometry/ResolvedDefectConservationLaw.lean`
- `RHTower/DeningerGreenResolvedDefectLaw.lean`
- `RHTower/CompleteResolutionCofinalConditioningLaw.lean`
- `RHTower/CompleteResolutionPrimeNormalHilbertSaturation.lean`
- `RHTower/CompleteResolutionPrimeNormalFiniteFibreGrading.lean`
- `RHTower/HypertranscendentalDivisorInformationLocalizationLaw.lean`
- `RHTower/MobiusThetaInternalJetPhysicalGraph.lean`
- `RHTower/MobiusThetaInternalJetSourceLocalSpanning.lean`
- `RHTower/DeningerMeyerXiSpectralInclusion.lean`
- `RHTower/DeningerMeyerFiniteXiJetPacket.lean`
- `RHTower/DeningerMeyerFullXiJetAdmissionBoundary.lean`
- `RHTower/DeningerMeyerXiCofinalSynthesisSingularity.lean`
- `RHTower/DeningerMeyerPointwiseXiComparisonSharpness.lean`
- `RHTower/DeningerMeyerPaugamGeneralizedJetPairing.lean`
- `RHTower/DeningerMeyerPaugamGradingObstruction.lean`
- `RHTower/DeningerMeyerInvariantEvaluationGaugeFrontier.lean`
- `RHTower/TransverseInformationInvariantGaugeDichotomy.lean`
- `RHTower/DeningerMeyerHalfDensityL1Completion.lean`
- `RHTower/DeningerMeyerLogGaussianUniversalOrbitCriterion.lean`
- `RHTower/BurnolCoPoissonBerezinFaithful.lean`
- `RHTower/BurnolCoPoissonBerezinReflection.lean`
