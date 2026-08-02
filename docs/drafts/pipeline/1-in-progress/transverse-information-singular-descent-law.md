# Transverse information under singular descent

Status: PAPER THEOREM PROVED FROM FORMALIZED CORPUS; CONSOLIDATED LEAN CAPSTONE PENDING.  
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

These are not three analogies.  They are three stages of one conservation statement:

> A nonzero transverse class cannot be created downstream.  Before descent it must be
> carried in a strict, locally finite associated grade; under regular descent it is erased;
> under closed ungraded relational descent it reappears only as maximal vertical
> multivaluedness.

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

## Corrected frontier

The old “common physical-jet/Hellinger-incidence graph bridge” is not the terminal frontier.
The literal Meyer quotient already supplies a source-native cohomology, reciprocal flow,
full finite Xi jet packets, and weight-one generalized Paugam pairings.

The minimal remaining RH object is one **strict finite-fibre positive admissible
completion** of that source-native middle cohomology.  It must satisfy the first clause
below.  The second clause is the stronger spectral-completeness problem, not a logical
prerequisite for zero exclusion.

1. **Positive admissible middle polarization (minimal RH gate):** the centered dilation
   flow acts isometrically on a Hausdorff positive completion of genuine Meyer middle
   cohomology, and every actual Xi zero-evaluation remains continuous and nonzero.  The
   Hodge structure cannot be the local reciprocal regulator polarization, whose restriction
   to genuine middle cycles is identically zero.
2. **Global spectral synthesis (stronger completion theorem):** vanishing of every
   multiplicity-bounded Xi jet forces a class to be a literal Poisson boundary.  This would
   identify the whole spectral quotient, but RH already follows from clause 1 and the
   proved one-way Xi spectral inclusion.

The finite-fibre law supplies the topology constraint; it does not prove either clause.
Clause 1 cannot be obtained by first taking ordinary completion and then adding positivity:
ordinary completion erases the normal class or becomes maximally vertical, while local
positivity is in the wrong cohomological degree.

If both clauses hold, every actual Xi generalized eigencharacter `exp(c rho)` lies in a
positive weight-one pairing.  For a nonzero eigenvector `v`,

`h(U_c v,U_c v)=exp(c)h(v,v)`

and also

`h(U_c v,U_c v)=|exp(c rho)|^2 h(v,v)=exp(2c Re rho)h(v,v)`.

Positivity gives `h(v,v)>0`, so `exp(2c Re rho)=exp(c)` for real `c`, hence
`Re rho=1/2`.  The already proved Meyer-to-Xi spectral inclusion supplies a nonzero actual
Xi evaluation at every divisor point; continuity/admission in the positive completion is
the missing step.  Therefore clause 1 alone implies RH.

## Antagonist audit

- The algebraic identity alone is elementary and not paper-level significance.
- The significant result is the sharp arithmetic realization: ordinary complete source
  topology collapses, projective normal tomography remains injective, regular comparisons
  erase reflection, closed infinite-fibre relations become maximally vertical, and finite
  grade fibres are exactly the proper-carrier boundary.
- No RH proof is claimed.  Global spectral synthesis and positive middle polarization remain
  unproved.
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
