# Inverse-response Ward mechanics: field laws

**Status:** `[FIELD PROGRAMME] [MECHANISM LEVEL] [PRE-RH]`

## 1. Why this mechanism

The frontier has already constructed source formation, inverse formation, several coefficient-
faithful intervention currents, a reflection-odd two-component horizontal carrier, and a positive
reflection-even Hodge mass.  It still lacks an independent global identity forcing that mass to
vanish.  Route-local work asks separately for a Green identity, a Cartier boundary, a Stokes
annihilator, or a trace formula.  Inverse-response Ward mechanics asks one higher question:

> Which conservation law is forced when several infinitesimal responses are formed from one
> invertible source law?

The answer is a mixed Riccati identity.  It is not attached to any proof route.

## 2. Primitive mechanism

Let `E` be a formed source law, `M=E^{-1}`, and let `D_i` be legal source interventions.  Define the
intervention current

\[
  \Theta_i=M D_iE.
\]

Leibniz differentiation of `ME=1` gives

\[
 D_iM=-M\Theta_i.
\]

Therefore every ordered pair of interventions obeys the mixed inverse-response law

\[
  D_i\Theta_j+\Theta_i\Theta_j=M D_iD_jE.                 \tag{IRW}
\]

This equation fuses four formerly separate organs:

1. **formation:** `E` and its inverse `M`;
2. **intervention:** source derivations `D_i,D_j`;
3. **generation:** logarithmic response currents `Theta_i,Theta_j`;
4. **conservation:** a Ward reporter annihilating total derivatives.

The right-hand side is source acceleration.  When the two-parameter source experiment is affine in
the `i` direction after applying `j`, it vanishes.  The product of two independently visible
currents is then an exact derivative:

\[
  \Theta_i\Theta_j=-D_i\Theta_j.                          \tag{W}
\]

Any additive reporter `tau` with `tau(D_i x)=0` satisfies the exact Ward conservation law

\[
  \tau(\Theta_i\Theta_j)=0.                               \tag{C}
\]

More generally, if `tau D_i=beta`, the exact anomalous balance is

\[
  \tau(\Theta_i\Theta_j)=\tau(MD_iD_jE)-\beta(\Theta_j).   \tag{A}
\]

For a logarithmic grading derivation, any strict linear reporter is blind on every nonzero grade.
Thus `(A)`, not the special case `(C)`, is the live arithmetic law.

## 3. Laws of the field

### Law I — formation creates response coupling

Currents formed through a common inverse are not independent.  Their bilinear product is controlled
by the mixed source acceleration through `(IRW)`.

### Law II — affine experiments convert coupling into conservation

Vanishing mixed source acceleration does not kill either local response.  It makes their product a
total derivative.  Conservation is therefore born from the intervention grammar, not postulated on
the receiver.

### Law III — reporters select only after fusion

A Ward reporter annihilates the fused product, not the individual currents.  If a faithful positive
realization identifies that product with a nonnegative mass, the Ward identity forces the current
into the radical.

### Law IIIa — grade support forces anomaly

If `Dx=wx` with nonzero scalar weight and a linear reporter kills all `D`-derivatives, it kills
`x`.  Prime-log grades therefore cannot be read by a strict invariant trace.  Any label-faithful
global reporter must have a typed boundary anomaly.

### Law IV — acceleration is the obstruction

If `D_iD_jE` is nonzero, the exact defect is `M D_iD_jE`.  There is no license to call the product
conserved.  This term is measurable source curvature in the literal sense of failure of affine
response, but no geometric curvature metaphor is required.

### Law V — mixed laws precede squares

The diagonal Riccati equation `D Theta + Theta^2=M D^2E` is only the one-intervention shadow.  The
mixed equation is the universal object because the frontier's positive Hodge current pairs two
structurally different odd components.

## 4. Reconstruction and prediction

Equation `(IRW)` reconstructs mixed source acceleration from formed currents:

\[
  D_iD_jE=E\bigl(D_i\Theta_j+\Theta_i\Theta_j\bigr).
\]

Thus the response packet determines whether an experiment is affine.  This is a genuine joint
reconstruction law: neither `Theta_i` nor `Theta_j` alone contains the acceleration term.

The fourth-organ prediction is exact:

> Every positive receiver of an inverse-formation experiment evaluates its integrated mixed
> Fisher/Hodge mass as source acceleration trace minus boundary anomaly.

This prediction is independent of RH and can be attacked in finite probability, operator, graph,
and arithmetic models.

## 5. RH gate

The existing source-zero carrier supplies two reflection-odd components and
`GaussHodgeMassCurrent` supplies their nonnegative, reflection-even, label-faithful product.  If the
literal pre-zero arithmetic source supplies:

1. two derivations realizing those components as `Theta_1,Theta_2` from one invertible `E`;
2. an additive global reporter with typed anomaly `tau D_1=beta`;
3. identification of `tau(Theta_1 Theta_2)` with total Gauss Hodge mass;
4. an independently proved balance `tau(MD_1D_2E)=beta(Theta_2)`;

then `(A)` forces total Hodge mass zero, and the already formalized critical-radical theorem gives
RH.  None of these four arithmetic realization claims is asserted here.  They are now a typed,
falsifiable construction target rather than a request for an unspecified source-native object.

## 6. Anti-theatre tests

- Arbitrary unrelated currents fail Law I: they need not share an inverse formation.
- Strict invariant traces are provably grade-blind; the anomaly must be constructed, not declared.
- Non-affine source experiments retain the explicit acceleration defect.
- Positivity alone does not supply conservation; the existing Hodge firewall remains valid.
- Conservation alone does not imply RH until the reporter is identified with the literal positive
  Hodge mass before divisor specialization.

## 7. Next construction

Construct the literal pre-zero two-parameter formation experiment and its boundary reporter.
Candidate parameters are not route names but source operations: logarithmic scale and
reflection/prime-depth formation.  Compute both `tau(MD_1D_2E)` and `beta(Theta_2)` before applying
Xi, completion, or a zero-indexed evaluation.  The programme lives or dies on their equality.
