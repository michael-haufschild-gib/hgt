# Source-pointed observation network law

- **ID:** `resolved-defect-augmentation-conservativity-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL EXACT-DESCENT LAW / RH FRONTIER CORRECTION
- **Status:** `[CONJECTURE SURVIVED] [PAPER PROOF COMPLETE] [LEAN CORE COMPLETE] [NOVELTY UNVERIFIED]`
- **Lean parents:**
  - `formal/GaloisForLFunctions/HTGeometry/ResolvedDefectConservationLaw.lean`
  - `formal/GaloisForLFunctions/RHTower/Deninger/DeningerGreenInternalDefectCancellationLaw.lean`
  - `formal/GaloisForLFunctions/RHTower/Deninger/DeningerResolvedDefectHellingerGammaBalancedCofaceNoGo.lean`
  - `formal/GaloisForLFunctions/RHTower/Deninger/DeningerCalderonWittResolvedCrossEffectBoundary.lean`
  - `formal/GaloisForLFunctions/RHTower/Deninger/DeningerCalderonWittCompletedXiHellingerGammaGradedVerticalObstruction.lean`

## Frontier correction

The finite Deninger Green composite is already Frobenius-covariant unconditionally.  Its conjugate
Riesz and odd-Hodge covariance defects need not vanish; they are equal and opposite after
transport, hence cancel.  Therefore

```text
"the composite Frobenius--Hodge commutator vanishes"
```

is not an RH-producing condition.  It is an identity which can hide the off-critical boundary
fracture.  The missing datum is factor-resolved conservativity before the two defects are added.

This corrects the frontier statement in
`docs/drafts/pipeline/4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`.

## Strengthened frozen conjecture

The original augmentation statement survived but is not maximally universal.  It is one edge of
the following serial law.

> **[CONJECTURE — SOURCE-POINTED OBSERVATION NETWORK LAW.]**
> For a chain `E_0 -> ... -> E_m`, propagate the actual source sector by image.  Composite
> observation is conservative on the initial sector exactly when every edge is conservative on
> the sector delivered to it.  Stagewise uniform lower bounds multiply.  Hence every successful
> route must preserve source separation edge by edge; no downstream construction can recover a
> distinction killed earlier, and faithful recovery from a cofinally collapsing source must be
> singular.  For parallel readers, joint kernel is intersection of marginal kernels; independent
> coordinates can therefore protect a distinction only when retained before the lossy edge.

The two-stage theorem and quantitative composition law are now formalized; arbitrary finite form
is their induction.

### Augmentation specialization

> **[CONJECTURE — RESOLVED-DEFECT AUGMENTATION CONSERVATIVITY LAW.]**
> Every compositional conservation law has a canonical resolved defect whose components are the
> transported defects of its factors.  Ordinary observation is augmentation: it adds those
> components.  The observed composite defect vanishes exactly when the resolved defect lies in
> the zero-sum cancellation module.  Consequently observed conservation implies factorwise
> conservation on a source sector exactly when augmentation is conservative on that sector.
>
> For an analytic or Hilbert completion, algebraic injectivity is insufficient: the completed
> source sector must remain transverse to the cancellation module.  Equivalently, no nonzero
> cancellation vector may enter the closure of the resolved source range.  Disjoint retained
> grades, a pointed one-sided cone, or a uniform positive angle are three sufficient realizations
> of the same conservativity condition.

The conjecture is deliberately broader than the present two-factor Lean theorem.  It predicts an
arbitrary finite-factor exact sequence and a completion criterion.  It is false if a finite
factorization has a composite covariance defect not equal to the sum of its transported factor
defects, or if augmentation is conservative on a sector that meets its zero-sum kernel nontrivially.

## Exact finite law to prove

Let

```text
X_0 --T_0--> X_1 --T_1--> ... --T_(n-1)--> X_n
```

be linear maps, and let `C_i` be the source evolution on `X_i`.  Put

```text
D_i = C_(i+1) T_i - T_i C_i.
```

Transport each `D_i` through all factors before and after it to obtain an endpoint-valued defect
`Dhat_i : X_0 -> X_n`.  Then

```text
C_n (T_(n-1)...T_0) - (T_(n-1)...T_0) C_0
  = sum_(i=0)^(n-1) Dhat_i.                              (1)
```

Define the resolved defect and augmentation by

```text
Dres(x) = (Dhat_0(x),...,Dhat_(n-1)(x)),
epsilon(z_0,...,z_(n-1)) = sum_i z_i.                    (2)
```

For `n >= 1`, the universal cancellation sequence is exact:

```text
0 -> Z^(n-1) --boundary--> Z^n --epsilon--> Z -> 0,       (3)

boundary(w_0,...,w_(n-2))
  = (-sum_i w_i,w_0,...,w_(n-2)).                        (4)
```

Hence

```text
ker epsilon = range boundary.                            (5)
```

For every resolved source sector `S <= Z^n`, the following are equivalent:

```text
epsilon is conservative on S;
S intersect ker(epsilon) = {0};
S intersect range(boundary) = {0};
for every d in S, epsilon(d)=0 implies d=0.               (6)
```

Equations `(1)`--`(6)` are the theorem, not an analogy.

## Riemann specialization

For the arithmetic Green factorization, the two resolved channels are

```text
D_H(a) = Hodge covariance defect after conjugate Riesz,
D_R(a) = odd Hodge applied to the Riesz covariance defect.
```

Lean proves

```text
D_H(a)+D_R(a)=0                                          (7)
```

for every finite multiplicity-exact source vector.  Each coordinate defect is multiplication by
the signed boundary fracture

```text
2 Re(rho)-1.                                              (8)
```

One basis coordinate vanishes exactly when `Re(rho)=1/2`.  Thus RH follows if the actual resolved
Green defect range lies in two disjoint retained grades.  This implication is already Lean:
`riemannHypothesis_of_greenInternalDefectGradeSeparation`.

The research frontier is therefore not construction of another covariant composite.  It is:

```text
construct a source-forced factor-provenance resolution whose two completed defect grades
remain disjoint (or uniformly transverse) through the Gamma/co-Poisson boundary.              (9)
```

## Shadow map across the corpus

The law explains prior results by identifying their observation and hidden cancellation sector.

| Corpus result | Resolved object | Augmentation / loss | Exact verdict |
|---|---|---|---|
| Deninger Green covariance | Riesz and Hodge factor defects | composition adds them | unconditional antidiagonal cancellation |
| Calderón--Witt self-cup | two ordered cross-effects | alternating cup codiagonal | nonzero arithmetic boundary is killed |
| Hellinger--Gamma finite coface | two positive Hodge channels | codiagonal | each finite grade is transverse to cancellation kernel |
| Hellinger infinite completion | adjacent depth grades | closed graph descent | endpoint charge becomes vertical; conservativity fails |
| Cartan-slope conservation | primal/dual transported slope | norm or positive descent | nonzero slope survives, enters radical, or forces singularity |
| source-reversal anomaly | oriented source pair | invariantization | cocycle becomes invisible on balanced cancellation locus |
| physical fat point/Koszul row | unit-scaled coface row | ideal/row reduction | valuation survives; orientation-bearing units are quotiented |
| finite Rees fibres | depth-labelled defect | forgetting grade | finite fibres exact; ungraded closure maximally vertical |
| Hedenmalm/Burnol/Sonin consumers | source and reflected channels | scalar trace/aperture | exact readers, not source-sector conservativity proofs |
| four-unit Ward positivity | resolved oriented boundary | positive scalar response | consumer is decisive only after source cone is pointed |
| compact recurrence | phase-frequency packet | orbit closure/Bohr mean | compact rank is independent of split cancellation defect |

## Hostile attacks

1. **Tautology attack.**  `S intersect ker epsilon={0}` is elementary.  Survivor: the scientific
   content is identification of the actual Green map as an unconditionally cancelling composite,
   the explicit arithmetic defect `(8)`, and the proof that existing finite and completed source
   transports land on opposite sides of `(9)`.
2. **Commutator attack.**  A vanishing total Frobenius commutator might already imply RH.  Refuted:
   Lean proves total Green covariance for every divisor while the two internal defects are
   generally nonzero.
3. **Finite-grade attack.**  Positive Hellinger coefficients might supply separation.  Refuted:
   every finite balanced grade is transverse to the antidiagonal and therefore cannot represent
   the required nonzero resolved defect at all; a factor-provenance lift is extra structure.
4. **Completion attack.**  Orthogonal grade labels might solve the problem automatically.  Refuted:
   factorial damping plus adjacent exactness puts nonzero endpoint charge in the vertical graph
   closure, so the one-marginal boundary is not closed.
5. **Divisor attack.**  Exact zero and multiplicity data might recover factor defects.  Refuted by
   unit-scaled fat-point/Koszul equivalence and balanced source-reversal twins.
6. **Positivity attack.**  A positive scalar form might prevent cancellation.  Only if its source
   sector is a pointed cone before augmentation.  Post-augmentation positivity cannot distinguish
   an antidiagonal pair already mapped to zero.
7. **Over-universality attack.**  Not every route is literally a two-factor linear map.  The claim
   is restricted to compositional/additive conservation laws and their linearized defect sectors.
   Other routes are corollaries only after an explicit resolved-object/augmentation map is given.

## Positive survivor

The positive theorem is not another no-go.  It identifies a sufficient RH-producing object and
removes a false target:

```text
source-pointed factor resolution
  + retained provenance grades
  + completed transversality to the zero-sum boundary
  => componentwise weight-one covariance
  => vanishing signed boundary fracture
  => RH.                                                   (10)
```

Arbitrary-finite exactness and stagewise uniform composition are complete.  Next mathematical task
is source-specific: compare the coefficient-faithful physical/Hodge incidence with actual Green
factor provenance and prove that the resulting unsquared orientation survives the completed
Gamma/co-Poisson edge, or derive the equivalent source law forcing its secondary trace to vanish.

## Gates

- [x] conjecture frozen before strengthening the proof
- [x] exact falsifiers stated
- [x] two-factor algebraic law already formalized
- [x] arithmetic Green cancellation already formalized
- [x] grade-separated RH implication already formalized
- [x] finite Hellinger transversality and infinite vertical obstruction separated
- [x] arbitrary finite cancellation sequence formalized
- [x] uniform completion/transversality sufficient theorem formalized
- [x] dependency-closed paper proof
- [x] paper rewritten around one theorem
- [x] source-pointed serial/parallel network parent law formalized
- [x] local physical-to-Hodge incidence bridge incorporated
- [x] antagonistic general-journal review refreshed after final formal audit
