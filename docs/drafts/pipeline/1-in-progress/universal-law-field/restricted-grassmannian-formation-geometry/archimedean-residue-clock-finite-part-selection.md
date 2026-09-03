# Archimedean residue-clock finite-part selection

- **ID:** ULF-ARCFP-001
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction programme
- **Status:** `[OPEN CORE] [SOURCE LAW PROVED] [MODEL CLASS NARROWED] [NOVELTY UNVERIFIED]`
- **Parent:** ULF-PHSR-001

## 1. Big-picture higher law

The completion problem is not to transport one operator from primes to theta.  Prime history and
fixed theta history do not even occupy the same critical ideal.  The corpus's inverse first-atom
saddle supplies a canonical moving archimedean clock; ULF-GTSD-001 proves that it reaches the
source residue only after a forced double-log transgression.

Source law ULF-PHSR-001 supplies a residue-three affine leaf

```text
mathscr C_3 = mathscr D_1 + S_1
```

and the prime-mixed integral nuclear defect `mathsf T` is a distinguished translation by one in
its finite-part coordinate.  Literal fixed theta time lies outside this leaf.  The proposed higher
law is:

> Poisson self-duality selects and transports the inverse-saddle theta clock, its double-log
> transgression lands in `mathscr C_3`, the unique archimedean anomaly chooses an origin of the
> remaining finite-part torsor, integer formation is the translation lattice, and off-line
> relation horizons are nonzero positive translations from that origin.

On this reading, the critical line is not selected by positivity of a spectral operator.  It is
the zero-translation sector of a source-formed singular clock after the archimedean place has
chosen its canonical time origin.

## 2. Corpus audit before conjecture

Searches used the Lean-corpus research tool for `source hazard finite part torsor logarithmic
residue clock completion`, `finite part weak trace class trace class perturbation source
completion`, `trace class perturbation finite part logarithmic divergence diagonal operator`, and
`moment ratio hazard superpolynomial moments weak trace class theta`.

Established facts:

- `ULF-PHSR-001` proves `Res(mathscr D_N)=3N`, `Res(E_j)=3`,
  `FP(mathscr D_1)=-3 psi(9/2)`, and
  `FP(mathscr D_N+mathsf T)=FP(mathscr D_N)+1` on the canonical prime-formed record carrier.
- The same card proves the fixed-theta history hazard is not weak `S_1`; no trace-class
  correction can turn it into `mathscr D_1`.
- `ULF-GTSD-001` constructs from the corpus's unique response-centered first-atom saddle a moving
  theta clock `A_lambda`.  Its unique source-residue calibration is six,
  `Res(A_lambda)=Res(mathscr D_1)=3`, while
  `mathscr D_1-A_lambda` has exact double-log residue `3` and a closed second finite part.
- `ULF-UASA-001` proves literal theta asymptotics force exactly the
  `pi exp(2|x|)` Szegő subtraction.  Its residual is outer, but scalar completion loses the
  unsquared odd source amplitude.
- `ULF-DLLA-001` proves that relative determinant fillings differ by an integral deck degree and
  that boundary holonomy alone forgets this integer.
- `SoninPrincipalRelativeTraceSplitting` and `SoninFinitePartUniqueness` already construct a unique
  signed finite part on a *finite-prime* direct sum of a logarithmic principal shell and its
  `S_1` relative ideal.  Their own scope excludes cofinal compatibility and archimedean
  completion.
- `WeakSchattenResidue`, `PositiveSchattenLogResidueTraceClassPerturbation`, and
  `ConnesConsaniResiduePerturbationCapstone` prove the residue is invariant under trace-class
  perturbation.  Therefore residue alone cannot see a rank-one off-line horizon.
- `xiRightPrimeMixedHorizonDefect` gives a positive rank-one nuclear horizon of trace one for each
  strict-right divisor copy.  This object is target-side and must not be inserted into the source
  construction.
- Locks CANNOT-94/CANNOT-98 permit invisible finite Krein spectators until exhaustion is proved;
  CANNOT-235 forbids recovering source orientation from positive dephased data alone; FAIL-84
  forbids a scalar Hardy completion of the odd source line.

No checked corpus theorem selects the physical saddle aperture from Poisson self-duality,
transports the double-log anomaly through the oriented completion, proves a cofinal finite-part
origin, or identifies target horizon trace with displacement in the source clock leaf.

## 3. Exact object to construct

Construct from literal integer summation and self-dual Fourier normalization, before divisor
input, a tuple

```text
(lambda_P, B_Pois, FP_Pois, L_T).                    (ARCFP.1)
```

It must obey all following laws.

### A. Poisson selection of the proved saddle clock

Poisson self-duality must select a physical `lambda_P<=0`, without divisor input, in the already
proved family of inverse-saddle clocks `A_lambda`.  The unique residue-matching calibration is
six, and ULF-GTSD-001 proves

```text
Res(A_(lambda_P))=3,
mathscr D_1-A_(lambda_P) has double-log residue 3.   (ARCFP.2)
```

Choosing `lambda_P` by fitting source moments is disallowed.  Selection must come from the same
Poisson identity that exchanges integer formation with Fourier inversion and must preserve
unsquared Euler coefficients and the odd orientation line.

### B. Double-log anomaly transport

`B_Pois` must be the transported form of the explicit pre-divisor transgression

```text
B_(lambda_P)=mathscr D_1-A_(lambda_P).                (ARCFP.3)
```

Its ordinary logarithmic residue is zero, its double-log residue is three, and its exact second
finite part is fixed by ULF-GTSD-001.  Literal Poisson completion must preserve these data and
subtract this term before any `S_1` comparison.  An arbitrary double-log counterterm with matching
growth is not admissible.

### C. Unique archimedean finite-part origin

Subtract precisely the Szegő anomaly forced by ULF-UASA-001.  The subtraction must make the
renormalized prefixes converge to a finite-part functional

```text
FP_Pois(mathscr D_1+K)=FP_Pois(mathscr D_1)+Tr(K)    (ARCFP.4)
```

for every admitted trace-class relative correction `K`.  On the source chart it must recover the
already forced value

```text
FP_Pois(mathscr D_1)=-3 psi(9/2).                    (ARCFP.5)
```

Changing cutoff, theta scale, or local trivialization may not change `(ARCFP.5)` except by an
independently identified integral deck transformation.

### D. Integral formation lattice

The oriented prime-mixed `mathsf T`, not an abstract rank-one projection, must determine the
admitted positive unit translation:

```text
FP_Pois(mathscr D_1+mathsf T)-FP_Pois(mathscr D_1)
 =Tr(mathsf T)=1.                                    (ARCFP.6)
```

ULF-PHSR-001 already proves this in the source clock basis.  Missing work is to prove that Poisson
completion preserves the same unit and that no arbitrary real-trace spectator is admitted by the
literal formation algebra.

### E. Horizon displacement and exhaustion

After completed divisor specialization, every strict-right copy must contribute its existing
positive horizon projection `P_rho` as a relative correction in the *same* finite-part frame:

```text
Tr(P_rho)=1,
FP_Pois(A+P_rho)-FP_Pois(A)=1.                       (ARCFP.7)
```

Critical-line copies contribute no transverse horizon.  Functional-equation/Schwarz reflection
must pair the remaining sides without negative trace compensation.  Asymptotic completeness must
show that the target relative correction is exactly the sum of these horizons plus the transported
neutral source formation—no invisible `S_1` spectator.

## 4. Exact RH closure

Let `k` be number of strict-right completed relation horizons, counted with multiplicity.  Compare
actual completed clock with neutral completion in canonical Poisson finite-part frame.  Source
formation and both universal anomalies occur in both and cancel.  Laws `(ARCFP.3)--(ARCFP.7)` give

```text
source relative displacement = 0,
target relative displacement = sum_rho Tr(P_rho)=k.
```

Information-neutral Poisson completion gives `0=k`.  Positivity makes `k>=0`, so no strict-right
copy exists.  Functional-equation reflection excludes strict-left copies; all nontrivial zeros lie
on the critical line.

This closes RH only if `lambda_P`, `B_Pois`, `FP_Pois`, and exhaustion are constructed without
consulting the zero divisor.  Defining the neutral comparison by deleting off-line factors is
circular.

## 5. First attack: what is already forced

The source side is unusually rigid:

1. residue `3` is forced by exact rational Hodge survival, not normalization;
2. finite part `-3 psi(9/2)` is forced by literal history origin `n=0`;
3. the unit translation is the actual prime-mixed `mathsf T`, with trace one and operator norm
   `2/3`, not an inserted projection;
4. fixed theta time is excluded at ideal level;
5. inverse-saddle theta time is the unique audited moving candidate and its scale six is uniquely
   fixed by residue matching;
6. source-versus-saddle discrepancy has forced double-log residue three and an exact second finite
   part;
7. the coefficient of the leading theta metric subtraction is uniquely `pi`.

Thus construction has no free clock family, residue, double-log coefficient, finite-part target,
unit, or leading anomaly coefficient.  Only physical aperture selection, oriented cofinal
transport, and exhaustion remain unknown.

## 6. Hostile falsifiers

The programme fails if any one occurs:

- Poisson self-duality selects no source-pure `lambda_P`, or selects incompatible apertures in
  different charts;
- the inverse-saddle clock cannot carry the odd unsquared orientation line;
- the proved double-log transgression is not preserved by completion;
- the unique Szegő metric subtraction does not control the history hazard prefixes;
- preserving unsquared Euler orientation is incompatible with the positive clock leaf;
- a strict-right horizon is not an additive positive `S_1` correction in the common frame;
- a negative or nonintegral trace-class spectator can compensate its trace while respecting all
  literal formation laws;
- completion conservation is proved only after assuming absence of off-line copies;
- `FP_Pois` is merely a selected regularization rather than a consequence of Poisson self-duality.

## 7. Why this is not the retired return-degree card

ULF-FRRD-001 tried to manufacture integer degree `7` from a finite recurrent model.  The actual
source is not trace-class relative to the unilateral shift and its direct `det_2` has no winding.
This card uses the invariant the infinite source genuinely has: a measurable weak-`S_1` clock and
an ordinary-trace affine coordinate.  Its integer step is already realized by `mathsf T` on the
same carrier.  No determinant degree is postulated.

The open theorem is still hard: source formation must choose the admissible `S_1` sublattice and
Poisson self-duality must choose the origin.  But these are now falsifiable constructions with
fixed numerical outputs, not names for “completion should preserve information”.

## 8. Status

- Source residue clock, finite part, integral translation, and fixed-theta ideal no-go: proved in
  ULF-PHSR-001.
- Canonical inverse-saddle clock, unique six-unit residue match, double-log transgression, and
  second finite part: proved in ULF-GTSD-001.
- General finite-part/trace-class affine law: already represented in finite-prime Sonin corpus;
  cofinal Poisson transport absent.
- Open core: select physical `lambda_P`; transport `(ARCFP.3)` through literal oriented Poisson
  completion; prove finite-part origin, horizon additivity, and exhaustion in same frame.
- Lean: no new Lean work during current read-only research phase.  Formalize ULF-PHSR-001 first;
  do not formalize this conjecture as if its open laws were premises.
