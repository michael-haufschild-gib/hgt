# Finite modular-inverse rectangles with all frequency gcds retained

- **ID:** goldbach-modular-inverse-rectangle-completion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical bridge; no novelty claim
- **Sources:** [composite Kloosterman budget](goldbach-composite-kloosterman-budget.md), [flat prime-dilation dispersion](../../2-fully-proven/goldbach-flat-prime-dilation-dispersion.md)
- **Lean status:** Complete in `goldbach/ModularInverseRectangleCompletion.lean`. Direct leaf verification and all 42 theorem-closure audits pass without warnings; only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Exact statement

Let M≥1, let U and V be finite intervals of consecutive integers, and let
c be a residue modulo M. Write L=|U|, H=|V|, g=gcd(M,c.val),
λ=1+log M and τ=τ(M). Let C count the actual pairs (u,v)∈U×V satisfying
gcd(u,M)=1 and uv≡c modulo M. Then

    |C − φ(M)LH/M²|
      ≤ 24 τ M^(2/3) g^(1/3) λ² + τ λ (Lg+H)/M.       (R)

Lengths may be zero or exceed M, starts may be negative, and c may be
zero. No coprimality premise on c or on the Fourier frequencies appears.
The exponents in (R) are real powers of positive integers.

## Gates

- [x] Exact actual-source statement, with every endpoint retained.
- [x] Dependency-closed paper proof below, using the separate proved composite budget.
- [x] Direct Lean leaf check and proof-closure audit of (R).
- [x] No publication or scientific-novelty claim.

## Paper proof [PROVED HERE]

Put e_M(t)=exp(2πit/M) and

    F_U(a)=Σ_(u∈U) e_M(−au).

For a nonzero residue a, put h=min(a.val,M−a.val). The geometric-series
identity, including the case of an empty interval, gives

    |F_U(a)| ≤ 2/|1−e_M(a)| ≤ M/(2h).                  (2)

The first factor from the interval's starting point has modulus one.
For the second inequality, |1−e_M(a)|=2 sin(πh/M), and
sin t≥2t/π for 0≤t≤π/2. The latter follows from concavity of sine on
that interval and its endpoint values. Thus complete periods and finite
endpoints require no separate approximation.

Summing (2), pairing a.val with M−a.val, and bounding the harmonic sum
by its decreasing integral gives

    Σ_(a≠0 mod M) |F_U(a)| ≤ M(1+log M).              (3)

For M=1 the sum is empty. For M≥2 the pairing bound is at most
M H_(M−1), and H_(M−1)≤1+log M. This also proves (3) for every length L.

If d|M and q=M/d, the nonzero residues a with d|a.val are uniquely
a=dt with 1≤t<q. Their characters satisfy e_M(dtu)=e_q(tu). Applying
(3) at q and using 1+log q≤λ yields the progression-sensitive estimate

    Σ_(a≠0 mod M, d|a.val) |F_U(a)| ≤ (M/d) λ.        (4)

The same estimates hold for V.

Finite character orthogonality counts the residue multiplicities of U
and V. For a unit x, its pair fibre is the Cartesian product of the
entries of U reducing to x and the entries of V reducing to c x⁻¹.
Different unit fibres are disjoint, since their first coordinates have
different residues. Their union is precisely the counted pairs: a unit
first coordinate determines x uniquely, and uv=c is equivalent to
v=c x⁻¹. Thus the sum of the two residue-multiplicity products is the
cardinality of the actual finite pair set, including repeated residues
when the intervals exceed M. Exact Fourier inversion gives

    C = M⁻² Σ_(a,b mod M) F_U(a)F_V(b) S(a,bc;M).    (5)

Here S is the actual Kloosterman sum over units. Orthogonality follows
by summing a finite geometric series: the sum of e_M(at) over a is M
if t≡0 and zero otherwise. Substitution into the two residue counts and
finite regrouping prove (5), with no limiting operation. The (0,0)
term is exactly φ(M)LH/M².

For the nonzero/nonzero terms, the separately proved cubic bound implies

    |S(a,bc;M)| ≤ 8 τ M^(2/3) gcd(M,a.val,(bc).val)^(1/3).

The gcd is invariant under changing integer representatives. More precisely,

    gcd(M,a,bc mod M) | gcd(M,c) gcd(M,a,b).

For D=gcd(K,bc), first D divides both Kb and cb, hence divides
gcd(K,c)b. It also divides gcd(K,c)K. Taking another gcd gives
D | gcd(K,c)gcd(K,b). Apply this with K=gcd(M,a), then use
gcd(K,c)|gcd(M,c). Reduction modulo M does not change the common
divisibility because every divisor under consideration divides M.
This proves the stronger divisibility statement, including c=0.
For t=gcd(M,a.val,b.val), the term d=t
is present in the divisor sum, hence

    t^(1/3) ≤ Σ_(d|M, d|a.val, d|b.val) d^(1/3).

Triangle inequality, finite regrouping, and (4) bound the contribution
of all nonzero/nonzero frequencies to (5) by

    8 τ M^(2/3) g^(1/3) λ² Σ_(d|M) d^(−5/3)
      ≤ 24 τ M^(2/3) g^(1/3) λ².                    (6)

Indeed the divisor sum is at most the full positive-integer sum, which
is at most 1+∫_1^∞ t^(−5/3)dt=5/2≤3. The cube-root deduction uses
monotonicity of the cube on nonnegative reals; its right-hand cube is
exactly the existing bound 512 τ³ M² gcd(M,a,bc).

The two axes must be kept separately. The Ramanujan bound

    |c_M(t)| ≤ gcd(M,t)

follows directly from conductor descent. Put d=gcd(M,t), q=M/d.
Then t/d is a unit modulo q. The exact unit-fibre identity gives
c_M(t)=κ c_q(t/d), with κ≤d. The finite Möbius-divisor formula
reduces c_q(t/d) to μ(q), whose absolute value is at most one.
Thus |c_M(t)|≤d for every M, including M=1 and t=0.

As S(0,bc;M)=c_M(bc), F_U(0)=L, and
gcd(M,bc)≤g·gcd(M,b), the a=0,b≠0 contribution has modulus at most

    (Lg/M²) Σ_(b≠0) |F_V(b)| gcd(M,b.val)
      ≤ (Lg/M²) Σ_(d|M) d Σ_(b≠0,d|b.val) |F_V(b)|
      ≤ τ λ Lg/M.                                   (7)

The gcd product inequality follows from the same two gcd extractions.
The divisor expansion is an upper bound because it includes
d=gcd(M,b.val); every summand is nonnegative. Similarly,
S(a,0;M)=c_M(a) gives an a≠0,b=0 contribution at most τλH/M. Combining
(6), (7), and this second axis proves (R). If M=1 both nonzero frequency
sets are empty and (5) already equals its main term.

## Corpus audit and Lean implementation

`RHTower/Sieve/KloostermanSameModulusIntervalCompletion.lean` proves exact
column-correlation completion with a remainder bounded by Mφ(M).
`KloostermanAnalyticFrontier.lean` retains that remainder in the signed
Gram decomposition. Those are useful exact identities, but their bound
does not give (R): (R) counts a modular-inverse graph on a rectangle and
uses the progression-sensitive Fourier bound (4). Do not substitute a
column Gram estimate or an assumed Fourier-decay premise for this step.

`RHTower/Sieve/KloostermanCrossPhaseGeometric.lean` supplies
`stdAddChar_eq_one_iff` and `stdAddChar_nsmul_eq_pow`; its last proof
applies the existing `RHTower.norm_geom_sum_le`. The inspected
`RHTower/SawtoothFourierSeries.lean` also proves
`one_sub_exp_mul_I_eq`, the exact sine-times-unit formula for the chord.
These are concrete sources for (2), not a certificate for the summed
progression estimate (4).

The inspected `RHTower/Sieve/KuzminLandau.lean` proves
`two_mul_le_sin_pi_mul`, supplying the chord lower bound on the whole
unit band. The further corpus search found
`RHTower/SquareResidueQuadraticInterval.lean`'s
`squareResidue_sum_reciprocalChord_le`, already summing the reciprocal
chords for every positive modulus. The implementation uses this exact
finite theorem for (3), and `ramanujanMultiplesFinEquiv` for the actual
divisor-frequency descent in (4). The logarithmic harmonic mechanism
also appears in BiScaleUncertainty's `realHarmonic_le_one_add_log`.
The modulus-one case and each positive-index side condition are
discharged from the actual interval data.

The finite interval transform, (2)–(4), exact graph expansion (5), both
frequency axes, and their complete combination (R) are formalized. The
public theorem takes the actual positive modulus, residue, starts, and
lengths only. The flat dispersion theorem, Möbius progression input,
signed amplifier, and marked Type II sum remain separate proof obligations.

## Lean certificate

Module: `formal/GaloisForLFunctions/goldbach/ModularInverseRectangleCompletion.lean`.
Namespace: `GaloisForLFunctions.Goldbach`.

- `modularInverseRectanglePairs_error_le` proves (R) for the cardinality
  of the literal interval-index pair set.
- `modularInverseRectangleCount_eq_card_pairs` identifies that set with
  the unit-fibre multiplicity count, using a disjoint union of fibres.
- `modularInverseRectangleCount_fourier` proves the exact finite graph
  expansion before any estimates are applied.
- `intervalDivisorFourierMass_eq` gives exact descent to the quotient
  modulus; `intervalDivisorFourierMass_le` supplies (4).
- `intervalPairGcdFourierMass_le` retains the common frequency gcd and
  proves the summable divisor budget `3 M² (1+log M)²`.
- `norm_rectangleRowAxis_le`, `norm_rectangleColumnAxis_le`, and
  `norm_rectangleInterior_le` separately certify the three error terms.

The direct final audit was:

```text
cd formal
lake --old env lean GaloisForLFunctions/goldbach/ModularInverseRectangleCompletion.lean
```

Exit 0, no errors or warnings. Temporary `#print axioms` directives
covered every one of the 42 theorem declarations. Every transitive
closure contains only `propext`, `Classical.choice`, and `Quot.sound`;
no added analytic axiom or premise occurs. Audit log:
`/tmp/hgt-goldbach-rectangle-completion-audit.log`.
The directives were removed after verification, and the completed leaf
is imported by `goldbach/Main.lean`. No umbrella build was run.
Exact corpus lookup finds `modularInverseRectanglePairs_error_le`.
Targeted whitespace and forbidden-marker checks pass, and all 69 local
links in the six updated documents resolve. Completed scratch files were
removed; the proof-audit log is retained.

## Log

- 2026-10-24 — Completed the actual finite pair-cardinality estimate.
  Direct leaf check and all 42 closures pass without warnings, holes,
  added axioms, or analytic premises. Moved this exact theorem to stage 3.
  Flat dispersion and Goldbach remain unproved in Lean.

- 2026-10-24 — Separated rectangle completion from the reusable conductor
  module under the updated olean compilation rules. The full error
  inequality is now in Lean source, alongside exact interval descent,
  both Ramanujan axes, the double Fourier identity, and divisor-weighted
  Fourier budgets. Kernel verification remains pending; no certificate
  for (R) or Goldbach is claimed.
- 2026-10-23 — Formalization in progress in the existing Goldbach arithmetic
  leaf: actual finite interval transforms, character chords, and the
  progression-sensitive Fourier mass. The composite certificate remains
  complete; no certificate for (R) is claimed yet.
- 2026-10-23 — Extracted an explicit constant and a complete finite
  completion proof from the flat-dispersion argument. Existing column
  completion inspected and distinguished from the required graph count.
  No new Lean certificate or novelty claim.
