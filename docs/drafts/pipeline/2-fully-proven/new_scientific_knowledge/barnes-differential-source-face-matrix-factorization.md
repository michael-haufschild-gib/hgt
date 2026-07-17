# Barnes differential source-face matrix factorization

- **ID:** `barnes-differential-source-face-matrix-factorization`
- **Stage:** 2-fully-proven / algebraic core Lean-formalized
- **Type:** THEOREM / DERIVED SOURCE-FACE CONSERVATION / NONPERIODIC HT MODEL
- **Scientific status:** `[PAPER PROOF COMPLETE] [LEAN CORE FORMALIZED]`
  `[NOVELTY PROVISIONAL PASS AS PART OF THE BARNES CHARACTERISTIC THEOREM]`
  `[SIGNIFICANCE PASS] [NOT AN RH RESULT]`
- **Analytic parent theorem:**
  `barnes-multiple-gamma-translation-annihilator.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/NormalCrossingFaceMatrixFactorization.lean`

## The theorem

Let

```text
D_N = C[delta,T_1^(+-1),...,T_N^(+-1)],
x_j = T_j-1,
f_N = x_1...x_N.
```

For rationally independent Barnes periods, the proved full differential-translation annihilator
theorem identifies the DA-relative orbit module of the Barnes logarithmic derivative with

```text
M_N = D_N/(f_N).                                                (1)
```

Fix a source face `j` and put `p_j=product_(k!=j)x_k`, so `f_N=p_j x_j`.  Multiplication by the
two factors gives an exact two-periodic complex on `M_N`:

```text
... -> M_N --p_j-> M_N --x_j-> M_N --p_j-> M_N --x_j-> M_N -> ... .  (2)
```

Equivalently,

```text
ker(x_j:M_N->M_N)=im(p_j:M_N->M_N),
ker(p_j:M_N->M_N)=im(x_j:M_N->M_N).                         (3)
```

Let `S` be any nonempty set of source faces and

```text
B_S=D_N/(x_j:j in S).
```

Then derived source-face restriction has the exact Betti law

```text
Tor_i^(D_N)(M_N,B_S) = B_S,  i=0,1,
Tor_i^(D_N)(M_N,B_S) = 0,    i>=2.                           (4)
```

Thus every nonempty Barnes source face produces two identical free boundary modules in adjacent
degrees.  `H^0=B_S` is the capacity released when the characteristic relation becomes zero on the
face; `H^(-1)=B_S` is the killed relation retained as a derived class.  Relation death and
capacity birth are not analogous quantities.  They are the same boundary module with a one-degree
shift.

## Proof

The operator ring `D_N` is a domain and `f_N` is nonzero.  Therefore

```text
0 -> D_N --f_N-> D_N -> M_N -> 0                            (5)
```

is a free resolution.  Tensor `(5)` with `B_S`.  Since `S` is nonempty, at least one factor of
`f_N` vanishes in `B_S`, so the induced differential is zero.  The tensor complex is exactly

```text
0 -> B_S --0-> B_S -> 0.                                    (6)
```

This proves `(4)`.

For `(2)`--`(3)`, use the rank-one matrix factorization `(p_j,x_j)` of `f_N`.  In any domain `A`,
for nonzero `p,x`, put `M=A/(px)`.  If `x a=0` in `M`, then `px` divides `xa`; cancellation of
the nonzero factor `x` gives `p|a`, so `ker x=im p`.  The other equality follows by cancelling
`p`.  This universal argument is formalized in Lean.

## Decisive no-go and positive successor

```text
[NO-GO]
The number of specialized source coordinates is not a universal cohomological depth for
hypertranscendence.  In the Barnes hierarchy, specializing one face or every face gives the same
derived amplitude [0,1].  No higher Tor degree is created by deeper faces.
```

This rules out a universal Postnikov law in which each deleted source direction contributes one
new obstruction degree.  It also rules out identifying infinite HT capacity with unbounded
cohomological descent height: Barnes has unbounded `delta`-capacity but projective dimension one.

```text
[POSITIVE]
Barnes source-face conservation is exactly two-periodic.  Every nonempty face carries the
canonical self-matching pair (relation death, capacity birth)=(B_S[-1],B_S), and the complete
face fracture is retained by the matrix factorization (p_j,x_j).
```

The positive statement is stronger than vanishing of higher obstruction groups.  It identifies
the surviving modules and the two maps that transport them.

## Reconstruction consequence

The generic rank-at-least-two Barnes observer consisting of full logarithmic principal parts and
one regular pointing is injective.  At a source cusp, the singular observer can cease to be
uniformly conservative because elliptic divisors may escape and become regular rank-one units.
Equation `(4)` locates the algebraic loss: it is the degree `-1` copy of `B_S`, not missing
information that can be regenerated from the specialized bare source.

Therefore a conservative degeneration needs a transverse connecting reporter

```text
partial_S : B_S[-1] -> regular boundary inertia,             (7)
```

whose common kernel with the boundary singular marker and pointing is zero.  A Tate-theta cusp
family supplies the exact next discriminator: escaping elliptic divisors should map to the born
rank-one winding character.  The matrix factorization fixes the source of the class; it does not
manufacture the transverse map `(7)`.

## What this changes in the unified theory

The first candidate topology of an HT function is now concrete.  For a source-minimal germ `F`,
form its DA-relative differential operator module

```text
M_F=A_S/Ann_DA^diff(F).                                      (8)
```

The geometric support of `(8)` says where the function is constrained; the differential Rees
direction says how much HT capacity is stored there; a minimal resolution of `(8)` says how that
capacity fractures under source faces.  These are three independent invariants:

```text
support codimension,
differential prolongation growth,
homological fracture amplitude.                              (9)
```

Barnes has codimension one, unbounded differential growth, and fracture amplitude one.  The
multiple elliptic-gamma hierarchy has a Stanley--Reisner characteristic ideal and must be tested
by its multigraded face Betti table.  This gives a falsifiable classification program rather than
a metaphorical topology.

## Novelty gate

### Established parents not claimed as discoveries

1. Eisenbud matrix factorizations and two-periodic resolutions over hypersurfaces are classical.
2. Computing `(4)` from a length-one free resolution is standard homological algebra.
3. Tate-curve tropicalization, generalized Jacobians, and divisor-to-slope specialization are
   classical parents for the future analytic connecting map.

### Candidate-new conjunction

Targeted exact searches found no source which:

1. computes the full DA-relative differential-translation annihilator of rationally independent
   Barnes multiple gamma as `(x_1...x_N)`;
2. identifies its orbit module with the normal-crossing hypersurface `(1)`;
3. derives the exact all-face Tor law `(4)` and the source-face matrix factorization `(2)`; and
4. combines this with the rank-two singular-marker reconstruction transition.

The matrix-factorization lemma by itself is not new.  The candidate-new theorem is that the
analytic Barnes HT module is exactly the hypersurface module to which the lemma applies, with the
resulting reconstruction and degeneration consequences.  Novelty therefore inherits the open
Nishizawa and independent-specialist gates of the analytic parent theorem.

## Significance and anti-theatre gate

The theorem is significant because it gives the first complete nonperiodic HT model in which all
of the following are computed, rather than named:

```text
the exact differential characteristic boundary;
the infinite capacity direction;
the full face descent;
the derived face fracture;
the residual normalized reconstruction kernel.              (10)
```

It is strong enough to be a main theorem of a paper on Barnes characteristic boundaries.  The
matrix-factorization corollary alone would not warrant a separate paper, and it is not presented
as Fields-scale by itself.  Fields-scale promotion requires the next classification theorem:
prove that natural HT families have presentation-invariant characteristic resolutions and that
apparently different analytic obstruction receivers are conservative realizations of them.

The result fails the anti-theatre gate if the words “matrix factorization” are used without the
analytic annihilator identification, the exact maps `(2)`, or the Tor computation `(4)`.

## Lean certificate

`NormalCrossingFaceMatrixFactorization.lean` proves unconditionally, over every commutative
domain and every nonzero factor pair `p,x`:

```text
range_normalCrossingLeftFactor_eq_ker_rightFactor;
range_normalCrossingRightFactor_eq_ker_leftFactor;
normalCrossingFactorization_twoPeriodicExact.
```

No analytic Barnes theorem is inserted as an axiom.  The special-function identification `(1)`
remains the paper theorem; Lean certifies its complete local algebraic consequence.

## Gates

- [x] exact Barnes characteristic module available
- [x] face matrix factorization proved on paper
- [x] all nonempty-face Tor law proved
- [x] universal higher-face-depth conjecture falsified by a nonperiodic HT family
- [x] nontrivial positive two-degree conservation law isolated
- [x] algebraic core formalized unconditionally in Lean
- [x] direct Barnes/matrix-factorization literature search found no exact match
- [ ] full-text Nishizawa audit inherited from the analytic parent theorem
- [ ] independent specialist novelty and significance review
- [ ] construct the transverse divisor-to-winding connecting map in a natural cusp family
