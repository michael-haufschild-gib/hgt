# Hedenmalm--Weil self-adjoint completion and prime-rigidity theorem

- **ID:** `hedenmalm-weil-selfadjoint-completion-rigidity`
- **Stage:** 1-in-progress
- **Type:** THEOREM PACKAGE / DIRECT HILBERT--POLYA ARCHITECTURE
- **Scientific status:** `[CONJECTURE UNDER ATTACK] [NOVELTY UNVERIFIED]`
- **Target significance:** at least `90/100` only if every theorem below is proved, the direct
  literature parents are cleared, and the final manuscript is self-contained.

## Current route verdict

The divisor-indexed reciprocal operator, divided-chain/Jordan package, and faithful-quotient
implications are formalized but retired as new science. They score only `35--45/100`: the first is
target-fed, the second is classical local factorization, and the third assumes the carrier whose
construction is the problem. They remain useful theorem-level guards.

The open core is now deliberately narrower and constructive:

```text
from the theta kernel and completed all-prime source alone,
construct a nondegenerate quotient or Hilbert metric which annihilates the common source,
retains every required divided level, and makes coordinate multiplication symmetric.
```

No object indexed by the Xi zeros, no premise equivalent to positivity of the Weil form, and no
assumed faithful quotient counts as progress on this core.

The unconditional de Branges seam further compresses the target. With `A=XiC` and
`E=A+iA'`, the source-defined commutator of `E` and `E#` is exactly the removable derivative
Bezoutian

```text
B_A(z,v)=(A'(z)A(v)-A(z)A'(v))/(v-z),
```

with the diagonal filled by `A'(z)^2-A(z)A''(z)`. Distinct Xi zeros are orthogonal for this kernel,
and its diagonal at a divisor point is nonzero exactly at multiplicity one. This identifies the
Hedenmalm terminal metric with the classical de Branges/Weil kernel rather than producing a second
independent route. The constructive open core is therefore a theta/all-prime Gram factorization of
this fixed critical Bezoutian; abstract RKHS construction after assuming positivity does not count.

## Determinacy and extremality gate

An unpointed all-order moment sequence or formal asymptotic expansion is not a rigid carrier.
Indeterminate Hamburger fibers can retain global analytic and differential freedom after every
moment has been fixed. Therefore no argument may infer the theta/all-prime Gram factorization from
formal coefficient agreement alone.

The fixed prime--archimedean carrier crosses the local determinacy gate in a stronger category.
Put

```text
G(z)=normalizedPrimeArchMomentGerm(z),
T(z)=continuedPrimeArchSourceRelativeTrace(z).
```

The pointed analytic lift is exact:

```text
T(z)=-z G(z).                                              (D1)
```

Every analytic germ with the complete Taylor jet of `G` equals `G` near the center, so `(D1)`
recovers the distinguished Euler--Gamma trace rather than an arbitrary representative of a moment
fiber. Moreover,

```text
XiC'(z)+z G(z)XiC(z)=0                                    (D2)
```

near the center. Hence the same pointed germ reconstructs locally

```text
E(z)=XiC(z)(1-i z G(z))                                   (D3)
```

and, off the diagonal,

```text
B_A(z,v)
 =XiC(z)XiC(v)
   *[(vG(v)-zG(z))/(v-z)].                                (D4)
```

Together with the central normalization `XiC(0)`, `(D2)` determines `XiC` uniquely among entire
solutions: the difference of two solutions satisfies a homogeneous analytic first-order
constraint and vanishes at the center, hence vanishes locally by analytic-order comparison and
globally by the identity theorem. Thus moment reconstruction is not the remaining
Hilbert--Polya problem in this route. The
remaining datum is global orientation: a source-derived positive Gram factorization or canonical
extremal selection for the kernel represented by `(D4)`, compatible with the full all-prime trace.
Determinacy of the scalar theta measure alone does not imply that positivity.

For the implication to RH, full Gram positivity is stronger than necessary. On the centered upper
half-strip the Hermitian specialization satisfies

```text
B_A(z,conj(z))
 =|XiC(z)|^2
  *[(T(conj(z))-T(z))/(z-conj(z))].                       (D5)
```

The factor `|XiC(z)|^2` is strictly positive on the source domain. Therefore

```text
B_A(z,conj(z))>=0 at every regular upper-strip point
  <-> the continued source is anti-Herglotz there
  <-> RH.                                                  (D6)
```

This localizes the orientation core to one scalar inequality per source point. A full positive
kernel remains necessary for the intended de Branges Hilbert-space realization, but it is not
necessary merely to prove RH.

## Proposed theorem package

Let

```text
k(x)=2 VarTheta_00(i exp(2x)),
D=-i partial_x,
L=k D k^(-1),
hat k=Xi,
```

and let `q_W` be the completed Weil polarization, defined on the source side by the full
prime-power explicit formula plus the archimedean completion.

The target package is:

1. **Metric classification.** Every continuous positive Schwartz-core pullback which symmetrizes
   `(L D,L)` is a positive atomic Fourier measure on the real `Xi` divisor. Two independent prime
   dilations already force the full translation invariance needed for this classification.
2. **Canonical source metric.** The source-defined form `q_W` is the canonical multiplicity-exact
   member of the divisor form class; its Cauchy Gram kernel is the divided difference of one
   prime--Gamma relative-resolvent function.
3. **Closed operator realization.** If and only if RH and simplicity hold, the finite theta
   eigenfunction span completes under `q_W` to a Hilbert space on which the quotient operator
   induced by `L D` is essentially self-adjoint. Its closure has compact resolvent, the normalized
   theta eigenfunctions form a complete orthonormal basis, and its reciprocal regularized
   determinant is `Xi(z)/Xi(0)`.
4. **Finite prime--Weyl collapse.** On the full real-divisor sampling quotient, every finite
   polynomial shift--differential operator which descends is a polynomial spectral multiplier.
   Hence every symmetric descended operator is in `R[D]`, and no nonzero canonical commutator or
   finite prime mixing survives.
5. **Positive carrier conclusion.** A proof inside this architecture must place the all-prime
   arithmetic information in the nonlocal metric/domain or in a cofinally infinite kernel between
   divisor atoms; it cannot be added later as a finite prime-decorated local observable.

## Existing unconditional inputs

- `hedenmalm-theta-pair-divisor-supported-metric-law.md` proves item 1 from infinitesimal pair
  symmetry and proves the exact eigenfunction sampling law.
- `hedenmalm-pair-weil-polarization-law.md` proves the algebraic source form, Weil equivalence,
  and eigenfunction norms.
- `XiWeilResolventSource.lean`, `XiWeilHilbertCore.lean`, and companion modules internally verify
  the multiplicity-exact Cauchy kernel, source formula, and evaluation Hilbert carrier.
- `prime-modulated-weyl-idealizer-collapse-on-xi-sampling.md` proves item 4 on paper; its algebraic
  coefficient-separation core is internally formalized.
- `SquarefreeMoebiusNormalization.lean` and the infinite signed-channel modules provide an exact
  all-prime Hilbert carrier and reciprocal-zeta half-plane normalization. They are supporting
  carrier infrastructure, not yet the missing source-to-divisor incidence.
- `XiHedenmalmMomentDeterminacy.lean` verifies `(D1)`--`(D4)` in the analytic-germ category and
  proves that the complete Taylor jet of `G` has a unique analytic lift to the distinguished
  continued Euler--Gamma trace and uniquely determines `XiC` among entire normalized solutions of
  `(D2)`.
- `XiHedenmalmOrientationGate.lean` verifies `(D5)` and the unconditional equivalence `(D6)`.

## Open proof obligations

- [ ] prove that the normalized theta eigenvectors span the completed eigenfunction Hilbert space
      and identify it isometrically with `ell^2` of the distinct centered zeros under simplicity;
- [ ] prove essential self-adjointness and the explicit closure domain of the induced diagonal
      operator;
- [ ] prove compact resolvent and the exact genus-one determinant identity with multiplicities
      handled honestly;
- [ ] prove the converse direction without smuggling RH into the Hilbert-space definition;
- [ ] decide whether the Cauchy completion equals the eigenfunction completion under RH plus
      simplicity, or state the two completions separately;
- [ ] complete a primary-source literature audit of diagonal generalized-eigenvalue pencils,
      Hedenmalm's June 2026 paper, Weil polarization, and crossed Weyl idealizers;
- [ ] determine whether the assembled package clears the novelty and significance gates at 90.

## Attacks that must fail explicitly

1. **Target-fed diagonalization.** Listing zeros and declaring a diagonal operator is not the
   source construction. The operator must arise as the closure of the theta differential pair in
   the source-defined Weil metric.
2. **Multiplicity erasure.** The evaluation form counts multiplicity, but one theta eigenfunction
   per distinct zero cannot resolve a repeated zero. Exact determinant recovery therefore requires
   simplicity or an independently constructed root-vector tower.
3. **Semidefinite substitution.** A positive measure on the already-real zeros kills all off-line
   eigenfunctions. Conservativity is the RH-bearing clause.
4. **Finite-prime decoration.** A finite modulation or Weyl operator cannot be advertised as the
   arithmetic source after the sampling quotient; the idealizer theorem classifies that escape.
5. **Squarefree normalization overclaim.** The identity `1/zeta(2s)=sum mu(n)n^(-2s)` in
   `Re s>1/2` is zero-preserving carrier infrastructure, not a positivity or divisor-transfer
   theorem.
6. **All-order moment overclaim.** Equality of every formal moment or asymptotic coefficient does
   not select a global carrier without determinacy, extremality, or a nonflat pointing. Here the
   exact analytic lift `(D1)` supplies the pointing; it does not supply the positive orientation.
7. **Diagonal-equivalence overclaim.** The equivalence `(D6)` identifies the exact scalar sign but
   does not prove it. Rewriting the sign as anti-Herglotzness, vertical modulus monotonicity, or a
   Schur multiplier bound is coordinate change, not an orientation mechanism.

## Independent constraint--orientation geometry

The corpus contains a second architectural input which is logically independent of the theta
calculation. Finite rational surgery on a discrete Herglotz transform changes its exact number of
negative squares while preserving its full translated differential-relation field. The formal
substitution theorem `DifferentialIndependent.addBase` and its two-sided form
`differentialIndependent_addBase_iff` verify the algebraic mechanism: coordinatewise addition of
base-field rational jets preserves differential independence exactly.

Thus the differential-constraint coordinate and the Krein-orientation coordinate form a genuine
product geometry over one hypertranscendental field. This is used only as a positive carrier
obligation here:

```text
an RH-capable Hedenmalm construction
  must provide a cofinal source-defined section
  coupling the all-prime constraint carrier to the zero-index orientation chamber.
```

Neither maximal translated hypertranscendence nor the Krein index alone can supply that section.
The Weil polarization is the canonical candidate coupling because its source formula contains the
prime tail while its Pick/Krein signature reads the centered divisor.

## Publication boundary

The final paper must be a standalone mathematical article. It must contain complete analytic and
operator-theoretic proofs and no discussion of Lean or project-internal validation. Formal code is
used only as an internal unconditionality check.
