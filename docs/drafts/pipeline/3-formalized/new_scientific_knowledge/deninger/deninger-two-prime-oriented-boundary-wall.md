# Deninger two-prime oriented boundary wall

- **ID:** `deninger-two-prime-oriented-boundary-wall`
- **Stage:** 3-formalized
- **Type:** THEOREM / exact Route-L endpoint classifier
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY-PROVISIONAL] [NOT RH]`
- **Source:** `DeningerCalderonWittOrientedSource`,
  `DeningerOneSidedFramedMateCurvatureTransgression`, and the current Route-L
  source-null-homology wall
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/DeningerCalderonWittTwoPrimeOrientationBoundaryWall.lean`

## Statement

Let

\[
 C^1\xrightarrow{D}C^2\xrightarrow{T}\mathbb C\to0
 \tag{1}
\]

be the all-prime oriented Calder\'on--Witt source complex already constructed
in the corpus.  Write \(j_p:\mathbb C\to C^2\) for the constant-packet
orientation cochain at prime \(p\).  Its normalization is

\[
                         T(j_p(1))=1.                 \tag{2}
\]

For \(s\in\mathbb C\), put

\[
 t(s)=2\operatorname{Re}s-1,
 \qquad
 g_p(s)=\exp(t(s)\log p)=p^{t(s)}.                   \tag{3}
\]

Define the finite-support prime-indexed physical orientation reporter

\[
 \mathcal L_s(z,c)
   =\sum_p\bigl(g_p(s)-1\bigr)\tau_p(z_p),           \tag{4}
\]

where \(z=(z_p)_p\) and \(\tau_p\) is the source-normalized center trace.
Then:

1. the two-prime orientation difference is an explicit source boundary,
   \[
       j_2(1)-j_3(1)=D\,H\bigl(j_2(1)-j_3(1)\bigr),  \tag{5}
   \]
   with \(H\) the canonical all-prime top Green lift;
2. its physical readout is
   \[
       \mathcal L_s\!left(DH(j_2(1)-j_3(1))\right)
         =g_2(s)-g_3(s);                              \tag{6}
   \]
3. consequently
   \[
       \mathcal L_s\!left(DH(j_2(1)-j_3(1))\right)=0
       \quad\Longleftrightarrow\quad
       \operatorname{Re}s=\frac12.                  \tag{7}
   \]

At a Xi divisor point \(\rho\), multiplication by the already constructed
leading coefficient

\[
 c_\rho=\Xi^{(m_\rho)}(\rho)\ne0                    \tag{8}
\]

does not change the zero locus.  Therefore the coefficient-faithful physical
reader annihilates this single explicit two-prime source boundary exactly at
critical-line divisor fibres.  Annihilation at every Xi divisor is equivalent
to RH, but no such annihilation is asserted here.

## Proof

Equation (2) gives

\[
 T(j_2(1)-j_3(1))=1-1=0.
\]

The exactness \(\operatorname{im}D=\ker T\) already proves existence of a
primitive.  The source contains a canonical one: its top Green decomposition
is

\[
 DH(z)+\jmath T(z)=z.
\]

Substituting \(z=j_2(1)-j_3(1)\) and \(T(z)=0\) proves (5).

By definition of (4), normalized source traces give

\[
 \mathcal L_s(j_p(1))=g_p(s)-1.
\]

Linearity and (5) now give

\[
 \mathcal L_s(DH(j_2(1)-j_3(1)))
   =(g_2(s)-1)-(g_3(s)-1)=g_2(s)-g_3(s),
\]

which is (6).

The real exponential is injective, so equality of the two gains is equivalent
to

\[
 t(s)\log2=t(s)\log3,
 \qquad
 t(s)(\log2-\log3)=0.
\]

Strict monotonicity of \(\log\) on the positive reals and \(2<3\) give
\(\log2\ne\log3\).  Hence the equality is equivalent to \(t(s)=0\), which is
\(\operatorname{Re}s=1/2\).  This proves (7).  Equation (8) proves the
coefficient-faithful divisor specialization by cancellation.

## Exact Route-L contribution

This removes three false descriptions of the open core.

1. **Not an unspecified homology theory.**  One concrete source boundary is
   enough; no new absolute or cofinal homology group is required to state the
   obstruction.
2. **Not an infinite-prime convergence problem.**  The minimal obstruction is
   already present on primes 2 and 3.  Infinite completion is required only by
   a proposed producer, not by the logical detector.
3. **Not ordinary source exactness.**  The vector is unconditionally a source
   boundary.  Missing theorem is that the actual singular physical transport
   respects this one boundary.  The displayed reporter proves it does not do
   so formally off the critical line.

The exact theorem is therefore Route L's endpoint falsifier:

`[ENDPOINT FALSIFIER — XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT]`

> Any upstream source theorem must, before divisor specialization, force the
> singular Gamma/co-Poisson transport to annihilate canonical Green boundary
> (5), while retaining nonzero leading Xi jet and both prime labels. On this
> fixed boundary that conclusion is already (7), so it audits a proposed
> producer but cannot serve as its premise.

This is a strict weakening of requiring boundary compatibility on the whole
completed BV/Green source: only one fixed finite source boundary is needed.
It is not a proof of that boundary compatibility. Current upstream producer is
`DAC_DENINGER_RESOLVED_GREEN_SOURCE_ANNIHILATOR`; canonical Möbius inversion reduces it to
source-derived vanishing of
`Omega_(mu,Gamma)=S_mu G_Gamma D`.

## Hostile audit

1. **Is (7) merely another RH criterion?**  Its zero classification is
   elementary.  New project content is the identification of its left side
   with the physical readout of a canonical boundary in the already-built
   all-prime oriented source.  The theorem narrows the producer burden; it
   does not discharge it.
2. **Does source exactness prove the readout vanishes?**  No.  Exactness only
   constructs (5).  A linear functional annihilates it only if it descends
   through source cohomology.  Formula (6) is the exact obstruction to that
   descent.
3. **Could completion, a Tate tower, or a principal-parts duality remove the
   obstruction?**  Not without changing (6).  Any coefficient-faithful
   extension still contains this finite boundary.  A quotient killing it also
   kills the physical distinction that detects horizontal displacement.
4. **Is the global principal-parts module a rigid carrier?**  No.  For a
   domain \(R\) and nonunit \(x\), \(R[x^{-1}]/R\) has nonzero \(x\)-torsion
   and multiplication by \(x\) is surjective with nonzero kernel.  It is not
   finite projective and hence not dualizable as an ordinary module.  Any
   Cartier-duality implementation must be levelwise on finite perfect layers
   or in a genuine Ind/Pro/Tate category.  This carrier correction does not
   affect the finite boundary theorem.
5. **Does indefinite reflected-pair duality suffice?**  No.  Off-line gains
   \(\operatorname{diag}(p^{t/2},p^{-t/2})\) preserve a hyperbolic pairing for
   every real \(t\).  Bare duality, reflection, and transition compatibility
   therefore do not imply (7).  A valid producer must supply the missing
   source-selected boundary compatibility, not generic self-duality.

## Corpus and literature audit

Corpus search found all ingredients separately: global oriented-source
exactness, normalized local prime sections, Deninger mate gains, the physical
paracyclic residue, and the full strict-descent/RH equivalence.  It found no
theorem forming the prime-indexed reporter (4), evaluating it on the canonical
two-prime Green boundary, or reducing Route L to that one boundary.

Primary-literature search found Deninger's rational-Witt sheaf and
correspondence construction (arXiv:2508.05329), the Deninger--Oh Witt
Frobenius/Verschiebung deformation theory (arXiv:1604.03319), and standard
scaling-site/Frobenius programs.  None states (5)--(7), constructs the
prime-indexed Gamma/Xi physical reporter, or proves its source descent.
Novelty is therefore provisional and restricted to the route-specific
boundary identification and minimality reduction, not the exponential
injectivity argument or the parent exact-sequence algebra.

## Gates

- [x] internal corpus collision audit
- [x] external primary-literature collision audit
- [x] exact statement and dependency-closed proof
- [x] RH consumer and circularity boundary stated
- [x] explicit off-line hyperbolic countermodel to bare duality
- [x] unconditional Lean certificate
- [x] targeted axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] module wired into `RHTower.lean`
- [ ] clean repository-wide lint (currently blocked by unrelated concurrently added unreachable modules)

## Log

- 2026-08-07 -- Proved paper theorem, formalized canonical two-prime Green boundary,
  prime-indexed physical reporter, exact gain readout, critical-line equivalence, and
  nonzero-calibration stability. Direct `lake env lean` passed. Generated module `.olean`
  after building only missing `ChebyshevPsiPowerLogPNT.olean`; no full build was run.
