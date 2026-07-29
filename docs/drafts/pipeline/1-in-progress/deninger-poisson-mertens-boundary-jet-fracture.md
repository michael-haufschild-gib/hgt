# Deninger prime-orbit Poisson--Mertens boundary-jet fracture

- **ID:** `deninger-poisson-mertens-boundary-jet-fracture`
- **Stage:** 1-in-progress
- **Type:** SOURCE THEOREM + THIRD-COMPLETION CONJECTURE
- **Scientific status:** `[PAPER-PROVED SOURCE IDENTIFICATION]`
  `[PAPER-PROVED NO-GO]` `[NOVELTY UNVERIFIED]`
  `[CONJECTURAL HYPERFUNCTION WELD]` `[NOT RH]`
- **Parents:**
  - `deninger-prime-packet-topology-haar-retraction`
  - `deninger-tate-poisson-pro-hodge-rigging`
  - `../2-fully-proven/not_new_scientific_knowledge/mertens-logarithmic-corona-differential-tower`
  - `../2-fully-proven/not_new_scientific_knowledge/gamma-meixner-abel-mertens-corona-probe`
  - `../2-fully-proven/not_new_scientific_knowledge/local-euler-valuation-lorentz-log-colligation`
  - `arithmetic-schur-renormalization-law`
  - `source-curved-prime-torus-conormal-temperedness`
- **Statement:** Horizontal Euler translation is exactly a source-curved
  Poisson trajectory on Deninger's transverse prime circles.  Its time-one
  Hardy vector is the reciprocal-prime valuation kernel underlying the
  Gamma and Möbius Schur frames.  Globally, every positive-time trajectory
  vanishes in the Mertens corona while its complete time-zero jet survives
  as the graded logarithmic corona.  Hence the missing third completion
  cannot consist only of ordinary positive-time Hilbert vectors; it must
  retain an infinite-order local-cohomology or hyperfunction class at the
  Poisson-time boundary.

## 1. Two time normalizations which must not be conflated

Fix a rational prime \(p\), put \(L_p=\log p\), and let

\[
 S_p=\mathbb R/L_p\mathbb Z.
\]

This is Deninger's **transverse periodic prime orbit**, not the angular
circle of a Kummer leaf.  On its Fourier characters

\[
 \chi_{p,e}(t)=\exp(2\pi i e t/L_p),\qquad e\in\mathbb Z,
\]

the positive generator

\[
 A_p=|D_{S_p}|,\qquad \widehat A_p=L_pA_p
\]

has spectra

\[
 A_p\chi_{p,e}={2\pi|e|\over L_p}\chi_{p,e},\qquad
 \widehat A_p\chi_{p,e}=2\pi|e|\chi_{p,e}.               \tag{1}
\]

Common Tate time \(r\) for \(\exp(-r\widehat A_p)\) is independent of
\(p\) on Fourier modes.  Horizontal Euler translation by \(h\), however,
multiplies valuation depth \(e\) by \(p^{-he}\).  It is therefore the
**source-curved** Poisson family

\[
 \mathcal P_{p,h}
 =
 \exp\left(-{hL_p\over2\pi}\widehat A_p\right),
 \qquad h>0,                                             \tag{2}
\]

not common Tate time.  Equation `(1)` gives

\[
 \mathcal P_{p,h}\chi_{p,e}
 =p^{-h|e|}\chi_{p,e}.                                  \tag{3}
\]

The factor \(L_p/(2\pi)\) in `(2)` is forced.  Replacing it by one common
time destroys Euler translation covariance.

## 2. Prime-orbit Poisson--valuation Hardy weld

Let \(\delta_p^+\) denote the analytic Hardy half of the point conormal
at the origin of \(S_p\).  Algebraically its nonnegative Fourier
coefficients are all one.  For \(h>0\), `(3)` gives the honest Hardy
vector

\[
 c_{p,h}
 =
 \mathcal P_{p,h}\delta_p^+
 =
 (p^{-he})_{e\ge0}\in\ell^2(\mathbb N),                 \tag{4}
\]

with

\[
 \|c_{p,h}\|_2^2={1\over1-p^{-2h}}.                     \tag{5}
\]

At source time \(h=1\), put \(q_p=p^{-1}\).  Then

\[
 c_{p,1}=(1,q_p,q_p^2,\ldots)=k_{q_p},                  \tag{6}
\]

the reciprocal-prime Hardy kernel already used by the arithmetic Schur
tower.

The two independently constructed source frames are exact scalar
multiples of this one orbit vector:

\[
 H_e(p)
 =
 \sqrt{q_p}(1-q_p)q_p^e
 =
 \sqrt{q_p}(1-q_p)c_{p,1}(e),                           \tag{7}
\]

and

\[
 \Delta B_p(e)
 =
 {q_p(1-q_p)\over1+q_p}q_p^e
 =
 {q_p(1-q_p)\over1+q_p}c_{p,1}(e).                     \tag{8}
\]

Here `(7)` is the half-shifted Gamma valuation coordinate and `(8)` is
the forward Möbius--Schur depth difference.  The backward Hardy shift
therefore gives

\[
 S^*c_{p,1}=q_pc_{p,1},                                 \tag{9}
\]

which is exactly valuation successor and Gamma Schur elimination.

### Theorem A `[PROVED HERE]`

Equations `(2)`--`(9)` identify, without a Xi zero:

1. Deninger's transverse prime-orbit Poisson smoothing;
2. horizontal Euler translation on every prime-power valuation layer;
3. the reciprocal-prime Hardy kernel;
4. the Gamma half-shifted valuation frame;
5. the Möbius Schur difference frame; and
6. Schur residual translation.

They are one source object in different coordinates.  This theorem
does **not** identify the transverse circle Dirichlet form with the
leafwise Kummer Hodge cup metric.

### Proof

Equation `(3)` follows from the Fourier spectrum `(1)`.  Equations
`(4)`--`(6)` are the geometric-series norm and the specialization
\(h=1\).  Equations `(7)`--`(9)` are the closed source formulas proved
in `XiTransverseGammaValuationCoherence.lean`,
`XiMobiusSchurValuationIntertwiner.lean`, and
`ArithmeticSchurRenormalizationLaw.lean`.  No continuation or divisor
input is used.

## 3. The global Mertens corona is the complete boundary jet

For \(k\ge0\), define the first-positive-mode prime field

\[
 b_{k,h}(p)
 =
 L_p^k\,c_{p,h}(1)
 =
 (\log p)^k p^{-h},\qquad h\ge0.                         \tag{10}
\]

Let \(M_k\), \(M_{k,0}\), \(u_k(p)=(\log p)^k\), and
\[
 q_k:\mathbb C u_k+M_{k,0}\longrightarrow\mathbb C
\]
be the graded Mertens spaces and exact quotient maps constructed in
`mertens-logarithmic-corona-differential-tower`.  That theorem gives

\[
 b_{k,0}=u_k,\qquad q_k(b_{k,0})=1,                     \tag{11}
\]

whereas every strictly positive Euler translation satisfies

\[
 b_{k,h}\in M_{k,0},\qquad q_k(b_{k,h})=0
 \quad(h>0).                                            \tag{12}
\]

Coefficientwise differentiation of `(10)` gives the exact jet law

\[
 \partial_h^r b_{k,h}
 =
 (-1)^r b_{k+r,h}.                                      \tag{13}
\]

Consequently

\[
 q_{k+r}\!\left(\partial_h^r b_{k,h}|_{h=0}\right)
 =(-1)^r,                                               \tag{14}
\]

while for every \(h>0\),

\[
 q_{k+r}(\partial_h^r b_{k,h})=0.                       \tag{15}
\]

### Theorem B `[PROVED HERE]`

The complete graded Mertens logarithmic corona is the nonzero
time-zero boundary jet of the source-curved Deninger Poisson orbit
whose every positive-time germ is corona-zero.  Its \(r\)-th boundary
jet is exactly the \(r\)-th prime-log clock grade.

### Proof

Equation `(10)` is the \(e=1\) coefficient of `(4)`.  Equations
`(11)`--`(12)` are respectively the exact corona normalization and the
positive Euler-translation vanishing theorem.  Differentiating
\(p^{-h}=\exp(-h\log p)\) gives `(13)`, and applying the already-proved
quotient normalizations gives `(14)`--`(15)`.

## 4. Positive-time-only completion no-go

Suppose a Hausdorff topological vector space \(V\) receives the corona
class faithfully and the source-curved positive-time orbit descends
continuously to \(h=0\).  By `(12)`, its image is zero for every
\(h>0\).  Hausdorff continuity forces its value at \(h=0\) to be zero,
contradicting `(11)`.  If smooth descent is demanded, all boundary
derivatives also vanish, contradicting `(14)`.

### Theorem C `[PROVED HERE]`

No Hausdorff completion can simultaneously:

1. quotient every positive Euler translate by the Mertens
   vanishing-tail layer;
2. extend the resulting source-curved Poisson orbit continuously to
   \(h=0\); and
3. retain the nonzero Mertens corona class, let alone its complete
   logarithmic jet.

In particular, ordinary positive-time Hilbert vectors and their
Hausdorff projective limit are not by themselves the third completion.
The boundary charge must be added as a singular derived object.

This does not rule out a rigged Hilbert construction.  It says exactly
what such a rigging must add beyond its positive-time Hilbert levels.

## 5. First refinement: a two-sided Poisson hyperfunction weld

`[CONJECTURE] [DAC_SOURCE_CURVED_POISSON_HYPERFUNCTION_WELD]`

The completed Euler--Gamma/co-Poisson source has a source-defined,
Hausdorff local-cohomology rigging in the horizontal translation
parameter,

\[
 \Phi_{\rm arith}
 \subset
 \mathbb H^1_{\{h=0\}}(\mathscr E_{\rm Euler\text{-}Gamma})
 \subset
 \Phi_{\rm arith}',
                                                               \tag{16}
\]

with all of these properties:

1. its associated graded boundary module is the Mertens logarithmic
   corona \(Q_{\rm gr}=\mathbb C[L][u_0]\);
2. its local prime Fourier realization is `(4)`, so the arithmetic
   Gamma and Möbius Schur frames are literal Poisson boundary values;
3. it retains the two chiral boundary values \(h\to0^+\) and
   \(h\to0^-\), with functional-equation reflection exchanging them;
4. its source boundary map is conservative for the full
   Meyer/co-Poisson Cauchy data, including multiplicity jets;
5. its positive boundary residue is the global Green--Stokes/Paugam
   cup form, not an arbitrarily chosen Hilbert metric; and
6. its calibrated Gamma comparison preserves singular support in the
   horizontal translation variable.

For an on-shell Xi zero \(\rho\), the two reflected Mertens germs have
support locations

\[
 -\rho,\qquad \overline\rho-1.                           \tag{17}
\]

If the source comparison in item 6 identifies their classes while
conserving support, `(17)` forces

\[
 -\rho=\overline\rho-1,
\]

and hence \(\Re\rho=1/2\).  Thus items 4--6 contain the RH-bearing
theorem.  Items 1--3 are now forced by Theorems A--C rather than
postulated topology.

Hyperfunctions, rather than distributions, are the smallest natural
candidate because a point-supported distribution has finite order,
whereas `(14)` contains one nonzero symbol in every logarithmic grade.
This is a category prediction, not yet a construction.  The later
two-scale audit in `deninger-mertens-adiabatic-exponential-corner`
shows that it is still incomplete: a one-variable hyperfunction can
retain every \(h\)-jet but not the exponentially flat
\(\varepsilon_p=1/\log p\) rate-normal.  The sharpened third
completion is the two-sided adiabatic blow-up equipped with an
exponential/transseries associated graded; the present conjecture is
its \(\tau=0\) boundary face.

## 6. Why this changes the frontier

The previous alternatives were:

1. finite truncations retain evaluation but leak prime covariance;
2. ambient adelic \(L^2\) restores covariance but erases divisor
   fibres; and
3. positive-time pro-Hodge levels regularize local Green forms.

Theorems A--C add the missing fourth fact:

> arithmetic covariance itself follows a prime-dependent Poisson-time
> diagonal, and the complete HT/Mertens source charge lives only as
> its infinite-order boundary fracture.

Therefore no proof can obtain RH from positivity at a fixed collar
scale, or from an ordinary limit of such scales.  Required mechanism
is a positive **boundary residue on derived Poisson-time cohomology**.
This is where hypertranscendence can matter: finite differential
stencils see only finitely many grades and are already proved blind;
the source class has nonzero symbols at every grade.

## 7. Hostile audit

1. **Not Kummer leaf Hodge.**  \(S_p\) is transverse.  The theorem
   does not prove a Paugam cup-isometry.
2. **Not RH.**  Theorem C fixes the category of a possible solution;
   it does not prove support conservation in item 6.
3. **Not a renamed Hardy kernel.**  The Hardy kernel is classical.
   Corpus-new content is its exact simultaneous identification with
   Deninger orbit time, Euler horizontal translation, Gamma
   valuation, Möbius Schur depth, and every Mertens corona jet.
4. **No finite-jet escape.**  Any finite truncation of `(14)` is
   compatible with known off-line fake systems.  The full
   point-supported infinite-order class is essential.
5. **No arbitrary topology.**  `(11)`--`(15)` prescribe the boundary
   values and associated graded.  A topology that merely declares
   them continuous without realizing the source Poisson germs is
   rejected.
6. **No positivity import.**  Positive-time Poisson contraction is
   compatible with the corona erasure `(12)`.  Desired positive
   boundary residue must be derived from completed source
   Green--Stokes comparison.
7. **No automatic support faithfulness.**  Local cohomology records
   support, but the Euler--Gamma comparison could still collapse it.
   Proving it does not is the exact open core.

## 8. Falsifiers and next theorem

The conjecture fails if:

- the completed source has no two-sided horizontal boundary germ;
- the Gamma recurrence does not act on the same local-cohomology
  object as the Euler translation;
- Meyer Cauchy data do not map conservatively into `(16)`;
- Green--Stokes residue is indefinite on the source harmonic quotient;
  or
- calibrated comparison can identify noncoincident support germs.

The smallest constructive next theorem is:

> Build the reflected Euler--Gamma local-cohomology sheaf whose
> associated graded is \(Q_{\rm gr}\), prove that the first-mode
> boundary map is `(10)`--`(15)`, and compute its Gamma transgression.

Only after that dependency is closed should one attempt the
support-conservativity/RH theorem.

## 9. Novelty boundary

Circle Poisson semigroups, Hardy coherent kernels, Mertens asymptotics,
graded Marcinkiewicz quotients, and point-supported hyperfunctions are
parent mathematics.  Initial arXiv searches found Deninger prime
orbits, general Hardy Poisson kernels, and co-Poisson/scaling
constructions, but no source-curved prime-orbit Poisson identification
with the complete graded Mertens boundary jet.  This is search
noncollision, not a priority certificate.

Potentially new and significant content begins with:

1. Theorem B's exact arithmetic boundary-jet identification;
2. Theorem C's forced derived-completion category; and
3. construction of the source-selected weld `(16)` with conservative
   positive support.

## Gates

- [x] distinguish common Tate time from source-curved Euler time
- [x] prove local prime-orbit Poisson--Hardy identity
- [x] identify Gamma and Möbius valuation frames with the time-one
      orbit vector
- [x] prove the Mertens corona is the complete time-zero boundary jet
- [x] prove positive-time-only Hausdorff completion no-go
- [x] freeze the hyperfunction-weld conjecture before proof design
- [ ] independent specialist literature audit
- [ ] construct the reflected Euler--Gamma local-cohomology sheaf
- [ ] compute its Gamma transgression
- [ ] prove full-Cauchy/Meyer conservativity
- [ ] prove positive Green--Stokes boundary residue
- [ ] prove calibrated affine-support faithfulness
- [ ] formalize dependency-closed source theorems in Lean
- [ ] prove RH

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400.
- Paul S. Muhly and Baruch Solel, *The Poisson Kernel for Hardy
  Algebras*, arXiv:0707.1774.
- Alain Connes and Caterina Consani, *The Scaling Hamiltonian*,
  arXiv:1910.14368.

## Log

- 2026-07-28 — Identified Euler horizontal translation with the
  prime-dependent Poisson time \(h\log p/(2\pi)\), welded its time-one
  orbit to the Gamma/Möbius valuation Hardy kernel, and proved that
  the complete graded Mertens corona is its singular time-zero jet.
  This rules out positive-time-only completions and isolates the
  reflected Poisson hyperfunction weld as the new open core.
