# Prime--Gamma factorial fugacity boundary

- **ID:** `prime-gamma-factorial-fugacity-boundary`
- **Stage:** 1-in-progress
- **Type:** `[PAPER-PROVED THEOREM] [BOLD CONJECTURE] [RH FRONTIER]`
- **Scientific status:** `[CORPUS-NEW SYNTHESIS] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Source inputs:**
  - `julia-critical-factorial-defect-measure-completion.md`
  - `reflected-character-singular-splitting-bockstein-law.md`
  - `../4-publication-ready/riemann-source-modular-superselection/main.tex`
  - `../2-fully-proven/new_scientific_knowledge/gamma/gamma-factorial-hilbert-hankel-source-normal-bridge.md`
- **RH used:** no
- **Computation used:** no
- **Statement:** The complete factorial jet tower has a natural fugacity variable.  At critical
  Gamma damping its all-prime character is holomorphic precisely on one half-plane, with a unique
  logarithmic boundary singularity at the identity jet character.  Julia aperture regularizes
  every fugacity.  The even and odd completions both contain the same singular identity sector;
  their supertrace cancels exactly that sector and therefore cannot by itself force RH.

## Why this is a different completion

The critical even-factorial completion sums to `cosh`, so it retains two exponential jet
characters while hiding which one causes divergence.  Introduce a real factorial-jet fugacity
\(\lambda\) and write
\[
 \ell_x(p)=\operatorname{JuliaClock}_x(p),\qquad
 g_x(\lambda,p)
 =\phi_\infty(2\log p)\,p^{-1}e^{\lambda\ell_x(p)}.
\tag{PJF1}
\]
At \(x=0\), set \(\ell_0(p)=\log p\):
\[
 g_0(\lambda,p)
 =\phi_\infty(2\log p)\,p^{\lambda-1}.
\tag{PJF2}
\]
The sought third completion is therefore not forced to be one more Hilbert space.  It can be a
holomorphic field in \(\lambda\), together with a singular but Hausdorff conormal fibre at its
abscissa boundary.

## `[PAPER-PROVED]` Positive aperture regularizes every fugacity

For every \(x>0\) and every real \(\lambda\),
\[
 \sum_p g_x(\lambda,p)<\infty.
\tag{PJF3}
\]
Indeed
\[
 0\le\ell_x(p)\le {2\over\sqrt3\,x}
\]
and
\[
 \phi_\infty(2\log p)\le{\sqrt2\over p}.
\]
For \(\lambda\ge0\), the summand is bounded by
\(\sqrt2 e^{2\lambda/(\sqrt3x)}p^{-2}\); for \(\lambda<0\), it is bounded by
\(\sqrt2p^{-2}\).

This is an all-character statement.  Julia aperture cuts off exponential jet growth before any
divisor point is selected.

## `[PAPER-PROVED]` Exact critical abscissa

The critical boundary series has the sharp classification
\[
 \boxed{\qquad
 \sum_p g_0(\lambda,p)<\infty
 \quad\Longleftrightarrow\quad
 \lambda<1.
 \qquad}
\tag{PJF4}
\]
For \(\lambda<1\), the Gamma estimate gives
\[
 g_0(\lambda,p)\le\sqrt2\,p^{\lambda-2},
\]
whose prime sum converges because \(2-\lambda>1\).  For \(\lambda\ge1\),
\[
 g_0(\lambda,p)\ge g_0(1,p)
 =\phi_\infty(2\log p)\ge {1\over p},
\]
and the prime harmonic series diverges.

More precisely,
\[
 \sum_p g_0(\lambda,p)
 \sim \sqrt2\log {1\over1-\lambda}
 \qquad(\lambda\uparrow1).
\tag{PJF5}
\]
The exact identity
\[
 \phi_\infty(2\log p)
 ={ \sqrt2\over p\sqrt{1+p^{-4}}}
\]
differs from \(\sqrt2/p\) by an absolutely summable \(O(p^{-5})\) correction, uniformly for
\(\lambda\) near \(1\).  Equation `(PJF5)` is then the standard prime-zeta asymptotic at its
abscissa.

Thus critical prime-harmonic escape is one logarithmic conormal at one factorial character,
not diffuse failure of every infinite jet direction.

## `[PAPER-PROVED]` Circle-character and parity decomposition

For complex fugacity \(\lambda=e^{i\theta}\), absolute convergence is governed by
\(\Re\lambda=\cos\theta\).  Hence every nontrivial unit-circle character is trace class at the
critical boundary, while the identity character \(\theta=0\) is not:
\[
 \sum_p |g_0(e^{i\theta},p)|<\infty
 \quad\Longleftrightarrow\quad
 e^{i\theta}\ne1.
\tag{PJF6}
\]

The even and odd factorial sectors are
\[
 E_x(p)=\phi_\infty(2\log p)p^{-1}\cosh\ell_x(p),
\qquad
 O_x(p)=\phi_\infty(2\log p)p^{-1}\sinh\ell_x(p).
\tag{PJF7}
\]
They are the two parity projections of the fugacity characters:
\[
 E_x={g_x(1)+g_x(-1)\over2},
\qquad
 O_x={g_x(1)-g_x(-1)\over2}.
\tag{PJF8}
\]
At the critical boundary both \(\sum_pE_0(p)\) and \(\sum_pO_0(p)\) diverge, but
\[
 E_x(p)-O_x(p)
 =\phi_\infty(2\log p)p^{-1}e^{-\ell_x(p)}.
\tag{PJF9}
\]
Since the right side is bounded by \(\sqrt2p^{-2}\), dominated convergence gives the canonical
finite relative limit
\[
 \lim_{x\downarrow0}\sum_p(E_x(p)-O_x(p))
 =\sum_p\phi_\infty(2\log p)p^{-2}<\infty.
\tag{PJF10}
\]

The two parity defect measures have the same escaped part, so their normalized difference
vanishes.  Their unnormalized difference remains tight on the ordinary primes.  This explains,
in one formula, both why a graded relative completion can cross the Hilbert divergence and why
its scalar supertrace loses the RH-bearing escaped mass.

The same law holds for every finite cyclic grading.  Fourier decomposition of jet order modulo
\(k\) gives characters \(e^{2\pi i m/k}\); all nontrivial characters are critical trace-class,
and only \(m=0\) contains the logarithmic singularity.

## Relation to the updated fixed-width tomography

The formal identity
\[
 A_L(w)=\Theta_L\!\left(\frac12,\frac12-w\right)
\tag{PJF11}
\]
shows that fixed-width Xi tomography and the factorial fugacity field use the same unsquared
exponential interval cell.  Its pole residue is
\[
 2m(w)\Theta_L\!\left(\frac12,\frac12-w\right)^2,
\tag{PJF12}
\]
and the cell is nonzero on every right Xi divisor point.  Multiplication by this fixed nonzero
cell does not alter the fugacity abscissa.  What remains unproved is that the tomography polar
class pulls back *linearly, before the square*, to the singular identity fibre of `(PJF4)`.

## Reflected-character interpretation

Let
\[
 q=\Re\rho-\frac12.
\]
On the factorial boundary, source inverse and analytic adjoint differ by \(p^{2q}\).  Relative
to the identity factorial character, the two reflected sectors therefore have fugacity rates
\[
 \lambda_+(\rho)=1+2q,\qquad
 \lambda_-(\rho)=1-2q.
\tag{PJF13}
\]
If \(q\ne0\), exactly one lies in the convergent half-plane and the other lies beyond the
abscissa.  If \(q=0\), both are the same singular identity fibre:
\[
 \lambda_+(\rho)=\lambda_-(\rho)=1.
\tag{PJF14}
\]

This is the analytic-topological form of reflected-character diagonal Ext support.  A genuine
same-fibre dagger must preserve the abscissa stratum; it cannot identify a trace-class interior
fibre with a supercritical exterior fibre.

## `[BOLD CONJECTURE]` Factorial-fugacity boundary dagger law

`XI_FACTORIAL_FUGACITY_BOUNDARY_DAGGER_LANDING`

> The ordinary-prime Euler--Gamma--Julia preclosure has a source-defined factorial-fugacity
> completion \(\mathcal F\) with:
>
> 1. holomorphic interior \(\Re\lambda<1\) given by `(PJF2)`;
> 2. a Hausdorff logarithmic conormal fibre at \(\lambda=1\), obtained as the Julia-aperture
>    boundary and carrying the defect measure of the critical factorial incidence;
> 3. the complete finite cyclic jet gradings as its trace-class boundary characters;
> 4. a linear fixed-width-tomography/Gamma-interval pullback which sends every Xi polar class
>    nontrivially into that conormal fibre before squaring; and
> 5. the source reflection/Sonin involution extending as an internal bounded dagger on the image
>    of every Xi polar class.

Clauses 1--3 are explicit and unconditional.  Clause 4 is the current comparison problem.
Clause 5 is the RH-bearing theorem.  Given 4--5, `(PJF13)` and preservation of the abscissa
stratum force \(q=0\) for every nontrivial zero, hence RH.

The intended provider for boundedness is not an assumed metric.  At every positive aperture the
Julia lift is an explicit isometry and Sonin/Fourier reflection is contractive.  The required
theorem is that the source-defined tomography pullback is a restriction of those fixed
contractions with a bound uniform as \(x\downarrow0\).  A zero-dependent renormalization is
forbidden.

## Lean status

The dependency-closed boundary law is formalized in
`formal/GaloisForLFunctions/RHTower/PrimeGammaFactorialFugacityBoundary.lean`:

- every real fugacity is summable at positive Julia aperture;
- the critical boundary is summable exactly when \(\lambda<1\);
- reciprocal rates \(1+2q\) and \(1-2q\) have the same summability status exactly when \(q=0\);
- even minus odd critical columns equal the summable negative-fugacity character.

The conditional RH consumer is formalized separately in
`formal/GaloisForLFunctions/RHTower/PrimeGammaFactorialFugacityRH.lean`.
Its hypothesis is exactly the unproved dagger preservation of the two reciprocal Xi-fibre
summability classes.  No structure packages that hypothesis as constructed data.

## What this law explains

```text
finite Rees blindness
  = finite Taylor data cannot reach the exponential fugacity boundary

essential singularity requirement
  = identity jet character is a logarithmic abscissa conormal

critical Julia defect measure
  = microlocal blow-up of mass approaching lambda = 1

even/odd orientation loss
  = both parity projections contain the same identity singularity

finite supertrace no-go
  = grading cancels precisely the singular sector carrying escaped mass

hyperbolic/Krein uniqueness
  = reciprocal fugacity characters conserve only their cross pairing

fixed-width tomography
  = nonzero Xi polar square of the same exponential interval cell

critical line
  = reflected characters occupy one and the same abscissa fibre
```

## Hostile audit

1. **Elementary-series warning.** The convergence estimates and parity identities are elementary.
   Candidate novelty lies only in their joint source interpretation and proposed Xi pullback.
2. **Generalized-prime falsifier.** Any generalized-prime system with prime-harmonic density may
   have the same fugacity wall.  Existence of `(PJF4)` does not imply RH.
3. **Scalar-supertrace falsifier.** `(PJF10)` cancels the identity singularity and therefore erases
   the very stratum that distinguishes reflected rates.  A scalar Witten index is not the proof.
4. **Analytic-continuation falsifier.** Meromorphically continuing a fugacity series beyond
   \(\Re\lambda=1\) does not make reflection bounded in the source topology.
5. **Functional-equation falsifier.** Functional-equation reflection pairs the two rates but does
   not prove that they occupy one bounded same-fibre completion.
6. **Zero-fitting falsifier.** Neither \(\mathcal F\), its topology, nor its dagger may depend on
   \(\rho\).  Zeros enter only by evaluation of the already-constructed tomography class.
7. **Square-root falsifier.** Choosing a branch of the squared tomography residue after zero
   specialization is not a linear source pullback.

## Exact next obstacle

`XI_TOMOGRAPHY_FUGACITY_LINEAR_PULLBACK`

Construct one pre-divisor linear transform from the arithmetic fixed-width sequence to the
Julia-regularized fugacity field and prove:

1. it factors through the exact interval-cell identity `(PJF11)`;
2. it is nonzero on every tomography polar class;
3. it has a uniform contractive Sonin/Julia realization for positive aperture;
4. its limit lands in the logarithmic conormal at \(\lambda=1\);
5. reflection is dagger-natural on that limit.

Items 1--2 must not use a square root after residue extraction.  Items 3--5 are the load-bearing
source theorem.

## Gates

- [x] exact positive-aperture all-fugacity convergence
- [x] exact critical abscissa classification
- [x] circle-character and parity/supertrace consequences
- [x] fixed-width tomography interval-cell bridge
- [x] formalize the dependency-closed real-fugacity abscissa theorem, parity cancellation, and
      conditional RH consumer
- [ ] construct the linear tomography-to-fugacity pullback
- [ ] prove uniform Sonin/Julia contractivity and dagger naturality
- [ ] specialist external novelty audit

## Log

- 2026-07-31 — Reinterpreted the critical even-factorial divergence as one identity-character
  singularity in a complete factorial-fugacity field.  Proved the sharp abscissa
  \(\lambda=1\), all nontrivial circle twists trace-class, and canonical even--odd relative
  cancellation.  Isolated why scalar supertrace is a dead consumer and why a signed
  same-fibre dagger must act before that cancellation.
