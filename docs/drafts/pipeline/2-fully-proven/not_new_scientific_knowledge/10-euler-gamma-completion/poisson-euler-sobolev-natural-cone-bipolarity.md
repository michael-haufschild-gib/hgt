# Poisson--Euler Sobolev natural-cone bipolarity

- **ID:** `poisson-euler-sobolev-natural-cone-bipolarity`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** EXACT ADDITIVE--MULTIPLICATIVE IDENTIFICATION / RH MECHANISM BASE
- **Scientific status:** `[PAPER PROOF COMPLETE] [NOT RH]`
  `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE] [INTERPRETIVE SIGNIFICANCE PASS]`
- **Parents:**
  - `../../1-in-progress/squarefree-fourier-torsion-counterface-completion.md`;
  - `prime-valuation-dyadic-fermion-normal-cone-law.md`;
  - `../prime-valuation-kakutani-polar-third-completion.md`;
  - `../not_new_scientific_knowledge/fe-fourier-quasicrystal.md`.

## What was hidden by the separate languages

The Poisson/theta and Euler/prime-valuation constructions are not merely compatible descriptions
of zeta.  They are two polarizations of one source distribution.

Let
\[
 D=\delta_0-1\in{\cal D}'(\mathbb T).
 \tag{1}
\]
Its nonzero Fourier coefficients are all equal to one:
\[
 \widehat D(n)=1\qquad(n\in\mathbb Z\setminus\{0\}).
 \tag{2}
\]
The real-line lift of \(\delta_0\) is the ordinary integer Dirac comb
\[
 \Sha=\sum_{n\in\mathbb Z}\delta_n,
 \qquad
 \widehat\Sha=\Sha.
 \tag{3}
\]
Thus `(1)` is the mean-zero periodic boundary of the literal Poisson-self-dual source.

Additive Fourier analysis sees `(1)` as a point conormal with critical Sobolev order \(1/2\).
Multiplicative unique factorization sees the same positive-frequency coefficient vector as the
independent product of all prime-valuation geometric states.  The exact Hellinger--Rees
reflection fracture is therefore the natural-cone geometry of the Sobolev wall of the Poisson
comb.  It is not a probabilistic analogy added to zeta.

## 1. Exact Sobolev wall

On mean-zero distributions put
\[
 \|T\|_{\dot H^{-r}(\mathbb T)}^2
 =
 \sum_{n\ne0}|\widehat T(n)|^2|n|^{-2r}.
 \tag{4}
\]
Equations `(1)` and `(2)` give
\[
 \boxed{
 \|D\|_{\dot H^{-r}}^2=2\zeta(2r)
 }
 \qquad(r>1/2).
 \tag{5}
\]
Consequently
\[
 D\in\dot H^{-r}
 \Longleftrightarrow r>1/2,
 \qquad
 \lim_{r\downarrow1/2}(2r-1)\|D\|_{\dot H^{-r}}^2=2.
 \tag{6}
\]
The critical number \(1/2\) is the half-codimension regularity of a point distribution in one
real dimension.  It is already present before Mellin transformation or a zero divisor.

Let \(P_+D\) denote the positive-frequency part.  The coefficient map
\[
 U_r:\dot H^{-r}_+(\mathbb T)\longrightarrow\ell^2(\mathbb N),
 \qquad
 (U_rT)_n=\widehat T(n)n^{-r},
 \tag{7}
\]
is unitary by definition, and
\[
 U_r(P_+D)=v_r:=\sum_{n\ge1}n^{-r}e_n,
 \qquad
 \|v_r\|^2=\zeta(2r).
 \tag{8}
\]

## 2. Exact Euler natural-cone factorization

Unique factorization gives the canonical incomplete tensor-product identification
\[
 \ell^2(\mathbb N)
 \simeq
 \widehat\bigotimes_p\ell^2(\mathbb N_0),
 \qquad
 e_n\longmapsto\bigotimes_p e_{v_p(n)}.
 \tag{9}
\]
For \(r>1/2\), equation `(8)` factors as
\[
 v_r
 =
 \bigotimes_p
 \left(\sum_{k\ge0}p^{-rk}e_k\right).
 \tag{10}
\]
After normalization, its local squared amplitudes are
\[
 \Pr_r(v_p(n)=k)
 =
 (1-p^{-2r})p^{-2rk}.
 \tag{11}
\]
Put
\[
 c=\frac12-r.
 \tag{12}
\]
Then `(11)` is exactly the ordinary-prime valuation law
\[
 \mu_{p,c}(k)
 =
 (1-p^{-(1-2c)})p^{-(1-2c)k}.
 \tag{13}
\]

> **[THEOREM -- POISSON--EULER NATURAL-CONE IDENTIFICATION.]**
> The normalized positive-frequency Sobolev representative of the periodic Poisson comb at
> order \(r>1/2\) is, under unique factorization, exactly the square-root/natural-cone vector of
> the all-prime valuation product state at radial character \(c=1/2-r\).

For \(r,s>1/2\), its overlap is simultaneously
\[
 \begin{aligned}
 \left\langle\frac{v_r}{\|v_r\|},\frac{v_s}{\|v_s\|}\right\rangle
 &=
 \frac{\zeta(r+s)}
 {\sqrt{\zeta(2r)\zeta(2s)}}\\
 &=
 \prod_p
 \frac{\sqrt{(1-p^{-2r})(1-p^{-2s})}}
 {1-p^{-(r+s)}}.
 \end{aligned}
 \tag{14}
\]
The second line is precisely the product Hellinger affinity of `(11)`.  Finite-prime truncation
gives the finite Hellinger determinant before any limiting operation.

As \(r\downarrow1/2\), every fixed coefficient of the normalized vector tends to zero while its
norm remains one.  Hence
\[
 \frac{v_r}{\|v_r\|}\rightharpoonup0.
 \tag{15}
\]
This is the same weak escape proved independently for finite-prime valuation states.  The Wold
half-density scale, the pole of \(\zeta(2r)\), Kakutani disjointness, and point-conormal Sobolev
escape are four shadows of one vector.

## 3. Squarefree singular layer

Restrict `(8)` to squarefree frequencies:
\[
 v_r^{\rm sf}
 =
 \sum_{n\ge1}\mu^2(n)n^{-r}e_n,
 \qquad
 \|v_r^{\rm sf}\|^2
 =
 Z_{\rm sq}(2r)
 =
 \frac{\zeta(2r)}{\zeta(4r)}.
 \tag{16}
\]
Under `(9)`,
\[
 v_r^{\rm sf}
 =
 \bigotimes_p(e_0+p^{-r}e_1).
 \tag{17}
\]
Thus the squarefree Fourier--torsion distribution and the first fermionic digit of the
prime-valuation state are literally the same Sobolev vector.  The exact dyadic factorization of
the parent gives
\[
 v_r
 \simeq
 v_r^{\rm sf}
 \widehat\otimes
 v_{2r}^{\rm sf}
 \widehat\otimes
 v_{4r}^{\rm sf}
 \widehat\otimes\cdots .
 \tag{18}
\]
Only the first factor reaches a Sobolev pole at \(r=1/2\); every higher factor is regular there.
This proves at vector level, rather than only at Euler-product level, the decomposition
\[
 \text{critical Poisson comb}
 =
 \text{squarefree singular conormal}
 \widehat\otimes
 \text{regular dyadic tower}.
 \tag{19}
\]

The prime-profile theorem of the first parent is the full blow-up of `(16)`.  For
\(f\in C^1([0,1],\mathbb R)\), \(f(0)=0\), the finite-aperture deformed coefficients
\[
 \mu^2(n)n^{-1/2}
 \exp\!\left(\sum_{\substack{p\mid n\\p\le x}}
 f\!\left(\frac{\log p}{\log x}\right)\right)
\tag{20}
\]
are taken over squarefree \(n\) all of whose prime divisors are at most \(x\).
Their normalized vectors
have limiting Gram kernel
\[
 \exp\!\left[
 -\frac12\int_0^1
 (e^{f(t)}-e^{g(t)})^2\,\frac{dt}{t}
 \right].
 \tag{21}
\]
Hence the coherent Fock field over \(L^2((0,1),dt/t)\) is the normal bundle of the
squarefree Sobolev wall of the Poisson source.

## 4. The Mellin reporter is the other polarization

Let
\[
 \theta(t)=\langle\Sha,e^{-\pi t(\cdot)^2}\rangle
 =\sum_{n\in\mathbb Z}e^{-\pi n^2t}.
 \tag{22}
\]
For \(\Re s>1\),
\[
 \int_0^\infty(\theta(t)-1)t^{s/2-1}\,dt
 =
 2\pi^{-s/2}\Gamma(s/2)\zeta(s).
 \tag{23}
\]
Poisson self-duality `(3)` gives
\[
 \theta(t)=t^{-1/2}\theta(1/t),
 \tag{24}
\]
and therefore the completed zeta reflection after the two elementary boundary terms are
separated.

Equations `(10)` and `(23)` are two transforms of the same integer source:

```text
integer comb
  additive/Fourier polarization       -> theta--Poisson reflection;
  multiplicative/unique-factorization -> prime-valuation natural cone;
  Gaussian Mellin scalarization       -> completed zeta reporter.
```

The functional equation is exact in the additive reporter.  The Hellinger--Rees regularity
fracture is exact in the multiplicative producer.  The RH problem is the missing strict
comparison between these two polarizations at their common half-density wall.

## 5. Exact zero coordinate

For a nontrivial zeta zero \(\rho\), the corpus radial coordinate is
\[
 c_\rho=\frac12-\Re\rho.
 \tag{25}
\]
By `(12)`, its Sobolev coordinate is not a newly chosen parameter:
\[
 \boxed{r_\rho=\Re\rho.}
 \tag{26}
\]
Functional-equation reflection sends \(r_\rho\) to \(1-r_\rho\).  If
\(r_\rho>1/2\), the corresponding producer vector is an honest Sobolev/natural-cone vector while
its reflection is outside every such Hilbert chart.  At \(r_\rho=1/2\), both meet the common
enhanced boundary.  This is the literal regularity meaning of the critical line.

Equation `(26)` does not prove that a divisor conormal is represented by the producer vector.
That source-first landing is the remaining RH-bearing theorem.

## 6. What the universal law must now say

The data suggest the following statement, but it is not part of the proved theorem.

> **[FROZEN CONJECTURE -- ADDITIVE--MULTIPLICATIVE HALF-DENSITY PURITY.]**
> For the ordinary integer comb, every nontrivial Mellin divisor conormal and every top
> multiplicity jet has a presentation-independent lift to the enhanced critical Sobolev normal
> bundle before divisor specialization.  Poisson reflection acts strictly on that lift and
> preserves its prime-scale defect measure.  Therefore its Sobolev order equals the order of its
> reflected lift.

By `(25)`--`(26)` and the Hellinger--Rees trichotomy, this conjecture implies RH.  Its content is
not positivity of a completed function.  It is conservation of exact source regularity under the
comparison of the additive and multiplicative polarizations of one distribution.

This identifies the proposed third completion:

```text
not: another scalar L2 space;
but: enhanced critical Sobolev normal bundle of the Poisson comb,
     with additive Fourier and multiplicative Euler polarizations,
     squarefree singular Fock face, regular dyadic tower,
     half-normal and rapid/Stokes ends, and strict Mellin graph.
```

The arithmetic Calderón--Green intermediate extension and the strict squarefree
Fourier--Mellin graph are two existing corpus presentations of this same required comparison.

## 7. Hostile audit

1. **Classical identities remain classical.**  Poisson summation, `(5)`, unique factorization,
   Euler products, and `(23)` are not novelty claims.
2. **A common source does not give a strict comparison.**  Mellin scalarization can lose the
   Sobolev defect measure and point conormal.  This is precisely the open theorem.
3. **Fourier transform need not preserve Sobolev order in general.**  The conjecture concerns the
   source-effective lift of nontrivial Mellin divisor classes in the self-dual comb, not arbitrary
   tempered distributions.
4. **Endpoint residue is insufficient.**  The scalar residue in `(6)` loses isolated conormals.
   The full normal field `(20)`--`(21)` and its Stokes ends are required.
5. **Reflection can exchange boundary faces.**  Strictness cannot be declared.  It must follow
   from the source Fourier--Mellin graph and preserve the prime-scale defect measure.
6. **Generalized-prime countermodels do not carry `(3)`.**  Their target functional equation,
   positivity, or hypertranscendence does not supply the ordinary integer additive lattice and its
   unique-factorization polarization.  This explains why they do not falsify the conjecture, but
   does not prove it.
7. **The theorem does not see zero multiplicity.**  Top conormal-jet faithfulness remains
   independent.

## 8. Novelty and significance gate

Targeted searches found the classical ingredients separately but no source stating the exact
joint identification
\[
 \text{Sobolev natural-cone vector of the periodic Poisson comb}
 =
 \text{ordinary-prime valuation product state},
 \tag{27}
\]
together with its squarefree Fock normal bundle and interpretation of
\(r=\Re s\) as the shared additive--multiplicative regularity coordinate.  But every identity in
the present card is a direct composition of classical Sobolev Fourier coefficients, the
Hardy--Dirichlet reproducing kernel, unique factorization, and Poisson/Mellin formulas.  Absence of
the assembled sentence in a search does not make that composition new mathematics.  The card is
therefore classified as a corpus bridge, not external novelty.

- `[ANTI-THEATRE -- PASS AS INTERPRETATION, FAIL AS NOVEL THEOREM]` Equations `(5)`--`(19)` are
  elementary once the previously separate constructions are placed in one coefficient model.
  Their value is the exact bridge and the new proof target, not technical difficulty.
- `[SIGNIFICANCE -- PASS]` The bridge replaces an abstract producer--reporter pair by one explicit
  distribution with two polarizations and identifies the critical line as its common
  half-density wall.
- `[FIELDS VERDICT]` Not yet.  The Fields-scale theorem is the frozen strict comparison, which
  would prove RH.
- `[RH BOUNDARY]` No unconditional exclusion of off-line zeros is claimed.

## Gates

- [x] identify periodic Poisson point conormal and exact Sobolev wall
- [x] identify its positive-frequency Sobolev vector
- [x] prove exact prime-valuation natural-cone factorization
- [x] prove exact overlap/Hellinger identity
- [x] identify squarefree Fourier vector with singular fermionic digit
- [x] attach Gaussian Mellin completed-zeta reporter
- [x] identify zero radial coordinate with Sobolev order
- [x] preliminary corpus and external collision search
- [ ] independent harmonic-analysis audit
- [ ] independent analytic-number-theory audit
- [ ] construct strict enhanced Fourier--Mellin graph
- [ ] prove source-first Xi conormal and multiplicity landing
- [ ] prove reflection strictness for prime-scale defect measure
- [ ] RH
