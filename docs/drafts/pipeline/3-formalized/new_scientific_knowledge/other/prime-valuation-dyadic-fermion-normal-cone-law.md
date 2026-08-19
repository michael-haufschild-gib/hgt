# Dyadic fermionization of prime valuations and the universal critical normal cone

- **ID:** `prime-valuation-dyadic-fermion-normal-cone-law`
- **Stage:** 3-formalized / external novelty audit preliminary
- **Type:** EXACT PRIME-SOURCE FACTORIZATION / HELLINGER NORMAL-CONE THEOREM
- **Scientific status:** `[PAPER PROOF COMPLETE]`
  `[DYADIC SOURCE FACTORIZATION IS CORPUS-KNOWN PARENT]`
  `[HELLINGER NORMAL-CONE UNIVERSALITY CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[SIGNIFICANCE PASS] [NOT RH]`
- **Parents:**
  - `../../1-in-progress/prime-valuation-hellinger-rees-reflection-fracture.md`;
  - `../prime-valuation-kakutani-polar-third-completion.md`;
  - `../not_new_scientific_knowledge/dyadic-squarefree-euler-fock-source-factorization.md`;
  - `../../3-formalized/new_scientific_knowledge/prime-first-trace-exponential-flat-graph-fracture.md`;
  - `../../1-in-progress/deninger-enhanced-adiabatic-milnor-calderon-vanishing-cycle.md`.

## The jump

The corpus already proves that the geometric Euler state and the squarefree/Mobius state are the
bosonic and first fermionic faces of one exact dyadic Fock factorization, including its unitary,
logarithmic-current, Fisher-tangent, and affine-cutoff laws.  That factorization is accumulated
parent knowledge, not rediscovered novelty here.

The new question is what this exact source channel does to the three-face Hellinger--Rees
completion.  The answer is stronger than tangent-energy convergence: the squarefree digit carries
the entire non-Gaussian critical normal-cone profile, while every higher dyadic digit disappears
from that profile.

For \(0<q<1\), let
\[
 \mu_q(k)=(1-q)q^k,\qquad k\in\mathbb N.
\]
Write the binary expansion
\[
 k=\sum_{j\geq0}2^j\epsilon_j,\qquad \epsilon_j\in\{0,1\}.
\]
Then the digits are independent and
\[
 \boxed{
 \mu_q
 \simeq
 \bigotimes_{j\geq0}\nu_{q^{2^j}},
 \qquad
 \nu_r(\epsilon)=\frac{r^\epsilon}{1+r}.
 }                                                       \tag{1}
\]

The \(j=0\) digit is valuation parity.  At \(q=p^{-1}\), it is exactly the local squarefree
Bernoulli/Mobius state.  Every \(j\geq1\) digit has prime weight at most \(p^{-2}\) and belongs to
the regular all-prime tail.

Combining the parent factorization with the new Hellinger calculation gives:

1. the complete critical Hellinger normal cone is carried by the single squarefree digit;
2. every higher binary digit is asymptotically invisible on the critical \(1/\log x\) scale;
3. geometric valuation Fisher curvature splits exactly into the squarefree Fisher curvature plus
   a summable dyadic tower;
4. the only divergent all-prime first trace is the squarefree digit;
5. every strict-right zeta zero is already a zero of the squarefree Euler layer.

Items 1--3 are the new theorem surface.  Items 4--5 are known corpus consequences now seen to be
the two endpoint shadows of the same squarefree normal-cone law.

## 1. Exact local probability factorization

Euler's binary identity is
\[
 \prod_{j\geq0}(1+q^{2^j})=\frac1{1-q}.                  \tag{2}
\]
For a finite binary word \(\epsilon\) representing \(k\),
\[
 \prod_{j\geq0}
 \frac{q^{2^j\epsilon_j}}{1+q^{2^j}}
 =
 (1-q)q^k.                                               \tag{3}
\]
Moreover
\[
 \sum_{j\geq0}\frac{q^{2^j}}{1+q^{2^j}}<\infty,
\]
so the product Bernoulli measure has only finitely many nonzero digits almost surely.  Binary
summation is therefore an almost-sure inverse and `(1)` is an isomorphism of probability spaces.

The first split is already exact:
\[
 k=\epsilon+2m,\qquad
 \mu_q(k)=\nu_q(\epsilon)\mu_{q^2}(m).                   \tag{4}
\]
Thus parity and paired occupation are independent.  The parity pushforward is
\[
 \Pr(k\ {\rm even})=\frac1{1+q},\qquad
 \Pr(k\ {\rm odd})=\frac q{1+q}.                         \tag{5}
\]

For a finite prime aperture, product of the parity maps is the source-defined Markov channel from
full valuations to squarefree valuations.  Its pointed Hilbert/unitary refinement and Fisher
tangent transport are already proved in the dyadic-Fock parent.  Its pullback on commutative
observable algebras is unital and positive, and its standard \(L^2\) conditional expectation is
contractive.  This existing finite source leg still does not construct the independent Xi
reporter.

## 2. Exact Hellinger digit factorization

For the prime radial family put
\[
 q_{p,0}=p^{-1},\qquad q_{p,c}=p^{-(1-2c)}.
\]
The geometric Hellinger affinity is
\[
 H_p^{\rm geo}(c)
 =
 \frac{\sqrt{(1-q_{p,0})(1-q_{p,c})}}
 {1-\sqrt{q_{p,0}q_{p,c}}}.                              \tag{6}
\]
The \(j\)-th binary digit has affinity
\[
 H_{p,j}^{\rm bit}(c)
 =
 \frac{1+(q_{p,0}q_{p,c})^{2^{j-1}}}
 {\sqrt{(1+q_{p,0}^{2^j})(1+q_{p,c}^{2^j})}}
 =
 \frac{1+p^{-2^j(1-c)}}
 {\sqrt{(1+p^{-2^j})(1+p^{-2^j(1-2c)})}}.               \tag{7}
\]
For \(j=0\), the exponent \(2^{j-1}\) in the first expression means the square root; the second
expression is uniform and unambiguous.

Hellinger affinity is multiplicative on product measures.  Equation `(1)` gives
\[
 \boxed{
 H_p^{\rm geo}(c)=\prod_{j\geq0}H_{p,j}^{\rm bit}(c).
 }                                                       \tag{8}
\]
At the first split,
\[
 \frac{H_{p,0}^{\rm bit}(c)}{H_p^{\rm geo}(c)}
 =
 \frac{1-p^{-2(1-c)}}
 {\sqrt{(1-p^{-2})(1-p^{-2(1-2c)})}}
 \geq1.                                                  \tag{9}
\]
The inequality is the Hellinger data-processing inequality for parity; algebraically its square
reduces to \((a-b)^2\geq0\).

## 3. Squarefree universality of the critical normal cone

For \(x\geq2\), define
\[
 {\cal H}_x^{\rm geo}(c)=\prod_{p\leq x}H_p^{\rm geo}(c),
 \qquad
 {\cal H}_{x,j}^{\rm bit}(c)=\prod_{p\leq x}H_{p,j}^{\rm bit}(c).
\]
Let
\[
 \Phi(u)=\frac12\int_0^1\frac{(e^{ut}-1)^2}{t}\,dt.      \tag{10}
\]

> **[THEOREM -- SQUAREFREE CRITICAL NORMAL-CONE UNIVERSALITY.]**
> For every fixed \(u\in\mathbb R\), with \(c_x=u/\log x\),
> \[
> {\cal H}_{x,0}^{\rm bit}(c_x)\longrightarrow e^{-\Phi(u)},       \tag{11}
> \]
> \[
> \prod_{j\geq1}{\cal H}_{x,j}^{\rm bit}(c_x)\longrightarrow1,     \tag{12}
> \]
> and consequently
> \[
> {\cal H}_x^{\rm geo}(c_x)\longrightarrow e^{-\Phi(u)}.          \tag{13}
> \]

### Proof

For \(t_p=\log p/\log x\), Taylor expansion of `(7)` at \(j=0\) gives
\[
 \log H_{p,0}^{\rm bit}(c_x)
 =
 -\frac{(e^{ut_p}-1)^2}{2p}+O_u(p^{-2}),                \tag{14}
\]
where the total remainder tends to zero by dominated convergence: each fixed-prime remainder
tends to zero as \(c_x\to0\), and a summable \(O_u(p^{-2})\) majorant is available after finitely
many small primes are separated.

Prime-number-theorem partial summation gives, for every \(n\geq1\),
\[
 \frac1{(\log x)^n}
 \sum_{p\leq x}\frac{(\log p)^n}{p}\longrightarrow\frac1n.        \tag{15}
\]
Using
\[
 (e^{ut}-1)^2
 =
 \sum_{n\geq2}\frac{(2^n-2)u^n}{n!}t^n,
\]
uniform absolute convergence on \(0\leq t\leq1\) turns `(15)` into
\[
 \sum_{p\leq x}\frac{(e^{ut_p}-1)^2}{p}
 \longrightarrow
 \int_0^1\frac{(e^{ut}-1)^2}{t}\,dt.                    \tag{16}
\]
Equations `(14)`--`(16)` prove `(11)`.

For all sufficiently large \(x\), \(|c_x|<1/8\).  For \(j\geq1\), the two Bernoulli parameters in
`(7)` are bounded by a constant times
\[
 p^{-(3/4)2^j}.
\]
The double series over \(p\) and \(j\geq1\) is summable.  Each fixed \((p,j)\) affinity tends to one
as \(c_x\to0\), so dominated convergence gives `(12)`.  Equation `(8)` then gives `(13)`. `QED`

### Full two-parameter kernel and Fock realization

The one-point profile is the diagonal slice of a complete limiting experiment.  Let
\({\cal H}_x^{\rm geo}(c,d)\) and \({\cal H}_{x,j}^{\rm bit}(c,d)\) denote the affinities between
parameters \(c\) and \(d\).  For fixed real \(u,v\), put
\[
 c_x=\frac{u}{\log x},\qquad d_x=\frac{v}{\log x}.
\]
The same proof, with
\[
 -\frac{1}{2p}(e^{ut_p}-e^{vt_p})^2                   \tag{13a}
\]
in place of `(14)`, gives
\[
 \boxed{
 {\cal H}_x^{\rm geo}(c_x,d_x)
 \longrightarrow
 K(u,v)
 :=
 \exp\!\left[
  -\frac12\int_0^1\frac{(e^{ut}-e^{vt})^2}{t}\,dt
 \right].
 }                                                       \tag{13b}
\]
The squarefree digit has the same limit, while the product of all \(j\geq1\) digit affinities
tends to one.

This kernel has a literal positive completion.  Put
\[
 {\mathfrak h}=L^2((0,1),dt/t),\qquad
 F_u(t)=e^{ut}-1.                                       \tag{13c}
\]
Since \(F_u(t)=ut+O(t^2)\) at zero, \(F_u\in{\mathfrak h}\), and
\[
 K(u,v)=\exp[-\tfrac12\|F_u-F_v\|_{\mathfrak h}^2].     \tag{13d}
\]
If \({\rm Exp}(F)\) is the normalized exponential vector in the symmetric Fock space
\(\Gamma_s({\mathfrak h})\), then
\[
 \langle{\rm Exp}(F_u),{\rm Exp}(F_v)\rangle=K(u,v).    \tag{13e}
\]

Thus the critical all-prime Gram geometry of finite fermionic squarefree lines converges to a
bosonic coherent-state field.  This is the concrete positive normal-cone chart:
\[
 \text{finite prime exterior/Pluecker lines}
 \quad\longrightarrow\quad
 \{{\rm Exp}(F_u):u\in\mathbb R\}
 \subset\Gamma_s({\mathfrak h}).                         \tag{13f}
\]

### Prime-profile theorem: the scalar curve is a shadow of a full source field

The radial family \(u\mapsto ut\) is not the complete normal experiment.  Let
\[
 {\cal F}_0
 =
 \{f\in C^1([0,1],\mathbb R):f(0)=0\}.                  \tag{13p}
\]
For \(p\leq x\), put \(t_{p,x}=\log p/\log x\) and define the squarefree odds
\[
 r_{p,x}(f)=p^{-1}e^{2f(t_{p,x})}.                       \tag{13q}
\]
Let \(\nu_{p,x}^f\) be the Bernoulli law
\[
 \nu_{p,x}^f(\epsilon)
 =
 \frac{r_{p,x}(f)^\epsilon}{1+r_{p,x}(f)}
 \qquad(\epsilon\in\{0,1\}),                            \tag{13r}
\]
and let \({\cal B}_x(f,g)\) be the Hellinger affinity of the product laws
\(\bigotimes_{p\leq x}\nu_{p,x}^f\) and
\(\bigotimes_{p\leq x}\nu_{p,x}^g\).

> **[THEOREM -- PRIME-PROFILE SQUAREFREE FOCK LIMIT.]**
> For every \(f,g\in{\cal F}_0\),
> \[
>  {\cal B}_x(f,g)
>  \longrightarrow
>  {\cal K}(f,g)
>  :=
>  \exp\!\left[
>   -\frac12\int_0^1
>   \bigl(e^{f(t)}-e^{g(t)}\bigr)^2\,\frac{dt}{t}
>  \right].                                             \tag{13s}
> \]
> The same limit is obtained from the geometric prime-valuation laws with
> \(q_{p,x}(f)=p^{-1}e^{2f(t_{p,x})}\); their complete \(j\geq1\) dyadic tail has
> Hellinger affinity tending to one.

For the squarefree law the local affinity is
\[
 \frac{1+p^{-1}e^{f(t_{p,x})+g(t_{p,x})}}
 {\sqrt{(1+p^{-1}e^{2f(t_{p,x})})
              (1+p^{-1}e^{2g(t_{p,x})})}}.              \tag{13t}
\]
Uniformly on the bounded ranges of \(f\) and \(g\), its logarithm is
\[
 -\frac1{2p}\bigl(e^{f(t_{p,x})}-e^{g(t_{p,x})}\bigr)^2
 +R_{p,x},                                              \tag{13u}
\]
where \(|R_{p,x}|\leq C_{f,g}p^{-2}\).  For every fixed \(p\), both the displayed
principal term and \(R_{p,x}\) tend to zero because \(t_{p,x}\to0\) and
\(f(0)=g(0)=0\).  Dominated convergence gives
\[
 \sum_{p\leq x}R_{p,x}\longrightarrow0.                 \tag{13v}
\]
The function
\[
 A(t)=\bigl(e^{f(t)}-e^{g(t)}\bigr)^2
\]
satisfies \(A(t)=O(t^2)\).  Writing \(A(t)=tB(t)\), with \(B\) continuous and
\(B(0)=0\), prime-number-theorem partial summation gives
\[
 \sum_{p\leq x}\frac{A(t_{p,x})}{p}
 =
 \frac1{\log x}\sum_{p\leq x}
 B(t_{p,x})\frac{\log p}{p}
 \longrightarrow
 \int_0^1B(t)\,dt
 =
 \int_0^1A(t)\,\frac{dt}{t}.                            \tag{13w}
\]
This proves `(13s)`.  For the geometric laws, all sufficiently large \(x\) have
\(q_{p,x}(f),q_{p,x}(g)<1\) for every \(p\leq x\).  The \(j\geq1\) dyadic
parameters are then dominated by \(C_{f,g}p^{-2^j}\).  The same fixed-coordinate
limit plus double-series dominated convergence proves that the regular dyadic tail tends to one.

Put
\[
 G_f(t)=e^{f(t)}-1\in{\mathfrak h}.                      \tag{13x}
\]
Then
\[
 {\cal K}(f,g)
 =
 \exp[-\tfrac12\|G_f-G_g\|_{\mathfrak h}^2]
 =
 \langle{\rm Exp}(G_f),{\rm Exp}(G_g)\rangle.           \tag{13y}
\]
This field is total in the full symmetric Fock space.  Indeed, for every
\(\varphi\in{\cal F}_0\) and every sufficiently small real \(\epsilon\),
\[
 G_{\log(1+\epsilon\varphi)}=\epsilon\varphi.            \tag{13z}
\]
The space \({\cal F}_0\) is dense in \({\mathfrak h}\).  If a Fock vector is orthogonal to all
\({\rm Exp}(G_f)\), its entire coherent transform vanishes on every small line
\(\epsilon\varphi\).  Polarization kills each homogeneous tensor component, so the vector is zero.

More information survives than the scalar affinity.  The limit has the canonical
**prime-scale defect measure**
\[
 d\kappa_{f,g}(t)
 =
 \frac12\bigl(e^{f(t)}-e^{g(t)}\bigr)^2\,\frac{dt}{t},
 \qquad
 {\cal K}(f,g)=e^{-\kappa_{f,g}((0,1))}.                 \tag{13aa}
\]
Scalar fidelity remembers only its total mass.  The source incidence remembers its location in
logarithmic prime scale.

For reflection \(f\mapsto-f\), equality of the two defect measures relative to the critical
source is rigid:
\[
 \kappa_{f,0}=\kappa_{-f,0}
 \quad\Longleftrightarrow\quad
 f=0.                                                    \tag{13ab}
\]
Indeed equality of the absolutely continuous measures gives almost everywhere
\[
 (e^f-1)^2-(e^{-f}-1)^2
 =
 4\sinh(f)(\cosh(f)-1)=0,                               \tag{13ac}
\]
whose only real solution is \(f=0\); continuity gives pointwise vanishing.  On the radial line
\(f(t)=ut\), `(13aa)` reduces to \(\Phi(u)\), and `(13ab)` reduces to the unique zero of the
reflection-odd scalar anomaly \(\Phi(u)-\Phi(-u)\).

This is the first source-complete normal chart in the construction: arbitrary smooth
prime-scale probes, not one scalar radial parameter, separate the squarefree Fock sector.  It
also identifies the datum lost by earlier scalar routes.  Determinants, integrated energies,
single signs, and total Hellinger affinities apply the pushforward
\[
 \kappa_{f,g}\longmapsto\kappa_{f,g}((0,1)),
\]
before the all-prime limit.  That pushforward is not conservative for general profile fields.
The RH specialization uses the sign-definite radial subfield, but the producer--reporter
comparison must retain the measure-valued class to be presentation-controlled rather than
tailored to the radial answer.

The two-sided source reflection has a canonical positive realization as well.  In
\({\mathfrak h}\oplus{\mathfrak h}\), set
\[
 \widetilde F_u=F_u\oplus F_{-u}.                       \tag{13g}
\]
Its coherent kernel
\[
 K_{\rm bi}(u,v)
 =
 \exp[-\tfrac12\|\widetilde F_u-\widetilde F_v\|^2]      \tag{13h}
\]
is invariant under \(u\mapsto-u\): reflection is the unitary swapping the two summands.  This
unitarity is derived from the two literal chiral source profiles and is not imposed at selected
zeros.

For finite \(v\),
\[
 K(u,v)\longrightarrow0\qquad (u\to+\infty\ \text{or}\ u\to-\infty).          \tag{13i}
\]
Indeed \(\|F_u\|^2=2\Phi(u)\to\infty\) at both ends.  Since coherent vectors are total, the
normalized vectors \({\rm Exp}(F_u)\) escape weakly to zero as \(|u|\to\infty\).  A fixed
off-critical exponent \(c\ne0\) has \(u=c\log x\to\pm\infty\); the critical exponent has \(u=0\).
The rigged completion must retain the two escaping ends as half-normal and rapid boundary
functionals, but its positive Hausdorff middle chart is now explicit.

The theorem therefore says more than equality of two quadratic metrics.  The entire non-Gaussian
kernel `(13b)`, for every finite pair of normal coordinates, survives parity coarse-graining.
The higher occupation digits carry no part of that critical boundary experiment.

### The half-normal end as a generalized coherent boundary

The negative end admits an explicit rigged limit.  Let
\[
 \Phi_1=\{f\in C^\infty[0,1]:f(0)=0\}
 \subset{\mathfrak h}.
                                                               \tag{13j}
\]
With its usual smooth Fréchet topology, the functional
\[
 \ell_-(f)=-\int_0^1 f(t)\,\frac{dt}{t}                  \tag{13k}
\]
is continuous: \(f(t)/t\) extends continuously to \(t=0\).  For \(V\to+\infty\),
\[
 \langle F_{-V},f\rangle_{\mathfrak h}
 =
 \int_0^1(e^{-Vt}-1)f(t)\,\frac{dt}{t}
 \longrightarrow\ell_-(f)                              \tag{13l}
\]
by dominated convergence.  Hence \(F_{-V}\to\ell_-\) weakly in \(\Phi_1'\), although
\(\|F_{-V}\|_{\mathfrak h}\to\infty\).

Let \(e(F)\) denote the unnormalized exponential vector.  Since
\[
 e(F_{-V})=e^{\Phi(-V)}{\rm Exp}(F_{-V}),                \tag{13m}
\]
for every exponential test vector \(e(f)\), \(f\in\Phi_1\),
\[
 \langle e(F_{-V}),e(f)\rangle
 =
 \exp\langle F_{-V},f\rangle
 \longrightarrow
 \exp(\ell_-(f)).                                       \tag{13n}
\]
Thus the half-normal renormalization has a canonical generalized coherent boundary functional
\(e^{\ell_-}\) on the exponential test algebra.  Its scale is exact:
\[
 e^{\Phi(-V)}
 \sim
 \sqrt{\frac{e^\gamma V}{2}}.                           \tag{13o}
\]
With \(V=|c|\log x\), this is the inverse Wold half-density scale up to the explicit factor
\(\sqrt{|c|/2}\).

The positive end is genuinely different.  Pairing \(F_V\) with the single test function \(f(t)=t\)
already grows like \(e^V/V\), so \(F_V\) has no limit in \(\Phi_1'\).  It requires the
rapid/Stokes enhancement retained by the full boundary-complexity object.  In the doubled chart,
reflection exchanges which component has the half-normal generalized coherent limit and which
component escapes rapidly.

This is a literal three-face construction:

```text
finite u:       positive Hausdorff coherent Fock chart;
u -> -infinity: generalized coherent half-normal boundary in Phi_1';
u -> +infinity: no distributional limit; enhanced rapid/Stokes face required.
```

No Xi zero or divisor topology enters this rigging.

The scale is the Wold normal scale:
\[
 a_x=\prod_{p\leq x}(1-p^{-1})
 \sim\frac{e^{-\gamma}}{\log x},
 \qquad
 u=e^{-\gamma}\frac{c}{a_x}(1+o(1)).                    \tag{17}
\]

## 4. Exact dyadic Fisher decomposition

The critical Hellinger curvature of the geometric state is
\[
 -\left.\partial_c^2\log H_p^{\rm geo}(c)\right|_{c=0}
 =
 (\log p)^2\frac{q}{(1-q)^2},
 \qquad q=p^{-1}.                                       \tag{18}
\]
For the \(j\)-th binary digit it is
\[
 -\left.\partial_c^2\log H_{p,j}^{\rm bit}(c)\right|_{c=0}
 =
 (\log p)^2
 \frac{4^j q^{2^j}}{(1+q^{2^j})^2}.                    \tag{19}
\]
Differentiating `(8)`, or taking variance in the independent binary expansion of \(k\), gives the
exact identity
\[
 \boxed{
 \frac{q}{(1-q)^2}
 =
 \sum_{j\geq0}
 \frac{4^j q^{2^j}}{(1+q^{2^j})^2}.
 }                                                       \tag{20}
\]

The \(j=0\) term is precisely the squarefree Fisher/WKB capacity
\[
 d_p^2=\frac{p^{-1}}{(1+p^{-1})^2}.                     \tag{21}
\]
All \(j\geq1\) terms are summable over the ordinary primes.  Therefore
\[
 \frac1{(\log x)^2}
 \sum_{p\leq x}(\log p)^2
 \frac{p^{-1}}{(1-p^{-1})^2}
 \longrightarrow\frac12,                                \tag{22}
\]
and the same limit is obtained after retaining only \(j=0\).  The discarded dyadic tower changes
finite calibration but not the critical normal-cone metric or profile.

## 5. Euler factor and first-trace decomposition `[CORPUS-KNOWN PARENT, REINTERPRETED]`

Equation `(2)` gives, initially for \(\Re s>1\),
\[
 \frac1{1-p^{-s}}
 =
 \prod_{j\geq0}(1+p^{-2^j s}).                           \tag{23}
\]
Globally,
\[
 \prod_p(1+p^{-2^j s})
 =
 \frac{\zeta(2^j s)}{\zeta(2^{j+1}s)},                  \tag{24}
\]
so the binary tower telescopes to \(\zeta(s)\).  The singular first digit is
\[
 \prod_p(1+p^{-s})=\frac{\zeta(s)}{\zeta(2s)}.           \tag{25}
\]

At \(s=1\), only \(j=0\) has divergent first trace:
\[
 \sum_p p^{-1}=\infty,\qquad
 \sum_p p^{-2^j}<\infty\quad(j\geq1).                   \tag{26}
\]
Thus the Wold/BV first-trace anomaly and the squarefree Fisher seam are literally the same binary
source layer.  The higher bits form the regular determinant-compatible correction.

There is also an exact right-half divisor consequence.  If \(\Re\rho>1/2\), then
\(\Re(2\rho)>1\), so \(\zeta(2\rho)\) is finite and nonzero.  Hence
\[
 \zeta(\rho)=0
 \quad\Longleftrightarrow\quad
 \frac{\zeta(\rho)}{\zeta(2\rho)}=0
 \qquad(\Re\rho>1/2).                                   \tag{27}
\]
Every hypothetical strict-right zero is therefore already carried by the singular squarefree
digit.  Functional-equation reflection handles the strict-left mate.  No higher binary occupation
layer is needed to detect the RH obstruction.

## 6. Meaning for the third completion

The target-side third completion is not an unknown scalar Hilbert space.  The exact source
decomposition is
\[
 \text{prime valuation sector}
 =
 \text{squarefree singular sector}
 \widehat\otimes
 \text{summable dyadic regular tower}.                   \tag{28}
\]
On the critical normal cone, parity is asymptotically sufficient: its Markov channel retains the
complete Hellinger comparison profile and the entire divergent Fisher metric.  The regular tower
can be handled by ordinary determinant/Gamma transport; the squarefree sector requires the
singular Rees/Tate correspondence and carries every possible strict-right zeta zero.

The finite source leg was already closed by the dyadic-Fock parent.  The new theorem adds exact
normal-cone control: its parity reduction retains the full critical Hellinger experiment, not only
the limiting quadratic Fisher energy.  What remains open is the independent
source-to-reporter theorem:

```text
squarefree singular source correspondence
  -> exceptional Gamma/Mellin reporter
  -> every Xi principal conormal and multiplicity jet.
```

Neither `(1)` nor `(27)` constructs that arrow.

## 7. Hostile audit

1. **Binary factorization is corpus-known parent mathematics.**  Equations `(1)`--`(5)`, the
   global unitary, logarithmic-current split, Fisher-tangent split, dyadic telescope, and affine
   cutoff were already proved in
   `dyadic-squarefree-euler-fock-source-factorization.md`.  None is a novelty claim here.
2. **The crossover theorem is local in normal coordinate.**  Equations `(11)`--`(13)` hold for
   fixed \(u\).  Their \(u\to\pm\infty\) asymptotics match the independently proved fixed-\(c\)
   Rees laws, but no unproved uniform interchange of \(x\to\infty\) and \(u\to\infty\) is used.
3. **Parity is not globally sufficient.**  It discards paired prime occupation at finite aperture.
   Its sufficiency assertion is restricted to the critical Hellinger normal cone and divergent
   Fisher scale.
4. **The coherent chart is not the whole third completion.**  Fixed off-line characters escape
   to \(|u|=\infty\), and the aperture-Stokes regime
   \(\log X\asymp(\sigma-1)^{-2}\) lives beyond every compact \(u\)-chart.  The half-normal, rapid,
   and residue-sensitive Stokes ends must remain in a rigged/enhanced boundary.
5. **Right-half detection is not RH.**  Equation `(27)` says where an off-line zero would be
   represented, not that it cannot exist.
6. **No target divisor was inserted.**  Factorization, Markov channel, Hellinger profile, and
   Fisher decomposition are defined for every radial parameter before zero specialization.
7. **Multiplicity remains open.**  Polynomial valuation jets and the top Xi conormal jet have not
   yet been transported through the exceptional reporter.

## 8. Novelty and significance gate

Parent mathematics includes binary expansion, Euler's product `(2)`, Bose/Fermi product
factorizations, Hellinger data processing, Fisher information, Kakutani product measures, and
prime-number-theorem partial summation.  The complete dyadic source/Fisher factorization and
right-half squarefree localization are also accumulated corpus parents.  Searches checked
mod-Poisson prime-factor models, local asymptotic normality, geometric/Bose distributions, and
Bose--Fermi decompositions.

No located external source, and no prior corpus card, states the candidate-new residue
\[
 \text{prime geometric Hellinger local experiment}
 \xrightarrow{\rm parity}
 \text{same full coherent kernel }K(u,v)
 \text{, reflection-doubled Fock normal cone, and generalized half-normal end}
 \quad\text{with all higher dyadic experiments tending to the unit}.          \tag{29}
\]
The exact Fisher series `(20)` is a useful infinitesimal shadow of this profile, but is elementary
once the parent independent-digit decomposition is known.  This is a preliminary noncollision
finding, not a priority certificate.

- `[ANTI-THEATRE -- PASS]` Novelty is restricted to `(11)`--`(13i)` and their source-completion
  interpretation.  Parent binary/Fisher/divisor results are explicitly excluded.
- `[SIGNIFICANCE -- PASS]` The theorem proves that the already source-canonical parity channel is
  asymptotically sufficient for the complete critical Hellinger normal cone, not only its
  quadratic tangent, and constructs its positive reflection-doubled coherent-state chart.  It
  materially narrows the singular completion while reusing rather than renaming prior source work.
- `[FIELDS VERDICT]` Not by itself.  Fields-scale content begins with the squarefree
  source-to-exceptional-reporter equivalence and conormal conservativity, which would imply RH.
- `[RH BOUNDARY]` No source-to-Xi landing or exclusion theorem is proved.

## 9. Lean boundary

The local identities `(1)`--`(9)`, finite binary truncations, and finite Fisher decomposition are
appropriate unconditional Lean targets.  The infinite probability isomorphism needs an
almost-sure finite-support argument; `(11)`--`(13)` and `(22)` need prime asymptotics.  No analytic
claim is inserted as an axiom.  This section is superseded: the formalization was carried out
anyway and is complete — see the stage-3 audit at the end of this card.

## Gates

- [x] exact geometric valuation binary factorization inherited and re-audited
- [x] parity/Mobius source channel inherited and re-audited
- [x] exact Hellinger digit product proved here
- [x] squarefree-only critical normal-cone theorem proved
- [x] full two-parameter Hellinger kernel limit proved
- [x] coherent Fock and reflection-doubled positive normal-cone charts constructed
- [x] generalized coherent half-normal boundary constructed
- [x] rapid end proved absent from the distributional test dual
- [x] exact dyadic Fisher decomposition proved
- [x] first-trace divergence isolation inherited
- [x] strict-right zeta divisor localization inherited
- [x] finite source Markov/CP leg inherited
- [x] hostile limit-order audit recorded
- [x] preliminary external collision search
- [ ] independent probability/information-geometry audit
- [ ] independent analytic-number-theory audit
- [x] formalize dependency-closed algebraic core in Lean — 2026-08-18, every theorem of the card
- [ ] construct squarefree source-to-exceptional-reporter comparison
- [ ] prove Xi conormal and multiplicity-jet conservativity

## Lean progress — the binary-digit layer `(2)`, `(3)`, `(7)`--`(9)`

Unconditional, `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.HTGeometry`.

| Card step | Lean |
|---|---|
| `(2)` Euler binary product | `HTGeometry.one_sub_mul_prod_one_add_pow` (telescoping, any commutative ring), `HTGeometry.tendsto_prod_one_add_pow` (`|q| < 1`) |
| `(3)` digit weights of a binary word | `HTGeometry.prod_digit_div`, `HTGeometry.prod_digit_div_field` |
| `(7)` bit affinity | `HTGeometry.bitHellingerAffinity` |
| `(8)` digit factorization of the affinity | `HTGeometry.tendsto_prod_bitHellingerAffinity` |
| `(9)` parity ratio and its data-processing inequality | `HTGeometry.bitHellingerAffinity_zero_div_geometric`, `HTGeometry.one_le_parity_affinity_ratio` |

`(6)` was already owned as `HTGeometry.geometricHellingerAffinity` with
`HTGeometry.one_sub_geometricHellingerAffinity`, and the strict form of the parity comparison as
`RHTower.geometricPrimeValuationGramSq_lt_squarefreePrimeParityGramSq`.

The identity that makes `(8)` close is `1 - ab = (1 - sqrt(ab))(1 + sqrt(ab))`: the numerator product
telescopes to `(1 - sqrt(ab))^(-1)` while the denominator product telescopes to
`((1-a)(1-b))^(-1/2)`, and the two closed forms agree exactly.

## Lean progress — the two analytic halves of `(14)` and `(16)`

Both unconditional and axiom-clean, wired into their umbrellas.

### `(14)` — the parity digit carries the whole quadratic defect

`HTGeometry/ParityDigitAffinityExpansion.lean`:

```text
abs_log_one_add_taylor_le      |log(1+x) − x + x²/2| ≤ 4|x|³   for |x| ≤ 3/4
abs_log_bitHellingerAffinity_zero_add_le
    0 ≤ a, b ≤ 3/4  ⟹  |log H^bit_0(a,b) + ½ (√a − √b)²| ≤ 4 (a² + b²)
```

The first-order cancellation is exact and is the content of the estimate: with `s = √(ab)`,

```text
s − a/2 − b/2 = −½ (√a − √b)²,
```

so the linear terms of the three logarithms collect into the squared Hellinger displacement, and the
second-order terms collect into `(a − b)²/4`.  At the prime radial family `a = p^(−1)`,
`b = p^(−(1−2c))` this is exactly `(14)`, because `(√a − √b)² = (e^{u t_p} − 1)²/p`.

### `(16)` — the critical prime sum is a Mertens prime window

`RHTower/CriticalPrimeProfileSum.lean`:

```text
abs_exp_sub_one_le_mul      |e^x − 1| ≤ |x| e^{|x|}
critProfile u t = (e^{ut} − 1)²/t   (zero at the origin)
critProfile_le              critProfile u t ≤ u² e^{2|u|} t   on [0,1]
continuousOn_critProfile    continuity on [0,1], the origin included
mertensPrimeWindow_critProfile_div
    ∑_{p ≤ N} (e^{u t_p} − 1)²/p  =  mertensPrimeWindow (critProfile u) N / log N
tendsto_sum_critProfile
    ∑_{p ≤ N} (e^{u t_p} − 1)²/p → ∫₀¹ (e^{ut} − 1)²/t dt = 2 Φ(u)
```

`(15)` — the weighted Cesàro law `(log x)^{−n} ∑_{p ≤ x} (log p)^n/p → 1/n` — is not needed
separately: the corpus's `tendsto_mertensPrimeWindow_div_log` is the weak convergence of the whole
prime measure `(1/log N) ∑_{p ≤ N} (log p/p) δ_{log p/log N}` to Lebesgue measure on `[0,1]`, of
which `(15)` is the special case `g(t) = t^n`.  Applying it directly to the profile
`g(t) = (e^{ut} − 1)²/t` gives `(16)` in one step, and the continuity of that profile at the origin
— where the numerator vanishes to second order — is the only analytic input.

**Remaining for `(11)`:** the dominated-convergence assembly, i.e. that the total remainder of
`(14)` summed over the primes below the cutoff tends to zero; each term does, because at `c = 0`
the two radial parameters coincide and both sides of `(14)` vanish, and `4(a² + b²) ≤ 8/p²` is a
summable majorant.  Then `(12)` for the higher digits and `(13)`.

## Lean progress — `(11)`–`(13b)`, `(13s)`, `(13aa)`–`(13ac)`, `(20)`, `(22)`, `(23)`–`(27)`

All unconditional and axiom-clean (`[propext, Classical.choice, Quot.sound]`), wired into their
umbrellas.

### Reusable prime-window infrastructure

`RHTower/PrimeProfileWindowLimit.lean`:

```text
divProfile F t = F t / t            (zero at the origin)
tendsto_sum_divProfile
    ∑_{p ≤ N} F(log p / log N) / p  →  ∫₀¹ F(t) dt/t
    for every F whose quotient extends continuously to [0,1]
tendsto_finsetSum_Icc_zero          Tannery on the growing prime window
tendsto_prod_Icc_of_tendsto_sum_log a positive window product is exp of its window log-sum
```

`tendsto_sum_divProfile` is the corpus's Mertens weak convergence
(`tendsto_mertensPrimeWindow_div_log`) read at the profile `F t / t`; it is the single analytic
input behind every all-prime limit below, and it replaces the card's `(15)` entirely.

### The geometric affinity has the parity digit's quadratic expansion

`HTGeometry/GeometricHellingerExpansion.lean`:

```text
abs_log_geometricHellingerAffinity_add_le
    0 ≤ a,b ≤ 3/4  ⟹  |log H^geo(a,b) + ½ (√a − √b)²| ≤ 4 (a² + b²)
```

The mechanism is the same first-order cancellation `√(ab) − a/2 − b/2 = −½(√a − √b)²` that governs
the parity digit, so the two affinities agree to second order — this is *why* `(12)` holds, and it
makes `(13)` provable without ever interchanging the `p`- and `j`-products.

### `(11)`, `(12)`, `(13)`, `(13b)`

`RHTower/SquarefreeCriticalNormalCone.lean`:

```text
radialNome c n = n^{-(1-2c)}
sq_sqrt_radialNome_sub    (√q_{p,0} − √q_{p,c})² = (e^{c log p} − e^{d log p})² / p
radialNome_le             |c| ≤ 1/8 ⟹ q ≤ 3/4        (the Taylor window)
sq_radialNome_le          |c| ≤ 1/8 ⟹ q² ≤ p^{−3/2}  (the Tannery majorant)
coherentKernel u v = exp(−½ ∫₀¹ (e^{ut} − e^{vt})² dt/t)
tendsto_criticalParityAffinity     ∏_{p ≤ N} H^bit_{p,0}(c_N,d_N) → K(u,v)   -- (11), (13b)
tendsto_criticalGeometricAffinity  ∏_{p ≤ N} H^geo_p(c_N,d_N)     → K(u,v)   -- (13)
tendsto_higherDigitTail_one        their ratio → 1                          -- (12)
tendsto_criticalFisherCapacity     (log N)^{-2} ∑_{p<N} (log p)² p^{-1}/(1-p^{-1})² → 1/2  -- (22)
```

`(12)` is stated as the ratio because the finite prime product commutes with the per-prime digit
factorization `(8)`: `∏_{p≤x} ∏_{j≥1} H^bit_{p,j} = (∏_{p≤x} H^geo_p)/(∏_{p≤x} H^bit_{p,0})`.

`(22)` splits as the Mertens window of `t ↦ t²` (giving `∫₀¹ t dt = 1/2`) plus a Tannery-vanishing
correction `t_p²((1-p^{-1})^{-2} − 1)p^{-1} = O(t_p²/p²)`.

### The positive coherent chart `(13c)`–`(13f)`

`RHTower/CoherentKernelChart.lean`:

```text
primeScaleInner u v = ∫₀¹ (e^{ut}−1)(e^{vt}−1) dt/t
primeScaleInner_eq           = Φ(u) + Φ(v) − ½‖F_u − F_v‖²  (polarization)
primeScaleInner_self         ‖F_u‖² = 2 Φ(u)
coherentKernel_eq_exp_neg_half_dist                                   -- (13d)
coherentKernel_eq_exp_inner  K(u,v) = e^{−Φ(u)} e^{−Φ(v)} e^{⟨F_u,F_v⟩}
primeScaleInner_quadForm_nonneg   the Gram kernel is positive semidefinite
hadamardPow_posSemidef            Schur powers stay positive semidefinite
coherentKernel_quadForm_nonneg    ∑_{i,j} c_i K(u_i,u_j) c_j ≥ 0      -- (13e)
```

`(13e)` is formalized in its *content*: the kernel is the exponential of a Gram kernel damped by the
diagonal, hence positive definite — which is exactly what "`K(u,v) = ⟨Exp F_u, Exp F_v⟩` for
exponential vectors in `Γ_s(𝔥)`" asserts.  The Gram positivity is the literal statement that
`∑_{i,j} c_i c_j ⟨F_{u_i},F_{u_j}⟩ = ∫₀¹ (∑_i c_i F_{u_i})² dt/t ≥ 0`, and the exponential step is
Schur's theorem applied to the Hadamard powers plus the exponential series.

### The prime-profile theorem `(13s)`, `(13z)`

`RHTower/PrimeProfileFockLimit.lean`:

```text
profileNome f N n = n^{-1} e^{2 f(log n / log N)}
IsScaleProfile f L        continuity on [0,1] and |f(t)| ≤ L t  (the card's 𝓕₀)
profileNome_le_exp        q_{p,x}(f) ≤ p^{−7/8}   once  16 L ≤ log x
sq_sqrt_profileNome_sub   the displacement is (e^{f(t_p)} − e^{g(t_p)})² / p
continuousOn_divProfile_profileCoherent   (e^f − e^g)²/t extends continuously by zero
tendsto_profileParityAffinity
    ∏_{p ≤ N} H^bit_{p,0}(f,g) → exp(−½ ∫₀¹ (e^{f(t)} − e^{g(t)})² dt/t)     -- (13s)
profileParityAffinity_linear   the radial family is the linear profile
profileVector_log_one_add      G_{log(1+εφ)} = εφ                            -- (13z)
```

The uniform bound is the point: `|f(t)| ≤ L t` turns `e^{2f(t_p)}` into `p^{2L/\log x}`, so once the
cutoff dominates the slope *every* prime below it sits inside the Taylor window at once — no
"finitely many small primes" exception is needed.

### The defect measure `(13aa)`–`(13ac)`

`RHTower/CriticalDefectMeasure.lean`:

```text
reflectionAnomaly_eq          (e^x−1)² − (e^{−x}−1)² = 4 sinh x (cosh x − 1)
reflectionAnomaly_eq_zero_iff the anomaly vanishes exactly at x = 0
profileReflection_rigid       κ_{f,0} = κ_{−f,0} pointwise ⟹ f ≡ 0            -- (13ab)
coherentExponent_lt_of_pos    Φ(−u) < Φ(u) for u > 0
coherentExponent_reflection_eq_iff   Φ(u) = Φ(−u) ⟺ u = 0
```

### `(20)` and `(23)`–`(27)`

`HTGeometry/DyadicFisherDecomposition.lean`:

```text
dyadicVariance_step   r/(1−r)² = r/(1+r)² + 4r²/(1−r²)²
hasSum_dyadicFisher   q/(1−q)² = ∑_{j≥0} 4^j q^{2^j}/(1+q^{2^j})²             -- (20)
```

The identity is a telescoping induction: `(1+r)² − (1−r)² = 4r` is the whole content, and the
remainder `4^J q^{2^J}/(1−q^{2^J})²` vanishes by the ratio test on the doubly exponential majorant.

`RHTower/DyadicEulerTelescope.lean`:

```text
tendsto_prod_one_add_cpow     Euler's binary product over ℂ
tendsto_prod_one_add_primePow ∏_{j<J}(1 + p^{−2^j s}) → (1 − p^{−s})^{−1}      -- (23)
hasProd_one_add_primePow      ∏_p (1 + p^{−2^j s}) = ζ(2^j s)/ζ(2^{j+1} s)     -- (24), (25)
not_summable_primeReciprocal  ∑_p 1/p = ∞                                      -- (26)
summable_primePow_dyadic      ∑_p p^{−2^j} < ∞ for j ≥ 1                       -- (26)
riemannZeta_eq_zero_iff_squarefree_eq_zero
    Re ρ > 1/2 ⟹ (ζ(ρ) = 0 ⟺ ζ(ρ)/ζ(2ρ) = 0)                                  -- (27)
```

## Lean progress — `(13g)`–`(13n)`, `(17)`, `(18)`, `(19)`

### The escaping ends and the reflection-doubled chart

`RHTower/CoherentEscapeEnds.lean`:

```text
coherentExponent_neg_ge    Φ(−V) ≥ ½(1 − e^{−1})² log V        the half-normal end
coherentExponent_pos_ge    Φ(u)  ≥ (e^{u/2} − 1)²/4            the rapid end
primeScaleInner_cauchy     Cauchy–Schwarz for the prime-scale Gram form
tendsto_coherentExponent_of_tendsto
tendsto_coherentKernel_atTop, tendsto_coherentKernel_atBot   K(u,v) → 0        -- (13i)
bicoherentKernel u v = K(u,v) K(−u,−v)
bicoherentKernel_reflection        invariance under u ↦ −u                     -- (13h)
bicoherentKernel_quadForm_nonneg   the doubled kernel is again positive        -- (13g)
divProfile_rapidPairing            ⟨F_V, id⟩ = ∫₀¹ (e^{Vt} − 1) dt
tendsto_rapidPairing_atTop         the rapid end has no distributional limit
```

The two lower bounds are the whole asymmetry of the card's three-face picture: the negative end
diverges only logarithmically (so it survives as a *generalized* coherent functional), the positive
end diverges like `e^{u/2}` (so it does not).  Cauchy–Schwarz — itself the two-point instance of the
Gram positivity — upgrades the diagonal divergence to `K(u,v) → 0` for every fixed reference.

### The generalized coherent boundary `(13j)`–`(13n)`

`RHTower/HalfNormalCoherentBoundary.lean`:

```text
intervalIntegrable_divProfile_of_bounded    bounded quotients on (0,1] are integrable
halfNormalPairing f V = ⟨F_{−V}, f⟩,  halfNormalFunctional f = ℓ_-(f) = −∫₀¹ f dt/t
abs_halfNormalFunctional_le    |ℓ_-(f)| ≤ L    — continuity for the slope seminorm  -- (13k)
abs_halfNormalPairing_sub_le   |⟨F_{−V}, f⟩ − ℓ_-(f)| ≤ L/V                          -- (13l)
tendsto_halfNormalPairing      ⟨F_{−V}, f⟩ → ℓ_-(f)
tendsto_exp_halfNormalPairing  ⟨e(F_{−V}), e(f)⟩ → e^{ℓ_-(f)}                        -- (13n)
```

The rate is exact and elementary rather than a dominated-convergence citation: the difference is
`∫₀¹ e^{−Vt} f(t) dt/t`, whose integrand is bounded by `L e^{−Vt}`, so the whole difference is at
most `L(1 − e^{−V})/V ≤ L/V`.

### `(17)`

`RHTower/WoldNormalScale.lean`:

```text
tendsto_woldNormalScale        e^{−γ} / (a_N log N) → 1
tendsto_woldNormalCoordinate   (e^{−γ} c / a_N) / (c log N) → 1
```

### `(18)`, `(19)`

`RHTower/HellingerCurvature.lean`:

```text
logAffinityKernel a μ c = log(1 + a e^{μc}) − ½log(1+a) − ½log(1 + a e^{2μc})
hasDerivAt_logAffinityKernel
logAffinityKernelDeriv_zero            the critical source is stationary
hasDerivAt_logAffinityKernelDeriv      second derivative at 0 is −μ² a/(1+a)²
log_bitHellingerAffinity_radial        log H^bit_{p,j}(c) = Λ_{q^{2^j},\,2^j log p}(c)
log_geometricHellingerAffinity_radial  log H^geo_p(c) = −Λ_{−q,\,log p}(c)
hasDerivAt_bitCurvature                −∂²_c log H^bit_{p,j}|₀ = 4^j (log p)² q^{2^j}/(1+q^{2^j})²  -- (19)
hasDerivAt_geometricCurvature          −∂²_c log H^geo_p|₀   = (log p)² q/(1−q)²                    -- (18)
```

Both curvatures are the *same* universal kernel read at two parameter points: the digit at
`a = q^{2^j}`, `μ = 2^j log p`, and the geometric law at the reflected point `a = −q`, `μ = log p`.
That the second is the sum of the first over `j` is exactly `(20)`.

### `(13o)`: the exact half-normal scale, and the Frullani representation of `γ`

The last statement of the card needed one analytic asset that neither mathlib nor this tree owned:
the integral representation of the Euler–Mascheroni constant.  Mathlib defines `γ` by
`harmonic n − log n`; it is now also available here as an exponential integral.

`RHTower/EulerMascheroniExponentialIntegral.lean`:

```text
integral_exp_neg_mul_log        ∫₀^∞ e^{−t} log t dt = −γ
einProfile, frullaniHead        C₁ = ∫₀¹ (1 − e^{−t}) dt/t
frullaniTail                    C₂ = ∫₁^∞ e^{−t} dt/t
integral_exp_neg_mul_log_head   ∫₀¹ e^{−t} log t dt = −C₁
integral_exp_neg_mul_log_tail   ∫₁^∞ e^{−t} log t dt =  C₂
frullani_eq_eulerMascheroni     C₁ − C₂ = γ
ein a = ∫₀^a (1 − e^{−s}) ds/s
ein_eq                          Ein(a) = C₁ + log a − ∫₁^a e^{−s} ds/s
tendsto_ein_sub_log             Ein(a) − log a → γ
```

`∫₀^∞ e^{−t} log t dt = −γ` is mathlib's `Γ'(1) = −γ` compared with mathlib's derivative of the
Gamma *integral* — the two functions agree on the right half plane, so their derivatives at `1`
agree, and the Mellin derivative is literally that integral.  The two half-line evaluations are
fundamental-theorem computations for the primitives `(e^{−t} − 1) log t` on `[0,1]` and
`−e^{−t} log t` on `[1,∞)`; the shifted primitive on the head is what removes the singularity of
`∫ e^{−t} dt/t` at the origin, and it is exactly the step that produces `γ`.

`RHTower/HalfNormalExactScale.lean`:

```text
scaledEinProfile, integral_scaledEinProfile   ∫₀¹ (1 − e^{−Vt}) dt/t = Ein(V)
coherentExponent_neg_eq        2 Φ(−V) = 2 Ein(V) − Ein(2V)
tendsto_coherentExponent_neg_sub_log
                               2 Φ(−V) − log V → γ − log 2
tendsto_halfNormalExactScale   e^{Φ(−V)} / √(e^γ V/2) → 1                        -- (13o)
```

The algebraic identity behind it is `(e^{−x} − 1)² = 2(1 − e^{−x}) − (1 − e^{−2x})`, and the scaling
`∫₀¹ (1 − e^{−Vt}) dt/t = Ein(V)` is one change of variables.

**Every theorem this card proves is now Lean-proved, unconditional and axiom-clean**
(`[propext, Classical.choice, Quot.sound]`).  What remains open are the card's own declared research
gates — the squarefree source-to-exceptional-reporter comparison and Xi conormal/multiplicity-jet
conservativity — which the card explicitly does not claim, and the two independent expert audits.

## Stage-3 audit, 2026-08-19

Re-verified against the tree rather than against this card's own prose, because a card's Lean
section can go stale:

- every Lean declaration named anywhere in this card resolves in `formal/GaloisForLFunctions`;
  the only card tokens that do not resolve are mathematical notation and ordinary English words;
- `#print axioms` run on all **286** of them, module by module, returns
  `[propext, Classical.choice, Quot.sound]` and nothing else;
- none of the card's modules appears in the lint gate's unreachable-module report, so all are
  reachable from `GaloisForLFunctions.HTGeometry` / `GaloisForLFunctions.RHTower`;
- the project lint gate reports no `sorry`, `admit`, `axiom`, `opaque` or `unsafe` declaration.

The "Remaining for `(11)`" note in the Lean-progress sections above is chronological and is
superseded by the section that follows it, which proves `(11)`--`(13b)`.

The card moves to stage 3.  Its remaining unchecked gates are the two independent expert audits and
two declared future-research constructions (the squarefree source-to-exceptional-reporter comparison
and Xi conormal/multiplicity-jet conservativity), none of which this card claims to prove.
