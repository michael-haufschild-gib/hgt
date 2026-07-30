# Poisson strictness emerges only after infinite exponent depth

- **ID:** `bounded-exponent-poisson-strictness-emergence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / INFINITE SOURCE TOTALIZATION / MOVING-POLE FLUX
- **Source:** `prime-winning-cech-divisor-resolution.md`;
  `deninger-meyer-strict-nuclear-radial-angular-comparison.md`;
  `../3-formalized/high-exponent-shell-zero-free-common-divisor-law.md`
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC] [NOT RH]`
  `[CORPUS-NOVEL ADDITIVE--MULTIPLICATIVE FRACTURE] [LITERATURE NONCOLLISION PRELIMINARY]`
- **Statement:** Every finite maximum-exponent truncation of the positive integer dilation sum
  fails to map Meyer's Poisson test space into its strict nuclear target. Its denominator carries
  a scaled copy of the complete zeta divisor toward \(s=0\). The complete infinite-depth sum is
  Meyer's strict Poisson operator, while boundary blow-up recovers \(\zeta(0)/\zeta\) with every
  zeta zero and multiplicity retained as an exceptional-divisor pole.

## 1. Bounded-exponent dilation operators

For \(n\geq2\), let
\[
 M(n)=\max_p v_p(n).
\tag{1}
\]
Set \(M(1)=0\).
Fix \(M\geq1\). On an even Schwartz test function \(f\), define
\[
 Z_{\leq M}f(x)
 =
 \sum_{\substack{n\geq1\\M(n)\leq M}}f(nx),
\qquad x>0.
\tag{2}
\]
For fixed \(x>0\), the sum and every differentiated sum converge absolutely by Schwartz decay.

The coefficient set in `(2)` is the set of \((M+1)\)-free integers. Hence, for
\(\operatorname{Re}s>1\),
\[
\boxed{\quad
 A_M(s)
 :=
 \sum_{\substack{n\geq1\\M(n)\leq M}}n^{-s}
 =
 \frac{\zeta(s)}{\zeta((M+1)s)}.
 \quad}
\tag{3}
\]
With Mellin convention
\[
 {\mathcal M}f(s)=\int_0^\infty f(x)x^s\,\frac{dx}{x},
\tag{4}
\]
Fubini and \(u=nx\) give
\[
 {\mathcal M}(Z_{\leq M}f)(s)=A_M(s){\mathcal M}f(s)
\qquad(\operatorname{Re}s>1).
\tag{5}
\]

## 2. Forced moving pole `[PAPER-PROVED]`

Put
\[
 s_M=-\frac{2}{M+1}.
\tag{6}
\]
The trivial zero of \(\zeta\) at \(-2\) is simple. Also
\[
 -1\leq s_M<0,
\]
and \(\zeta(s_M)\ne0\): the only real zeta zeros on the negative axis are the negative even
integers. Every finite truncation multiplier therefore has a genuine simple pole:
\[
 \boxed{\quad
 \operatorname*{Res}_{s=s_M}A_M(s)
 =
 \frac{\zeta(s_M)}{(M+1)\zeta'(-2)}
 \ne0.
 \quad}
\tag{7}
\]

This pole is the uncancelled terminal denominator in the shell-depth telescope:
\[
 \begin{aligned}
 \sum_{m=1}^M H_m(s)
 &=
 \sum_{m=1}^M
 \left(
 \frac1{\zeta((m+1)s)}-\frac1{\zeta(ms)}
 \right)\\
 &=
 \frac1{\zeta((M+1)s)}-\frac1{\zeta(s)}.
 \end{aligned}
\tag{8}
\]
Multiplication by \(\zeta(s)\) gives \(A_M-1\); adjoining the depth-zero identity term gives
`(3)`. Every internal scaled-zeta pole cancels between adjacent depths; exactly one terminal pole
remains.

## 3. One explicit Meyer test detects every finite failure `[PAPER-PROVED]`

Let
\[
 f(x)
 =
 x^2\left(x^2-\frac{3}{2\pi}\right)e^{-\pi x^2}.
\tag{9}
\]
Then \(f\) is even Schwartz and
\[
 f(0)=0.
\]
Gaussian moments give
\[
 \int_{\mathbb R}x^2e^{-\pi x^2}\,dx=\frac1{2\pi},
\qquad
 \int_{\mathbb R}x^4e^{-\pi x^2}\,dx=\frac3{4\pi^2},
\]
so
\[
 \widehat f(0)=\int_{\mathbb R}f(x)\,dx=0.
\]
Thus \(f\) lies in Meyer's Poisson source space
\[
 \mathcal H_\cap
 =
 \{f\in\mathcal S(\mathbb R):
 f(-x)=f(x),\ f(0)=\widehat f(0)=0\}.
\tag{10}
\]

Direct Gamma integration gives
\[
 \boxed{\quad
 {\mathcal M}f(s)
 =
 \frac{s-1}{4}\,
 \pi^{-(s+4)/2}
 \Gamma\!\left(\frac{s+2}{2}\right).
 \quad}
\tag{11}
\]
This is nonzero at every \(s_M\in[-1,0)\). Therefore
\[
 A_M(s){\mathcal M}f(s)
\]
has a genuine pole at \(s_M\).

Mellin transforms of elements of
\[
 \mathcal H_-
 =
 \bigcap_{a\in\mathbb R}
 \mathcal S(\mathbb R_{>0}^\times)_a
\tag{12}
\]
are entire: functions in \(\mathcal H_-\) decay faster than every power at both multiplicative
ends. If \(Z_{\leq M}f\) belonged to \(\mathcal H_-\), its entire Mellin transform would agree
with `(5)` on \(\operatorname{Re}s>1\), hence with its meromorphic continuation everywhere. The
pole contradicts entireness.

Thus
\[
 \boxed{\quad
 Z_{\leq M}f\notin\mathcal H_-
 \quad\text{for every finite }M\geq1.
 \quad}
\tag{13}
\]
No finite bounded-exponent positive dilation operator is a restriction of Meyer's strict Poisson
map on this fixed source test.

## 4. Infinite-depth regularity creation `[PAPER-PROVED]`

Meyer's complete operator is
\[
 Zf(x)=\sum_{n\geq1}f(nx).
\tag{14}
\]
His Poisson theorem proves
\[
 Z:\mathcal H_\cap\longrightarrow\mathcal H_-
\]
is a strict closed embedding. Every integer has finite maximum prime exponent, so
\[
 Zf
 =
 \lim_{M\to\infty}Z_{\leq M}f
\tag{15}
\]
pointwise and in \(C^\infty_{\mathrm{loc}}(\mathbb R_{>0})\), by dominated differentiated
Schwartz sums.

Equations `(13)` and `(15)` give the fracture:
\[
 \boxed{\quad
 \forall M<\infty,\ Z_{\leq M}f\notin\mathcal H_-,
 \qquad
 \lim_{M\to\infty}Z_{\leq M}f=Zf\in\mathcal H_-.
 \quad}
\tag{16}
\]
This is not convergence inside \(\mathcal H_-\); none of the approximants is an element of that
space. Poisson strictness is created by the complete exponent-depth totalization.

The prime-winning Čech theorem resolves each depth \(m\):
\[
 Z_m
 =
 \sum_{\varnothing\ne F\Subset\mathbb P}
 (-1)^{|F|+1}Z_{F,m},
\tag{17}
\]
where \(Z_{F,m}\) sums the winning-face coefficients \(b_{F,m}\). The higher prime-dilation
identity
\[
 \Delta_Fa_m=(-1)^{|F|-1}(b_{F,m-1}-b_{F,m})
\tag{18}
\]
is precisely the transgression coupling the horizontal Čech direction to the vertical
shell-depth telescope `(8)`.

Hence the actual source supplies a double resolution:

```text
horizontal:
  prime-winning intersections generated by covariance failures;

vertical:
  adjacent maximum-exponent depths;

finite rectangle:
  one uncancelled scaled trivial-zero pole;

complete double augmentation:
  strict Meyer--Poisson operator.
```

## 5. Nonzero moving-pole boundary flux `[PAPER-PROVED]`

Although the pole tends to the boundary \(s=0\) and its residue tends to zero, the first-order
boundary record is nonzero:
\[
 \boxed{\quad
 \lim_{M\to\infty}
 (M+1)\operatorname*{Res}_{s=s_M}A_M(s)
 =
 \frac{\zeta(0)}{\zeta'(-2)}
 =
 \frac{2\pi^2}{\zeta(3)}.
 \quad}
\tag{19}
\]
Here
\[
 \zeta(0)=-\frac12,
\qquad
 \zeta'(-2)=-\frac{\zeta(3)}{4\pi^2}.
\]
Equivalently, residue divided by pole distance has limit
\[
 \boxed{\quad
 \lim_{M\to\infty}
 \frac{\operatorname*{Res}_{s=s_M}A_M(s)}{|s_M|}
 =
 \frac{\pi^2}{\zeta(3)}.
 \quad}
\tag{20}
\]
For a test \(g\in\mathcal H_\cap\) whose Mellin transform is nonzero at \(0\), the corresponding
operator multiplier carries boundary flux
\[
 \frac{2\pi^2}{\zeta(3)}\,{\mathcal M}g(0).
\tag{21}
\]
For the explicit test `(9)`,
\[
 {\mathcal M}f(0)=-\frac1{4\pi^2},
\]
so `(21)` equals
\[
 -\frac1{2\zeta(3)}.
\tag{22}
\]

## 6. Complete exceptional boundary profile `[PAPER-PROVED]`

The trivial-zero pole in `(6)` is one point of a complete scaled divisor. Every zero
\(\rho\) of \(\zeta\), trivial or nontrivial and with its full multiplicity, gives a pole of
\(A_M\) at
\[
 \frac{\rho}{M+1},
\tag{23}
\]
unless cancelled by the numerator. For all sufficiently large \(M\), the numerator
\(\zeta(\rho/(M+1))\) is close to \(\zeta(0)=-1/2\) and is therefore nonzero. Thus every zeta
divisor point is eventually present in the terminal scaled-pole packet.

Put
\[
 \varepsilon_M=\frac1{M+1},
 \qquad s=\varepsilon_M u.
\tag{24}
\]
Then the boundary blow-up is exact:
\[
 \boxed{\quad
 A_M(\varepsilon_M u)
 =
 \frac{\zeta(\varepsilon_M u)}{\zeta(u)}
 \longrightarrow
 \frac{\zeta(0)}{\zeta(u)}
 =
 -\frac1{2\zeta(u)}.
 \quad}
\tag{25}
\]
The convergence is locally uniform in the spherical/meromorphic sense and locally uniform as an
ordinary holomorphic function on compact sets avoiding the zeta divisor. It follows immediately
from local uniform convergence
\[
 \zeta(\varepsilon_Mu)\longrightarrow\zeta(0).
\]

If \(\rho\) is a zero of order \(d\), write
\[
 \zeta(u)=(u-\rho)^d v_\rho(u),
 \qquad v_\rho(\rho)\ne0.
\]
The exceptional profile has principal part
\[
 -\frac1{2v_\rho(\rho)}(u-\rho)^{-d}
\tag{26}
\]
plus lower pole orders. Hence the blow-up retains every zeta multiplicity jet without choosing or
enumerating zeros in its construction.

This is an explicit two-scale law:

```text
fixed bulk coordinate s, M -> infinity:
  A_M(s) -> zeta(s)                (Re(s)>0 away from the pole);

normal coordinate u=(M+1)s:
  A_M(u/(M+1)) -> zeta(0)/zeta(u).
```

The finite bounded-exponent source therefore contains both zeta and reciprocal zeta, but in
different asymptotic charts. Ordinary fixed-coordinate completion sees only the bulk section and
forgets the exceptional divisor. Pure boundary scaling sees the reciprocal divisor and forgets
the bulk. The required third completion is their deformation-to-normal-cone gluing.

The exceptional chart already has an honest meromorphic Rees family:
\[
 {\mathscr A}(\varepsilon,u)
 =
 \frac{\zeta(\varepsilon u)}{\zeta(u)},
\qquad
 {\mathscr A}(0,u)=\frac{\zeta(0)}{\zeta(u)}.
\tag{27}
\]
It is source-defined: the discrete fibres
\(\varepsilon=1/(M+1)\) are exactly the bounded-exponent Euler truncations.

## 7. Completed two-end exceptional fibre `[PAPER-PROVED]`

Let
\[
 \Xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)
\]
with the removable endpoint values filled in. Then \(\Xi\) is entire,
\[
 \Xi(s)=\Xi(1-s),
\qquad
 \Xi(0)=\Xi(1)=\frac12.
\tag{28}
\]
The Gamma-completed exceptional Rees family is
\[
 {\mathscr X}_0(\varepsilon,u)
 =
 \frac{\Xi(\varepsilon u)}{\Xi(u)}.
\tag{29}
\]
It extends meromorphically to \(\varepsilon=0\) with
\[
 \boxed{\quad
 {\mathscr X}_0(0,u)=\frac1{2\Xi(u)}.
 \quad}
\tag{30}
\]
Blowing up the opposite endpoint gives
\[
 {\mathscr X}_1(\varepsilon,u)
 =
 \frac{\Xi(1-\varepsilon u)}{\Xi(u)}.
\tag{31}
\]
Functional equation yields the stronger exact identity
\[
 \boxed{\quad
 {\mathscr X}_1(\varepsilon,u)
 =
 {\mathscr X}_0(\varepsilon,u)
 \quad\text{for every }\varepsilon,u.
 \quad}
\tag{32}
\]
Thus Gamma/Poisson reflection identifies the two endpoint normal cones before taking the
exceptional limit. Their common exceptional fibre is reciprocal completed zeta. Its poles are
exactly the nontrivial Riemann zeros, with exact multiplicities.

For discrete \(\varepsilon_M=1/(M+1)\), the quotient `(29)` is the bounded-exponent Euler
multiplier \(A_M(s)\), in the normal coordinate \(s=\varepsilon_Mu\), multiplied by the explicit
completion ratio
\[
 \frac{
  (\varepsilon_Mu)(\varepsilon_Mu-1)
  \pi^{-\varepsilon_Mu/2}\Gamma(\varepsilon_Mu/2)}
 {u(u-1)\pi^{-u/2}\Gamma(u/2)}.
\tag{33}
\]
Therefore the completed exceptional gluing is not an arbitrary divisor normalization; it is the
Gamma correction of the literal bounded-exponent source family.

This gives a precise role for the corpus's hypertranscendence:

> Gamma and scaled reciprocal-zeta hypertranscendence measure the impossibility of flattening the
> exceptional Rees family into any finite differential-algebraic state chart. Hypertranscendence
> does not locate zeros; it certifies that the boundary gluing is genuinely infinite and must be
> retained as an operation-valued transition law.

The remaining RH theorem is a purity theorem for the real structure on the pole divisor of
\(1/\Xi(u)\), not construction of that divisor.

## 8. Depth succession generates the Xi logarithmic connection `[PAPER-PROVED]`

Define the completed depth-\(M\) quotient in the physical spectral coordinate:
\[
 X_M(s)=\frac{\Xi(s)}{\Xi((M+1)s)}.
\tag{34}
\]
Compare consecutive depths at the same point
\[
 s=\varepsilon_Mu,
 \qquad
 \varepsilon_M=\frac1{M+1}.
\]
Then
\[
 \frac{X_{M+1}(\varepsilon_Mu)}
      {X_M(\varepsilon_Mu)}
 =
 \frac{\Xi(u)}
      {\Xi((1+\varepsilon_M)u)}.
\tag{35}
\]
On compact sets avoiding the Xi divisor, Taylor expansion gives
\[
 \boxed{\quad
 \lim_{M\to\infty}
 \varepsilon_M^{-1}
 \log
 \frac{X_{M+1}(\varepsilon_Mu)}
      {X_M(\varepsilon_Mu)}
 =
 -u\,\frac{\Xi'(u)}{\Xi(u)}.
 \quad}
\tag{36}
\]
Equivalently, without choosing logarithm branches,
\[
 \boxed{\quad
 \lim_{M\to\infty}
 \varepsilon_M^{-1}
 \left(
 \frac{X_{M+1}(\varepsilon_Mu)}
      {X_M(\varepsilon_Mu)}
 -1
 \right)
 =
 -u\,\frac{\Xi'(u)}{\Xi(u)}.
 \quad}
\tag{37}
\]

Thus three objects arise from one bounded-exponent source tower:

```text
bulk fixed-coordinate limit:
  Xi;

exceptional normal-cone state:
  Xi(0)/Xi(u);

infinitesimal exponent-depth successor law:
  -u Xi'(u)/Xi(u).
```

The determinant is not inserted after discovering its zeros. Its logarithmic connection is the
renormalized generator of adjoining one more allowed valuation depth.

Functional equation transports the endpoint-zero generator to the endpoint-one generator.
Their balanced sum is the centered reflection-invariant connection
\[
 {\mathcal G}_{\mathrm{bal}}(u)
 =
 -\left(u-\frac12\right)\frac{\Xi'(u)}{\Xi(u)}.
\tag{38}
\]
Indeed \(\Xi'(1-u)/\Xi(1-u)=-\Xi'(u)/\Xi(u)\), so
\[
 {\mathcal G}_{\mathrm{bal}}(1-u)
 =
 {\mathcal G}_{\mathrm{bal}}(u).
\tag{39}
\]
At a zero \(\rho\) of multiplicity \(d\), its residue is
\[
 \operatorname*{Res}_{u=\rho}{\mathcal G}_{\mathrm{bal}}(u)
 =
 -d\left(\rho-\frac12\right).
\tag{40}
\]
The missing horizontal displacement is therefore literally the radial residue of the
source-generated depth connection.

In centered coordinate \(u=1/2+iz\), RH is equivalent to the theorem that the corresponding
logarithmic derivative is a Nevanlinna/Herglotz function: such a function can have poles only on
the real \(z\)-axis, with the required residue orientation. This is not known. The exact producer
problem is now:

`[OPEN CORE] [SOURCE_DEPTH_CONNECTION_HERGLOTZ_PURITY]`

Derive the Herglotz property of the centered exceptional depth connection from a positive,
Gamma-reflected operator realization of the same prime-winning/depth transition maps. Scalar
positivity of \(X_M\) on the real half-line is insufficient; the realization must be
matrix-positive and conservative under Xi Cartier base change.

## 9. Meaning: regularity is generated, not inherited

The new universal interpretation is:

> A global source law can be strictly more regular than every finite operation-closed
> approximation because higher incidence cancels a defect that is pushed to the completion
> boundary. The conserved datum is the rate-normalized escaping defect, not finite cohomology.

This gives exact mathematical content to “complete under failures, not states.” The prime-winning
Čech cells generate horizontal failures. Shell depth carries them toward the archimedean
boundary. Poisson summation is the law asserting that the complete double augmentation closes
strictly.

It also identifies what a third completion must retain:

1. finite face and shell-depth cells, even though their positive sums are not in \(\mathcal H_-\);
2. the terminal moving pole and its nonzero flux `(19)`;
3. the strict infinite Poisson sum `(14)`;
4. the principal Xi conormal chart carried by every finite face; and
5. Gamma/Fourier reflection of the escaped \(s=0\) boundary record.

A completion containing only the strict limit forgets `(19)`. A direct sum of finite stages never
reaches `(14)`. The required object is a Hausdorff graph/Tate totalization in which the moving-pole
current, exceptional reciprocal-zeta fibre `(25)`, and strict Poisson limit coexist.

## 10. RH-bearing conjecture

`[CONJECTURE — POISSON CREATED-REGULARITY PURITY]`

> In the source-canonical graph completion retaining `(19)`, Gamma/co-Poisson reflection turns the
> horizontal prime-winning contraction and vertical depth telescope into adjoints. Their Hodge
> determinant is \(\Xi\). The only persistent interior conormal classes after the terminal
> scaled-pole tower has been absorbed at the archimedean boundary have zero arithmetic Hodge
> weight.

Under the face transition law, arithmetic Hodge weight at a divisor point \(\rho\) is
\[
 2\operatorname{Re}\rho-1.
\tag{34}
\]
The conjecture therefore implies RH. This is not yet proved: `(19)` constructs a genuine boundary
record, but no theorem currently identifies its reflected graph totalization with the Xi
principal-conormal Hodge complex.

`[OPEN CORE] [MOVING_POLE_POISSON_XI_GRAPH_TOTALIZATION]`

Construct the locally convex graph completion of the finite rectangles in `(17)`--`(18)`; prove
that:

1. the terminal-pole current converges to the explicit \(s=0\) boundary functional `(21)`;
2. the complete horizontal--vertical augmentation is Meyer's strict \(Z\);
3. Fourier/Gamma supplies the adjoint boundary map;
4. the quotient determinant is the standard \(\Xi\);
5. Xi Cartier base change preserves every principal normal multiplicity jet; and
6. Hodge classes in the interior are pure of weight zero.

## 11. Hostile audit

1. The \((M+1)\)-free Euler product `(3)`, trivial zeros, Gaussian Mellin transforms, and Meyer's
   Poisson theorem are parent mathematics.
2. Novelty candidate is their exact source-resolution conjunction: no finite exponent truncation
   lands in the Poisson target, while the complete prime-winning/depth double augmentation does,
   with boundary flux `(19)`.
3. Equation `(16)` is not an RH proof and does not constrain nontrivial zeros.
4. The reciprocal-zeta exceptional fibre `(25)` retains all zeros but does not constrain their
   locations. It is a carrier, not a purity theorem.
5. A moving pole approaching \(0\) is not automatically a cohomology class. The graph completion
   and its boundary current must be constructed.
6. Scaled residue `(19)` is normalization-sensitive. Its significance comes only if the
   normalization is forced by shell depth and is compatible with Gamma/Fourier gluing.
7. Off-line symmetric rational gauges can preserve a completed divisor while changing no finite
   pole calculation. The decisive theorem must identify the same source graph class with every Xi
   principal conormal.
8. Abstract homological perturbation or an ordinary derived inverse limit is insufficient.
9. Targeted corpus and web searches found the individual parent formulas but not this
   bounded-exponent Poisson-strictness emergence theorem. This is preliminary noncollision
   evidence, not a specialist priority certificate.

## Gates

- [x] bounded-exponent Euler multiplier
- [x] forced moving pole and residue
- [x] explicit fixed Meyer test
- [x] finite nonlanding theorem
- [x] infinite strictness creation
- [x] boundary-flux limit
- [x] exceptional reciprocal-zeta boundary profile
- [x] zero and multiplicity retention under blow-up
- [x] Gamma-completed two-end exceptional gluing
- [x] Xi logarithmic connection generated by depth succession
- [x] centered residue equals horizontal displacement
- [x] relation to prime-winning/depth double resolution
- [ ] unconditional Lean formalization
- [ ] locally convex graph/Tate completion
- [ ] Gamma/Fourier adjoint
- [ ] Xi determinant and conormal purity
- [ ] RH

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*:
  `https://arxiv.org/abs/math/0412277`.
- Standard Euler product for \((M+1)\)-free integers.
- Standard functional equation and trivial-zero derivative formula for \(\zeta\).
