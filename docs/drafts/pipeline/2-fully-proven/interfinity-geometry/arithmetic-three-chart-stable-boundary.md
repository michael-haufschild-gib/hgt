# Arithmetic three-chart stable boundary

- **ID:** `arithmetic-three-chart-stable-boundary`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `../../1-in-progress/interfinity-geometry/interfinity-geometry-program.md` · Theorem
  XXVII
- **Statement:** One source-defined degree-two stable-primitive quotient is canonically
  one-dimensional, and its coordinate is simultaneously mixed prime--depth Stokes density,
  negative Sonin torsion slope, and normalized Route-R BV--Wold triangle holonomy.

## Goal

Instantiate interfinity geometry on noncoherent arithmetic HGT data without choosing a zero and
without asserting RH-bearing vanishing.  Prove three existing obstruction charts factor through
one exact class.

## Gates

- [x] 0 → 1 in-progress: prime/depth clocks and critical bornology fixed source-first
- [x] 1 → 2 fully-proven: quotient and three-chart identity proved below
- [ ] 2 → 3 formalized: no Lean work authorized in source task
- [ ] 3 → 4 publication-ready: independent priority/significance review remains open

## Source complex

Let `P` be the primes and fix base prime `2`.  For a real function
`f:P x N_0 -> R`, define

\[
 \begin{aligned}
 B_{P,M}f
 &=f(P,M)-f(P,0)-f(2,M)+f(2,0),\\
 q(f)
 &=\lim_{\substack{P\to\infty\\M\to\infty}}
 {B_{P,M}f\over(\log P-\log2)M},
 \end{aligned}
\tag{1}
\]

when the joint limit exists.  Let `R` be the vector space of such functions satisfying, for every
fixed prime `p`,

\[
 B_{p,M}f=O_p(M).
\tag{2}
\]

Predeclare the critical mixed bornology

\[
 \mathcal S=\ker q
 =\{f\in\mathcal R:B_{P,M}f=o((\log P-\log2)M)\}.
\tag{3}
\]

Define the full rectangular difference

\[
 (Df)(p,q;m,n)
 =f(p,m)-f(p,n)-f(q,m)+f(q,n),
\tag{4}
\]

and the two-term complex

\[
 C^1_{\rm rad}=\mathcal R,
 \qquad C^2_{\rm rad}=D\mathcal R,
 \qquad d=D,
 \qquad C^3_{\rm rad}=0.
\tag{5}
\]

This observer is fixed before any spectral specialization.  Condition `(2)` guarantees that its
mixed rate does not depend on the chosen finite base prime.

## Theorem

1. Replacing `2` in `(1)` by any fixed base prime gives the same `q` on `R`.
2. Mixed rate induces an isomorphism

   \[
   \bar q:
   \mathbb H^2_\infty(C_{\rm rad})
   ={D\mathcal R\over D\mathcal S}
   \xrightarrow{\ \cong\ }\mathbb R,
   \qquad [Df]\longmapsto q(f),
   \tag{6}
   \]

   while ordinary `H^2(C_rad)=0`.
3. For every `s` in the source-chart domain, let

   \[
   \ell_s(p,m)=(1-2\operatorname {Re}s)m\log p.
   \tag{7}
   \]

   Let the Sonin relative determinant torsion be

   \[
   \tau_r(s)=r^{2\operatorname {Re}s-1},\qquad r>1.
   \tag{8}
   \]

   On the Route-R same-prime cells `i_e=(2,e)`, put

   \[
   m_e=2^{-(e+1)},
   \qquad \lambda_e=(e+1)\log2,
   \qquad \theta(i_e,i_f)=m_e\lambda_f-m_f\lambda_e,
   \tag{9}
   \]

   `U_a(i,j)=exp(a theta(i,j))`, `a_s^R=2 Re(s)-1`, and

   \[
   \operatorname {Hol}_R(s)
   ={U_{a_s^R}(i_0,i_1)U_{a_s^R}(i_1,i_2)
     \over U_{a_s^R}(i_0,i_2)}.
   \tag{10}
   \]

   Then

   \[
   \boxed{
   \bar q([D\ell_s])
   =1-2\operatorname {Re}s
   =-{\log\tau_r(s)\over\log r}
   ={8\over\log2}\log\operatorname {Hol}_R(s).
   }
   \tag{11}
   \]

4. Reflection `s -> 1-conj(s)` negates this class, which vanishes exactly when
   `Re(s)=1/2`.

## Proof

Let `B^b` use fixed base prime `b`.  Then

\[
 B^b_{P,M}f=B^2_{P,M}f-B^2_{b,M}f.
\]

The second term is `O_b(M)` by `(2)`, both denominators are asymptotic to `M log P`, and their
ratio tends to one.  Thus `q_b=q_2`.

If `Dh=0`, use `(4)` with `q=2`, `n=0`:

\[
 h(p,m)=h(p,0)+h(2,m)-h(2,0).
\tag{12}
\]

Hence `B_(P,M)h=0` and `q(h)=0`.  Therefore `(6)` is well-defined.  It is surjective because
`f_a(p,m)=a m log p` belongs to `R` and has `q(f_a)=a`.  If `q(f)=0`, then `f in S` and
`[Df]=0`.  Conversely every element of `D S` maps to zero.  This proves `(6)`.  Since
`C_rad^2=D R` and `C_rad^3=0`, ordinary `H^2` is zero.

Substituting `(7)` into `(1)` gives

\[
 \bar q([D\ell_s])=1-2\operatorname {Re}s.
\]

Equation `(8)` gives the second coordinate in `(11)`.  Direct calculation from `(9)` gives

\[
 \theta(i_0,i_1)+\theta(i_1,i_2)-\theta(i_0,i_2)
 =-{log2\over8}.
\tag{13}
\]

Since `a_s^R=-(1-2 Re(s))`, `(10)` and `(13)` give

\[
 \log\operatorname {Hol}_R(s)
 ={\log2\over8}(1-2\operatorname {Re}s),
\]

which completes `(11)`.  Finally
`1-2 Re(1-conj(s))=-(1-2 Re(s))`, and vanishing is equivalent to the critical-line equation.
`QED`

## No-circularity boundary

The quotient, bornology, and clocks are defined before divisor localization.  Formula `(11)` is
valid for every source parameter in the chart domain, not only for zeros.  At an actual Xi
conormal it detects off-line displacement, but nothing in this theorem forces the class to vanish.
That missing source-dagger/Stokes statement remains RH-bearing and is not assumed.

## Lean handoff notes

The quotient proof needs finite differences, two-variable limits, and quotient modules.  Route-R
identity `(13)` and its exponentiated holonomy already exist in
`GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential`; later formalization should
reuse that module.  Sonin and mixed-boundary equalities should be connected only after their exact
existing theorem names are located with the project research tool.

## Boundary

The one-dimensional quotient is intentionally modest.  It is not the full conjectural
`H^2_mod(zeta)` and proves no anomaly-capacity bound.  New candidate knowledge is exact
factorization of three internally distinct arithmetic readers through one source-stable class.

