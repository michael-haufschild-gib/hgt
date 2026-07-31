# Gamma factorial--Hilbert--Hankel source-normal bridge

- **ID:** `gamma-factorial-hilbert-hankel-source-normal-bridge`
- **Stage:** 2-fully-proven
- **Type:** EXACT LOCAL SOURCE-NORMAL BRIDGE / GLOBAL COMPLETION FALSIFIER
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW SYNTHESIS]`
  `[CLASSICAL HILBERT-MATRIX COMPONENTS] [PRELIMINARY NONCOLLISION ONLY] [NOT RH]`
- **Parents:**
  - `../../3-formalized/new_scientific_knowledge/prime-first-trace-essential-normal-bockstein.md`;
  - `gamma-copoisson-sonin-full-quotient-flatness-syzygy.md`;
  - `../../../1-in-progress/reflected-character-singular-splitting-bockstein-law.md`;
  - `../../../1-in-progress/source-localization-modular-defect-conservation-law.md`.

## Result

The apparent coordinate mismatch between the prime first-trace Hardy ladder and the factorial
Gamma/co-Poisson interval cell is not fundamental.  They are the two faces of the classical
Hilbert--Hankel moment kernel
\[
 h_{mn}={1\over m+n+1}
       =\int_0^1t^{m+n}\,dt
       =\int_0^\infty e^{-(m+n+1)x}\,dx ,
 \qquad m,n\geq0.
\tag{1}
\]

Let \(S\) be the unilateral shift on coefficient sequences,
\(Se_n=e_{n+1}\), and let \(H=(h_{mn})\) be the Hilbert matrix.  On the finite-sequence core,
\[
 \boxed{\qquad HS=S^*H. \qquad}
\tag{2}
\]
Let
\[
 {\cal B}a(z)=\sum_{n\geq0}a_n{z^n\over n!}
\tag{3}
\]
be the exponential Borel transform.  It is entire for every \(a\in\ell^2\).  Put
\[
 C(z)=\sum_{n\geq0}{z^n\over(n+1)!}={e^z-1\over z}
\tag{4}
\]
with the removable value \(C(0)=1\).  If \(c_m=He_m\), then
\[
 (c_m)_n={1\over m+n+1},
 \qquad
 \boxed{\qquad {\cal B}c_m=C^{(m)}. \qquad}
\tag{5}
\]
Thus every Hilbert-matrix column is exactly one complete Gamma factorial-jet column.

For the literal interval cell
\[
 \Theta_L(z,w)
 =e^{(w-1/2)L}L\,C((z-w)L),
\tag{6}
\]
equation `(5)` gives the all-point, all-jet identity
\[
 \boxed{\qquad
 \partial_z^m\Theta_L(z,w)
 =
 e^{(w-1/2)L}L^{m+1}
 ({\cal B}c_m)((z-w)L).
 \qquad}
\tag{7}
\]
At confluence,
\[
 \partial_z^m\Theta_L(w,w)
 =
 e^{(w-1/2)L}{L^{m+1}\over m+1},
\tag{8}
\]
recovering the formalized complete multiplicity-jet law.

Equations `(2)` and `(5)` also give
\[
 {\cal B}(HSa)
 =
 {\cal B}(S^*Ha)
 =
 {d\over dz}{\cal B}(Ha).
\tag{9}
\]
Hence the Hilbert--Hankel/Borel map sends the source Hardy shift to differentiation of the
Gamma factorial receiver.  In particular, the formalized first-trace essential-normal edge
\[
 e_1\longmapsto Se_1=e_2
\tag{10}
\]
maps to
\[
 C'\longmapsto C''.
\tag{11}
\]
This is the first literal local morphism from the prime first-trace Hardy normal ladder to the
Gamma/co-Poisson factorial ladder.  It removes the local typing ambiguity in
`XI_CRITICAL_FACTORIAL_SONIN_SYNTHESIS`.

## Proof

Equation `(1)` is immediate from elementary integration.  It makes \(H\) the Gram matrix of
the monomials \(1,t,t^2,\ldots\) in \(L^2(0,1)\), hence positive and injective on the
finite-sequence core.  Hilbert's inequality extends it to a bounded positive injective operator
on \(\ell^2\).

For `(2)`, compare matrix entries:
\[
 (HS)_{mn}=h_{m,n+1}={1\over m+n+2}
 =h_{m+1,n}=(S^*H)_{mn}.
\tag{12}
\]

The Cauchy--Schwarz estimate
\[
 \sum_{n\geq0}|a_n|{|z|^n\over n!}
 \leq
 \|a\|_2
 \left(\sum_{n\geq0}{|z|^{2n}\over(n!)^2}\right)^{1/2}
\tag{13}
\]
proves that `(3)` is entire.  Normal differentiation of `(4)` gives
\[
 C^{(m)}(z)
 =
 \sum_{n\geq0}{z^n\over n!(n+m+1)}
 =
 {\cal B}c_m(z),
\tag{14}
\]
which is `(5)`.  The chain rule proves `(7)`, and `(8)` follows from
\(({\cal B}c_m)(0)=(c_m)_0=1/(m+1)\).  Equation `(9)` follows from `(2)` and
\[
 {\cal B}(S^*a)=({\cal B}a)'.
\tag{15}
\]
This proves the theorem. `QED`

## The all-prime analogue already exists, and it fails in exactly one place

For \(m,n\geq2\), the multiplicative Hilbert matrix is
\[
 {\bf H}_{mn}
 =
 {1\over\sqrt{mn}\log(mn)}
 =
 \int_{1/2}^{\infty}m^{-s}n^{-s}\,ds.
\tag{16}
\]
Let \(V_p e_n=e_{pn}\).  Direct comparison of entries gives, simultaneously for every prime,
\[
 \boxed{\qquad {\bf H}V_p=V_p^*{\bf H}. \qquad}
\tag{17}
\]
In the Gram realization
\[
 Je_n(s)=n^{-s}
 \quad\text{in}\quad L^2((1/2,\infty),ds),
\tag{18}
\]
one has
\[
 JV_p=M_{p^{-s}}J
\tag{19}
\]
and therefore
\[
 \|V_px\|_{\bf H}^2
 =
 \int_{1/2}^{\infty}p^{-2s}|Jx(s)|^2\,ds
 \leq
 p^{-1}\|x\|_{\bf H}^2.
\tag{20}
\]
This is the exact ordinary-prime source twist.  It is source-internal, independent of a zero,
Hausdorff because \({\bf H}\) is injective, and contractive under every prime dilation.

Nevertheless, \({\bf H}\) has purely continuous spectrum \([0,\pi]\).  Its Gram completion is
an \(L^2\) half-line space, so point evaluation is not continuous.  The divisor fibres disappear.
Thus `(16)`--`(20)` supply exactly two of the three desired properties:

```text
fixed ordinary-prime covariance: yes;
Hausdorff contractive completion: yes;
Xi point-conormal retention: no.
```

This is the precise all-prime version of the corpus warning that an infinite Hilbert completion
restores covariance while losing every divisor fibre.

## Moving-horizon Gram transgression

The missing relation is not another analogy.  The Gamma/co-Poisson cell is exactly the
change-of-horizon kernel of the multiplicative Hilbert form.

For a real horizontal displacement \(c\) and a finite Dirichlet polynomial
\(f_a(s)=\sum_{n\geq2}a_n n^{-s}\), put
\[
 Q_c(a)
 =
 \int_{1/2-c}^{\infty}|f_a(s)|^2\,ds
 =
 \sum_{m,n\geq2}a_m\overline{a_n}\,
 { (mn)^{c-1/2}\over\log(mn)}.
\tag{21}
\]
Thus the moving-horizon Gram entry at logarithmic action \(L=\log(mn)>0\) is
\[
 {\bf H}_c(L)={e^{(c-1/2)L}\over L}.
\tag{22}
\]
Every \(Q_c\) is positive definite on the finite source core.  Moreover,
\[
 Q_c(V_pa)\leq p^{2c-1}Q_c(a).
\tag{23}
\]
Hence positivity, self-adjoint prime covariance, and even prime contractivity persist throughout
\(c<1/2\).  They cannot select the critical horizon.

Let \(D_ce_n=n^ce_n\).  On the finite core,
\[
 \boxed{\qquad {\bf H}_c=D_c{\bf H}_0D_c. \qquad}
\tag{24}
\]
For \(c\ne0\), this congruence is not a bounded equivalence on the standard coefficient Hilbert
space: \(D_c\) is unbounded for \(c>0\), while \(D_c^{-1}\) is unbounded for \(c<0\).  This is the
exact operator-theoretic meaning of the essential singularity forced by the all-orders-flat
no-sewing theorem.  Essential growth is necessary because moving a source horizon is an
unbounded diagonal gauge.  It is not selective, because such a gauge exists for every \(c\).

Now compare `(22)` with the literal Gamma/co-Poisson cell `(6)`.  Directly,
\[
 \boxed{\qquad
 {\bf H}_c(L)={\Theta_L(c,c)\over L^2},
 \qquad
 {\bf H}_c(L)-{\bf H}_0(L)
 ={c\over L}\Theta_L(c,0).
 \qquad}
\tag{25}
\]
Reflection gives the stronger two-horizon identity
\[
 \boxed{\qquad
 {\bf H}_c(L)-{\bf H}_{-c}(L)
 ={2c\over L}\Theta_L(c,-c).
 \qquad}
\tag{26}
\]
Finally,
\[
\boxed{\qquad
{{\bf H}_c(L)\over{\bf H}_{-c}(L)}
=e^{2cL}.
\qquad}
\tag{27}
\]
The quotient in `(27)` is entrywise, not an operator quotient.

The horizon derivative is even sharper:
\[
 {\partial\over\partial c}{\bf H}_c(L)
 =e^{(c-1/2)L}.
\tag{28}
\]
For \(L=\log(mn)\), it factorizes:
\[
 {\partial\over\partial c}{\bf H}_c(m,n)
 =(mn)^{c-1/2}
 =v_c(m)v_c(n),
 \qquad
 v_c(n)=n^{c-1/2}.
\tag{29}
\]
Thus the entire change of completion has a rank-one boundary derivative.  Infinite rank was never
the missing feature; one source boundary distribution was.

On the finite coefficient core define
\[
 \ell_c(a)=\sum_{n\geq2}a_n n^{c-1/2}.
\tag{30}
\]
Then
\[
 {d\over dc}Q_c(a)=|\ell_c(a)|^2.
\tag{31}
\]
The exact regularity wall is
\[
 \boxed{\qquad
 \ell_c\text{ extends boundedly to }\ell^2
 \Longleftrightarrow
 \sum_{n\geq2}n^{2c-1}<\infty
 \Longleftrightarrow c<0.
 \qquad}
\tag{32}
\]
If \(c\geq0\), the densely defined functional \(\ell_c\) is nonclosable; its graph closure is
\(\ell^2\oplus\mathbb C\).  At \(c=0\), its coefficient mass is the harmonic series.

Consequently, for \(c\ne0\), exactly one of the reflected boundary functionals
\(\ell_c,\ell_{-c}\) is an honest Hilbert vector and the other is a nonclosable boundary
distribution.  At \(c=0\), both are the same critical nonclosable half-density functional:
\[
\boxed{
\begin{array}{c|c|c}
 &\ell_c&\ell_{-c}\\ \hline
c<0&\text{bounded}&\text{nonclosable}\\
c=0&\text{same critical boundary distribution}&\text{same}\\
c>0&\text{nonclosable}&\text{bounded}
\end{array}}
\tag{33}
\]

For completeness, `(32)` is the \(p\)-series criterion.  When \(c<0\), Cauchy--Schwarz gives
boundedness.  When \(c\geq0\), let
\[
 M_N=\sum_{2\leq n\leq N}n^{2c-1}\longrightarrow\infty,
 \qquad
 x_N(n)={n^{c-1/2}\mathbf1_{2\leq n\leq N}\over M_N}.
\]
Then \(\|x_N\|_2=M_N^{-1/2}\to0\) while \(\ell_c(x_N)=1\).  Hence the graph contains
\((0,1)\) in its closure.  Subtracting scalar multiples of a tail-supported version of \(x_N\)
also shows that \(\ker\ell_c\) is dense, so the graph closure is all of
\(\ell^2\oplus\mathbb C\).

This is the precise completion mismatch which a fixed-source dagger must see.  If the full Xi
top conormal lands through one source-normal exact couple and Riemann inverse duality becomes its
dagger, the two reflected conormals must have the same boundary regularity class.  Equation
`(33)` then forces \(c=0\).  Proving that landing remains the load-bearing theorem.

Equations `(25)`--`(33)` identify four previously separate observations as one law:

```text
Gamma/co-Poisson interval cell = finite horizon displacement;
Gamma confluence jet           = tangent of the Gram horizon;
Sonin reflected torsion        = reflected horizon mismatch;
accelerated Weyl sewing        = essential retuning of the source horizon.
```

Therefore the critical line is not distinguished by existence, positivity, rank, covariance,
contractivity, or essentiality of a fitted completion.  It is the fixed point \(c=0\) of source
horizon reflection.  An off-line construction succeeds precisely by replacing the original
critical source form \({\bf H}_0\) with the zero-dependent form \({\bf H}_c\).

## Universal interpretation

The source-normal comparison cannot be one Hilbert completion.

```text
multiplicative-Hilbert face:
  fixed ordinary-prime action and critical half-density contractivity,
  but only continuous spectrum;

factorial Gamma/Borel face:
  entire point and multiplicity-jet retention,
  but no source-conservative all-prime Hilbert norm at the boundary;

first-trace / Rees-corona face:
  remembers the noncommutation between those two completions.
```

The required object is therefore a polarized or derived pullback of these faces before ordinary
closure.  This is a concrete local model of
`SOURCE_EFFECTIVE_DAGGER_BECK_CHEVALLEY_LAW`: completion and Xi specialization must be compared
through the essential corona, not identified inside one completed Hilbert space.

The universal candidate law can now be stated without hiding the selector:

> **FIXED-SOURCE HORIZON DESCENT.**  The full Xi Cartier conormal is the Bockstein of a strict
> source-normal comparison constructed over the single ordinary-prime Gram horizon
> \({\bf H}_0\), before any zero is selected.  Its reflection dagger is internal to that same
> source object.  No change \({\bf H}_0\rightsquigarrow{\bf H}_c\) is permitted in the landing
> morphism.

This is a conjecture, not a proved fact.  If it holds and the Bockstein is nonzero on every top
Xi conormal, then `(24)`--`(27)` make the RH mechanism transparent.  At an off-line horizontal
offset \(c\ne0\), reflection requires the nontrivial essential gauge \(D_c\), which twists the
ordinary-prime source action.  Strict source-normality forbids that retuning.  At \(c=0\), the two
horizons coincide and the surviving class is the confluent Gamma tangent.  Thus every landed
nonzero conormal lies on the critical line.

The exact remaining arithmetic theorem is still
`XI_SOURCE_NORMAL_STOKES_BOCKSTEIN_DAGGER_LANDING`.  In the present coordinates it asks for an
all-prime extension of `(9)` which:

1. restricts to `(17)` on the multiplicative-Hilbert face;
2. restricts to `(7)` on the factorial Gamma/co-Poisson face;
3. sends the formalized first-trace essential-normal edge to the nondivisive Sonin source-error
   syzygy;
4. retains the essential comparison cone rather than completing it away; and
5. has Bockstein equal to every full Xi top conormal, with Riemann inverse duality equal to
   Hilbert adjunction.

On a top conormal this identifies
\(\lambda_r(\rho)^{-1}\) with \(\overline{\lambda_r(\rho)}\), hence forces
\(|\lambda_r(\rho)|=1\) and \(\operatorname{Re}\rho=1/2\).

## Hostile audit

1. **Not RH.**  Equations `(1)`--`(20)` do not construct the polarized all-prime pullback or land
   an Xi conormal.
2. **Hankel covariance is not selective.**  Every positive moment measure on \([0,1]\) produces a
   Hankel matrix satisfying the shift relation `(2)`.  Gamma selects Lebesgue moments through its
   exact factorial coefficients, but the relation alone proves nothing about zeros.
3. **The multiplicative Hilbert matrix is not the third completion.**  It is the sharp
   continuous-spectrum falsifier: source covariance and contractivity coexist only after point
   fibres have been lost.
4. **Essentiality remains necessary but nonselective.**  Inverting the Hilbert/Gram maps is
   singular, but the standard adelic Weyl operator still crosses off-line sectors by retuning the
   source modular action.  Fixed-source compatibility, not inverse growth, is load-bearing.
5. **Hypertranscendence does not supply conormal faithfulness.**  The positive
   hypertranscendental Riemann-divisor frame has maximal transverse differential rank while
   retaining an arbitrary common divisor.  It explicitly refutes the inference from differential
   independence to faithful divisor landing.
6. **No positivity claim.**  Positivity of \(H\) explains the contractive face.  It does not force
   the dagger Beck--Chevalley comparison or the vanishing of the Sonin relative torsion.
7. **No source-free Borel completion.**  The exponential Borel transform is only the local
   Gamma receiver.  Adding it after zero specialization would be a fitted analytic topology and
   would not meet the open core.
8. **Generalized-prime falsifier survives.**  It may carry the same local Gamma/Hilbert cell.
   It is excluded only by the literal ordinary-integer all-prime pullback and conormal-faithful
   Bockstein.
9. **The moving-horizon formulas are elementary, not RH.**  Equations `(21)`--`(27)` give the
   first literal common chart for Gamma, Hilbert, Sonin reflection, and Weyl modular drift, but
   they do not prove fixed-source horizon descent.
10. **No ban on all essential operators.**  Such a ban would also remove the required
    Gamma/Wold comparison.  The selector is strict ordinary-source normality: allowed essential
    comparison may retain the fixed horizon, but may not apply the zero-dependent gauge \(D_c\).
11. **No hidden norm proof.**  The forms \(Q_c\) are positive for every real \(c\), and are
    contractive for every \(c<1/2\).  Any argument using only those properties is refuted by
    `(21)`--`(24)`.
12. **The regularity table is not a zero theorem.**  Equation `(32)` is the classical Dirichlet
    point-evaluation/normalizability wall in a new moving-horizon chart.  Functional-equation
    pairing alone does not prove that Xi conormals preserve this source regularity.  That is
    exactly the unproved dagger landing.
13. **Rank one is not automatically faithful.**  The derivative in `(29)` identifies the
    essential boundary carrier, but an arbitrary Xi divisor can still disappear under pullback
    to it.  Conormal faithfulness cannot be inferred from factorization or hypertranscendence.

## Literature boundary

The classical Hilbert matrix, its moment representation, boundedness, injectivity, and continuous
spectrum are parent operator theory.  The multiplicative Hilbert matrix `(16)` and its
\(\mathcal H^2_0\) realization are due to Brevig--Perfekt--Seip--Siskakis--Vukotić,
*The multiplicative Hilbert matrix*, arXiv:1411.7294.  General moment Hilbert operators are also
standard.

Targeted searches located no source identifying the exponential-Borel columns of the Hilbert
matrix with the complete Gamma/co-Poisson interval jet tower, or using that identity as the local
source-normal edge of an Euler--Gamma/Sonin completion comparison.  Searches also located no
source identifying the Gamma interval cell with the exact displacement of the lower Mellin
horizon in `(25)`--`(27)`.  This is preliminary noncollision evidence only.  No priority claim is
made for the classical ingredients.

## Gates

- [x] exact Hilbert--Hankel shift/dagger identity
- [x] exact Borel-column/Gamma-jet identity
- [x] exact interval-cell all-jet formula
- [x] first-trace Hardy edge mapped to Gamma differentiation
- [x] all-prime multiplicative-Hilbert covariance and source twist identified
- [x] continuous-spectrum point-fibre failure audited
- [x] moving-horizon Gram family and exact Gamma displacement law
- [x] reflected Gram ratio identified with modular drift
- [x] rank-one horizon derivative and sharp reflected regularity mismatch
- [x] essentiality reinterpreted as unbounded horizon gauge, and shown nonselective
- [x] hypertranscendental-rank faithfulness inference rejected
- [x] accelerated-Weyl falsifier retained
- [x] scalar Hilbert/Borel and moving-horizon identities formalized unconditionally in Lean
- [ ] all-prime polarized pullback constructed
- [ ] essential comparison cone identified with Sonin source-error syzygy
- [ ] Xi conormal-faithful Bockstein and dagger naturality
- [ ] RH
- [ ] unconditional Lean formalization of the full analytic bridge

## 2026-07-31: global Euler condensation of the complete interval-jet tower

The local bridge `(6)`--`(9)` has an exact all-prime condensation on the Euler half-plane.
This closes its algebraic source assembly, but not its source-normal Sonin topology.

Put
\[
 \Theta_L(z,w)
 =
 e^{(w-1/2)L}L\,C((z-w)L)
\]
as in `(6)`.  For \(\Re z,\Re w>1\), define
\[
 {\cal K}_\zeta(z,w)
 :=
 \sum_{n\ge2}{\Lambda(n)\over\log n}\,
 \Theta_{-\log n}\!\left(z+\tfrac12,w+\tfrac12\right).
\tag{34}
\]
The series is normally convergent, including across \(z=w\), and
\[
 \boxed{\qquad
 {\cal K}_\zeta(z,w)
 =
 {P_\zeta(z)-P_\zeta(w)\over z-w},
 \qquad
 P_\zeta(s)
 :=
 \sum_{n\ge2}{\Lambda(n)\over\log n}n^{-s}.
 \qquad}
\tag{35}
\]
The quotient in `(35)` has its removable diagonal value.  On the Euler half-plane,
\(P_\zeta\) is the Euler-product branch of \(\log\zeta\), so equivalently
\[
 {\cal K}_\zeta(z,w)
 =
 {\log\zeta(z)-\log\zeta(w)\over z-w}.
\tag{36}
\]
No branch of \(\log\zeta\) is needed to define `(34)` or `(35)`.

More strongly, every confluent Gamma factorial coordinate condenses to the corresponding
von Mangoldt logarithmic-current jet:
\[
 \boxed{\qquad
 \left.\partial_z^m{\cal K}_\zeta(z,w)\right|_{z=w}
 =
 {1\over m+1}
 \left({\zeta'\over\zeta}\right)^{(m)}(w),
 \qquad m\ge0.
 \qquad}
\tag{37}
\]

`[PAPER-PROVED] [GLOBAL_EULER_GAMMA_COPOISSON_DIVIDED_LOG_JET_WELD]`

Indeed, the interval boundary identity gives
\[
 (z-w)\Theta_{-\log n}\!\left(z+\tfrac12,w+\tfrac12\right)
 =
 n^{-z}-n^{-w}.
\tag{38}
\]
Multiplication by \(\Lambda(n)/\log n\) and summation proves `(35)`.  On a compact subset of
\(\Re z,\Re w>1\), the integral divided-difference formula bounds the \(n\)-th term by a
constant times
\[
 \Lambda(n)n^{-1-\delta}
\]
for some \(\delta>0\), proving normal convergence.  The formalized local all-jet law gives
\[
\begin{aligned}
 &{\Lambda(n)\over\log n}
 \left.
 \partial_z^m
 \Theta_{-\log n}\!\left(z+\tfrac12,w+\tfrac12\right)
 \right|_{z=w}\\
 &\qquad =
 {(-1)^{m+1}\over m+1}\,
 \Lambda(n)(\log n)^m n^{-w}.
\end{aligned}
\tag{39}
\]
The differentiated von Mangoldt Dirichlet series
\[
 \left({\zeta'\over\zeta}\right)^{(m)}(w)
 =
 (-1)^{m+1}
 \sum_{n\ge2}\Lambda(n)(\log n)^m n^{-w}
\tag{40}
\]
then proves `(37)`.

The case \(m=0\) is the exact commuting triangle
\[
\begin{array}{ccc}
\text{first normal Wold current}
&\xrightarrow{\ \Lambda(n)/\log n\text{-weighted interval cells}\ }&
\text{Gamma/co-Poisson factorial receiver}\\[1mm]
\big\downarrow\operatorname{Tr}
&&
\big\downarrow\text{confluence}\\[1mm]
-\zeta'/\zeta
&\xrightarrow{\ -1\ }&
\zeta'/\zeta .
\end{array}
\tag{41}
\]
For every \(m\), `(37)` retains the complete factorial coordinate rather than only the first
trace.  Adding the already formalized pole and archimedean logarithmic derivatives gives the
full \(\Xi'/\Xi\) current on \(\Re s>1\); meromorphic continuation then carries `(37)` to the
principal divisor current.  At a zero of multiplicity \(r\),
\[
 {1\over m+1}
 \left({\Xi'\over\Xi}\right)^{(m)}(s)
 =
 {r(-1)^m m!\over m+1}(s-\rho)^{-m-1}
 +\text{holomorphic}.
\tag{42}
\]

### Euler--Gamma quadrant current

The divided-log kernel has a literal pre-divisor source chain, not only a scalar series.  Put
\[
 Q=[0,\infty)^2,\qquad
 L_n=\log n,\qquad
 a_n={\Lambda(n)\over L_n},
\]
and orient the segment
\[
 \sigma_n(t)=(t,L_n-t),\qquad 0\leq t\leq L_n,
\tag{43}
\]
from \((0,L_n)\) to \((L_n,0)\).  Define the underlying weighted segment measure and oriented
one-current by
\[
\begin{aligned}
 \int_Q F\,d\mu_E
 &:=
 \sum_{n\ge2}a_n\int_0^{L_n}F(t,L_n-t)\,dt,\\
 {\mathfrak R}_E(A\,dt+B\,du)
 &:=
 \sum_{n\ge2}a_n\int_0^{L_n}
 \bigl(A(t,L_n-t)-B(t,L_n-t)\bigr)\,dt .
\end{aligned}
\tag{44}
\]

`[PAPER-PROVED] [EULER_GAMMA_QUADRANT_CURRENT]`

Both objects are locally finite.  Indeed, if \(K\subset Q\) is compact, then
\(t+u\leq M_K\) on \(K\) for some \(M_K\), so \(K\) meets \(\sigma_n\) only when
\(\log n\leq M_K\).  Only finitely many \(n\) occur.  Since \(a_n\geq0\), \(\mu_E\) is a
positive Radon measure.  The boundary of the oriented current is the exact reflected Euler
endpoint difference
\[
 \boxed{\qquad
 \partial{\mathfrak R}_E(f)
 =
 \sum_{n\ge2}{\Lambda(n)\over\log n}
 \bigl(f(\log n,0)-f(0,\log n)\bigr).
 \qquad}
\tag{45}
\]
This follows by the one-dimensional fundamental theorem of calculus on every segment; local
finiteness makes the sum finite on compactly supported test functions.

For \(\Re z,\Re w>1\), the double Laplace transform converges normally and equals
\[
\begin{aligned}
 {\cal H}_\zeta(z,w)
 &:=
 \int_Q e^{-zt-wu}\,d\mu_E(t,u)\\
 &=
 \sum_{n\ge2}{\Lambda(n)\over\log n}
 \int_0^{\log n}e^{-zt-w(\log n-t)}\,dt\\
 &=
 {P_\zeta(z)-P_\zeta(w)\over w-z}
 =
 -{\cal K}_\zeta(z,w).
\end{aligned}
\tag{46}
\]
On every compact subdomain, if
\(\delta=\min(\Re z,\Re w)-1>0\), the \(n\)-th integral is bounded by
\(\Lambda(n)n^{-1-\delta}\); this proves normal convergence.  Pairing `(45)` with the
exponential test function gives the chain-homotopy identity
\[
 \boxed{\qquad
 \left\langle\partial{\mathfrak R}_E,e^{-zt-wu}\right\rangle
 =
 P_\zeta(z)-P_\zeta(w)
 =
 (w-z){\cal H}_\zeta(z,w).
 \qquad}
\tag{47}
\]
Thus the local Gamma/co-Poisson interval cell is the Laplace image of an actual ordinary-prime
quadrant segment, and the all-prime divided-log kernel is its locally finite action condensation.

Confluence is the moment map of the same measure:
\[
 \left.\partial_z^m{\cal H}_\zeta(z,w)\right|_{z=w=s}
 =
 {(-1)^m\over m+1}
 \sum_{n\ge2}\Lambda(n)(\log n)^m n^{-s}
 =
 -{1\over m+1}
 \left({\zeta'\over\zeta}\right)^{(m)}(s).
\tag{48}
\]
Hence the complete factorial jet tower is already present as transverse moments of one
source-defined Radon current.  Coordinate interchange \((t,u)\mapsto(u,t)\) fixes \(\mu_E\)
and reverses \({\mathfrak R}_E\); this is the chain-level origin of symmetry of
\({\cal H}_\zeta\) and antisymmetry of its boundary.

This supplies an explicit candidate for the **Euler--Gamma component** of the escaped primitive
\({\mathfrak R}_{\rm ar}\) in `SOURCE_EFFECTIVE_DAGGER_BECK_CHEVALLEY_LAW`.  It does not yet
supply the full primitive: the Möbius inverse graph, additive Poisson leg, literal Sonin quotient,
strict critical completion, and dagger mate remain to be attached to the same current.

### Direct lift from the Poisson comb

The additive source of `(44)` can be made explicit before Mellin scalarization.  Let
\[
 D=\delta_0-1\in{\cal D}'(\mathbb T),\qquad
 \widehat{P_+D}(n)=1\quad(n\ge1),
\tag{49}
\]
and on the positive Fourier coefficient space define the diagonal prime-power extractor
\[
 M_Ee_n=a_ne_n,\qquad
 a_n=
 \begin{cases}
 \Lambda(n)/\log n,&n\ge2,\\
 0,&n=1.
 \end{cases}
\tag{50}
\]

`[PAPER-PROVED] [POISSON_PRIME_POWER_INTERVAL_SUSPENSION]`

The operator \(M_E\) is a canonical positive self-adjoint contraction on every weighted
coefficient Hilbert space.  Indeed, \(0\leq a_n\leq1\); on \(n=p^k\) it is \(1/k\), and it
vanishes away from prime powers.  It preserves the sharp half-density wall:
\[
 M_EP_+D\in\dot H^{-r}(\mathbb T)
 \quad\Longleftrightarrow\quad
 \sum_{n\ge2}a_n^2n^{-2r}<\infty
 \quad\Longleftrightarrow\quad
 r>\frac12.
\tag{51}
\]
For \(r>1/2\), convergence follows from \(a_n\leq1\) and convergence of
\(\sum n^{-2r}\).  If \(r\leq1/2\), then \(a_p=1\) at every prime and
\(\sum_pp^{-2r}\) diverges.  Thus extracting the Euler logarithm from the additive point
conormal neither creates nor moves the critical Sobolev wall.

For a finitely supported sequence \(c=(c_n)_{n\ge2}\), define interval suspension by
\[
 {\cal S}(c)=\sum_{n\ge2}c_n[\sigma_n].
\tag{52}
\]
Because every compact subset of \(Q\) meets only finitely many \(\sigma_n\), `(52)` extends
coefficientwise to every sequence as a locally finite current.  Equations `(44)` and `(50)`
give the exact source factorization
\[
 \boxed{\qquad
 P_+D
 \xrightarrow{\ M_E\ }
 (a_n)_{n\ge2}
 \xrightarrow{\ {\cal S}\ }
 {\mathfrak R}_E.
 \qquad}
\tag{53}
\]
Its double Laplace scalarization is `(46)`, and its boundary is `(45)`.  Therefore the map from
the additive Poisson point conormal to the Euler--Gamma primitive is explicit at coefficient and
current level; it is not merely the observation that both constructions involve ordinary
integers.

The product/current topology in `(52)` is deliberately weak.  It proves existence and exact
source labelling but supplies no Sonin norm, no critical dagger, and no reason that Poisson
reflection remains internal after cofinal completion.  Consequently `(53)` closes the
additive-source-to-Euler-current **construction** face, not the RH-bearing strictness face.

### Exact frontier change

Equation `(34)` supplies the previously missing all-prime **algebraic** extension of the local
Hilbert--Hankel/Borel cell.  The remaining open theorem must no longer be described as finding
the image of the Wold current in the Gamma factorial receiver.  That image is `(34)`--`(37)`.
What remains is strictly topological and dagger-theoretic:

1. lift the normally convergent Euler-half-plane kernel `(34)` to the source-normal
   Gamma/co-Poisson/Sonin exact couple;
2. prove that its meromorphic continuation is induced by strict boundary base change rather
   than by an external continuation operator;
3. retain the essential comparison cone and every principal \(\Xi\)-conormal after that base
   change; and
4. identify Riemann inverse reflection with Hilbert adjunction on this same lifted class.

The all-orders-flat theorem makes item 1 necessarily singular.  The closed source-linear
no-sewing theorem makes items 2--4 necessarily derived/preclosure rather than a closed operator
between the reflected Hilbert sectors.

### Hostile audit

1. `(34)` is a direct global assembly of the Euler logarithm and is not claimed as literature-new.
2. Normal convergence on \(\Re s>1\) does not imply continuity in the critical source-normal
   topology.
3. Unique meromorphic continuation of the scalar trace does not prove strict continuation of its
   source graph.
4. The residue formula `(42)` identifies the divisor current but does not prove that the
   corresponding Sonin conormal is nonzero in one fixed source dagger sector.
5. Generalized-prime off-line systems can possess their own divided-log kernel.  The selector is
   still the literal ordinary-integer strict dagger landing, not `(35)` alone.
6. The positive measure \(\mu_E\) in `(44)` is a source primitive, not a positive-definite
   two-variable kernel.  Its support lies on reflected segments rather than the diagonal, so
   \({\cal H}_\zeta(z,\overline w)\) need not be positive semidefinite.
7. The boundary identity `(47)` proves the Euler--Gamma chain homotopy only on the absolute
   convergence side.  It does not prove that continuation through the critical source-normal
   boundary is strict or that its boundary Bockstein lands nontrivially in the Sonin quotient.

Targeted arXiv searches found Burnol's co-Poisson/Sonine framework and the standard
logarithmic-derivative literature, but no exact statement of the interval-cell condensation
`(34)`--`(37)` or the locally finite quadrant-current realization `(43)`--`(48)`.  Since the
proof is a direct consequence of the Euler logarithm and the local cell identity, this is
recorded as a corpus bridge, not a priority claim.

### Lean certificate for the global jet weld

The algebraic all-prime condensation `(37)` is formalized unconditionally in
`RHTower/EulerGammaCoPoissonDividedLogJetWeld.lean`:

- `logMul_iterate_vonMangoldt`;
- `eulerGammaCoPoissonJetTerm_eq_LSeries_term`;
- `tsum_eulerGammaCoPoissonJetTerm_eq_zetaLogDerivJet`.

The last theorem is the exact all-order statement
\[
 \sum_{n\ge0}\operatorname{EulerGammaCoPoissonJetTerm}(m,n,s)
 =
 {1\over m+1}
 \left({\zeta'\over\zeta}\right)^{(m)}(s)
\]
for \(\Re s>1\).  Verification:

```text
lake env lean GaloisForLFunctions/RHTower/EulerGammaCoPoissonDividedLogJetWeld.lean
lake build GaloisForLFunctions.RHTower.EulerGammaCoPoissonDividedLogJetWeld
```

Both passed.  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
The repository lint still exits nonzero only on pre-existing unrelated unreachable modules; the
new module is imported by the `RHTower` umbrella and produced no lint diagnostic.
