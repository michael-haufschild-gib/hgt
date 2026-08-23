# Prime-tail co-Poisson essential boundary and divisor Bockstein

- **ID:** `prime-tail-copoisson-essential-boundary-bockstein`
- **Stage:** 3-formalized / needs independent audit
- **Type:** EXACT ALL-PRIME SOURCE LIFT / ESSENTIAL-BOUNDARY CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parents:**
  - `gamma-factorial-hilbert-hankel-source-normal-bridge.md`;
  - `burnol-prime-dilation-copoisson-quotient-law.md`;
  - `../../../1-in-progress/reflected-character-singular-splitting-bockstein-law.md`.
- **RH used:** no
- **Computation used:** no
- **Lean:** complete; see the formalization table below

## Result

The Euler--Gamma quadrant current has a literal one-variable co-Poisson preclosure.  It is not an
ordinary compact co-Poisson seed: prime condensation forces the sharp boundary singularity
\[
 \frac{1}{x\log(1/x)}.
\]
After the standard logarithmic half-density change, this becomes
\[
 \frac{e^{L/2}}{L},\qquad L=\log(1/x),
\]
so the all-prime object has an essential cofinal type rather than any fixed finite Rees order.

More importantly, analytic continuation of this same source object has explicit divisor
monodromy
\[
 2\pi i\,m_\rho x^{-\rho}.
\]
Normalized dilation acts on this germ by the source-inverse character
\(r^{1/2-\rho}\); inversion followed by conjugation produces the analytic-adjoint germ
\(x^{\bar\rho-1}\), on which normalized dilation acts by
\(r^{\bar\rho-1/2}\).

Thus the all-prime interval current now constructs, before scalar specialization:

```text
ordinary prime-power tail
  -> literal co-Poisson interval preclosure
  -> essential source boundary
  -> nonzero divisor monodromy germ
  -> source-inverse and analytic-adjoint reflected modes.
```

It does **not** yet prove that the two reflected modes define one nonzero relative class.  That
strict cross-landing remains the RH-bearing theorem.

## 1. The prime-tail seed

Put
\[
 a_n=
 \begin{cases}
  \Lambda(n)/\log n,&n\ge2,\\
  0,&n=1,
 \end{cases}
 \qquad
 P(z)=\sum_{n\ge2}a_nn^{-z}=\log\zeta(z)
 \quad(\Re z>1).
\tag{1}
\]
For \(n\ge2\), \(\Re z>1\), and \(0<x<1\), define the compact interval seed
\[
 g_{n,z}(x)
 =n^{-z}x^{-z}\mathbf 1_{[1/n,1]}(x)
\tag{2}
\]
and its all-prime condensation
\[
 G_z(x)
 =\sum_{n\ge2}a_ng_{n,z}(x)
 =x^{-z}\sum_{\substack{n\ge2\\nx\ge1}}a_nn^{-z}.
\tag{3}
\]
For every fixed \(x>0\), the sum in `(3)` converges absolutely.

Let the right Mellin transform be
\[
 \widehat f(s)=\int_0^\infty f(x)x^{-s}\,dx.
\tag{4}
\]
Then, for \(\Re z,\Re w>1\),
\[
\begin{aligned}
 \widehat g_{n,z}(1-w)
 &=n^{-z}\int_{1/n}^1x^{w-z-1}\,dx\\
 &=\frac{n^{-w}-n^{-z}}{z-w},
\end{aligned}
\tag{5}
\]
with removable diagonal value \(n^{-z}\log n\).

In Burnol's centered character convention, put
\[
 \gamma_{n,\nu}(x)
 =n^{\nu-1/2}x^{\nu-1}\mathbf 1_{[1/n,1]}(x).
\tag{6}
\]
Then
\[
 \boxed{\qquad
 g_{n,z}=n^{-1/2}\gamma_{n,1-z}.
 \qquad}
\tag{7}
\]
Consequently each cell in `(3)` is exactly the reflected, half-density-normalized
Burnol/co-Poisson divided-difference seed, not merely a scalar function with the same Mellin
transform.

## 2. Exact Mellin scalarization

`[PAPER-PROVED] [PRIME_TAIL_COPOISSON_MELLIN_WELD]`

For \(\Re z,\Re w>1\),
\[
 \boxed{\qquad
 \int_0^1G_z(x)x^{w-1}\,dx
 =
 \frac{P(z)-P(w)}{w-z}.
 \qquad}
\tag{8}
\]
At \(w=z\), the removable value is
\[
 \int_0^1G_z(x)x^{z-1}\,dx
 =
 \sum_{n\ge2}\Lambda(n)n^{-z}
 =
 -\frac{\zeta'(z)}{\zeta(z)}.
\tag{9}
\]

### Proof

For \(\Re z,\Re w>1\), the absolute-value version of the termwise integral is bounded by a
convergent von Mangoldt Dirichlet series at
\(\min(\Re z,\Re w)>1\).  Tonelli--Fubini and `(5)` therefore give
\[
\begin{aligned}
 \int_0^1G_z(x)x^{w-1}\,dx
 &=\sum_{n\ge2}a_n
   \frac{n^{-w}-n^{-z}}{z-w}\\
 &=\frac{P(z)-P(w)}{w-z}.
\end{aligned}
\]
The diagonal follows either by dominated confluence or directly from
\(a_n\log n=\Lambda(n)\).  `QED`

Under \(x=e^{-u}\), equation `(5)` is exactly the \(u\)-coordinate pushforward of the segment
\[
 (t,u)=(\log n-u,u),\qquad 0\le u\le\log n,
\tag{10}
\]
in the Euler--Gamma quadrant current.  Thus `(8)` is the one-variable pre-scalarization of that
current, not a second construction.

## 3. Prime condensation creates the sharp essential boundary

Let
\[
 J(X)=\sum_{2\le n\le X}a_n
 =\sum_{p^k\le X}\frac1k
\tag{11}
\]
be Riemann's weighted prime-power counting function.  The prime number theorem gives
\[
 J(X)\sim\operatorname{Li}(X)\sim\frac{X}{\log X}.
\tag{12}
\]

For fixed \(z\) with \(\Re z>1\), partial summation gives
\[
 \sum_{n\ge y}a_nn^{-z}
 =
 -J(y^-)y^{-z}
 +z\int_y^\infty J(t)t^{-z-1}\,dt.
\tag{13}
\]
Using `(12)` and
\[
 \int_y^\infty\frac{t^{-z}}{\log t}\,dt
 \sim
 \frac{y^{1-z}}{(z-1)\log y}
\tag{14}
\]
in `(13)` yields
\[
 \sum_{n\ge y}a_nn^{-z}
 \sim
 \frac{y^{1-z}}{(z-1)\log y}.
\tag{15}
\]
Substitute \(y=1/x\) in `(3)`.

`[PAPER-PROVED] [PRIME_TAIL_SHARP_ESSENTIAL_BOUNDARY]`

For every fixed \(z\) with \(\Re z>1\),
\[
 \boxed{\qquad
 G_z(x)
 \sim
 \frac{1}{(z-1)x\log(1/x)}
 \qquad(x\downarrow0).
 \qquad}
\tag{16}
\]
Hence, for every real \(\alpha\),
\[
 \boxed{\qquad
 x^\alpha G_z(x)\in L^2(0,1)
 \quad\Longleftrightarrow\quad
 \alpha\ge\frac12.
 \qquad}
\tag{17}
\]
The endpoint \(\alpha=1/2\) is included only because of the prime logarithm:
\[
 \int_0^\varepsilon
  \left|x^{1/2}G_z(x)\right|^2dx
 \asymp
 \int_0^\varepsilon\frac{dx}{x\log^2(1/x)}
 <\infty.
\tag{18}
\]
In contrast, \(G_z\notin L^1(0,1)\).

Let
\[
 (Wf)(L)=e^{-L/2}f(e^{-L}),\qquad L>0,
\tag{19}
\]
be the logarithmic half-density transform.  Equation `(16)` becomes
\[
 \boxed{\qquad
 (WG_z)(L)
 \sim
 \frac{e^{L/2}}{(z-1)L}.
 \qquad}
\tag{20}
\]
Thus the literal all-prime preclosure has exponential cofinal growth after every fixed
polynomial/Rees shadow is removed.  Infinite rank is not responsible; the singularity already
occurs in this one source boundary coordinate.

## 3A. Canonical pole-vacuum removal creates the all-orders-flat irregular sector

The leading term in `(16)` is not an unexplained divergence.  It is exactly the continuous prime
vacuum supplied by the pole at \(z=1\).

For \(X\ge e\), put
\[
 J_0(X)=\int_e^X\frac{dt}{\log t}
\tag{20a}
\]
up to an irrelevant additive constant, and define its interval suspension
\[
 V_z(x)
 =
 x^{-z}
 \int_{\max(e,1/x)}^\infty\frac{t^{-z}}{\log t}\,dt,
 \qquad 0<x<1.
\tag{20b}
\]
If
\[
 V(z)=\int_e^\infty\frac{t^{-z}}{\log t}\,dt
 =E_1(z-1),
\tag{20c}
\]
then the same Tonelli calculation as in `(8)` gives
\[
 \int_0^1V_z(x)x^{w-1}\,dx
 =
 \frac{V(z)-V(w)}{w-z}.
\tag{20d}
\]
Here \(E_1\) is the exponential integral in its standard branch.  Near \(z=1\),
\[
 V(z)=-\gamma-\log(z-1)+O(z-1),
\tag{20e}
\]
whereas
\[
 P(z)=\log\zeta(z)=-\log(z-1)+O(z-1).
\tag{20f}
\]
Therefore
\[
 P(z)-V(z)
\tag{20g}
\]
is single-valued and holomorphic at \(z=1\), up to the harmless choice of additive constant.
This is the chain-level continuous-density realization of the pole cancellation in
\((z-1)\zeta(z)\).

Put
\[
 R_z(x)=G_z(x)-V_z(x).
\tag{20h}
\]
The classical quantitative prime number theorem gives constants \(c,C>0\) such that
\[
 J(X)-J_0(X)
 =
 O\!\left(Xe^{-c\sqrt{\log X}}\right).
\tag{20i}
\]
An additive constant in \(J_0\) changes only a bounded lower-end source term.  Stieltjes partial
summation of the signed measure \(d(J-J_0)\) now gives, for every fixed
\(\Re z>1\), some \(c_z,C_z>0\) with
\[
 \boxed{\qquad
 |R_z(x)|
 \le
 C_zx^{-1}e^{-c_z\sqrt{\log(1/x)}}
 \qquad(x\downarrow0).
 \qquad}
\tag{20j}
\]
Indeed, with \(y=1/x\) and \(E=J-J_0\),
\[
 \int_{[y,\infty)}t^{-z}\,dE(t)
 =
 -E(y^-)y^{-z}
 +z\int_y^\infty E(t)t^{-z-1}\,dt,
\tag{20k}
\]
and `(20i)` bounds both terms by
\(O_z(y^{1-\Re z}e^{-c_z\sqrt{\log y}})\).

Equations `(16)` and `(20j)` imply
\[
 \frac{R_z(e^{-L})}{V_z(e^{-L})}
 =
 O_z\!\left(Le^{-c_z\sqrt L}\right).
\tag{20l}
\]
Consequently, for every \(N\ge0\),
\[
 \boxed{\qquad
 L^N\frac{R_z(e^{-L})}{V_z(e^{-L})}
 \longrightarrow0.
 \qquad}
\tag{20m}
\]
The vacuum-normalized arithmetic remainder is all-orders flat.  The unconditional source estimate
for its absolute half-density size is
\[
 \boxed{\qquad
 |(WR_z)(L)|
 \le
 C_ze^{L/2-c_z\sqrt L},
 \qquad}
\tag{20n}
\]
The envelope on the right dominates every fixed power of \(L\), so the quantitative PNT does not
supply absolute finite-Rees control.  Thus:

```text
continuous pole vacuum:
  e^(L/2)/L, not all-orders flat;

ordinary-prime irregular remainder relative to that vacuum:
  all-orders flat;

available absolute arithmetic envelope:
  essential scale; no finite-Rees bound follows from PNT.
```

This is the literal prime-tail realization of the corpus's flat-irregular/nonflat-vacuum
fracture.  A finite-Rees multiplier cannot reconstruct the irregular remainder from the vacuum,
while merely allowing arbitrary essential growth does not select a horizontal zero location.

## 4. The divisor Bockstein is explicit

For fixed \(x\in(0,1)\), equation `(3)` can be written
\[
 G_z(x)
 =
 x^{-z}
 \left(
  P(z)
  -\sum_{\substack{n\ge2\\nx<1}}a_nn^{-z}
 \right).
\tag{21}
\]
The second term in parentheses is a finite, single-valued entire function of \(z\).  Therefore
all branch monodromy of `(21)` comes from \(P(z)=\log\zeta(z)\).

Let \(\rho\) be a nontrivial zero of multiplicity \(m_\rho\).  Continuation once positively
around \(\rho\) gives
\[
 \boxed{\qquad
 \Delta_\rho G_z(x)
 =
 2\pi i\,m_\rho x^{-z}.
 \qquad}
\tag{22}
\]
At \(z=\rho\), its boundary value is the nonzero germ
\[
 b_\rho(x)=2\pi i\,m_\rho x^{-\rho}.
\tag{23}
\]
Every differentiated logarithmic jet also survives:
\[
 \left.
 \partial_z^k\Delta_\rho G_z(x)
 \right|_{z=\rho}
 =
 2\pi i\,m_\rho(-\log x)^kx^{-\rho},
 \qquad k\ge0.
\tag{24}
\]
Because \(0<\Re\rho<1\), every germ in `(24)` is locally integrable at \(0\).  Thus the
source-tail continuation retains the principal divisor multiplicity and the complete finite
logarithmic jet tower even though the uncontinued preclosure `(16)` does not extend as an
ordinary \(L^1\) seed across the source boundary.

The polynomial and Gamma factors in \(\Xi\) are single-valued and nonzero at every nontrivial
zero, so `(22)`--`(24)` are also the nontrivial-divisor monodromy of the completed logarithmic
source.

## 5. Reflected characters arise from the same germ

Let normalized dilation act locally by
\[
 (U_rf)(x)=r^{1/2}f(rx),\qquad r>1.
\tag{25}
\]
Then the germ in `(23)` obeys
\[
 U_rb_\rho
 =
 r^{1/2-\rho}b_\rho.
\tag{26}
\]
Thus its exact character is the source inverse
\[
 \alpha_\rho(r)=r^{1/2-\rho}.
\tag{27}
\]

Let
\[
 (If)(x)=x^{-1}f(x^{-1})
\tag{28}
\]
be multiplicative inversion.  The reflected conjugate germ is
\[
 b_\rho^\dagger
 :=
 I\overline{b_\rho}
 =
 -2\pi i\,m_\rho x^{\bar\rho-1},
\tag{29}
\]
and
\[
 U_rb_\rho^\dagger
 =
 r^{\bar\rho-1/2}b_\rho^\dagger.
\tag{30}
\]
Its character is exactly the analytic adjoint
\[
 \beta_\rho(r)=r^{\bar\rho-1/2}.
\tag{31}
\]
Under the logarithmic transform `(19)`, the two homogeneous modes are
\[
 e^{(\rho-1/2)L},
 \qquad
 e^{(1/2-\bar\rho)L}.
\tag{32}
\]
They coincide in radial type exactly on the critical line.  Equations `(26)` and `(30)` derive
the two characters from one ordinary-prime continuation germ and its co-Poisson inversion; they
are not fitted after a zero is selected.

## 6. Exact frontier change

The previous open core asked for an all-prime extension of the local Gamma/co-Poisson interval
cell whose Bockstein is the Xi divisor conormal.  Equations `(3)`, `(8)`, and `(22)` now provide
that extension and Bockstein at the punctured-source/distribution-germ level:

```text
finite interval cell:
  g_(n,z);

all-prime action condensation:
  G_z;

essential boundary:
  G_z(x) ~ 1/((z-1)x log(1/x));

divisor Bockstein:
  Delta_rho G = 2 pi i m_rho x^(-rho);

reflected source actions:
  alpha_rho and beta_rho.
```

The remaining theorem is no longer “construct some conormal-faithful all-prime primitive.”
It is:

`[OPEN CORE — PRIME_TAIL_SONIN_REFLECTED_CROSS_LANDING]`

> Extend the punctured prime-tail family \(G_z\), together with its archimedean completion,
> through one strict source-normal co-Poisson/Sonin finite-part functor, and prove that the
> nonzero monodromy germ `(23)` and its reflected dagger germ `(29)` are the two endpoint actions
> of one nonzero relative Bockstein class after strict Xi Cartier base change.

If that class lies in
\[
 \operatorname{Ext}_{\mathbb C[\mathbb N_{>0}]}^q
 \left(
  \mathbb C_{\alpha_\rho},
  \mathbb C_{\beta_\rho}
 \right)
\tag{33}
\]
for some \(q\) and is nonzero, the already-proved off-diagonal Ext support theorem forces
\(\alpha_\rho=\beta_\rho\), hence \(\Re\rho=1/2\).

## Hostile audit

1. **Not RH.**  Equation `(22)` constructs a nonzero self-monodromy mode for every zero, including
   a hypothetical off-line zero.  It does not yet construct a nonzero cross-class in `(33)`.
2. **Monodromy is not a selector.**  The corpus already proves that complete prime-grade
   monodromy is equivalent to divisor data.  The new delta is the coefficient-tail/source
   coupling `(3)` and its literal co-Poisson interval lift, not the fact that
   \(\log\zeta\) winds around zeros.
3. **Two nonzero modes are not one relative class.**  Off the critical line,
   \(\alpha_\rho\ne\beta_\rho\), and every ordinary relative Ext class splits.  Treating
   `(23)` and `(29)` as if their coexistence implied nonzero cross-cohomology would be false.
4. **Essentiality is necessary, not selective.**  The growth `(20)` supplies the kind of
   preclosure invisible to every fixed finite-Rees shadow.  A generic essential distribution
   completion can still contain both members of an off-line quartet.
5. **The half-weight endpoint is not a Hilbert--Pólya proof.**  Equation `(17)` is a sharp
   source-boundary classification.  Changing the weight shifts dilation characters and cannot
   be used to declare an off-line mode unitary.
6. **Generalized-prime falsifier remains.**  A Beurling system with
   \(J(X)\sim X/\log X\) has the same boundary asymptotic `(16)` and may have off-line zeros.
   The surviving arithmetic input must use the literal ordinary-integer Poisson/Fourier
   intertwining, not only the weighted prime-power asymptotic.
7. **No automatic Sonin landing.**  Each finite \(g_{n,z}\) is a compact interval seed, but
   \(G_z\notin L^1\) at \(0\).  Passing termwise to Burnol's closed co-Poisson source space is
   precisely the strict finite-part problem, not a consequence of `(8)`.
8. **No hidden multiplicity claim.**  The monodromy coefficient records \(m_\rho\), and `(24)`
   retains every logarithmic derivative of the homogeneous germ.  Identifying this tower with
   Burnol's full top multiplicity evaluator requires the open strict Sonin comparison.

## Literature boundary

The ingredients \(P(z)=\log\zeta(z)\), Riemann's weighted prime-power counting function
\(J(X)\), its prime-number-theorem asymptotic, Mellin partial summation, and Burnol's compact
co-Poisson interval formula are established mathematics.  The construction is therefore
classified as `[BRIDGE]`, regardless of whether the exact tail kernel `(3)` and its quadrant
interpretation have appeared verbatim.

Primary parent sources:

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Théor. Nombres Bordeaux 16 (2004), 65--94.
- J.-F. Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007), 525--602.

A targeted corpus and web/arXiv search found the standard Mellin pair for \(J(X)\) and
\(\log\zeta\), but not the exact quadrant-pushforward kernel `(3)`, boundary wall `(17)`, and
source-character monodromy chain `(22)`--`(31)` as one theorem.  This is not a priority claim.

## Gates

- [x] exact interval-seed/right-Mellin convention fixed
- [x] all-prime quadrant pushforward constructed
- [x] divided-log Mellin scalarization proved
- [x] sharp PNT boundary asymptotic and half-weight wall proved
- [x] divisor monodromy and every logarithmic germ jet computed
- [x] source-inverse and analytic-adjoint characters derived from dilation/inversion
- [x] self-monodromy separated from the missing reflected cross-class
- [ ] attach archimedean finite-part source at chain level
- [ ] prove strict ordinary-integer co-Poisson/Sonin extension
- [ ] prove nonzero reflected cross-landing after Xi Cartier base change
- [ ] formalize only after the literal analytic interfaces and paper theorem close

## Lean formalization

Every displayed claim of this card is proved unconditionally in Lean 4; each theorem below has
been checked to depend only on `propext`, `Classical.choice`, `Quot.sound`.

| card item | Lean declaration | module |
|---|---|---|
| `(2)`, `(6)`, `(7)` | `primeTailSeed`, `burnolCell`, `primeTailSeed_eq_burnolCell` | `RHTower/PrimeTailCoPoissonBoundary` |
| `(5)` | `integral_primeTailSeed` | `RHTower/PrimeTailCoPoissonBoundary` |
| `(3)` | `primeTailCurrent` | `RHTower/PrimeTailCoPoissonBoundary` |
| **`(8)`** | `primeTailCurrent_mellin` | `RHTower/PrimeTailCoPoissonBoundary` |
| **`(9)`** | `primeTailCurrent_mellin_diag` | `RHTower/PrimeTailCoPoissonBoundary` |
| `(11)` | `primeTailCount` | `RHTower/PrimeTailCoPoissonBoundary` |
| **`(12)`** | `tendsto_primeTailCount` | `RHTower/PrimeTailCoPoissonBoundary` |
| `(13)` | `primeTailSum_eq_integral` | `RHTower/PrimeTailBoundaryAsymptotic` |
| `(14)` | `integral_logPowerTail_one`, `norm_integral_logPowerTail_le` | `RHTower/PrimeTailBoundaryAsymptotic` |
| **`(15)`** | `tendsto_primeTailSum_div` | `RHTower/PrimeTailBoundaryAsymptotic` |
| **`(16)`** | `tendsto_primeTailCurrent_boundary` | `RHTower/PrimeTailBoundaryAsymptotic` |
| **`(17)`** | `primeTailCurrent_halfWeight_wall` | `RHTower/PrimeTailHalfWeightWall` |
| `(18)` | `integrableOn_halfWeight_critical`, `not_integrableOn_primeTailCurrent` | `RHTower/PrimeTailHalfWeightWall` |
| `(19)` | `logHalfDensity` | `RHTower/PrimeTailHalfWeightWall` |
| **`(20)`** | `tendsto_logHalfDensity_primeTailCurrent` | `RHTower/PrimeTailHalfWeightWall` |
| `(20a)` | `logIntegralCount` | `RHTower/PrimeVacuumCurrent` |
| `(20b)` | `primeVacuumCurrent` | `RHTower/PrimeVacuumCurrent` |
| **`(20c)`** | `primeVacuumValue_eq`, `primeVacuumTail_eq_expIntegralOneC` | `RHTower/PrimeVacuumExponentialIntegral` |
| **`(20d)`** | `integral_vacuumMellin` | `RHTower/PrimeVacuumMellin` |
| **`(20e)`** | `primeVacuumValue_ofReal` | `RHTower/PrimeVacuumPoleCancellation` |
| **`(20f)`** | `canonicalEulerLogZeta_ofReal_eq` | `RHTower/PrimeVacuumPoleCancellation` |
| **`(20g)`** | `primePoleCancellation`, `tendsto_primePoleCancellation` | `RHTower/PrimeVacuumPoleCancellation` |
| `(20h)` | `primeRemainderCurrent` | `RHTower/PrimeVacuumFlatRemainder` |
| **`(20i)`** | `exists_primeTailCount_sub_logIntegralCount_bound` | `RHTower/PrimeVacuumErrorTransfer` |
| `(20k)` | `primeRemainderTail_eq`, `primeVacuumTail_eq_window` | `RHTower/PrimeVacuumFlatRemainder`, `RHTower/PrimeVacuumCurrent` |
| **`(20j)`** | `exists_norm_primeRemainderCurrent_bound` | `RHTower/PrimeVacuumFlatRemainder` |
| **`(20l)`, `(20m)`** | `tendsto_pow_mul_flatRatio` | `RHTower/PrimeVacuumFlatRemainder` |
| **`(20n)`** | `exists_norm_logHalfDensity_primeRemainderCurrent_bound` | `RHTower/PrimeVacuumFlatRemainder` |
| `(21)` | `primeTailCurrent_eq_finitePart` | `RHTower/PrimeTailCoPoissonBoundary` |
| **`(22)`** | `primeTailCurrent_monodromy` | `RHTower/PrimeTailCoPoissonBoundary` |
| `(23)` | `monodromyGerm_ne_zero` | `RHTower/PrimeTailCoPoissonBoundary` |
| **`(24)`** | `iteratedDeriv_monodromyGerm` | `RHTower/PrimeTailCoPoissonBoundary` |
| `(25)`, `(28)` | `normalizedDilation`, `multiplicativeInversion` | `RHTower/PrimeTailCoPoissonBoundary` |
| **`(26)`–`(31)`** | `normalizedDilation_monodromyGerm`, `multiplicativeInversion_conj_monodromyGerm`, `normalizedDilation_reflectedGerm`, `dilation_characters_eq_iff` | `RHTower/PrimeTailCoPoissonBoundary` |

Notes on the formalization.

* The two Abel transforms — arithmetic and continuous — are proved by different devices.  The
  arithmetic one is Fubini in disguise: `u^{-z} = z ∫_u^∞ v^{-z-1} dv` turns each Dirichlet term
  into an indicator integral and a sum–integral interchange finishes.  The continuous one is
  proved by differentiating in the cut: both sides have derivative `-y^{-z}/log y` and vanish at
  infinity, which avoids product-measure Fubini entirely.  The same device proves `(20d)`.
* `(20i)` avoids Stieltjes integration by parts: `1/log n = 1/log X + ∫_n^X dt/(t log² t)` turns
  both counting functions into integrals of `psi` respectively the identity against one kernel.
* `(20e)`–`(20g)` reuse the corpus: `RHTower/EulerMascheroniGaussKernel` supplies
  `∫_ε^∞ e^{-t}/t = -log ε + Ein(ε) - γ` with `|Ein(ε)| ≤ ε`, and
  `RHTower/EulerFisherPoincareBoundary` supplies the analytic regular part of the Euler logarithm
  at the pole.  The logarithms then cancel identically, with no branch analysis.
