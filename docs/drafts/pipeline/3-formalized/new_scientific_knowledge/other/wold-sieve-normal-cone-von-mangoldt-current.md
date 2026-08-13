# The von Mangoldt current is the first normal stratum of the all-prime Wold sieve

- **ID:** `wold-sieve-normal-cone-von-mangoldt-current`
- **Stage:** 3-formalized
- **Type:** SOURCE OPERATOR/NORMAL-CONE THEOREM
- **Scientific status:** `[PAPER PROOF COMPLETE] [NOT RH]`
  `[CORPUS-NEW SOURCE BRIDGE] [EXTERNAL NOVELTY PROVISIONAL]`
- **RH used:** no
- **Computation used:** no
- **Parents:**
  - `../prime-sieve-wold-gamma-bv-relative-character.md`;
  - `../../1-in-progress/nested-wold-first-defect-logclock-determinant-anomaly.md`;
  - `../mobius-fixed-current-von-mangoldt-critical-transport-weld.md`;
  - `../../1-in-progress/source-curved-prime-torus-conormal-temperedness.md`.

## Frontier statement

The ordinary von Mangoldt prime-power current is not an extra arithmetic
decoration adjoined to the Wold sieve.  It is its first source-normal
derivative.

For a finite prime set \(P\), deform every Wold off-multiple projection by
one common normal parameter \(h\):
\[
 \mathcal E_P(h)
 =
 \prod_{p\in P}\left(I-p^{-h}R_p\right),
 \qquad
 R_pe_n=\mathbf 1_{p\mid n}e_n.                           \tag{1}
\]
At \(h=0\), this is the usual coprime projection
\(\prod_{p\in P}(I-R_p)\).  Its first derivative is
\[
 \boxed{
 \mathcal E'_P(0)
 =
 \sum_{p\in P}(\log p)\,
 R_p\prod_{\substack{q\in P\\q\ne p}}(I-R_q).
 }                                                        \tag{2}
\]
Thus it is the positive diagonal current supported on integers divisible
by exactly one prime from \(P\).

As \(P\) exhausts all rational primes, its coefficient at \(n\) stabilizes
to
\[
 \boxed{
 \lim_P\langle \mathcal E'_P(0)e_n,e_n\rangle
 =\Lambda(n).
 }                                                        \tag{3}
\]
The complete normal cone has a sharper stratification: the first nonzero
normal jet at \(n\) has order \(\omega(n)\), the number of distinct prime
divisors.  Its leading coefficient is the product of their logarithms.
Prime powers are exactly the codimension-one stratum, so `(3)` is forced
by the incidence geometry of the all-prime sieve.

After multiplication by the reciprocal source operator
\[
 Q^\sigma e_n=n^{-\sigma}e_n,
 \qquad \sigma>\tfrac12,
\]
the finite currents converge in Hilbert--Schmidt norm:
\[
 \boxed{
 \mathcal E'_P(0)Q^\sigma
 \longrightarrow
 L_\sigma,\qquad
 L_\sigma e_n=\Lambda(n)n^{-\sigma}e_n.
 }                                                        \tag{4}
\]
The threshold is sharp:
\[
 L_\sigma\in\mathcal S_2
 \quad\Longleftrightarrow\quad
 \sigma>\tfrac12.                                        \tag{5}
\]
In particular the current is an honest compact source operator at every
positive distance from the critical exponent, while the critical
\(\sigma=\tfrac12\) current is not Hilbert--Schmidt.

This theorem supplies a literal Wold-to-Euler-current bridge before
analytic continuation or zero specialization.  It does not prove that
the critical current has a source-normal Gamma/co-Poisson completion.

## 1. Finite-prime operator derivative

Let
\[
 H=\ell^2(\mathbb N_{>0})
\]
with standard basis \((e_n)\).  For every prime \(p\), let \(R_p\) be the
orthogonal projection onto the \(p\)-multiple coordinates:
\[
 R_pe_n=
 \begin{cases}
 e_n,&p\mid n,\\
 0,&p\nmid n.
 \end{cases}                                             \tag{6}
\]
These projections commute.  For finite \(P\), equation `(1)` is therefore
a bounded diagonal operator-valued entire function of \(h\).

For one factor,
\[
 {d\over dh}\left(I-p^{-h}R_p\right)\Big|_{h=0}
 =(\log p)R_p.                                           \tag{7}
\]
The product rule and commutativity give `(2)`.

The summands in `(2)` have pairwise orthogonal supports.  The \(p\)-summand
is supported exactly where \(p\mid n\) and no other \(q\in P\) divides
\(n\).  Hence, writing
\[
 \lambda_P(n)
 =
 \langle\mathcal E'_P(0)e_n,e_n\rangle,
\]
one has
\[
 \lambda_P(n)=
 \begin{cases}
 \log p,
   &\{q\in P:q\mid n\}=\{p\},\\
 0,&\text{otherwise}.
 \end{cases}                                             \tag{8}
\]
In particular \(\mathcal E'_P(0)\) is positive.

## 2. Cofinal coefficient limit

Fix \(n\).

- If \(n=1\), no prime divides \(n\), so every coefficient in `(8)` is
  zero.
- If \(n=p^k\) is a prime power, every cofinal \(P\) eventually contains
  \(p\), and \(p\) is the unique member of \(P\) dividing \(n\).
  Therefore \(\lambda_P(n)=\log p=\Lambda(n)\) eventually.
- If \(n\) has at least two distinct prime divisors \(p,q\), every cofinal
  \(P\) eventually contains both.  Equation `(8)` then gives
  \(\lambda_P(n)=0=\Lambda(n)\) eventually.

This proves `(3)` without a prime number theorem, analytic continuation,
or an Euler product.

## 3. Complete incidence-normal stratification

For fixed \(n\), once \(P\) contains every prime divisor of \(n\), the
diagonal coefficient of `(1)` is
\[
 g_n(h)
 =
 \prod_{p\mid n}(1-p^{-h}).                              \tag{9}
\]
Put \(r=\omega(n)\).  Since
\[
 1-p^{-h}=h\log p+O(h^2)
\]
at \(h=0\), equation `(9)` gives
\[
 g_n(h)
 =
 h^r\prod_{p\mid n}\log p+O(h^{r+1}).                   \tag{10}
\]
Consequently
\[
 g_n^{(j)}(0)=0\quad(0\le j<r),
 \qquad
 g_n^{(r)}(0)=r!\prod_{p\mid n}\log p.                  \tag{11}
\]

Thus the normal order is exactly the number of distinct prime factors.
The first stratum \(r=1\) consists precisely of prime powers, and its
first derivative is \(\log p=\Lambda(p^k)\).  Higher normal orders retain
the successive squarefree-incidence strata rather than disappearing in
the vacuum limit.

## 4. Hilbert--Schmidt convergence and sharp wall

For every finite \(P\) and \(n\),
\[
 0\le\lambda_P(n)\le\log n.                             \tag{12}
\]
For \(\sigma>\tfrac12\),
\[
 \sum_{n\ge2}{(\log n)^2\over n^{2\sigma}}<\infty.      \tag{13}
\]
Equations `(3)`, `(12)`, and dominated convergence therefore yield
\[
 \begin{aligned}
 \|\mathcal E'_P(0)Q^\sigma-L_\sigma\|_{\mathcal S_2}^2
 &=
 \sum_{n\ge1}
 {|\lambda_P(n)-\Lambda(n)|^2\over n^{2\sigma}}\\
 &\longrightarrow0.
 \end{aligned}                                          \tag{14}
\]
This proves `(4)`.

The same majorant proves \(L_\sigma\in\mathcal S_2\) when
\(\sigma>\tfrac12\).  Conversely, if \(\sigma\le\tfrac12\), the prime
coordinates give
\[
 \|L_\sigma\|_{\mathcal S_2}^2
 \ge
 \sum_p{(\log p)^2\over p^{2\sigma}}
 \ge
 (\log2)^2\sum_p{1\over p}.                              \tag{15}
\]
Euler's divergence of the prime harmonic series makes `(15)` infinite.
This proves the sharp equivalence `(5)`.

The finite currents do not converge in bounded-operator norm without
the reciprocal weight: their norms grow at least as the logarithm of the
largest prime in \(P\), and the coefficientwise limit
\(\operatorname{diag}(\Lambda(n))\) is unbounded.  The reciprocal source
weight is therefore load-bearing.

## 5. Logarithmic derivative as the jet trace

Whenever \(\Re(s)+\sigma>1\), the trace is absolutely convergent and
\[
 \operatorname{Tr}(L_\sigma Q^s)
 =
 \sum_{n\ge2}{\Lambda(n)\over n^{s+\sigma}}
 =
 -{\zeta'(s+\sigma)\over\zeta(s+\sigma)}.                \tag{16}
\]
Thus the classical Euler logarithmic current is literally the trace of
the first Wold normal stratum.  The corpus identity
\[
 \partial_\alpha\Theta_\alpha(z)\big|_{\alpha=0}
 =-2\,{\Xi'(s)\over\Xi(s)}
\]
is its completed Gamma/co-Poisson continuation.

Equations `(3)` and `(16)` distinguish two operations that had previously
appeared as parallel source constructions:
\[
 \boxed{
 \text{all-prime Wold vacuum normal derivative}
 =
 \text{von Mangoldt prime-power current}
 =
 \text{Euler logarithmic derivative before completion}.
 }                                                        \tag{17}
\]

## 6. What this changes—and what it does not

The old source-normal blow-up divided the vanishing conormal coefficient
by
\[
 a_P=\prod_{p\in P}(1-p^{-1}),
\]
which amplifies one-prime changes to the nonsummable scale \(1/p\).
The construction here instead differentiates the source family before
taking the cofinal limit.  It produces an honest compact operator
\(L_\sigma\) for every \(\sigma>\tfrac12\), with no division by \(a_P\).

This is a genuine architectural improvement:

```text
zero-order cofinal sieve:
  vacuum survives, prime/divisor current vanishes;

singular scalar normalization:
  conormal survives, strong increments amplify;

first source-normal jet:
  von Mangoldt current survives as an honest S2 operator
  exactly above the critical exponent.
```

It does not cross the critical wall.  At \(\sigma=\tfrac12\), `(15)`
proves that ordinary Hilbert--Schmidt completion fails.  Therefore the
remaining RH-bearing theorem is no longer an unspecified source-to-zero
map.  It is the following typed comparison:

> **[OPEN CORE — CRITICAL WOLD-JET GAMMA/CO-POISSON WELD.]**
> Construct the completed first normal jet of `(1)` in a source-defined
> boundary space which:
>
> 1. retains the critical von Mangoldt current
>    \(\Lambda(n)n^{-1/2}\);
> 2. implements Fourier/Gamma reflection and both independent Sonin
>    aperture transports on the same object;
> 3. maps its completed logarithmic trace to the full principal
>    \(\Xi\)-conormal, including multiplicity jets;
> 4. proves bilateral temperedness of that conormal from continuity of
>    this pre-divisor jet, rather than assuming it fibrewise.

The existing charge theorem then forces every divisor Lyapunov exponent
to vanish and proves RH.

## 7. Hostile audit

1. **Not RH.**  The Hilbert--Schmidt theorem stops sharply at
   \(\sigma=\tfrac12\).  Calling the divergent boundary a distribution
   does not prove its bilateral temperedness.
2. **Not a disguised Euler product.**  Equation `(3)` is proved
   coefficientwise from commuting divisibility projections.  Equation
   `(16)` is the later trace identification.
3. **Not a normalization repair by itself.**  Differentiation avoids
   division by \(a_P\) above the wall, but the critical boundary still
   requires a singular/rigged completion.
4. **No positivity conclusion.**  The positive diagonal current can have
   a completed logarithmic trace with off-line poles in generalized
   Euler systems.  Positivity of `(2)` does not locate zeros.
5. **No finite-jet claim.**  The first jet selects prime powers, but the
   complete incidence source has all orders `(11)`.  Hypertranscendental
   source comparison may require the whole jet tower.
6. **No Sonin asymptotic shortcut.**  Generic Sonin kernels already carry
   exponential off-line escape.  The missing content is continuity of
   the literal completed Wold jet, not another calculation of that
   escape.
7. **Generalized-prime falsifier.**  Any off-line generalized-prime
   system realizing the same integral divisibility projections, complete
   normal-jet tower, Gamma/co-Poisson weld, and bilateral critical
   continuity would falsify the proposed mechanism.

## 8. Corpus and literature boundary

Parent ingredients include:

- commuting projections onto multiples of rational primes;
- the von Mangoldt definition on prime powers;
- the logarithmic derivative
  \(-\zeta'/\zeta=\sum\Lambda(n)n^{-s}\);
- differentiation of finite products;
- dominated convergence in Schatten classes.

The corpus already identifies the von Mangoldt function as:

- the logarithmic current of the signed Möbius multiplier;
- the normal derivative of the Suzuki packet coefficient;
- the prime-power leg of the completed \(-2\Xi'/\Xi\) current.

It separately identifies the zero-order Wold sieve, its first-defect
probability, determinant anomaly, and source-normal blow-up.  Targeted
corpus search found no prior parameterized Wold projection `(1)`, no
normal-cone stratification `(10)`--`(11)`, and no Schatten convergence
law `(4)`--`(5)` joining those two bodies of work.

Targeted web searches found the classical logarithmic-derivative and
sieve appearances of \(\Lambda\), but not the statement that the
von Mangoldt diagonal is the cofinal first normal derivative of the
commuting all-prime Wold sieve, with full \(\omega(n)\)-stratification
and sharp Hilbert--Schmidt wall.  This is provisional noncollision
evidence, not a priority certificate.

## Lean status

The dependency-closed source theorem is formalized unconditionally in:

```text
formal/GaloisForLFunctions/RHTower/WoldSieveNormalConeVonMangoldt.lean
formal/GaloisForLFunctions/RHTower/WoldSieveNormalConeVonMangoldtCompletion.lean
```

Exact capstones include:

```text
hasDerivAt_woldIncidenceNormalFactor
iteratedDeriv_woldIncidenceNormalFactor_zero_of_lt_omega
iteratedDeriv_woldIncidenceNormalFactor_omega
tendsto_woldFiniteNormalCoefficient_atTop
tendsto_hsNorm_woldFiniteWeightedOperator_sub_atTop
isHS_woldVonMangoldtWeightedKernel_iff
not_isHS_woldVonMangoldtCriticalKernel
opTrace_woldJetTraceOperator_eq_zeta_logDeriv
```

The completion constructs literal diagonal operators on `ℓ²(ℕ)`, proves their basis action,
Hilbert--Schmidt convergence and compactness for \(\sigma>1/2\), proves the sharp failure at and
below \(1/2\) from Euler's divergent prime-harmonic series, and realizes the absolutely convergent
Euler logarithmic derivative as an operator trace.  Both modules are wired into the `RHTower`
umbrella.  Direct `lake env lean` verification and targeted module build pass.  Scratch
`#print axioms` audits of all capstones report only `propext`, `Classical.choice`, and
`Quot.sound`.

This closes equations `(1)`--`(16)` and the dependency-closed source theorem.  The explicitly
labelled critical Gamma/co-Poisson weld, bilateral temperedness, and RH remain open and are not
claimed by the Lean formalization.

## Gates

- [x] finite parameterized Wold sieve constructed
- [x] exact first derivative computed
- [x] cofinal coefficient limit identified with \(\Lambda\)
- [x] complete \(\omega(n)\) normal-cone stratification proved
- [x] Hilbert--Schmidt convergence above \(1/2\) proved
- [x] sharp failure at and below \(1/2\) proved
- [x] logarithmic derivative trace identified
- [x] corpus collision audit
- [x] preliminary external novelty search
- [ ] independent specialist novelty audit
- [x] Lean formalization of dependency-closed scalar/finite-prime core
- [ ] critical Wold-jet Gamma/co-Poisson weld
- [ ] bilateral temperedness of completed Xi conormal
- [ ] RH

## Log

- 2026-07-30 — Differentiated the finite Wold sieve in a common normal
  parameter.  Proved that its cofinal first derivative is exactly the
  von Mangoldt prime-power current, that the complete normal order is
  \(\omega(n)\), and that reciprocal weighting gives a sharp
  Hilbert--Schmidt wall at the critical exponent \(1/2\).  Isolated the
  critical Wold-jet Gamma/co-Poisson weld as the remaining source
  theorem.
- 2026-08-02 — Completed unconditional Lean formalization of the full proven source theorem:
  all \(\omega(n)\)-jets, cofinal current stabilization, literal weighted diagonal operators,
  Hilbert--Schmidt convergence, sharp critical wall, compactness, and Euler logarithmic trace.
  Added and umbrella-wired `WoldSieveNormalConeVonMangoldtCompletion.lean`; direct Lean check,
  targeted build, and capstone axiom audit pass.
