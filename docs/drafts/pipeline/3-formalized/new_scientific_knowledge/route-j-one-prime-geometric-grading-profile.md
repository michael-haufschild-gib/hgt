# Route J one-prime geometric grading profile

- **ID:** `route-j-one-prime-geometric-grading-profile`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scientific status:** CANDIDATE NEW SCIENTIFIC KNOWLEDGE, source-specific and provisional
- **Route owner:** `route-j-principal-relative-julia-current.md`, survivor `J-SF5`
- **Lean certificate:**
  `formal/GaloisForLFunctions/RHTower/SoninSemilocalGradingGeometricProfile.lean`

## 1. Literal source coefficient

Fix a prime \(p\). Put

\[
 r_p=p^{-1/2},\qquad
 \phi(t)=\sqrt{\frac{2}{\cosh t}},
\]

and for \(k,M\geq0\) define the positive raw frequency magnitude

\[
 B_{k,p}(M)
 =
 r_p^M\phi(M\log p)\tanh(M\log p)^{2k}.                 \tag{1}
\]

The literal one-prime even Jacobi magnitude series and coefficient are

\[
 R_{k,p}=\sum_{M\geq0}B_{k,p}(M),                       \tag{2}
\]
\[
 S_{k,p}=c_{2k}R_{k,p},\qquad
 |C_{k,p}|=P_pS_{k,p},\qquad
 P_p=\frac{2}{1-p^{-1}},                                \tag{3}
\]

where \(c_n\) is the archimedean Jacobi normalization already constructed in the
semilocal source. For \(k>0\), the \(M=0\) term in (2) is zero.

Earlier work proved only

\[
 |C_{k,p}|\asymp_p k^{-3/4}.                            \tag{4}
\]

The new theorem retains the discrete prime-lattice phase hidden by (4).

## 2. Exact bilateral profile

For \(c>0\), define

\[
 F_p(c)
 =
 \sum_{z\in\mathbb Z}
 \sqrt{2c}\,p^{-z}\exp\!\left(-4c\,p^{-2z}\right).       \tag{5}
\]

The series in (5) is absolutely convergent and strictly positive. For every positive integer
\(c\),

\[
 \boxed{
 \lim_{j\to\infty}
 \sqrt{c\,p^{2j}}\,
 R_{c p^{2j},p}
 =
 F_p(c).
 }                                                       \tag{6}
\]

Equivalently, in terms of the literal Jacobi coefficient,

\[
 \boxed{
 \lim_{j\to\infty}
 \frac{\sqrt{c\,p^{2j}}}
      {P_p\,c_{2c p^{2j}}}
 |C_{c p^{2j},p}|
 =
 F_p(c)>0.
 }                                                       \tag{7}
\]

The profile has exact discrete-scale invariance

\[
 F_p(cp^2)=F_p(c).                                      \tag{8}
\]

Equation (8) is proved in Lean at positive integral \(c\), which is exactly the parameter range
needed by the integer-degree subsequences in (6)--(7). Reindexing (5) proves the same identity
for every real \(c>0\) on paper.

The Wallis identity

\[
 c_n^4 W_n(2n+1)=1,\qquad W_n\longrightarrow\frac{\pi}{2},
\]

also gives

\[
 c_{2k}\sim(2\pi k)^{-1/4}.
\]

Thus (7) sharpens (4) to the ordinary normalization

\[
 (c p^{2j})^{3/4}|C_{c p^{2j},p}|
 \longrightarrow
 P_p(2\pi)^{-1/4}F_p(c).                                \tag{9}
\]

The formal certificate uses the exact intrinsic normalization in (7), so no informal
asymptotic replacement is present in the Lean theorem.

## 3. Proof

The exact prime formulas already proved in the semilocal corpus are

\[
 \left(r_p^M\phi(M\log p)\right)^2
 =\frac{2}{p^{2M}+1},                                   \tag{10}
\]
\[
 \tanh(M\log p)
 =\frac{p^{2M}-1}{p^{2M}+1}.                            \tag{11}
\]

### 3.1 Nonnegative frequency offsets

Set

\[
 k_j=cp^{2j},\qquad M=j+s,\qquad s\geq0.
\]

From (10),

\[
 \sqrt{k_j}\,r_p^{j+s}\phi((j+s)\log p)
 \longrightarrow
 \sqrt{2c\,p^{-2s}}.                                    \tag{12}
\]

By (11),

\[
 \tanh((j+s)\log p)
 =
 1-\frac{2}{p^{2(j+s)}+1}.
\]

The standard exponential limit, with exponent \(2k_j\), gives

\[
 \tanh((j+s)\log p)^{2k_j}
 \longrightarrow
 \exp(-4c\,p^{-2s}).                                    \tag{13}
\]

Multiplying (12) and (13),

\[
 \sqrt{k_j}B_{k_j,p}(j+s)
 \longrightarrow
 \sqrt{2c}\,p^{-s}e^{-4cp^{-2s}}.                       \tag{14}
\]

### 3.2 Negative frequency offsets

For a fixed \(D\geq1\), take \(M=j-D\). After writing \(j=n+D\), the same calculation is (14)
with the positive integer scale constant replaced by \(cp^{2D}\) and offset zero. Hence

\[
 \sqrt{k_j}B_{k_j,p}(j-D)
 \longrightarrow
 \sqrt{2c}\,p^D e^{-4cp^{2D}}.                          \tag{15}
\]

This is the \(z=-D\) term of (5).

### 3.3 Uniform domination

The already-formalized tail estimate

\[
 B_{k,p}(M)\leq2p^{-M}
\]

gives, for \(M=j+s\),

\[
 \sqrt{k_j}B_{k_j,p}(j+s)
 \leq2\sqrt c\,p^{-s}.                                  \tag{16}
\]

The right side is a summable geometric sequence in \(s\).

For \(M=j-D\), use the complementary low-frequency bound

\[
 B_{k,p}(M)\leq\frac{p^M}{k}.
\]

Since \(c\geq1\),

\[
 \sqrt{k_j}B_{k_j,p}(j-D)
 \leq\frac{1}{\sqrt c}\,p^{-D}
 \leq p^{-D}.                                           \tag{17}
\]

This is another summable geometric majorant. Tannery's theorem applies independently to
(14) and (15).

### 3.4 Exact reindexing

For each \(j\), split (2) at \(M=j\). The lower block is finite and the reflection
\(D\mapsto j-D\) identifies it with the negative-offset sum. The upper block is
\(M=j+s\). Therefore

\[
 \sqrt{k_j}R_{k_j,p}
 =
 \sum_{D\geq1}\sqrt{k_j}B_{k_j,p}(j-D)\mathbf1_{D\leq j}
 +
 \sum_{s\geq0}\sqrt{k_j}B_{k_j,p}(j+s).                 \tag{18}
\]

Equations (14)--(18) prove (6). Equation (3) gives (7). Every summand of (5) is positive,
so \(F_p(c)>0\).

Finally,

\[
 k_j(cp^2)=cp^2p^{2j}=cp^{2(j+1)}=k_{j+1}(c).
\]

The shifted sequence has the same limit as the original sequence. Uniqueness of limits gives
(8) directly, independently of a formal bilateral-integer reindexing.

## 4. What this changes

This is not a new global prime-clock direction. The updated
`source-horizon-riemann-divisor/main.tex` proves that every one-prime source lies in
\(\mathcal A_{\rm fin}\), is zero in the global clock quotient \(\mathcal Q\), and has analytic
carrier in \(\mathcal K_{\rm loc}\).

The theorem instead resolves a hard local input to `J-SF5`:

1. the literal finite-place Euler grading coefficient has a positive, exact discrete-scale
   profile rather than only an unspecified \(k^{-3/4}\) envelope;
2. the profile depends on the prime label before scalarization;
3. a global semilocal boundary construction cannot obtain credit from one fixed prime or any
   fixed finite set of primes; it must retain these profiles through a cofinal infinite-label
   source limit, or use topology singular relative to the canonical source norms;
4. smooth Birkhoff--Adams coefficient assumptions cannot be inserted without first proving how
   the prime-lattice profile behaves in the actual cofinal Jacobi radii.

This moves, but does not close, `J-SF5`. Remaining hard theorem: propagate the prime-resolved
profile through the finite-set orthogonalization, determine the critical residual
`routeJProlateSourceCriticalResidual` for a cofinal source family, and derive or exclude a
source-selected self-adjoint boundary through the Sonin corner.

## 5. Hostile audit

- **Not an RH theorem.** No divisor exclusion or global conservative descent is constructed.
- **Not a global-source claim.** One-prime data are explicitly local Euler data and quotient-zero.
- **Not generic harmonic-sum novelty.** Mellin analysis of geometrically rescaled harmonic sums
  and periodic fluctuations is classical.
- **Not a recurrence-coefficient classification.** \(C_{k,p}\) is the literal Euler grading
  coefficient in the archimedean Jacobi basis, not yet the recurrence radius of the fully
  orthogonalized cofinal semilocal measure.
- **No unproved oscillation claim.** Periodicity and positivity are proved. Nonconstancy of
  \(F_p\), although suggested by its Mellin Fourier coefficients, is kept as an open strengthening
  until separately formalized.
- **No asymptotic assumption.** Lean derives every atom, majorant, series split, limit, positivity
  statement, and discrete-scale invariance from exact source formulas.

## 6. Novelty audit

Mandatory internal search:

```text
scripts/formal_tools.py research
  "one-prime semilocal grading geometric profile log-periodic Jacobi coefficient"
```

The internal corpus contained the exact coefficient series and two-sided \(k^{-3/4}\) bounds, but
no subsequential limit, bilateral profile, or discrete-scale law.

External comparison:

- Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*
  (arXiv:2310.18423), constructs the semilocal prolate framework but does not derive (5)--(9).
- Flajolet--Gourdon--Dumas, *Mellin Transforms and Asymptotics: Harmonic Sums*,
  Theoretical Computer Science 144 (1995), 3--58, gives the classical general mechanism by which
  geometric harmonic sums produce periodic fluctuations.
- General discrete-scale-invariance literature likewise makes logarithmic periodicity classical.

Targeted theorem-level searches found no source-specific statement for the exact
Connes--Consani--Moscovici one-prime Euler/Gamma Jacobi coefficient, its bilateral profile (5), or
the intrinsic coefficient limit (7). Candidate novelty is restricted to that exact
source-specific theorem and its `J-SF5` consequence.

## 7. Lean boundary

The formal module proves:

- exact positive- and negative-offset atom limits;
- summable geometric majorants on both sides;
- Tannery interchange of limit and infinite sum;
- exact finite-head/infinite-tail reindexing of the literal raw source series;
- strict positivity and summability of both profile halves;
- exact intrinsic normalization of the literal Jacobi coefficient;
- the subsequential limit (7);
- discrete-scale invariance under \(c\mapsto cp^2\).

No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or computation is used.
