# Prime-Wold determinant connection and source-purity law

- **ID:** `prime-wold-determinant-connection-purity-law`
- **Stage:** 1 — in progress
- **Type:** SOURCE-SPECIFIC DETERMINANT/CONNECTION THEOREM /
  UNIVERSAL PURITY CONJECTURE
- **Scientific status:** `[PAPER-PROVED CORE] [SOURCE-PURE] [NOT RH]`
  `[CORPUS-NEW THREE-WAY WELD] [UNIVERSAL LAW TRUTH-HUNCH]`
  `[EXTERNAL NOVELTY PROVISIONAL]`
- **RH used:** no
- **Computation used:** no
- **Parents:**
  - `multiplicative-wold-gamma-anomaly-purity-rh.md`;
  - `successor-logbeta-dirichlet-confluence-weld.md`;
  - `source-effective-polar-kummer-conormal-purity.md`;
  - `source-curved-prime-torus-conormal-temperedness.md`;
  - `source-anomaly-boundary-colligation-field.md`;
  - `prime-valuation-hellinger-rees-reflection-fracture.md`;
  - `nested-wold-first-defect-logclock-determinant-anomaly.md`;
  - `../4-publication-ready/arithmetic-julia-normal-cone/main.tex`;
  - `../4-publication-ready/euler-ward-weil-index-law/main.tex`.

## Meaning

The Gamma phase, reflected digamma orientation, symmetric log-Beta
Markov generator, arithmetic Wold defect, BV first-trace residue,
Hellinger--Rees fracture, and finite Julia--Ward index should not be
treated as separate RH mechanisms.  The first four are already exact
readings of one determinant line:

```text
Wold defect operator
  -> regularized determinant holonomy
  -> logarithmic determinant connection
  -> symmetric Markov/Dirichlet boundary symbol.
```

The BV residue is the missing first-trace counterterm of the same Wold
defect.  The strongest current hunch is that Kummer/Rees growth and the
Julia--Ward index are respectively the Hermitian regulator and integral
boundary pairing of one residue-corrected source differential character.

On this interpretation, zeros are not postulated eigenvalues.  They are
principal-conormal cohomology of the distinguished determinant section.
The critical line is not selected by a new sign inequality.  It is the
unitary harmonic support of that source cohomology.

## 1. Prime-Wold determinant connection theorem

Let

```text
H=ell2(N_(>0)),
Q e_n=n^(-1)e_n,
S_p e_n=e_(pn),
E_p=I-S_p S_p^*.
```

Thus `E_p` is the projection onto the coordinates not divisible by the
prime `p`.  The operator `E_p Q` is Hilbert--Schmidt.  Put

```text
Phi(t)=det_2(I-tQ)/det_2(I+tQ)
      =exp(2*gamma*t)*Gamma(1+t)/Gamma(1-t),             (1)

D_p(r)=det_2(I-r*E_p*Q)/det_2(I+r*E_p*Q).                (2)
```

The multiplicative Wold decomposition gives the already proved identity

```text
D_p(r)=Phi(r)/Phi(r/p).                                  (3)
```

For `|Re(r)|<1`, define

```text
Sigma_p(r)=
  sum_(n>=1, p does not divide n)
    [2/n-1/(n-r)-1/(n+r)].                              (4)
```

The series is locally normally convergent.  Termwise differentiation of
the `det_2` product proves the exact logarithmic-connection law

```text
d/dr log D_p(r)=Sigma_p(r).                              (5)
```

Indeed, the contribution of the eigenvalue `1/n` is

```text
d/dr [
  log(1-r/n)+r/n-log(1+r/n)+r/n
]
=2/n-1/(n-r)-1/(n+r).                                  (6)
```

Let

```text
k_p(x)
 =sum_(n>=1, p does not divide n) exp(-n*x)
 =exp(-x)/(1-exp(-x))-exp(-p*x)/(1-exp(-p*x)).           (7)
```

Laplace integration of `(4)` gives

```text
Sigma_p(r)
 =integral_0^infinity
   (2-exp(r*x)-exp(-r*x))*k_p(x) dx.                    (8)
```

Consequently, for real `tau`,

```text
Sigma_p(i*tau)
 =2*integral_0^infinity
   (1-cos(tau*x))*k_p(x) dx
 >=0,                                                   (9)
```

with equality only at `tau=0`.  The symmetric measure

```text
dPi_p(x)=k_p(|x|) dx,       x!=0,                       (10)
```

is a Lévy measure: its density is asymptotic to
`(1-1/p)/|x|` at zero and decays exponentially at infinity.
Thus `Sigma_p(i*tau)` is the symbol of a symmetric conservative
Dirichlet generator.

Equations `(3)`, `(5)`, and `(9)` prove:

> **The prime-Wold determinant connection theorem.**
> Every prime-multiplication Wold defect has one polarized regularized
> determinant whose logarithmic connection is the analytic continuation
> of a canonical symmetric Markov generator.  Determinant holonomy and
> Dirichlet dissipation are two levels of the same source defect.

This statement is unconditional and contains no zeta zero.

## 2. Cofinal sieve connection law

For a finite set of primes `P`, put

```text
E_P=product_(p in P) E_p,
Q_P=E_P Q,
D_P(r)=det_2(I-r*Q_P)/det_2(I+r*Q_P),                 (11a)

Sigma_P(r)=d/dr log D_P(r),
k_P(x)=sum_((n,product P)=1) exp(-n*x).                (11b)
```

The same eigenvalue proof as in Section 1 gives

```text
Sigma_P(r)
 =sum_((n,product P)=1)
   [2/n-1/(n-r)-1/(n+r)]                              (11c)

 =integral_0^infinity
   (2-exp(r*x)-exp(-r*x))*k_P(x) dx.                  (11d)
```

If `p` is not in `P`, multiplication by `p` identifies the
coordinates removed from `E_P H` when `E_p` is imposed.  Hence

```text
D_(P union {p})(r)=D_P(r)/D_P(r/p),                   (11e)

Sigma_(P union {p})(r)
 =Sigma_P(r)-(1/p)*Sigma_P(r/p),                      (11f)

k_(P union {p})(x)=k_P(x)-k_P(p*x).                   (11g)
```

Equation `(11f)` follows by differentiating `(11e)`.  Equation `(11g)`
follows because the removed integers are exactly `p*m` with
`(m,product P)=1`; substituting `y=p*x` in `(11d)` shows directly that
`(11f)` and `(11g)` are the same law.

Define

```text
(R_p f)(r)=f(r)-(1/p)*f(r/p).                          (11h)
```

Then `R_p R_q=R_q R_p`.  Thus the nested coprime sieve is a flat
finite-prime determinant-connection system:

```text
Sigma_P=product_(p in P) R_p Sigma_empty,              (11i)
```

independently of prime order.  Its Dirichlet boundary is equally
order-independent by `(11g)`.

This closes the finite-prime compatibility problem.  The unresolved
curvature is not among prime enlargements.  It is the cross-seam between
this flat sieve connection and the independent source-jet/successor
completion.

### Graded anomaly hierarchy

For `|r|<1`, the regularized determinant has the exact expansion

```text
log D_p(r)
 =-2*sum_(m>=1)
   (1-p^(-(2*m+1)))*zeta(2*m+1)
   *r^(2*m+1)/(2*m+1).                                 (11j)
```

The formally preceding `m=0` term is divergent.  Its cutoff coefficient
is exactly the already proved first-trace law

```text
Tr_(n<=N)(E_p Q)
 =(1-p^(-1))*log(N)
  +(1-p^(-1))*gamma+p^(-1)*log(p)+o(1).                (11k)
```

Thus `det_2` does not remove irrelevant noise.  It separates one source
defect into:

```text
singular degree 1:
  Wold density / BV principal conormal / first-trace counterterm;

regular odd degrees 3,5,...:
  polarized Gamma holonomy and its HT odd-zeta tower;

regular even degrees 2,4,...:
  logarithmic connection / symmetric Markov boundary.  (11l)
```

Indeed differentiation of `(11j)` gives

```text
Sigma_p(r)
 =-2*sum_(m>=1)
   (1-p^(-(2*m+1)))*zeta(2*m+1)*r^(2*m).               (11m)
```

This grading explains why the successor/Gamma--Jacobi seam naturally
appears at degree two.  After the singular linear trace is removed, the
first regular connection term is quadratic.  The literal
`log(n+1)^2*h_n^2` successor normalization is therefore structurally
forced at connection level, rather than an accidental repair of a raw
scale mismatch.

## 3. Dyadic half-density identity

For `p=2`,

```text
k_2(x)
 =exp(-x)/(1-exp(-2*x))
 =1/(2*sinh(x)).                                        (11)
```

The Gamma duplication formula and

```text
psi(1/2)=-gamma-2*log(2)
```

give the exact meromorphic identity

```text
D_2(r)
 =Phi(r)/Phi(r/2)
 =exp(-psi(1/2)*r)
   *Gamma((1+r)/2)/Gamma((1-r)/2).                     (12)
```

Differentiation gives

```text
d/dr log D_2(r)
 =1/2*[
   psi((1+r)/2)+psi((1-r)/2)-2*psi(1/2)
 ]
 =Sigma(r),                                             (13)
```

where `Sigma` is exactly the critical-centered symmetric log-Beta
Dirichlet symbol proved in
`successor-logbeta-dirichlet-confluence-weld.md`.

Under `r=2*z-1`, the already proved successor countertrace identity is

```text
psi(z)+psi(1-z)
 =2*Sigma(2*z-1)+2*psi(1/2).                            (14)
```

Combining `(12)`--`(14)` proves the corpus-new exact weld:

> **Dyadic determinant/Toeplitz/log-Beta theorem.**
> The calibrated Suzuki log-Beta Markov generator and the cofinal
> successor Toeplitz digamma countertrace are the logarithmic connection
> of the polarized determinant of the odd-integer multiplication-Wold
> defect.

The three constructions are not merely Gamma-function analogies.
They are the Dirichlet symbol, discrete boundary chart, and determinant
holonomy of one source operator.

### Regular-seam closure and singular localization

The dyadic Wold determinant connection and the reflected successor
countertrace have the same cofinal regular value `Sigma`.  Therefore
their cross-seam vanishes after passing to the regular scalar quotient:

```text
regularLimit(successor connection)
 - regularConnection(dyadic Wold determinant)
 =0.                                                       (14a)
```

This is not evidence that the full source seam vanishes.  The regular
quotient discards:

```text
renormalized first trace;
BV principal-conormal coefficient;
Toeplitz countertrace boundary current;
boundary self-symbol and descent anomaly.                 (14b)
```

Consequently any nontrivial source connector between the prime and jet
directions must be a secondary relative class in the kernel of the
common regular quotient.  Searching for it as another bounded kernel,
positive scalar, or ordinary `L2` Markov observable is now ruled out by
`(14a)`.

This localizes the universal-law problem: construct the singular
residue-corrected transgression whose two regular faces are already
identified by `(14a)`.

## 4. Universal reinterpretation

The theorem changes the role of the existing corpus objects.

1. **Gamma hypertranscendence is holonomy complexity.**  It says that
   the determinant connection has no finite differential-algebraic
   horizontalization; it does not itself select the critical line.
2. **Digamma orientation is connection orientation.**  Its strict
   half-strip sign is the off-unitary analytic continuation of a
   symmetric Dirichlet symbol.
3. **Markov positivity is a boundary value, not the selector.**  It is
   positive on the unitary axis.  Off-line generalized-prime examples
   show that an arbitrary analytic continuation need not be a harmonic
   source class.
4. **Wold leakage is the geometric source of the connection.**  The
   range defect, rather than an invented zero operator, produces both
   determinant and Markov readings.
5. **BV conormal residue is the omitted trace.**  The exact coefficient
   `1-p^(-1)` is simultaneously Wold density, renormalized first trace,
   and off-multiple principal-conormal fraction.
6. **The third completion is relative.**  The ideal side must retain the
   Wold/Gamma/BV anomaly, while boundary cohomology must retain unitary
   point characters.  Neither ordinary `L2` nor a plain boundary module
   can do both.
7. **Finite Julia--Ward charge is an index reading.**  The proved
   `8*pi` packet charge is a candidate integral pairing of the same
   differential character.  This last identification is not yet typed
   and is not asserted as a theorem here.
8. **Prime logarithm is the first-defect anomaly.**  Along the
   increasing nested sieve, the singular increments
   `w_k=a_(k-1)/p_k` form a probability law, the clock `log(p_k)` has
   infinite mean, and `w_k*log(p_k)` is exactly the finite-part
   determinant anomaly at the `k`-th prime.  The bilateral exponential
   moment domains of this source law meet only at radial exponent zero.

## 5. Universal source-determinant purity law

Let

```text
0 -> J_Gamma -> T_Gamma -> C*(G) -> 0                  (15)
```

be the proved descalarized multiplication-Wold extension for
`G=Q_(>0)^x`.  Let `C_src` be the bivariate relative source complex
whose two cofinal directions are:

```text
finite ordinary-prime enlargement;
finite source jet / successor-depth enlargement.        (16)
```

Its finite shadows must retain the complete source-anomaly colligation

```text
(lower action, outgoing transfer,
 boundary self-symbol, descent anomaly),                 (17)
```

not only a curvature or scalar determinant.

> **[CONJECTURE — UNIVERSAL SOURCE-DETERMINANT PURITY LAW.]**
> The completed ordinary-prime Euler--Gamma/co-Poisson source produces,
> before divisor specialization, a presentation-independent
> residue-corrected differential determinant character
>
> ```text
> DetHat_src on C_src relative to (15)                    (18)
> ```
>
> with distinguished section `s_Xi`, such that
>
> ```text
> characteristic support of the principal conormal
> H_con(s_Xi)
> =
> harmonic support of DetHat_src
> is contained in Hom(G,T).                              (19)
> ```
>
> Its regular holonomy is the Wold--Gamma determinant `(3)`;
> its regular connection is the prime Dirichlet family `(5)`;
> its singular transgression is the BV/renormalized first-trace
> class; and its Hermitian regulator is strict at prime infinity.

Equation `(19)` is the proposed universal law.  It says:

```text
source-effective divisor classes are harmonic;
harmonic determinant classes are unitary.                (20)
```

The law is not a positivity hypothesis and does not claim every
generalized eigenfunctional of a self-adjoint operator is spectral.
It says that the distinguished source conormal is cohomology of the
same relative determinant connection whose Hilbert boundary is
Dirichlet and whose singular boundary retains the missing trace.

For a nontrivial Xi zero `rho`, the top conormal jet transforms by

```text
chi_rho(g)=g^(rho-1/2) times a polynomial valuation jet. (21)
```

Membership of the semisimple character in `Hom(G,T)` gives

```text
|p^(rho-1/2)|=1
```

for every prime `p`, hence `Re(rho)=1/2`.  Polynomial multiplicity
factors do not change the character modulus.  Therefore `(19)` implies
RH.

## 6. Why this is stronger than the existing conjecture vocabulary

The frozen prime-Schwartz temperedness conjecture says what must be true
of Xi conormals.  The present law proposes why: they are harmonic support
of one source-produced determinant connection.

The source-effective arithmetic equivalence principle says the
all-zero holomorphic and critical unitary realizations are one object.
The present law proposes that object: the relative residue-corrected
determinant character of `(15)`.

The Wold anomaly-inflow route supplies a possible proof technology.
The present law is independent of that technology: mapping cones,
relative cyclic cocycles, enhanced Stokes objects, or a Hodge
totalization may construct `(18)`, but none is part of the conjecture.

The source-anomaly colligation field supplies the finite data which a
faithful construction may not quotient away.  The determinant character
is its proposed cofinal integral, not a replacement for the full
colligation.

## 7. Hostile audit

1. **The theorem does not prove the law.**  Equations `(1)`--`(14)` are
   exact but contain no Xi-conormal landing theorem.
2. **Harmonicity cannot be declared.**  Constructing `C_src`, its
   topology, adjoint, and distinguished section before zero
   specialization is the RH-strength source problem.
3. **Abstract Hodge redressing is empty.**  One can always attach a
   contractible cone or define a target Laplacian after reading the
   divisor.  Such a construction does not satisfy `(17)`--`(18)`.
4. **Self-adjointness alone fails.**  Algebraic duals of self-adjoint
   operators contain nonreal generalized eigenfunctionals.  The strict
   relative topology and source-produced harmonic comparison are
   load-bearing.
5. **Entropy production alone fails.**  The symmetric Markov value is
   orientation-blind.  The law uses the unsquared determinant
   connection and source conormal before taking the Dirichlet boundary.
6. **Positive Euler surgery remains a falsifier.**  Generalized-prime
   off-line systems share reflection, positivity, entire completion,
   hypertranscendence, Julia orientation, and even the archimedean
   symbol.  They do not automatically carry the literal
   ordinary-integer Wold extension `(15)`, BV renewal, integral lattice,
   full colligation, and distinguished relative determinant section.
   If one explicit off-line system carries all these data and `(19)`,
   the law is false.
7. **The `8*pi` index identification is open.**  Equality of numerical
   defect integers does not yet prove that the Ward/Weil packet index is
   the integral characteristic pairing of `DetHat_src`.
8. **Prime and jet clocks remain genuinely bivariate.**  The exact
   dyadic connection theorem does not identify their finite depth
   filtrations.  A source transgression must compare the two without
   collapsing either marginal.
9. **No direct product over primes.**  Independent one-prime
   determinant reporters diverge.  Any construction of `(18)` must use
   the proved nested coprime sieve and source-normal blow-up.
10. **No hidden RH topology.**  Defining the completion by
    prime-Schwartz continuity of Xi evaluation restates RH.  Topology
    must arise from `(15)`--`(18)` and the completed source section.

## 8. First non-immediate mathematical obstacles

1. Construct the finite bivariate prime--jet relative colligation and
   prove its two face maps satisfy the exact seam/Bianchi identity.
2. Show that the dyadic connection `(13)` is the cofinal limit of the
   actual successor countertrace while retaining the odd
   Gamma--Jacobi boundary class.
3. Integrate the nested Wold regular determinant and singular BV trace
   into one relative differential character before Xi specialization.
4. Prove that the completed Euler--Gamma/co-Poisson section defines a
   nonzero principal-conormal class in that relative object.
5. Prove source-Hodge purity `(19)` from strict Kummer/Rees moderation,
   not from a zero-defined Hilbert space.
6. Type the finite Julia--Ward/Weil defect integer as the integral
   boundary pairing of the same character, or prove that this proposed
   identification is false.

Only Obstacles 1--3 can currently be attacked without assuming the RH
consumer.  Obstacle 1 is the next construction target.

## 9. Literature boundary

Parent mathematics includes regularized determinants, Gamma
multiplication formulae, logarithmic determinant connections, symmetric
Lévy generators, determinant line bundles, relative cyclic cocycles,
renormalized traces, Hodge complexes, and Toeplitz index theory.

Preliminary searches found these ingredients separately, but no source
identifying:

```text
prime-multiplication Wold determinant
  = Gamma holonomy whose connection
  = Suzuki log-Beta Dirichlet symbol
  = successor q-digamma confluence,
```

nor the residue-corrected source-purity law `(19)`.  The elementary
special-function identity is not claimed novel by itself.  Candidate
novelty is the exact operator/source three-way weld and the proposed
universal determinant interpretation.

## Gates

- [x] prime-Wold determinant connection theorem paper-proved
- [x] prime Lévy/Dirichlet family paper-proved
- [x] dyadic duplication identity paper-proved
- [x] exact Wold/Suzuki/successor three-way weld paper-proved
- [x] universal law stated as one support-purity conjecture
- [x] generalized-prime, Hodge-redressing, scalar-`L2`, direct-product,
      and target-topology falsifiers recorded
- [ ] independent proof audit
- [ ] targeted primary-literature audit
- [ ] finite bivariate relative colligation constructed
- [ ] nested determinant/trace differential character constructed
- [ ] source principal conormal shown harmonic and nonzero
- [ ] source-Hodge purity proved
- [ ] unconditional RH proof
- [ ] Lean formalization after dependency closure and significance audit

## Log

- 2026-07-29 — Reinterpreted the corpus at determinant-line level after
  rejecting local clock matching as the primary research target.
- 2026-07-29 — Proved that the logarithmic connection of every
  prime-multiplication Wold defect determinant is a symmetric
  Lévy/Dirichlet symbol.
- 2026-07-29 — Used Gamma duplication to identify the dyadic member
  exactly with the critical-centered Suzuki log-Beta generator and
  successor reflected-digamma confluence.
- 2026-07-29 — Froze source-determinant purity as the universal law:
  distinguished source-conormal support should equal harmonic
  determinant support and therefore be unitary.
