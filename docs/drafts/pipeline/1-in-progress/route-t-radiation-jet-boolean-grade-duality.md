# Route T radiation-jet / Boolean-grade duality

- **ID:** `route-t-radiation-jet-boolean-grade-duality`
- **Stage:** 1 — in progress
- **Date opened:** 2026-08-10
- **Parent:** `rh-current-frontier-map.md`, Route T
- **Labels:** `[LOCAL-RESEARCH] [PAPER-PROVED CORE] [NOVELTY UNVERIFIED] [RH OPEN]`

## Frozen question

Can cofinal Euler/Hodge interaction depth remove the infinite deep-time radiation jet which
defeats every fixed Route T aperture renormalization, while preserving the valuation-one
true-prime current?

This card records the exact algebraic answer, its sharp threshold, and the support obstruction
which prevents counting the algebra alone as RH progress.

## 1. Two Boolean radiation currents

For edge lengths `w_1,...,w_r`, put `h_S=sum_(i in S)w_i`.  For a polynomial `Q` and basepoint
`b`, define

```text
D_(r,b,w)[Q]
  =sum_(S subset [r])(-1)^|S| Q((b-h_S)^2),

J_(r,b,w)[Q]
  =sum_(S subset [r])(-1)^|S| (b-h_S)Q((b-h_S)^2).       (RJG1)
```

`D` is the detector current.  `J` is the covariant logarithmic-source current obtained when the
face logarithmic observable is multiplied by the detector before taking supertrace.

Let `deg Q=j` with leading coefficient `c_j ne 0`.

### Theorem A — sharp detector bandwidth `[PROVED HERE]`

```text
D_(r,b,w)[Q]=0                         if r>2j,           (RJG2)
D_(2j,b,w)[Q]=(2j)! c_j product_i w_i if r=2j.           (RJG3)
```

The threshold value is independent of `b` and is nonzero when every edge length is nonzero.

### Theorem B — sharp source-covariant bandwidth `[PROVED HERE]`

```text
J_(r,b,w)[Q]=0                              if r>2j+1,    (RJG4)
J_(2j+1,b,w)[Q]
  =(2j+1)! c_j product_i w_i                if r=2j+1.    (RJG5)
```

Consequently a covariant Boolean current of grade `r` annihilates exactly every polynomial
radiation jet with

```text
j <= floor((r-2)/2).                                      (RJG6)
```

The minimal grade which kills jets `j=0,...,m-1` is `r=2m`.

### Proof

Set `P_D(X)=Q((b-X)^2)` and `P_J(X)=(b-X)Q((b-X)^2)`.  Their degrees are respectively `2j` and
`2j+1`; their top coefficients are `c_j` and `-c_j` after the displayed choice of variable.
The subset sum is an unequal-step iterated finite difference.  Prouhet annihilation kills every
polynomial of degree strictly below the number of steps.  At equality, the iterated difference
of `X^r` is `(-1)^r r! product_i w_i`; multiplication by the two displayed leading coefficients
gives (RJG3) and (RJG5), with the signs cancelling.  This also proves sharpness.

No analytic estimate, zero hypothesis, or computation enters.

## 2. Exact mass-Bessel specialization

The proven Route T deep-time expansion has coefficient polynomials

```text
Q_(j,a)(s),
deg Q_(j,a)=j,
[s^j]Q_(j,a)=(-a/2)^j/j!.                                (RJG7)
```

Therefore

```text
D_(2j,b,w)[Q_(j,a)]
 = (2j)! (-a/2)^j/j! product_i w_i,                      (RJG8)

J_(2j+1,b,w)[Q_(j,a)]
 = (2j+1)! (-a/2)^j/j! product_i w_i.                    (RJG9)
```

Thus radiation order and Euler interaction depth are dual with exact slope two.  Every fixed
interaction grade sees only finitely many radiation coefficients, explaining in one law why
both fixed radiation subtraction and fixed-grade Euler completion fail.

## 3. Hodge meaning and true-prime boundary

On the Boolean divisor fibre of `n`, the face logarithm is `L_S=b-h_S`.  The existing Hodge
transgression uses the detector as an external scalar and gives

```text
external detector * Str(L)=external detector * Lambda(n). (RJG10)
```

Moving a radiation jet inside the observable instead gives `Str(L Q(L^2))=J[Q]`.  For a
valuation-one true prime, `r=1` and `b=w_1`, so

```text
J_(1,w_1,w_1)[Q]=w_1 Q(w_1^2),                           (RJG11)
```

exactly the prime radiation-jet atom.  At higher support, (RJG4) supplies the new cancellations.
This is the precise seam between Route T and future-dressed Euler transgression.

## 4. Conjecture loop 1 — free cofinal renormalization

### Conjecture

Replace the external detector in (RJG10) by the covariant detector and raise Boolean grade
cofinally.  Equations (RJG4)--(RJG6) should remove the whole radiation jet while leaving the
valuation-one scalar unchanged.

### Verdict: `[FAILED — NOT SCALAR-PRESERVING]`

Adding one future edge changes the current by a translated finite difference:

```text
J_(U union {v})[Q;b]=J_U[Q;b]-J_U[Q;b-v].                (RJG12)
```

It does not preserve `J_U`.  Existing finite Hodge selection factors a detector which is constant
on each divisor fibre; the cancellation in (RJG4) appears only after making the detector
face-dependent.  That replacement creates the full composite, zero-integral causal field rather
than an identity for the old scalar prime response.  Reassembling it source-canonically is the
existing future-dressed causal ridge-joining problem, not a consequence of Prouhet cancellation.

### Positive survivor

The composite field discarded by scalar Hodge pushforward is exactly the carrier which can absorb
successive radiation jets.  It is not algebraic noise.  The open FCRJ field has an analytic role:
interaction grade is its radiation-renormalization order.

### Theorem C — source-preserving linear filtration is impossible `[PROVED HERE]`

Let `Delta_w^r` be any nontrivial grade-`r` Boolean translation difference, and let `E_b` be
evaluation at a basepoint.  On any vector space of tests containing the polynomials of degree
less than `r`, there is no linear operator `A` such that

```text
E_b=A composed with Delta_w^r.                            (RJG13)
```

Indeed `Delta_w^r` annihilates that whole polynomial subspace while `E_b(1)=1`.  The same argument
applies to the logarithmic-source functional `Q |-> b Q(b^2)`: for every grade which kills a
radiation jet, any exact scalar reconstruction must add a complementary term which reproduces
that jet in full.

This rules out a broad class, not one formula.  No linear, translation-generated cofinal filter
can both erase low radiation jets and preserve the Route T scalar on a test space containing
those jets.  A successful construction must retain a coupled boundary relation and prove a sign
or cancellation before scalar reconstruction.  Inverting the difference after norming necessarily
restores the killed radiation modes through the zero of its translation multiplier.

## 5. Conjecture loop 2 — asymptotic grade capacity

The fixed-order dyadic radiation obstruction has size

```text
sqrt(X)/(log X)^(2m+2).                                  (RJG14)
```

Writing `L=log X`, boundedness at the fixed-order scale suggests `m` of order
`L/(4 log L)`, hence covariant grade `r=2m` of order `L/(2 log L)`.  The largest possible distinct
prime support below `X` has order `L/log L`.  Algebraic capacity therefore has a factor-two margin.

### Verdict: `[CAPACITY PLAUSIBLE; UNIFORM CLAIM UNPROVED; SUPPORT FAILS]`

Three hostile corrections are mandatory.

1. Existing Bessel remainder is uniform only for fixed `m`; a growing-order sectorial/Gevrey
   remainder has not been proved.
2. Threshold constants contain `(2j)!/j!` and `product log p`; fixed-order asymptotics may not be
   extrapolated to `j=j(L)`.
3. Most importantly, the hard near-aperture true primes have support grade one.  High grade below
   the same arithmetic aperture belongs to smooth composite integers, not to those prime atoms.
   Dressing a near-boundary prime by enough distinct primes crosses the aperture and produces the
   unresolved endpoint field.  Abstract maximal grade is therefore not available where the Route
   T source needs it.

The factor-two count is a design capacity, not an estimate and not an RH advance by itself.

## 6. Higher universal principle

The infinite radiation wall and fixed-interaction wall are the same filtered-colimit defect.
Scalarization takes the Boolean trace before analytic completion, retaining the valuation-one
current but deleting all higher-grade countertransport.  Radiation renormalization needs the
opposite order: complete the face-dependent interaction tower before scalar trace.  The two orders
do not commute, and their commutator is the future-dressed composite endpoint field.

```text
Boolean scalar trace -> true-prime source + infinite radiation jet,
cofinal covariant trace -> low-jet cancellation + composite endpoint defect. (RJG15)
```

Every failed fixed jet, fixed grade, regular quotient, and external-detector Hodge argument is a
shadow of this noncommutation.  Any successful successor must control the commutator itself; it
cannot separately bound its prime and composite scalar images.

## 7. Exact next theorem

Construct the Route T Bessel specialization of the future-dressed causal field before log-threshold
pushforward and prove a signed coarea identity of the form

```text
old true-prime response
 = cofinal covariant Boolean response + boundary transgression,           (RJG16)
```

where:

- the covariant response admits the sharp all-jet cancellation (RJG4);
- the boundary transgression is supported only in the asymptotically caustic endpoint layer;
- neither term is normed before their shared orientation is retained;
- the identity is source-defined and does not use the terminal RH-equivalent scalar.

If (RJG16) cannot be constructed, the Boolean-radiation bridge is explanatory only and Route T
must pivot to the Gamma-averaged rational source cone, which removes the PNT/radiation topology
without claiming scalar preservation.

## 8. Formalization ledger

- Existing exact input:
  `GaloisForLFunctions.prouhet_alternating_annihilation`.
- Paper-closed targets:
  sharp unequal-step threshold formulas (RJG3), (RJG5), and Bessel coefficient substitutions
  (RJG8), (RJG9).
- Deferred analytic target:
  growing-order Bessel/Gevrey remainder; no Lean statement before paper closure.
- RH status: open.  No statement in this card assumes a line bound, zero location, positivity
  cone, or extra axiom.

## 9. Novelty protocol

Internal exact-identifier search found Prouhet annihilation, all-order completed-source Boolean
bandwidth, and the independent mass-Bessel infinite-jet obstruction, but no theorem coupling the
Bessel coefficient degree `j`, source-covariant degree `2j+1`, and sharp Euler grade `2j+2`.

External priority search is deferred until the exact source-preserving or no-go theorem (RJG16) is
frozen.  Current label remains `[NOVELTY UNVERIFIED]`.

## Log

- 2026-08-10 — exact detector and source-covariant jet/grade thresholds proved.
- 2026-08-10 — free scalar-preserving cofinal renormalization falsified by (RJG12), then excluded
  for every linear translation-generated factorization by Theorem C.
- 2026-08-10 — factor-two asymptotic capacity isolated, then corrected for growing-order constants
  and near-aperture grade-one support.
- 2026-08-10 — higher noncommuting completion/trace principle and exact next identity (RJG16)
  frozen.

---

## 10. Conjecture loop 3 — uniform scalar chirp separation

The finite-packet receiver in the mass-Xi corpus suggests taking a faithful moving aperture
`a(u)=u^theta`, `1/3<theta<1/2`, and passing its chirp mean-square argument through the full Xi
sum.  This would remove scalar cross-orbit cancellation without changing the Route T observable.

### Verdict: `[FAILED AS AN ABSOLUTE/FINITE-JET PASSAGE]`

Let `H=H(u)` be a growing height cutoff.  Uniform use of

```text
sqrt(a^2+alpha^2)=a+alpha^2/(2a)+O(|alpha|^4/a^3)
```

on `|alpha|<=H` requires

```text
u H^4/a^3 -> 0.                                            (RJG17)
```

For `a=u^theta` this confines the uniform chirp packet to
`H=o(u^((3theta-1)/4))`, far below even the aperture.  By contrast, the unconditional strip bound
`|Im beta|<1/2` gives the squared tail envelope

```text
sum_(Re alpha>=H) ||exp(-(sigma+iu)beta)||^2
  <= exp(u) sum_(Re alpha>=H) exp(-2sigma Re alpha).        (RJG18)
```

Absolute suppression therefore needs `H` of linear order `u`.  No overlap exists with (RJG17).
Adding any fixed number of square-root expansion terms does not repair this: the uniform remainder
condition remains `H=o(a)`, whereas the absolute spectral horizon remains linear in `u`.

There is a sharper scale contradiction.  Suppressing every possible strip-edge tail already at
height `H=a` requires `sigma*a>u/2`, while retaining one fixed off-line mass charge requires
`sigma*a^2<u*R|J|`.  As `a->infinity` the former implies `sigma*a^2>u*a/2`, contradicting the
latter.  Hence every absolute tail argument strong enough to close the full scalar sum erases the
fixed off-line signal it was meant to detect.

This disproves the proposed proof mechanism, not the scalar criterion.  A genuinely conditional
mean-square theorem could still exploit Xi-specific phases, but it cannot follow from zero count,
the strip, a finite Taylor jet, or termwise domination.

## 11. Conjecture loop 4 — reflection-diagonal vertical Hilbert energy

The failure above says the packet cutoff is artificial.  Keep every divisor copy and move the norm
inside the trace.  For `a>=1/2`, `sigma>0`, and `u>=0`, define

```text
V_(a,sigma)(u) = sum_q ||exp(-(sigma+iu) beta_(a,q))||^2,
beta_(a,q)=sqrt(a^2+alpha_q^2).                            (RJG19)
```

This is the Hilbert--Schmidt mass of the mass half-wave, equivalently the line-reflection-diagonal
twisted trace

```text
Tr(exp(-tau B_a) C exp(-conj(tau) B_a) C),                (RJG20)
```

where `C` exchanges a divisor copy with its critical-line conjugate.  Formula (RJG20) is an
operator interpretation only; (RJG19) is the definition and needs no unconstructed operator.

### Theorem D — complete cubic-clock dichotomy `[PAPER-PROVED]`

Fix `sigma>0` and put `u=a^3`.  Then

```text
RH      => V_(a,sigma)(a^3) -> 0,
not RH  => V_(a,sigma)(a^3) -> +infinity.                 (RJG21)
```

In particular

```text
RH iff V_(a,sigma)(a^3) -> 0.                             (RJG22)
```

#### Proof

Write `beta=M+iK`, `alpha=R+iJ`.  Under RH, `K=0`.  Mass geometry gives both `M>=a` and `M>=R`,
so `2M>=a+R`.  Therefore

```text
||exp(-(sigma+ia^3)beta)||^2
 = exp(-2sigma M)
 <= exp(-sigma a) exp(-sigma R).
```

Summing over the complete multiplicity-exact Xi divisor is legitimate because
`sum_q exp(-sigma R_q)<infinity`; hence

```text
0 <= V_(a,sigma)(a^3)
   <= exp(-sigma a) sum_q exp(-sigma R_q) -> 0.            (RJG23)
```

If RH fails, choose one copy with `J ne 0` and replace it by its line conjugate if necessary so
the mass displacement `K` is positive.  Charge conservation and the height cap give

```text
K M=R|J|=:c>0,                 M<=a+R.
```

That single nonnegative summand satisfies

```text
log ||exp(-(sigma+ia^3)beta)||^2
 = -2sigma M+2a^3 K
 >= -2sigma(a+R)+2c a^3/(a+R) -> +infinity.               (RJG24)
```

Thus the entire positive sum tends to `+infinity`.  No interchange of a limit with the sum is used
in the off-line direction.  This proves (RJG21)--(RJG22). `QED`

### Hostile audit

- **No scalar cancellation:** every term of (RJG19) is nonnegative.
- **No growing packet:** RH uses one summable majorant; failure uses one fixed divisor copy.
- **No zero gap or zero count asymptotic:** only admissible-family summability and line conjugation.
- **No hidden RH premise:** reality is used only in the forward implication; the reverse starts
  from one explicit nonreal copy forced by `not RH`.
- **Not yet a Route T proof:** (RJG19) is quadratic and reflection-diagonal.  The scalar explicit
  formula computes `Tr(exp(-tau B_a))`, not (RJG20).  Declaring the latter prime-accessible would be
  theatre.

## 12. Higher principle sharpened

Route T's obstruction is not lack of a faithful receiver.  The complete positive receiver (RJG19)
exists and is stronger than every finite chirp projector.  Missing datum is the **diagonal
coproduct** that remembers one divisor label across a source/co-source pair.  Scalar explicit
formula applies the counit first and produces all cross-label interference; Hilbert energy applies
the diagonal first and forbids that interference.

```text
linear explicit trace:       source --counit--> scalar,
faithful quadratic receiver: source --diagonal--> source tensor source --reflection--> energy.
                                                                  (RJG25)
```

This is the same noncommutation as (RJG15), now with an exact complete-divisor witness.  Boolean
grade is not valuable because high grade is large; it is valuable only if it constructs this
source-defined diagonal before scalarization.

## 13. Exact successor theorem

Construct a literal prime--Gamma/source operator `A_(a,tau)` and reflection `C_src` for which the
known scalar mass formula is its trace and prove the coefficient-exact diagonal identity

```text
Tr(A_(a,tau)^* A_(a,tau))
 = V_(a,sigma)(u) + B_(a,sigma)(u),                       (RJG26)
```

with `B>=0` or `B` uniformly bounded on the cubic clock.  An equivalent source-side Parseval or
coarea identity is acceptable, but it must retain equal divisor labels and derive from the literal
centered von Mangoldt/Gamma source.  Combining (RJG26) with any unconditional decay of the left
side would prove RH by Theorem D.  Without the equal-label identity, a positive source norm is only
an unrelated majorant.

## 14. Updated formalization ledger

- `[PAPER-PROVED]`: scalar head/tail incompatibility (RJG17)--(RJG18).
- `[PAPER-PROVED]`: complete cubic-clock Hilbert dichotomy (RJG21)--(RJG24).
- Lean target: specialize `sigma=1`, `a_n=n+1`, `u_n=(n+1)^3`; prove the closed theorem
  `RiemannHypothesis iff Tendsto V_n atTop (nhds 0)` plus off-line divergence.
- Source landing (RJG26): open; no Lean statement before coefficient-exact paper construction.

## Log, continued

- 2026-08-10 — full-sum finite-chirp passage falsified by incompatible Taylor and absolute-tail
  horizons.
- 2026-08-10 — complete positive cubic-clock divisor receiver (RJG19) and exact RH dichotomy
  (RJG21) proved on paper; source-diagonal coproduct isolated as sole new bridge.
