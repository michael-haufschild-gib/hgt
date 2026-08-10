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

---

## 15. Conjecture loop 5 — a diagonal source operator is necessary

### Verdict: `[FAILED — THE ENERGY IS LINEAR IN THE DIVISOR CURRENT]`

The norm square in (RJG19) makes the receiver look quadratic in the divisor trace, but the complete
energy is not the square of a divisor sum.  It is the linear pairing of the multiplicity-exact
counting current with one nonholomorphic test:

```text
W_(a,tau)(z) = |exp(-tau sqrt(a^2+z^2))|^2,
V_(a,sigma)(u) = sum_q W_(a,sigma+iu)(alpha_q).           (RJG27)
```

Here `alpha_q=xiSpectralPoint(q)`.  Replacing `alpha_q` by the folded Poisson point does not change
`W`, because `W(-z)=W(z)`.  Thus no label coproduct is logically required.  What fails is only the
**holomorphic test category** of the ordinary scalar explicit formula: `W` depends on both `z` and
`conj(z)`.

### Theorem E — compact-test Xi Poincare--Lelong landing `[PAPER-PROVED]`

Let `phi : C -> R` be `C^2` with compact support.  Then

```text
sum_q phi(alpha_q)
  = (1/(2*pi)) integral_C log|XiC(z)| Delta phi(z) dz.    (RJG28)
```

The sum is multiplicity-exact.  This is already a literal completed-theta source identity, since
`XiC` is source-defined; it does not enumerate zeros on the right-hand side.

#### Proof from corpus data

The proved Hadamard identity is

```text
XiC(z) = XiC(0) product_q E_1(z/alpha_q),
E_1(w)=(1-w)exp(w),                                      (RJG29)
```

and the corpus proves `sum_q |alpha_q|^-2 < infinity`.  On any fixed compact set,
`log|E_1(z/alpha_q)|=O(|z|^2/|alpha_q|^2)` uniformly for all sufficiently large `q`.  Hence the
logarithmic product may be integrated termwise against the compactly supported bounded function
`Delta phi`.  The constant `log|XiC(0)|` contributes zero because `integral Delta phi=0`.  In each
genus-one factor, `Re(z/alpha_q)` is harmonic and also contributes zero.  The remaining term is
`log|z-alpha_q|` up to a constant, and the already formalized planar fundamental-solution law gives

```text
integral_C log|z-alpha_q| Delta phi(z) dz = 2*pi*phi(alpha_q).
```

Only finitely many singular factors meet the support, so their local integrability is harmless;
the inverse-square majorant handles the tail.  Summing proves (RJG28). `QED`

### Corollary — exact cutoff landing of the cubic energy `[PAPER-PROVED]`

Fix `a>1/2` and `tau=sigma+iu`, `sigma>0`.  Choose `C^2` compact cutoffs `chi_N`, with
`0<=chi_N<=1` and `chi_N(z)->1`.  The fixed-parameter energy is summable, so dominated convergence
on the counting measure and (RJG28) give

```text
V_(a,sigma)(u)
 = lim_(N->infinity) (1/(2*pi))
     integral_C log|XiC(z)| Delta(chi_N(z) W_(a,tau)(z)) dz.  (RJG30)
```

This is coefficient-exact source landing.  It replaces the unneeded operator identity (RJG26).
The remaining RH-bearing problem is now an unconditional cubic-clock estimate for the explicit
source potentials in (RJG30), not construction of a divisor diagonal.

### Exact bulk curvature

On the open strip `|Im z|<a`, let `beta_a(z)=sqrt(a^2+z^2)` be the branch with positive real part
and `f(z)=exp(-tau beta_a(z))`.  Since `W=|f|^2` and
`f'(z)=-tau*z*f(z)/beta_a(z)`, one has

```text
Delta W_(a,tau)(z)
 = 4 |tau|^2 |z|^2 / |a^2+z^2| * W_(a,tau)(z) >= 0.      (RJG31)
```

At the cubic clock, the bulk curvature carries factor `1+a^6`.  Thus Poincare--Lelong does not
make the estimate soft: it transfers vertical amplification into a large positive curvature.

### Theorem F — positive compact cutoff is impossible `[PAPER-PROVED]`

If `psi : C -> R` is `C^2`, compactly supported, and `Delta psi>=0`, then `psi=0`.  Indeed,
`integral Delta psi=0`; nonnegativity forces `Delta psi=0`, and a compactly supported harmonic
function is zero.  Consequently every nontrivial compact approximation `chi_N W` in (RJG30) has a
signed cutoff-curvature layer.  No Poincare--Lelong proof may discard that layer by positivity or
absolute values.

This is the exact replacement for the earlier diagonal diagnosis:

```text
ordinary explicit formula obstruction = nonholomorphic test,
Poincare--Lelong repair             = nonlinear Xi logarithmic potential,
new unavoidable boundary           = signed cutoff curvature.          (RJG32)
```

The higher noncommutation principle survives in corrected form.  The operations that fail to
commute are not `diagonal` and `trace`, but **holomorphic scalarization** and **positive
realification**.  Poincare--Lelong realifies first and therefore lands the receiver, at the price
of replacing the linear centered current by its nonlinear logarithmic potential.

## 16. Revised successor theorem

For `a_N=N+1`, `u_N=a_N^3`, construct a concrete cutoff schedule in (RJG30) and prove directly from
the completed theta/von-Mangoldt source that the full signed potential pairing tends to zero:

```text
lim_N lim_H (1/(2*pi)) integral_C log|XiC(z)|
  Delta(chi_H(z) W_(a_N,1+iu_N)(z)) dz = 0.              (RJG33)
```

Order of limits and all cutoff faces are part of the theorem.  The bulk/cutoff split must be kept
signed; Theorem F rules out an absolute or positive-cutoff closure.  By (RJG30) and Theorem D,
(RJG33) is sufficient for RH.

## 17. Updated formalization ledger

- `[PAPER-PROVED]`: compact-test Xi Poincare--Lelong identity (RJG28), using existing Hadamard and
  planar fundamental-solution corpus.
- `[PAPER-PROVED]`: exact cutoff source landing (RJG30) and bulk curvature (RJG31).
- `[PAPER-PROVED]`: positive compact-cutoff no-go (Theorem F).
- Lean targets: first close cubic-clock criterion; then formalize (RJG28) as an Xi-specific theorem,
  reusing existing Riesz infrastructure rather than building a new distribution framework.
- RH-bearing source estimate (RJG33): open.

## Log, continued again

- 2026-08-10 — diagonal-coproduct necessity falsified: cubic energy recognized as a linear divisor
  current pairing.
- 2026-08-10 — exact Poincare--Lelong source landing and unavoidable signed cutoff-curvature layer
  proved on paper; obstruction moved from label recovery to nonlinear source-potential control.

---

## 18. Conjecture loop 6 — close Poincare--Lelong by absolute strip-boundary control

### Verdict: `[FAILED — THE SAFE BOUNDARY OUTGROWS EVERY INTERIOR SIGNAL]`

One might replace compact cutoffs by Green's identity on a horizontal strip and bound its boundary
faces absolutely from the Euler-product line.  The cubic receiver excludes this mechanism sharply.

### Theorem G — cubic boundary dominance `[PAPER-PROVED]`

Fix `R>0` and `0<=J<d<1/2`.  For `y in [0,d]`, write

```text
sqrt(a^2+(R+i y)^2)=M_y(a)+i K_y(a),
W_a(R+i y)=exp(-2 M_y(a)+2 a^3 K_y(a)).                 (RJG34)
```

Then

```text
lim_(a->infinity) a^-2 log(W_a(R+i d)/W_a(R+i J))
  = 2 R (d-J) > 0.                                      (RJG35)
```

Indeed `M_y(a)/a -> 1`, while mass charge gives `M_y(a)K_y(a)=R y`; hence

```text
a K_y(a)=R y /(M_y(a)/a) -> R y,
M_y(a)/a^2 -> 0.
```

Dividing the difference of the two logarithms in (RJG34) by `a^2` proves (RJG35). `QED`

Thus any fixed safe horizontal boundary `d` outside an off-line copy at displacement `J` carries
an exponentially larger absolute cubic weight.  Absolute Green-boundary estimates lose before
zero counting, exactly as the scalar absolute tail did in §10.  A viable use of (RJG30) must retain
signed cancellation between bulk and cutoff/boundary curvature; neither Carleman determinant growth
nor an Euler-line modulus bound can be inserted termwise.

This identifies one principle behind both failures:

```text
faithful cubic amplification is ordered by transverse displacement;
every enclosing absolute boundary has strictly larger exponential type.  (RJG36)
```

The remaining source theorem (RJG33) must therefore be an exact signed Ward/Green identity, not a
growth estimate for `log|XiC|` on the enclosing strip.

## 19. Formalization ledger after boundary audit

- `[PAPER-PROVED]`: cubic safe-boundary dominance (RJG35).
- `[FAILED]`: absolute strip-boundary closure of the Poincare--Lelong landing.
- Surviving core: signed bulk--boundary cancellation for the literal completed source.

---

## 20. Conjecture loop 7 — transverse cutoff faces are intrinsically non-arithmetic

### Verdict: `[FAILED — MOVE THEM INTO THE PROVED ZERO-FREE COLLAR]`

The Xi divisor lies in `|Im z|<1/2` in the centered spectral coordinate.  Therefore choose once and
for all

```text
1/2 < d < a.
```

The mass branch is holomorphic on `|Im z|<a`, while both horizontal faces `Im z=+-d` lie outside
the divisor.  In the original zeta coordinate `s=1/2+i z`, the lower face is the safe Euler line
`Re s=1/2+d>1`; Xi evenness and Schwarz symmetry carry the upper face to the same line.  Thus the
transverse cutoff is not an unknown divisor face.  It can be replaced by an exact safe-line Green
current.

### Theorem H — safe-strip Green landing `[PAPER-PROVED]`

Put

```text
U(z)=log|XiC(z)|,
S_d={z=x+i y: |y|<d}.
```

For fixed `a>d`, `sigma>0`, and real `u`, the mass weight `W=W_(a,sigma+iu)` and its first two
derivatives decay exponentially as `|x|->infinity` on the closed strip; `U` and its first
derivatives have only order-one completed-Xi growth on the two zero-free faces.  Green's second
identity, first on finite rectangles and then at infinite width, gives

```text
2*pi V_(a,sigma)(u)
 = integral_(S_d) U Delta W dA
   + integral_(boundary S_d) (W partial_n U-U partial_n W) dx.  (RJG37)
```

The divisor contribution is exactly `2*pi sum_q W(alpha_q)`, including multiplicities; every XiC
zero lies inside `S_d`, and the vertical rectangle faces vanish.  This is (RJG28) without a
transverse compact cutoff.

Let `c=1/2+d` and write on the upper face

```text
sqrt(a^2+(x+i d)^2)=M+i K,
A=(x+i d)/(M+i K)=A_r+i A_i,
U_c(x)=log|xi(c+i x)|.
```

Xi evenness and Schwarz symmetry give the same `U_c` on both faces and identify their common
outward normal derivative with `partial_c U_c`.  Moreover

```text
W_+ + W_- = 2 exp(-2 sigma M) cosh(2uK),

partial_n W_+ + partial_n W_-
 = 4 exp(-2 sigma M)
     [sigma A_i cosh(2uK)+u A_r sinh(2uK)].              (RJG38)
```

Consequently the complete boundary term in (RJG37) is the single safe-line current

```text
integral_R {
  2 exp(-2 sigma M) cosh(2uK) partial_c U_c(x)
  -4 U_c(x) exp(-2 sigma M)
     [sigma A_i cosh(2uK)+u A_r sinh(2uK)]
} dx.                                                    (RJG39)
```

On `c>1`, both `U_c` and `partial_c U_c` have coefficient-exact Gamma/rational plus absolutely
convergent Euler representations: `log zeta` contributes `Lambda(n)/log(n)`, while its derivative
contributes `-Lambda(n)`.  Hence (RJG39) is a literal prime--Gamma source current, not divisor-fed
notation.

### Hostile audit

- (RJG37) is still an identity, not an estimate.  Its interior term
  `integral U Delta W` contains the nonlinear completed-Xi potential and carries the RH-bearing
  cancellation.
- Theorem G forbids taking absolute values in (RJG39): its two hyperbolic boundary channels have
  larger cubic type than every interior off-line copy.
- The advance is exact localization: all non-arithmetic transverse cutoff ambiguity is removed,
  and the full boundary is now a known safe-line Euler--Gamma functional.
- The remaining producer is one signed bulk-to-boundary Ward identity proving cancellation of the
  positive curvature `Delta W` against (RJG39) at the cubic clock.

## 21. Revised open core

Prove, directly from the centered theta/von-Mangoldt source and without absolute values,

```text
integral_(S_d) U Delta W_(a,1+i a^3) dA
  + BoundaryEulerGamma_(a,d) -> 0                       (RJG40)
```

as `a->infinity`, where `BoundaryEulerGamma` is exactly (RJG39).  By (RJG37) and Theorem D this
proves RH.  Any valid proof must exhibit the cancellation before estimating the two terms; each
term separately has the enclosing-boundary exponential type from Theorem G.

## Log, continued once more

- 2026-08-10 — transverse cutoff ambiguity removed: safe-strip Green identity reduces both
  horizontal faces to one absolutely convergent Euler--Gamma line and isolates a single signed
  nonlinear bulk cancellation (RJG40).

## 22. Conjecture loop 8 — source-holomorphic reciprocal heat receiver

The Poincare--Lelong landing changed the diagnosis but did not yet remove the nonlinear bulk.
Instead of forcing the nonholomorphic mass energy through `log|XiC|`, pass to the fixed compact
theta-source inverse

```text
B = thetaKernelOperator.
```

Its nonzero spectral values are, with full algebraic multiplicity,

```text
mu_q = -(alpha_q)^(-1),                                  (RJG41)
```

and `B` is defined from the theta density before any Xi divisor is enumerated.  The reciprocal
square is therefore the correct entire coordinate at the compact accumulation point:

```text
mu |-> exp(-i t mu^2),                                   (RJG42)
```

whereas the mass square-root receiver has an essential singularity when rewritten at `mu=0`.

### First conjecture

Use the Hilbert--Schmidt norm of `B exp(-i t B^2)` as the positive source lift of the reciprocal
spectral energy.

### Verdict: `[TOO LARGE; POSITIVE SURVIVOR BELOW]`

The norm sees any quasinilpotent radical and every nonorthogonality of the root spaces, neither of
which belongs to the Xi divisor.  Subexponential growth of that full Hilbert--Schmidt orbit is a
strictly stronger demand than control of the nonzero spectrum.  The compact source already has a
canonical finite observation which removes this excess: its rank-two pinned boundary defect.

## 23. The rank-two observed square-flow law

Let

```text
C = pinnedBoundaryCLM,
O(t) = C exp(-i t B^2),        t>=0.                       (RJG43)
```

The operator `C` is source-defined, has range spanned by the constant and centered-coordinate
vectors, and has nonzero eigenvalues `+-1/sqrt(12)`.  Equivalently it reads only the two moments

```text
m(g)=integral_0^1 g,
r(g)=integral_0^1 t g.                                   (RJG44)
```

Thus `O(t)` has rank at most two for every `t`; it is a two-channel boundary observation, not a
divisor Hilbert sum.

### Theorem I — every theta divisor mode is boundary-observable `[PAPER-PROVED]`

For the canonical source eigenvector `f_q=thetaXiDivisorEigenvector(q)`, the corpus gives

```text
B f_q = mu_q f_q,
m(f_q)=sqrt(thetaSource.mass) != 0.                        (RJG45)
```

Since

```text
C g=0 iff m(g)=0 and r(g)=0,
```

one has `C f_q != 0` for every multiplicity copy, on-line or off-line.  Functional calculus then
gives the exact observed mode law

```text
O(t) f_q = exp(-i t mu_q^2) C f_q,
norm(O(t) f_q)=exp(t Im(mu_q^2)) norm(C f_q).              (RJG46)
```

No diagonal extraction, root-vector orthogonality, simplicity, or completeness is used.

### Theorem J — exact boundary growth exponent `[PAPER-PROVED]`

Put `A=-i B^2` and

```text
omega_boundary = lim_(t->infinity) log(norm(O(t)))/t.
```

Then the limit exists and

```text
omega_boundary
 = max(0, sup_(mu in spectrum(B), mu!=0) Im(mu^2))
 = max(0, sup_q Im(alpha_q^(-2))).                         (RJG47)
```

Proof: for every bounded operator `A`, spectral mapping and Gelfand's formula give

```text
lim_(t->infinity) log(norm(exp(t A)))/t
  = sup_{lambda in spectrum(A)} Re(lambda).                (RJG48)
```

Indeed this is Gelfand's formula for integer `t` applied to `exp(A)`, while the bounded remainder
`exp((t-floor(t))A)` handles real `t`.  Hence

```text
limsup log(norm(O(t)))/t
 <= max(0, sup Im(mu^2)).                                  (RJG49)
```

Conversely (RJG46) gives, for every `q`,

```text
norm(O(t))
 >= exp(t Im(mu_q^2)) norm(C f_q)/norm(f_q).               (RJG50)
```

If the spectral bound is positive, compactness makes it an attained nonzero eigenvalue; (RJG50)
matches the upper exponent.  If it is zero, nonemptiness of the Xi divisor and (RJG45)--(RJG50)
give the matching lower exponent zero.  This proves (RJG47).

### Corollary — source-defined RH equivalence `[PAPER-PROVED]`

Conjugation of the Xi divisor sends `mu_q^2` to its complex conjugate.  Therefore the right side of
(RJG47) vanishes exactly when every reciprocal square is real.  The open-strip reciprocal-square
criterion already proves that this is equivalent to every `alpha_q` being real.  Hence

```text
RH
 iff omega_boundary=0
 iff for every epsilon>0 there is M_epsilon such that
      norm(C exp(-i t B^2)) <= M_epsilon exp(epsilon t)
      for every t>=0.                                     (RJG51)
```

Unlike (RJG19), every object in the last condition is defined directly from the fixed theta
source.  Unlike (RJG37), no logarithmic Xi potential or signed two-dimensional bulk remains.

## 24. Higher universal principle revised again

The mass-cone obstruction is a coordinate shadow.  In the original divisor coordinate `alpha`,
transverse displacement must be converted to growth by a moving mass and a cubic clock, which
creates a larger enclosing Euler boundary.  The compact inverse has already performed the needed
renormalization:

```text
alpha transverse displacement
  -> Im(alpha^(-2))
  -> exponential type of exp(-i t B^2)
  -> two pinned boundary moments.                          (RJG52)
```

The universal principle is **unstable spectrum equals observable boundary type**.  A full Hilbert
metric is unnecessary.  It is enough that one finite source boundary observation see every
unstable root space; (RJG45) proves that exact observability here.

This is genuine new route knowledge, not an RH proof.  General semigroup spectral mapping is
classical.  The source-specific content is the splice of the fixed Hedenmalm compact inverse, its
multiplicity-exact Xi spectrum, and the rank-two pinned monopole observation.  Hedenmalm's 2026
paper constructs the theta differential-pair eigenproblem and discusses pair self-adjointness; the
targeted primary-source search found no reciprocal-square observed-flow law or rank-two growth
formula.  Search noncollision is not a priority claim.  Status: `[NOVELTY UNVERIFIED]`.

## 25. New exact producer, after removing the Green bulk

The Route T open core can now be stated without a divisor sum:

```text
for every epsilon>0, prove from the theta/von-Mangoldt source that
norm(C exp(-i t B^2)) = O_epsilon(exp(epsilon t)).          (RJG53)
```

Because `C` has rank two, this is equivalent to subexponential growth of two adjoint source
orbits issued from the constant and centered-coordinate boundary vectors.  A proposed proof must
estimate those two vectors before spectral decomposition.  Assuming spectral reality,
self-adjointness, reciprocal-square positivity, or (RJG53) itself is rejected as circular.

## Log, source-flow pivot

- 2026-08-10 — replaced nonlinear Poincare--Lelong bulk by exact rank-two theta-boundary square
  flow; paper-proved full exponential-type law (RJG47) and source-defined RH equivalence (RJG51).
